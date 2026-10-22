//! Prover: commit trace, constraint quotient, FRI randomizer, OOD, DEEP, FRI, queries.
//!
//! With n = trace_len, H the size-n trace domain and Z_H(x) = x^n - 1, the commitments are
//!
//! 1. trace:      every column T_c(x), as one Merkle leaf per LDE row
//! 2. quotient:   q(x) = C(x) / Z_H(x), where C(x) = sum_k alpha^k * constraint_k(T(x))
//!    (`composition`)
//! 3. randomizer: a random polynomial R(x) that masks FRI
//!
//! The identity being proven is C(x) = q(x) * Z_H(x). It holds with q of low degree iff every
//! constraint is zero on every row of H. The verifier checks it at a random point z, and DEEP +
//! FRI tie the values at z to the committed codewords.

use rayon::prelude::*;
use sha2::{Digest, Sha256};
use toyni::babybear::BabyBear;
use toyni::ext::Ext;
use toyni::math::domain::BabyBearDomain;
use toyni::math::fri::fri_fold_ext;
use toyni::math::mask::mask_poly_base;
use toyni::merkle::{MerkleProof, MerkleTree};
use toyni::transcript::FiatShamirTranscript;

use crate::air::{self, AuthRecord, Row, NUM_COLS, NUM_CONSTRAINTS, NUM_PUBLIC};
use crate::poseidon1::{AirField, Poseidon1};

pub const NUM_QUERIES: usize = 132;
pub const BLOWUP: usize = 16;
pub const CONSTRAINT_DEGREE: usize = 3;
/// Blinding coefficients per witness column (X + Z_H * R).
pub const MASK_DEGREE: usize = 2 * NUM_QUERIES + 4;
pub const COSET_SHIFT: u64 = 7;
/// Smallest trace with FRI rate <= 1/4; at 256 the rate is 1/2 and forgeable (AUTH-01).
pub const MIN_ROWS: usize = 512;

/// Power of two above deg(DEEP) = max(deg T, deg Q) < 3(n + MASK) - n.
pub fn fri_degree_bound(trace_len: usize) -> usize {
    (CONSTRAINT_DEGREE * (trace_len + MASK_DEGREE) - trace_len).next_power_of_two()
}

pub fn trace_len_for(num_auths: usize) -> usize {
    num_auths.next_power_of_two().max(MIN_ROWS)
}

#[derive(Debug, Clone)]
pub struct RowOpening {
    pub index: usize,
    pub values: Vec<BabyBear>,
    pub proof: MerkleProof,
}

#[derive(Debug, Clone)]
pub struct ScalarOpening {
    pub index: usize,
    pub value: Ext,
    pub proof: MerkleProof,
}

/// One FRI leaf: the two values a fold combines, f(y) at `index` and f(-y) at `index + half`.
#[derive(Debug, Clone)]
pub struct FriPairOpening {
    pub index: usize,
    pub values: [Ext; 2],
    pub proof: MerkleProof,
}

#[derive(Debug, Clone)]
pub struct QueryProof {
    pub index: usize,
    pub trace_opening: RowOpening,
    pub quotient_opening: ScalarOpening,
    pub randomizer_opening: ScalarOpening,
    /// `fri_pairs[k]` opens FRI layer k (layer 0 = DEEP), one per fold.
    pub fri_pairs: Vec<FriPairOpening>,
}

#[derive(Debug)]
pub struct AuthProof {
    pub num_auths: usize,
    pub trace_len: usize,
    pub lde_size: usize,
    pub trace_commitment: Vec<u8>,
    pub quotient_commitment: Vec<u8>,
    pub randomizer_commitment: Vec<u8>,
    pub trace_at_z: Vec<Ext>,
    pub q_z: Ext,
    pub fri_commitments: Vec<Vec<u8>>,
    pub fri_final_layer: Vec<Ext>,
    pub query_proofs: Vec<QueryProof>,
}

pub(crate) fn absorb_statement(transcript: &mut FiatShamirTranscript, records: &[AuthRecord], trace_len: usize) {
    transcript.absorb(b"toyni-auth-v1");
    transcript.absorb_field(BabyBear::from_u32(records.len() as u32));
    transcript.absorb_field(BabyBear::from_u32(trace_len as u32));
    for r in records {
        for v in r.public_values() {
            transcript.absorb_field(v);
        }
    }
}

pub(crate) fn public_columns(p: &Poseidon1, records: &[AuthRecord], trace_len: usize) -> Vec<Vec<BabyBear>> {
    let (pad, _) = air::padding(p);
    let mut cols = vec![Vec::with_capacity(trace_len); NUM_PUBLIC];
    for i in 0..trace_len {
        let vals = records.get(i).unwrap_or(&pad).public_values();
        for (c, v) in cols.iter_mut().zip(vals) {
            c.push(v);
        }
    }
    cols
}

pub(crate) fn constraint_weights(alpha: Ext) -> Vec<Ext> {
    let mut w = Vec::with_capacity(NUM_CONSTRAINTS);
    let mut cur = Ext::one();
    for _ in 0..NUM_CONSTRAINTS {
        w.push(cur);
        cur = cur * alpha;
    }
    w
}

/// C(row) = sum_k weights[k] * constraint_k(row), with weights[k] = alpha^k.
pub(crate) fn composition<F: AirField>(p: &Poseidon1, row: &Row<F>, weights: &[Ext]) -> Ext {
    air::constraints(p, row).into_iter().zip(weights).fold(Ext::zero(), |acc, (c, &w)| acc + c.scaled_by(w))
}

/// Z_H(x) = x^n - 1: zero exactly on the trace domain.
fn vanishing(x: BabyBear, trace_len: usize) -> BabyBear {
    x.pow(trace_len as u64) - BabyBear::one()
}

pub(crate) fn derive_z(transcript: &mut FiatShamirTranscript) -> Ext {
    loop {
        let z = transcript.squeeze_ext_challenge();
        if !z.is_base() {
            return z;
        }
    }
}

pub fn prove(records: &[AuthRecord], secrets: &[[BabyBear; 4]]) -> AuthProof {
    assert_eq!(records.len(), secrets.len());
    assert!(!records.is_empty());
    let t_total = std::time::Instant::now();
    let p = Poseidon1::new();
    let trace_len = trace_len_for(records.len());
    let lde_size = trace_len * BLOWUP;
    assert!(lde_size >= 4 * fri_degree_bound(trace_len), "FRI rate must be <= 1/4");

    let domain = BabyBearDomain::new(trace_len);
    let extended_domain = BabyBearDomain::new(lde_size);
    let shifted_domain = extended_domain.get_coset(BabyBear::new(COSET_SHIFT));
    let shifted_elements = shifted_domain.elements();

    let t = std::time::Instant::now();
    let (pad, pad_x) = air::padding(&p);
    let rows: Vec<Vec<BabyBear>> = (0..trace_len)
        .into_par_iter()
        .map(|i| match records.get(i) {
            Some(r) => air::trace_row(&p, r, secrets[i]),
            None => air::trace_row(&p, &pad, pad_x),
        })
        .collect();
    let columns: Vec<Vec<BabyBear>> =
        (0..NUM_COLS).into_par_iter().map(|c| rows.iter().map(|row| row[c]).collect()).collect();
    drop(rows);
    eprintln!("[auth-prove] witness: {} rows x {} cols in {:.2?}", trace_len, NUM_COLS, t.elapsed());

    let t = std::time::Instant::now();
    // Only witness columns are masked; public columns are bound by the verifier.
    let trace_polys: Vec<Vec<BabyBear>> = columns
        .par_iter()
        .enumerate()
        .map(|(c, col)| {
            let mut poly = domain.ifft(col);
            if c >= NUM_PUBLIC {
                mask_poly_base(&mut poly, trace_len, MASK_DEGREE, &mut rand::thread_rng());
            }
            poly
        })
        .collect();
    let trace_lde: Vec<Vec<BabyBear>> = trace_polys.par_iter().map(|c| shifted_domain.fft(c)).collect();
    eprintln!("[auth-prove] trace IFFT + LDE in {:.2?}", t.elapsed());
    let t = std::time::Instant::now();
    let trace_tree = build_row_merkle_tree(&trace_lde, lde_size);
    let trace_commitment = trace_tree.root().unwrap();
    eprintln!("[auth-prove] trace merkle in {:.2?}", t.elapsed());

    let mut transcript = FiatShamirTranscript::new();
    absorb_statement(&mut transcript, records, trace_len);
    transcript.absorb_commitment(&trace_commitment);

    let alpha = transcript.squeeze_ext_challenge();
    let weights = constraint_weights(alpha);
    let t = std::time::Instant::now();
    // q(x) = C(x) / Z_H(x) at every LDE point x, from the LDE row at x.
    let mut q_evals = vec![Ext::zero(); lde_size];
    q_evals.par_iter_mut().enumerate().for_each_init(
        || vec![BabyBear::zero(); NUM_COLS],
        |cells, (i, q)| {
            for (c, v) in cells.iter_mut().enumerate() {
                *v = trace_lde[c][i];
            }
            let c_x = composition(&p, &Row::from_cells(cells), &weights);
            *q = c_x.mul_base(vanishing(shifted_elements[i], trace_len).inverse());
        },
    );
    eprintln!("[auth-prove] constraint quotient over {} rows in {:.2?}", lde_size, t.elapsed());
    let t = std::time::Instant::now();
    let q_tree = build_scalar_merkle_tree_ext(&q_evals);
    let quotient_commitment = q_tree.root().unwrap();
    eprintln!("[auth-prove] quotient merkle in {:.2?}", t.elapsed());
    transcript.absorb_commitment(&quotient_commitment);

    // Zero-knowledge: a uniformly random Ext polynomial of the FRI degree bound, committed
    // before the DEEP coefficients and added to the DEEP layer, so FRI reveals nothing.
    let t = std::time::Instant::now();
    let r_limbs: Vec<Vec<BabyBear>> = (0..4)
        .into_par_iter()
        .map(|_| {
            let mut rng = rand::thread_rng();
            let coeffs: Vec<BabyBear> = (0..fri_degree_bound(trace_len)).map(|_| BabyBear::random(&mut rng)).collect();
            shifted_domain.fft(&coeffs)
        })
        .collect();
    let r_evals: Vec<Ext> = (0..lde_size)
        .into_par_iter()
        .map(|i| Ext::new([r_limbs[0][i], r_limbs[1][i], r_limbs[2][i], r_limbs[3][i]]))
        .collect();
    drop(r_limbs);
    let r_tree = build_scalar_merkle_tree_ext(&r_evals);
    let randomizer_commitment = r_tree.root().unwrap();
    transcript.absorb_commitment(&randomizer_commitment);
    eprintln!("[auth-prove] randomizer in {:.2?}", t.elapsed());

    let t = std::time::Instant::now();
    let z = derive_z(&mut transcript);
    let trace_at_z: Vec<Ext> = trace_polys.par_iter().map(|c| z.eval_base_at_ext(c)).collect();
    let q_coeffs = shifted_domain.ifft_ext(&q_evals);
    let q_z = z.eval_ext_at_ext(&q_coeffs);
    let c_z = composition(&p, &Row::from_cells(&trace_at_z), &weights);
    let z_h_z = z.pow_u128(trace_len as u128) - Ext::one();
    assert_eq!(c_z, q_z * z_h_z, "OOD constraint check failed");
    for &v in &trace_at_z {
        transcript.absorb_ext(v);
    }
    transcript.absorb_ext(q_z);
    eprintln!("[auth-prove] OOD in {:.2?}", t.elapsed());

    let deep_coeffs: Vec<Ext> = (0..NUM_COLS + 2).map(|_| transcript.squeeze_ext_challenge()).collect();
    // DEEP polynomial: each committed polynomial P minus its claimed value at z, divided by (x - z).
    // This divides evenly only if the claimed value is correct, so FRI on d checks the values at z.
    //
    //   d(x) =   a_0 * (T_0(x) - T_0(z)) / (x - z)      one term per trace column T_c
    //          + ...
    //          + a_q * (q(x)   - q(z))   / (x - z)      the quotient
    //          + a_r * R(x)                             random mask (zero knowledge)
    //
    // a_* are random coefficients (`deep_coeffs`). Below, all "value at z" parts are summed once
    // into `k_const`, so the division by (x - z) happens once per point.
    let c_r = deep_coeffs[NUM_COLS + 1];
    let mut k_const = deep_coeffs[NUM_COLS] * q_z;
    for c in 0..NUM_COLS {
        k_const = k_const + deep_coeffs[c] * trace_at_z[c];
    }
    let t = std::time::Instant::now();
    // Per row chunk, stream columns sequentially (column-major data).
    const CHUNK: usize = 1 << 12;
    let mut d_evals: Vec<Ext> = vec![Ext::zero(); lde_size];
    d_evals.par_chunks_mut(CHUNK).enumerate().for_each(|(ci, out)| {
        let start = ci * CHUNK;
        let end = start + out.len();
        for (j, a) in out.iter_mut().enumerate() {
            *a = deep_coeffs[NUM_COLS] * q_evals[start + j] - k_const;
        }
        for c in 0..NUM_COLS {
            let coeff = deep_coeffs[c];
            for (a, &t) in out.iter_mut().zip(&trace_lde[c][start..end]) {
                *a = *a + coeff.mul_base(t);
            }
        }
        for (j, a) in out.iter_mut().enumerate() {
            *a = *a * (Ext::from(shifted_elements[start + j]) - z).inverse() + c_r * r_evals[start + j];
        }
    });
    eprintln!("[auth-prove] DEEP in {:.2?}", t.elapsed());

    let t = std::time::Instant::now();
    let mut fri_layers: Vec<Vec<Ext>> = vec![d_evals.clone()];
    let tree0 = build_pair_merkle_tree(&d_evals);
    let mut fri_commitments = vec![tree0.root().unwrap()];
    transcript.absorb_commitment(&fri_commitments[0]);
    let mut fri_trees = vec![tree0];
    let mut current = d_evals;
    let mut xs = shifted_elements.clone();
    let final_layer_size = lde_size / fri_degree_bound(trace_len);
    while current.len() > final_layer_size {
        let beta = transcript.squeeze_ext_challenge();
        let folded = fri_fold_ext(&current, &xs, beta);
        xs.truncate(folded.len());
        for x in &mut xs {
            *x = *x * *x;
        }
        // The final layer is sent whole and never opened, so it keeps one value per leaf.
        let tree = if folded.len() > final_layer_size {
            build_pair_merkle_tree(&folded)
        } else {
            build_scalar_merkle_tree_ext(&folded)
        };
        let root = tree.root().unwrap();
        transcript.absorb_commitment(&root);
        fri_commitments.push(root);
        fri_trees.push(tree);
        fri_layers.push(folded.clone());
        current = folded;
    }
    let fri_final_layer = current;
    eprintln!("[auth-prove] FRI in {:.2?} ({} layers)", t.elapsed(), fri_layers.len());

    let query_indices = transcript.squeeze_indices(NUM_QUERIES, lde_size);
    let query_proofs = query_indices
        .iter()
        .map(|&qi| {
            let mut lo = qi;
            let fri_pairs = (0..fri_layers.len() - 1)
                .map(|k| {
                    lo %= fri_layers[k].len() / 2;
                    open_pair(&fri_trees[k], &fri_layers[k], lo)
                })
                .collect();
            QueryProof {
                index: qi,
                trace_opening: RowOpening {
                    index: qi,
                    values: (0..NUM_COLS).map(|c| trace_lde[c][qi]).collect(),
                    proof: trace_tree.get_proof(qi).unwrap(),
                },
                quotient_opening: open_scalar(&q_tree, &q_evals, qi),
                randomizer_opening: open_scalar(&r_tree, &r_evals, qi),
                fri_pairs,
            }
        })
        .collect();
    eprintln!("[auth-prove] TOTAL {:.2?}", t_total.elapsed());

    AuthProof {
        num_auths: records.len(),
        trace_len,
        lde_size,
        trace_commitment,
        quotient_commitment,
        randomizer_commitment,
        trace_at_z,
        q_z,
        fri_commitments,
        fri_final_layer,
        query_proofs,
    }
}

pub(crate) fn row_leaf(values: &[BabyBear]) -> Vec<u8> {
    let mut h = Sha256::new();
    for v in values {
        h.update(v.to_bytes());
    }
    h.finalize().to_vec()
}

fn build_row_merkle_tree(cols: &[Vec<BabyBear>], lde_size: usize) -> MerkleTree {
    let leaves = (0..lde_size)
        .into_par_iter()
        .map_init(
            || vec![BabyBear::zero(); cols.len()],
            |row, i| {
                for (c, v) in row.iter_mut().enumerate() {
                    *v = cols[c][i];
                }
                row_leaf(row)
            },
        )
        .collect();
    MerkleTree::new(leaves)
}

pub(crate) fn build_scalar_merkle_tree_ext(evals: &[Ext]) -> MerkleTree {
    MerkleTree::new(evals.iter().map(|v| v.to_bytes().to_vec()).collect())
}

fn open_scalar(tree: &MerkleTree, evals: &[Ext], index: usize) -> ScalarOpening {
    ScalarOpening { index, value: evals[index], proof: tree.get_proof(index).unwrap() }
}

pub fn fri_pair_leaf(values: &[Ext; 2]) -> Vec<u8> {
    [values[0].to_bytes(), values[1].to_bytes()].concat()
}

/// A FRI layer as len/2 leaves; leaf j = (layer[j], layer[j + len/2]), the values at y and -y.
pub fn build_pair_merkle_tree(layer: &[Ext]) -> MerkleTree {
    let half = layer.len() / 2;
    MerkleTree::new((0..half).map(|j| fri_pair_leaf(&[layer[j], layer[j + half]])).collect())
}

fn open_pair(tree: &MerkleTree, layer: &[Ext], lo: usize) -> FriPairOpening {
    let half = layer.len() / 2;
    FriPairOpening { index: lo, values: [layer[lo], layer[lo + half]], proof: tree.get_proof(lo).unwrap() }
}

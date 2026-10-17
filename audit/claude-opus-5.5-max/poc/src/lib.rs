//! Malicious-prover toolkit for the auth-air PoCs: `Forger` replays the verifier's
//! transcript but lets the caller choose every prover message.

pub mod ktree;

use auth_air::air::{self, AuthRecord, NUM_COLS, NUM_CONSTRAINTS, NUM_PUBLIC};
use auth_air::poseidon1::Poseidon1;
use auth_air::prover::{
    fri_degree_bound, trace_len_for, AuthProof, QueryProof, RowOpening, ScalarOpening, BLOWUP,
    COSET_SHIFT, NUM_QUERIES,
};
use sha2::{Digest, Sha256};
use toyni::babybear::BabyBear;
use toyni::ext::Ext;
use toyni::math::domain::BabyBearDomain;
use toyni::math::fri::fri_fold_ext;
use toyni::merkle::MerkleTree;
use toyni::transcript::FiatShamirTranscript;

pub const P: u32 = BabyBear::PRIME;
/// 2^32 mod p: the error a single u32 wrap introduces into BabyBear arithmetic.
pub const DELTA: u32 = ((1u64 << 32) % P as u64) as u32;

pub struct Forger {
    pub p: Poseidon1,
    pub n: usize,
    pub lde: usize,
    pub domain: BabyBearDomain,
    pub shifted_domain: BabyBearDomain,
    pub xs: Vec<BabyBear>,
    transcript: FiatShamirTranscript,
    trace_lde: Option<Vec<Vec<BabyBear>>>,
    trace_tree: Option<MerkleTree>,
    trace_root: Vec<u8>,
    q_evals: Option<Vec<Ext>>,
    q_tree: Option<MerkleTree>,
    q_root: Vec<u8>,
    r_evals: Vec<Ext>,
    r_tree: Option<MerkleTree>,
    r_root: Vec<u8>,
    pub alpha: Ext,
    pub z: Ext,
    trace_at_z: Vec<Ext>,
    q_z: Ext,
    pub deep_coeffs: Vec<Ext>,
}

impl Forger {
    /// Starts the transcript exactly like `prover::absorb_statement`, over the
    /// raw bytes of `records` (as the verifier does).
    pub fn new(records: &[AuthRecord]) -> Self {
        let n = trace_len_for(records.len());
        let lde = n * BLOWUP;
        let domain = BabyBearDomain::new(n);
        let shifted_domain = BabyBearDomain::new(lde).get_coset(BabyBear::new(COSET_SHIFT));
        let xs = shifted_domain.elements();
        let mut transcript = FiatShamirTranscript::new();
        transcript.absorb(b"toyni-auth-v1");
        transcript.absorb_field(BabyBear::from_u32(records.len() as u32));
        transcript.absorb_field(BabyBear::from_u32(n as u32));
        for r in records {
            for v in r.public_values() {
                transcript.absorb_field(v);
            }
        }
        Self {
            p: Poseidon1::new(),
            n,
            lde,
            domain,
            shifted_domain,
            xs,
            transcript,
            trace_lde: None,
            trace_tree: None,
            trace_root: Vec::new(),
            q_evals: None,
            q_tree: None,
            q_root: Vec::new(),
            r_evals: Vec::new(),
            r_tree: None,
            r_root: Vec::new(),
            alpha: Ext::zero(),
            z: Ext::zero(),
            trace_at_z: Vec::new(),
            q_z: Ext::zero(),
            deep_coeffs: Vec::new(),
        }
    }

    /// Commits an arbitrary trace LDE (column-major, `lde` values per column).
    pub fn commit_trace(&mut self, trace_lde: Vec<Vec<BabyBear>>) -> Ext {
        assert_eq!(trace_lde.len(), NUM_COLS);
        let tree = row_tree(&trace_lde, self.lde);
        self.trace_root = tree.root().unwrap();
        self.transcript.absorb_commitment(&self.trace_root);
        self.trace_lde = Some(trace_lde);
        self.trace_tree = Some(tree);
        self.alpha = self.transcript.squeeze_ext_challenge();
        self.alpha
    }

    /// Commits arbitrary quotient values and derives z.
    pub fn commit_quotient(&mut self, q_evals: Vec<Ext>) -> Ext {
        assert_eq!(q_evals.len(), self.lde);
        let tree = ext_tree(&q_evals);
        self.q_root = tree.root().unwrap();
        self.transcript.absorb_commitment(&self.q_root);
        self.q_evals = Some(q_evals);
        self.q_tree = Some(tree);
        // A zero FRI randomizer; a malicious prover may commit any.
        self.r_evals = vec![Ext::zero(); self.lde];
        let r_tree = ext_tree(&self.r_evals);
        self.r_root = r_tree.root().unwrap();
        self.transcript.absorb_commitment(&self.r_root);
        self.r_tree = Some(r_tree);
        self.z = loop {
            let z = self.transcript.squeeze_ext_challenge();
            if !z.is_base() {
                break z;
            }
        };
        self.z
    }

    /// Sends the out-of-domain values (any encoding) and returns the DEEP coefficients.
    pub fn send_ood(&mut self, trace_at_z: Vec<Ext>, q_z: Ext) -> Vec<Ext> {
        assert_eq!(trace_at_z.len(), NUM_COLS);
        for &v in &trace_at_z {
            self.transcript.absorb_ext(v);
        }
        self.transcript.absorb_ext(q_z);
        self.trace_at_z = trace_at_z;
        self.q_z = q_z;
        self.deep_coeffs = (0..NUM_COLS + 2).map(|_| self.transcript.squeeze_ext_challenge()).collect();
        self.deep_coeffs.clone()
    }

    pub fn trace_lde(&self) -> &[Vec<BabyBear>] {
        self.trace_lde.as_ref().unwrap()
    }

    pub fn q_evals(&self) -> &[Ext] {
        self.q_evals.as_ref().unwrap()
    }

    /// The honest DEEP layer of the committed columns, using the given
    /// (field-correct) OOD values.
    pub fn honest_deep(&self, tau: &[Ext], q_z: Ext) -> Vec<Ext> {
        let c = &self.deep_coeffs;
        let mut k = c[NUM_COLS] * q_z;
        for i in 0..NUM_COLS {
            k = k + c[i] * tau[i];
        }
        let trace = self.trace_lde();
        let q = self.q_evals();
        (0..self.lde)
            .map(|i| {
                let mut acc = c[NUM_COLS] * q[i] - k;
                for col in 0..NUM_COLS {
                    acc = acc + c[col].mul_base(trace[col][i]);
                }
                acc * (Ext::from(self.xs[i]) - self.z).inverse()
            })
            .collect()
    }

    /// Commits `layer0` as the DEEP layer, runs FRI and answers the queries.
    pub fn finish(mut self, layer0: Vec<Ext>) -> AuthProof {
        assert_eq!(layer0.len(), self.lde);
        let mut layers = vec![layer0];
        let mut trees = vec![ext_tree(&layers[0])];
        let mut fri_commitments = vec![trees[0].root().unwrap()];
        self.transcript.absorb_commitment(&fri_commitments[0]);
        let mut xs = self.xs.clone();
        let final_size = self.lde / fri_degree_bound(self.n);
        while layers.last().unwrap().len() > final_size {
            let beta = self.transcript.squeeze_ext_challenge();
            let folded = fri_fold_ext(layers.last().unwrap(), &xs, beta);
            xs.truncate(folded.len());
            for x in &mut xs {
                *x = *x * *x;
            }
            let tree = ext_tree(&folded);
            let root = tree.root().unwrap();
            self.transcript.absorb_commitment(&root);
            fri_commitments.push(root);
            trees.push(tree);
            layers.push(folded);
        }
        let half0 = self.lde / 2;
        let trace_lde = self.trace_lde.as_ref().unwrap();
        let trace_tree = self.trace_tree.as_ref().unwrap();
        let q_evals = self.q_evals.as_ref().unwrap();
        let q_tree = self.q_tree.as_ref().unwrap();
        let (r_tree, r_evals) = (self.r_tree.as_ref().unwrap(), &self.r_evals);
        let query_proofs = self
            .transcript
            .squeeze_indices(NUM_QUERIES, self.lde)
            .into_iter()
            .map(|qi| {
                let mut idx = qi;
                let fri_openings = (1..layers.len() - 1)
                    .map(|l| {
                        let half = layers[l].len() / 2;
                        idx %= half;
                        (open(&trees[l], &layers[l], idx), open(&trees[l], &layers[l], idx + half))
                    })
                    .collect();
                QueryProof {
                    index: qi,
                    trace_opening: RowOpening {
                        index: qi,
                        values: (0..NUM_COLS).map(|c| trace_lde[c][qi]).collect(),
                        proof: trace_tree.get_proof(qi).unwrap(),
                    },
                    quotient_opening: open(q_tree, q_evals, qi),
                    randomizer_opening: open(r_tree, r_evals, qi),
                    deep_opening: open(&trees[0], &layers[0], qi),
                    deep_opening_pair: open(&trees[0], &layers[0], qi ^ half0),
                    fri_openings,
                }
            })
            .collect();
        AuthProof {
            num_auths: 0, // set by the caller
            trace_len: self.n,
            lde_size: self.lde,
            trace_commitment: self.trace_root.clone(),
            quotient_commitment: self.q_root.clone(),
            randomizer_commitment: self.r_root.clone(),
            trace_at_z: self.trace_at_z.clone(),
            q_z: self.q_z,
            fri_commitments,
            fri_final_layer: layers.last().unwrap().clone(),
            query_proofs,
        }
    }
}

/// Public column values per row (records, then the padding record), as the verifier builds them.
pub fn public_columns(p: &Poseidon1, records: &[AuthRecord], n: usize) -> Vec<Vec<BabyBear>> {
    let (pad, _) = air::padding(p);
    let mut cols = vec![Vec::with_capacity(n); NUM_PUBLIC];
    for i in 0..n {
        let vals = records.get(i).unwrap_or(&pad).public_values();
        for (c, v) in cols.iter_mut().zip(vals) {
            c.push(BabyBear::new(v.value as u64));
        }
    }
    cols
}

/// alpha^0 .. alpha^(NUM_CONSTRAINTS-1), as `prover::constraint_weights`.
pub fn weights(alpha: Ext) -> Vec<Ext> {
    let mut w = Vec::with_capacity(NUM_CONSTRAINTS);
    let mut cur = Ext::one();
    for _ in 0..NUM_CONSTRAINTS {
        w.push(cur);
        cur = cur * alpha;
    }
    w
}

/// sum_k w_k C_k(row), evaluated with toyni's arithmetic (exactly what the verifier computes).
pub fn combined_constraint(p: &Poseidon1, row: &[Ext], w: &[Ext]) -> Ext {
    let mut acc = Ext::zero();
    let mut k = 0;
    air::eval_constraints(p, row, |v| {
        acc = acc + w[k] * v;
        k += 1;
    });
    acc
}

pub fn row_tree(cols: &[Vec<BabyBear>], lde: usize) -> MerkleTree {
    let leaves = (0..lde)
        .map(|i| {
            let mut h = Sha256::new();
            for c in cols {
                h.update(c[i].to_bytes());
            }
            h.finalize().to_vec()
        })
        .collect();
    MerkleTree::new(leaves)
}

pub fn ext_tree(evals: &[Ext]) -> MerkleTree {
    MerkleTree::new(evals.iter().map(|v| v.to_bytes().to_vec()).collect())
}

fn open(tree: &MerkleTree, evals: &[Ext], index: usize) -> ScalarOpening {
    ScalarOpening { index, value: evals[index], proof: tree.get_proof(index).unwrap() }
}

/// Random record whose anchor has no known preimage.
pub fn random_record(rng: &mut impl rand::Rng) -> AuthRecord {
    let mut r = |_| BabyBear::random(rng);
    AuthRecord {
        anchor: std::array::from_fn(&mut r),
        m: std::array::from_fn(&mut r),
        next: std::array::from_fn(&mut r),
        c: std::array::from_fn(&mut r),
    }
}

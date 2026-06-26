//! Empirical probe: does the FRI verify path actually enforce a low-degree
//! bound, or does folding all the way to size 1 make the test vacuous?
//!
//! This replicates the EXACT prover fold (zkvm-prover/src/lib.rs:462-480) and
//! verifier fold-consistency + final-value check (zkvm-verifier/src/lib.rs:
//! 309-343) on two codewords: one that is genuinely low-degree (< LDE/BLOWUP)
//! and one that is high-degree (~LDE). If BOTH verify, the low-degree test is
//! not enforcing the rate-1/8 bound the soundness claim relies on.

use toyni::babybear::BabyBear;
use toyni::ext::Ext;
use toyni::math::domain::BabyBearDomain;
use toyni::math::fri::fri_fold_ext;

const LDE: usize = 256;
const BLOWUP: usize = 8;
const DEGREE_BOUND: usize = LDE / BLOWUP; // 32 — the bound rate-1/8 should enforce
const SHIFT: u64 = 7;

fn coset() -> Vec<BabyBear> {
    BabyBearDomain::new(LDE)
        .get_coset(BabyBear::new(SHIFT))
        .elements()
}

fn ext(a: u32, b: u32, c: u32, d: u32) -> Ext {
    Ext::new([
        BabyBear::from_u32(a),
        BabyBear::from_u32(b),
        BabyBear::from_u32(c),
        BabyBear::from_u32(d),
    ])
}

// Deterministic pseudo-random Ext, varying per index (no low-degree structure).
fn prng(i: usize) -> Ext {
    let m = |s: u64| ((i as u64).wrapping_mul(s).wrapping_add(s ^ 0x9E37)) as u32;
    ext(m(2654435761), m(40503), m(2246822519), m(3266489917))
}

// One challenge per fold, deterministic but "random enough".
fn betas() -> Vec<Ext> {
    (0..16).map(|k| prng(1000 + k)).collect()
}

/// Prover fold, verbatim shape of zkvm-prover: fold until length <= 1.
fn prover_fold(d_evals: &[Ext], shifted: &[BabyBear], betas: &[Ext]) -> (Vec<Vec<Ext>>, Ext) {
    let mut layers = vec![d_evals.to_vec()];
    let mut current = d_evals.to_vec();
    let mut xs = shifted.to_vec();
    let mut k = 0;
    loop {
        if current.len() <= 1 {
            break;
        }
        let beta = betas[k];
        k += 1;
        let folded = fri_fold_ext(&current, &xs, beta);
        xs.truncate(folded.len());
        for x in &mut xs {
            *x = *x * *x;
        }
        layers.push(folded.clone());
        current = folded;
    }
    (layers.clone(), current[0])
}

/// Verifier check, verbatim shape of zkvm-verifier: fold the query position
/// down through every committed layer, then compare to the scalar final value.
fn verifier_accepts(
    layers: &[Vec<Ext>],
    final_value: Ext,
    shifted: &[BabyBear],
    betas: &[Ext],
    qi: usize,
) -> bool {
    let half_inv = BabyBear::new(2).inverse();
    let half0 = LDE / 2;
    let a0 = layers[0][qi];
    let b0 = layers[0][qi + half0];
    let x0_inv = shifted[qi].inverse();
    let avg = (a0 + b0).mul_base(half_inv);
    let diff = (a0 - b0).mul_base(half_inv);
    let mut prev_folded = avg + diff * betas[0] * Ext::from(x0_inv);

    let mut pos = qi;
    let num_open = layers.len() - 2; // verifier folds layers 1..len-1
    for layer in 0..num_open {
        let fold_k = layer + 1;
        let layer_size = LDE >> fold_k;
        let half = layer_size / 2;
        let lo = pos % half;
        let in_first_half = pos == lo;
        let op = layers[fold_k][lo];
        let op_pair = layers[fold_k][lo + half];
        let opened = if in_first_half { op } else { op_pair };
        if opened != prev_folded {
            return false;
        }
        let x_inv = shifted[lo].pow(1u64 << fold_k).inverse();
        let avg = (op + op_pair).mul_base(half_inv);
        let diff = (op - op_pair).mul_base(half_inv);
        prev_folded = avg + diff * betas[fold_k] * Ext::from(x_inv);
        pos = lo;
    }
    prev_folded == final_value
}

fn low_degree_evals(shifted: &[BabyBear]) -> Vec<Ext> {
    // A genuine degree-<DEGREE_BOUND polynomial, evaluated on the coset.
    let coeffs: Vec<Ext> = (0..DEGREE_BOUND).map(|i| prng(7000 + i)).collect();
    shifted
        .iter()
        .map(|&x| {
            let xe = Ext::from(x);
            let mut acc = Ext::zero();
            for c in coeffs.iter().rev() {
                acc = acc * xe + *c;
            }
            acc
        })
        .collect()
}

fn all_queries_accept(layers: &[Vec<Ext>], final_value: Ext, shifted: &[BabyBear], betas: &[Ext]) -> bool {
    (0..LDE / 2).all(|qi| verifier_accepts(layers, final_value, shifted, betas, qi))
}

#[test]
fn fri_accepts_high_degree_codeword() {
    let shifted = coset();
    let betas = betas();

    // (1) Honest low-degree codeword verifies.
    let low = low_degree_evals(&shifted);
    let (low_layers, low_final) = prover_fold(&low, &shifted, &betas);
    assert!(
        all_queries_accept(&low_layers, low_final, &shifted, &betas),
        "low-degree codeword should verify"
    );

    // (2) THE PROBE: a high-degree codeword (no degree-<32 structure) also
    // verifies under the exact same fold-to-1 + final-value check.
    let high: Vec<Ext> = (0..LDE).map(prng).collect();
    let (high_layers, high_final) = prover_fold(&high, &shifted, &betas);
    let high_passes = all_queries_accept(&high_layers, high_final, &shifted, &betas);

    // (3) What a correct rate-1/8 check would inspect: the layer of size BLOWUP.
    // For the low-degree codeword it must be constant (degree < 1 after folding
    // down to size BLOWUP); for the high-degree one it is NOT.
    let blowup_layer_idx = (LDE / BLOWUP).trailing_zeros() as usize; // log2(256/8) = 5
    let low_blowup_const = low_layers[blowup_layer_idx].iter().all(|v| *v == low_layers[blowup_layer_idx][0]);
    let high_blowup_const = high_layers[blowup_layer_idx].iter().all(|v| *v == high_layers[blowup_layer_idx][0]);

    println!("high-degree codeword passes fold-to-1 FRI: {high_passes}");
    println!("size-{BLOWUP} layer constant?  low={low_blowup_const}  high={high_blowup_const}");

    assert!(
        high_passes,
        "PROBE RESULT: high-degree codeword was REJECTED -> FRI does enforce a bound; claim refuted"
    );
    assert!(low_blowup_const, "low-degree size-BLOWUP layer should be constant");
    assert!(
        !high_blowup_const,
        "high-degree size-BLOWUP layer is constant -> codeword wasn't actually high degree"
    );
}

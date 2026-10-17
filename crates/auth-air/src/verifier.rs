//! Verifier. The caller supplies the expected public records; the proof does not.

use toyni::babybear::{BabyBear, BABYBEAR_PRIME};
use toyni::ext::Ext;
use toyni::math::domain::BabyBearDomain;
use toyni::merkle::verify_merkle_proof;
use toyni::transcript::FiatShamirTranscript;

use crate::air::{self, AuthRecord, NUM_COLS, NUM_PUBLIC};
use crate::poseidon1::Poseidon1;
use crate::prover::{
    absorb_statement, build_scalar_merkle_tree_ext, constraint_weights, derive_z, fri_degree_bound,
    public_columns, row_leaf, trace_len_for, AuthProof, RowOpening, ScalarOpening, BLOWUP,
    COSET_SHIFT, NUM_QUERIES,
};

pub fn verify(proof: &AuthProof, records: &[AuthRecord]) -> bool {
    let p = Poseidon1::new();
    if records.is_empty() || proof.num_auths != records.len() { return false; }
    let trace_len = trace_len_for(records.len());
    let lde_size = trace_len * BLOWUP;
    if proof.trace_len != trace_len || proof.lde_size != lde_size { return false; }
    if proof.trace_at_z.len() != NUM_COLS { return false; }
    if !canonical(proof, records) { return false; }

    let domain = BabyBearDomain::new(trace_len);
    let shifted_domain = BabyBearDomain::new(lde_size).get_coset(BabyBear::new(COSET_SHIFT));

    let mut transcript = FiatShamirTranscript::new();
    absorb_statement(&mut transcript, records, trace_len);
    transcript.absorb_commitment(&proof.trace_commitment);
    let alpha = transcript.squeeze_ext_challenge();
    let weights = constraint_weights(alpha);
    transcript.absorb_commitment(&proof.quotient_commitment);
    transcript.absorb_commitment(&proof.randomizer_commitment);
    let z = derive_z(&mut transcript);
    for &v in &proof.trace_at_z { transcript.absorb_ext(v); }
    transcript.absorb_ext(proof.q_z);

    let pub_cols = public_columns(&p, records, trace_len);
    for c in 0..NUM_PUBLIC {
        if proof.trace_at_z[c] != lagrange_ext(&pub_cols[c], z, &domain) { return false; }
    }

    let mut c_z = Ext::zero();
    let mut k = 0;
    air::eval_constraints(&p, &proof.trace_at_z, |v| {
        c_z = c_z + weights[k] * v;
        k += 1;
    });
    let z_h_z = z.pow_u128(trace_len as u128) - Ext::one();
    if c_z != proof.q_z * z_h_z { return false; }

    let deep_coeffs: Vec<Ext> = (0..NUM_COLS + 2).map(|_| transcript.squeeze_ext_challenge()).collect();
    let d_bound = fri_degree_bound(trace_len);
    if lde_size < 4 * d_bound { return false; }
    let final_layer_size = lde_size / d_bound;
    let expected_folds = (lde_size / final_layer_size).trailing_zeros() as usize;
    if proof.fri_commitments.len() != expected_folds + 1 { return false; }
    if proof.fri_final_layer.len() != final_layer_size { return false; }
    // Low-degree check: the final layer must be constant.
    if !proof.fri_final_layer.iter().all(|v| *v == proof.fri_final_layer[0]) { return false; }
    if build_scalar_merkle_tree_ext(&proof.fri_final_layer).root().unwrap()
        != *proof.fri_commitments.last().unwrap()
    {
        return false;
    }
    transcript.absorb_commitment(&proof.fri_commitments[0]);
    let mut fri_betas = Vec::new();
    for i in 1..proof.fri_commitments.len() {
        fri_betas.push(transcript.squeeze_ext_challenge());
        transcript.absorb_commitment(&proof.fri_commitments[i]);
    }

    let half0 = lde_size / 2;
    let query_indices = transcript.squeeze_indices(NUM_QUERIES, lde_size);
    if proof.query_proofs.len() != NUM_QUERIES { return false; }
    let shifted_elements = shifted_domain.elements();
    let half_inv = BabyBear::new(2).inverse();

    for (qp, &qi) in proof.query_proofs.iter().zip(&query_indices) {
        if qp.index != qi { return false; }
        if qp.fri_openings.len() != expected_folds - 1 { return false; }
        if !verify_row(&qp.trace_opening, &proof.trace_commitment, qi, lde_size) { return false; }
        if !verify_scalar(&qp.quotient_opening, &proof.quotient_commitment, qi, lde_size) { return false; }
        if !verify_scalar(&qp.randomizer_opening, &proof.randomizer_commitment, qi, lde_size) { return false; }
        if !verify_scalar(&qp.deep_opening, &proof.fri_commitments[0], qi, lde_size) { return false; }
        if !verify_scalar(&qp.deep_opening_pair, &proof.fri_commitments[0], qi ^ half0, lde_size) { return false; }

        let inv_x_z = (Ext::from(shifted_elements[qi]) - z).inverse();
        let mut expected = Ext::zero();
        for c in 0..NUM_COLS {
            expected = expected
                + deep_coeffs[c] * (Ext::from(qp.trace_opening.values[c]) - proof.trace_at_z[c]) * inv_x_z;
        }
        expected = expected + deep_coeffs[NUM_COLS] * (qp.quotient_opening.value - proof.q_z) * inv_x_z;
        expected = expected + deep_coeffs[NUM_COLS + 1] * qp.randomizer_opening.value;
        if qp.deep_opening.value != expected { return false; }

        // qi ranges over the whole domain; fold with (a0, b0) at (lo0, lo0 + lde/2).
        let lo0 = qi % half0;
        let (a0, b0) = if qi == lo0 {
            (qp.deep_opening.value, qp.deep_opening_pair.value)
        } else {
            (qp.deep_opening_pair.value, qp.deep_opening.value)
        };
        let mut folded = (a0 + b0).mul_base(half_inv)
            + (a0 - b0).mul_base(half_inv) * fri_betas[0] * Ext::from(shifted_elements[lo0].inverse());
        let mut pos = lo0;
        for (layer, (op, op_pair)) in qp.fri_openings.iter().enumerate() {
            let fold_k = layer + 1;
            let layer_size = lde_size >> fold_k;
            let half = layer_size / 2;
            let lo = pos % half;
            if !verify_scalar(op, &proof.fri_commitments[fold_k], lo, layer_size) { return false; }
            if !verify_scalar(op_pair, &proof.fri_commitments[fold_k], lo + half, layer_size) { return false; }
            let mine = if pos == lo { op.value } else { op_pair.value };
            if mine != folded { return false; }
            let x_inv = shifted_elements[lo].pow(1u64 << fold_k).inverse();
            folded = (op.value + op_pair.value).mul_base(half_inv)
                + (op.value - op_pair.value).mul_base(half_inv) * fri_betas[fold_k] * Ext::from(x_inv);
            pos = lo;
        }
        if proof.fri_final_layer[pos] != folded { return false; }
    }
    true
}

/// Every field element must be < p: the u32 arithmetic and `==` are wrong otherwise (AUTH-02, AUTH-03).
fn canonical(proof: &AuthProof, records: &[AuthRecord]) -> bool {
    let ok = |v: &BabyBear| v.value < BABYBEAR_PRIME;
    let ext_ok = |e: &Ext| e.c.iter().all(ok);
    records.iter().all(|r| r.public_values().iter().all(ok))
        && proof.trace_at_z.iter().all(ext_ok)
        && ext_ok(&proof.q_z)
        && proof.fri_final_layer.iter().all(ext_ok)
        && proof.query_proofs.iter().all(|qp| {
            qp.trace_opening.values.iter().all(ok)
                && [&qp.quotient_opening, &qp.randomizer_opening, &qp.deep_opening, &qp.deep_opening_pair].iter().all(|o| ext_ok(&o.value))
                && qp.fri_openings.iter().all(|(a, b)| ext_ok(&a.value) && ext_ok(&b.value))
        })
}

fn verify_row(opening: &RowOpening, root: &[u8], index: usize, num_leaves: usize) -> bool {
    opening.index == index
        && opening.values.len() == NUM_COLS
        && verify_merkle_proof(&row_leaf(&opening.values), index, num_leaves, &opening.proof, root)
}

fn verify_scalar(opening: &ScalarOpening, root: &[u8], index: usize, num_leaves: usize) -> bool {
    opening.index == index
        && verify_merkle_proof(&opening.value.to_bytes(), index, num_leaves, &opening.proof, root)
}

/// Interpolant of `values` over the trace domain, evaluated at z (barycentric).
fn lagrange_ext(values: &[BabyBear], z: Ext, domain: &BabyBearDomain) -> Ext {
    let n = values.len();
    let z_n = z.pow_u128(n as u128) - Ext::one();
    let mut sum = Ext::zero();
    for (v, w) in values.iter().zip(domain.elements()) {
        sum = sum + (z - Ext::from(w)).inverse().mul_base(*v * w);
    }
    (sum * z_n).mul_base(BabyBear::new(n as u64).inverse())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::air::{h1, h2};
    use crate::prover::prove;
    use rand::SeedableRng;

    fn batch(n: usize) -> (Vec<AuthRecord>, Vec<[BabyBear; 4]>) {
        let p = Poseidon1::new();
        let mut rng = rand::rngs::StdRng::seed_from_u64(7);
        let mut r = |_| BabyBear::random(&mut rng);
        (0..n)
            .map(|_| {
                let x: [BabyBear; 4] = std::array::from_fn(&mut r);
                let m: [BabyBear; 8] = std::array::from_fn(&mut r);
                let next = h1(&p, std::array::from_fn(&mut r));
                (AuthRecord { anchor: h1(&p, x), m, next, c: h2(&p, m, x, next) }, x)
            })
            .unzip()
    }

    #[test]
    fn honest_batch_verifies_and_tampered_records_fail() {
        let (records, secrets) = batch(5);
        let proof = prove(&records, &secrets);
        assert!(verify(&proof, &records));

        let mut bad = records.clone();
        bad[2].m[0] = bad[2].m[0] + BabyBear::one();
        assert!(!verify(&proof, &bad), "changed message accepted");
        let mut bad = records.clone();
        bad[0].anchor[3] = bad[0].anchor[3] + BabyBear::one();
        assert!(!verify(&proof, &bad), "changed anchor accepted");
        let mut bad = records.clone();
        bad[4].next[1] = bad[4].next[1] + BabyBear::one();
        assert!(!verify(&proof, &bad), "changed next anchor accepted");
        assert!(!verify(&proof, &records[..4]), "dropped record accepted");
    }

    #[test]
    fn tampered_proofs_fail() {
        let (records, secrets) = batch(3);
        let mut proof = prove(&records, &secrets);
        assert!(verify(&proof, &records));

        let one = Ext::one();
        proof.q_z = proof.q_z + one;
        assert!(!verify(&proof, &records), "changed q(z) accepted");
        proof.q_z = proof.q_z - one;

        proof.trace_at_z[24] = proof.trace_at_z[24] + one;
        assert!(!verify(&proof, &records), "changed T(z) accepted");
        proof.trace_at_z[24] = proof.trace_at_z[24] - one;

        let v = &mut proof.query_proofs[7].trace_opening.values[300];
        *v = *v + BabyBear::one();
        assert!(!verify(&proof, &records), "changed trace opening accepted");
        let v = &mut proof.query_proofs[7].trace_opening.values[300];
        *v = *v - BabyBear::one();

        let r = &mut proof.query_proofs[7].randomizer_opening.value;
        *r = *r + one;
        assert!(!verify(&proof, &records), "changed randomizer opening accepted");
        let r = &mut proof.query_proofs[7].randomizer_opening.value;
        *r = *r - one;

        proof.randomizer_commitment[0] ^= 1;
        assert!(!verify(&proof, &records), "changed randomizer commitment accepted");
        proof.randomizer_commitment[0] ^= 1;

        proof.fri_final_layer[0] = proof.fri_final_layer[0] + one;
        assert!(!verify(&proof, &records), "changed FRI final layer accepted");
        proof.fri_final_layer[0] = proof.fri_final_layer[0] - one;

        assert!(verify(&proof, &records), "restored proof should verify again");
    }

    #[test]
    #[should_panic(expected = "H2(m, x, next) != c")]
    fn prover_refuses_a_forged_commitment() {
        let (mut records, secrets) = batch(2);
        records[1].c[0] = records[1].c[0] + BabyBear::one();
        prove(&records, &secrets);
    }
}

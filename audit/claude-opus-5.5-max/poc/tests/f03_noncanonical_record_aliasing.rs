//! AUTH-03 regression: a non-canonical record is rejected, so verified bytes are the authorized ones.

use auth_air::air::{self, h1, h2, AuthRecord, NUM_COLS};
use auth_air::poseidon1::Poseidon1;
use auth_air::verifier::verify;
use auth_audit_poc::{combined_constraint, weights, Forger, P};
use rand::SeedableRng;
use toyni::babybear::BabyBear;
use toyni::ext::Ext;

#[test]
fn aliased_record_is_rejected() {
    let p = Poseidon1::new();
    let mut rng = rand::rngs::StdRng::seed_from_u64(0xF03);
    let mut r = |_| BabyBear::random(&mut rng);
    let x: [BabyBear; 4] = std::array::from_fn(&mut r);
    let mut m: [BabyBear; 8] = std::array::from_fn(&mut r);
    m[0] = BabyBear::new(5); // e.g. "amount = 5"
    let next = h1(&p, std::array::from_fn(&mut r));
    let signed = AuthRecord { anchor: h1(&p, x), m, next, c: h2(&p, m, x, next) };

    let mut submitted = signed;
    submitted.m[0] = BabyBear { value: 5 + P }; // same field element, different u32
    assert_ne!(submitted, signed);

    // Honest witness for the signed record; the transcript absorbs the submitted bytes.
    let mut f = Forger::new(&[submitted]);
    let (n, lde) = (f.n, f.lde);
    let (pad, pad_x) = air::padding(&p);
    let rows: Vec<Vec<BabyBear>> =
        (0..n).map(|i| if i == 0 { air::trace_row(&p, &signed, x) } else { air::trace_row(&p, &pad, pad_x) }).collect();
    let coeffs: Vec<Vec<BabyBear>> =
        (0..NUM_COLS).map(|c| f.domain.ifft(&rows.iter().map(|row| row[c]).collect::<Vec<_>>())).collect();
    let trace_lde: Vec<Vec<BabyBear>> = coeffs.iter().map(|c| f.shifted_domain.fft(c)).collect();

    let alpha = f.commit_trace(trace_lde.clone());
    let w = weights(alpha);
    let q_evals: Vec<Ext> = (0..lde)
        .map(|i| {
            let row: Vec<Ext> = (0..NUM_COLS).map(|c| Ext::from(trace_lde[c][i])).collect();
            let z_h = f.xs[i].pow(n as u64) - BabyBear::one();
            combined_constraint(&p, &row, &w).mul_base(z_h.inverse())
        })
        .collect();
    let q_coeffs = f.shifted_domain.ifft_ext(&q_evals);
    let z = f.commit_quotient(q_evals);
    let tau: Vec<Ext> = coeffs.iter().map(|c| z.eval_base_at_ext(c)).collect();
    let q_z = z.eval_ext_at_ext(&q_coeffs);
    f.send_ood(tau.clone(), q_z);
    let layer0 = f.honest_deep(&tau, q_z);
    let mut proof = f.finish(layer0);
    proof.num_auths = 1;

    assert!(!verify(&proof, &[submitted]), "aliased record accepted");
    assert!(!verify(&proof, &[signed]), "the aggregator chooses which encoding verifies");
    assert_eq!(signed.m[0].value, 5);
    assert_eq!(submitted.m[0].value, 2013265926);
}

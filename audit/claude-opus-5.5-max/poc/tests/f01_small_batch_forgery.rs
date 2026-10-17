//! AUTH-01 regression: the small-batch forgery fails now that every trace has >= 512 rows (rate <= 1/4).

use auth_air::air::{AuthRecord, NUM_COLS, NUM_PUBLIC};
use auth_air::verifier::verify;
use auth_audit_poc::{combined_constraint, public_columns, random_record, weights, Forger};
use rand::SeedableRng;
use toyni::babybear::BabyBear;
use toyni::ext::Ext;

#[test]
fn small_batch_forgery_is_rejected() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(0xF01);
    // A victim's anchor (preimage unknown to anyone) authorizing an attacker message.
    let records: Vec<AuthRecord> = (0..3).map(|_| random_record(&mut rng)).collect();

    let mut f = Forger::new(&records);
    assert_eq!(f.n, 512);
    let (n, lde) = (f.n, f.lde);

    // 1. Commit an all-zero trace and an all-zero quotient.
    let alpha = f.commit_trace(vec![vec![BabyBear::zero(); lde]; NUM_COLS]);
    let z = f.commit_quotient(vec![Ext::zero(); lde]);

    // 2. Public OOD values must match the records; witness ones are free; q(z) solves C(z) = q(z) Z_H(z).
    let pub_cols = public_columns(&f.p, &records, n);
    let mut tau = vec![Ext::zero(); NUM_COLS];
    for c in 0..NUM_PUBLIC {
        tau[c] = z.eval_base_at_ext(&f.domain.ifft(&pub_cols[c]));
    }
    let c_z = combined_constraint(&f.p, &tau, &weights(alpha));
    let z_h = z.pow_u128(n as u128) - Ext::one();
    let q_z = c_z * z_h.inverse();
    let coeffs = f.send_ood(tau.clone(), q_z);

    // 3. On the first half H1 the verifier expects d(x) = -K/(x - z); g(X) = K (V(X)/V(z) - 1)/(X - z),
    //    V = prod_{h in H1}(X - h), matches it there; its degree |H1| - 1 is below the bound only at rate 1/2.
    let mut k = coeffs[NUM_COLS] * q_z;
    for c in 0..NUM_COLS {
        k = k + coeffs[c] * tau[c];
    }
    let half = lde / 2;
    let h1 = &f.xs[..half];
    let v_z = h1.iter().fold(Ext::one(), |acc, &h| acc * (z - Ext::from(h)));
    let v_z_inv = v_z.inverse();
    let layer0: Vec<Ext> = (0..lde)
        .map(|i| {
            let x = f.xs[i];
            let v_x = if i < half {
                BabyBear::zero()
            } else {
                h1.iter().fold(BabyBear::one(), |acc, &h| acc * (x - h))
            };
            k * (v_z_inv.mul_base(v_x) - Ext::one()) * (Ext::from(x) - z).inverse()
        })
        .collect();

    let mut proof = f.finish(layer0);
    proof.num_auths = records.len();

    assert!(!verify(&proof, &records), "forged proof accepted");
}

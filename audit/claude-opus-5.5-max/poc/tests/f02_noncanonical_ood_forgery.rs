//! AUTH-02 regression: the non-canonical OOD forgery is rejected by the canonical-input check.

use auth_air::air::{AuthRecord, H1_CELLS, H2_CELLS, M, NEXT, NUM_COLS, NUM_PUBLIC, X};
use auth_air::poseidon1::{Poseidon1, SBOXES, WIDTH};
use auth_air::verifier::verify;
use auth_audit_poc::ktree::{self, CELLS_USED, V};
use auth_audit_poc::{combined_constraint, public_columns, random_record, weights, Forger, DELTA, P};
use rand::SeedableRng;
use toyni::babybear::BabyBear;
use toyni::ext::Ext;

fn to_v(e: Ext) -> V {
    std::array::from_fn(|i| e.c[i].value % P)
}

/// The S-box inputs v_s the verifier computes from `tau` (all S-box outputs y = tau_y).
fn sbox_inputs(p: &Poseidon1, tau: &[Ext]) -> Vec<Ext> {
    let mut vs = Vec::with_capacity(2 * SBOXES);
    let zero = Ext::zero();
    let x: [Ext; 4] = std::array::from_fn(|i| tau[X + i]);
    let h1_in: [Ext; WIDTH] = std::array::from_fn(|i| if i < 4 { x[i] } else { zero });
    let h2_in: [Ext; WIDTH] = std::array::from_fn(|i| match i {
        0..8 => tau[M + i],
        8..12 => x[i - 8],
        _ => tau[NEXT + i - 12],
    });
    for (input, cells) in [(h1_in, H1_CELLS), (h2_in, H2_CELLS)] {
        let mut k = cells;
        p.permute_with(input, |v| {
            vs.push(v);
            let y = tau[k + 1];
            k += 2;
            y
        });
    }
    vs
}

fn a_cell_column(s: usize) -> usize {
    if s < SBOXES { H1_CELLS + 2 * s } else { H2_CELLS + 2 * (s - SBOXES) }
}

#[test]
#[cfg_attr(debug_assertions, ignore = "u32 overflow panics in debug builds; run with --release")]
fn noncanonical_ood_forgery_is_rejected() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(0xF02);
    let records: Vec<AuthRecord> = (0..300).map(|_| random_record(&mut rng)).collect();
    let mut f = Forger::new(&records);
    assert_eq!(f.n, 512, "F-01 (first-half rate 1) does not apply at this size");
    let (n, lde) = (f.n, f.lde);

    // 1. Commit the true public columns and all-zero witness columns, and a zero quotient.
    let pub_cols = public_columns(&f.p, &records, n);
    let mut trace_lde = vec![vec![BabyBear::zero(); lde]; NUM_COLS];
    let mut tau = vec![Ext::zero(); NUM_COLS];
    for c in 0..NUM_PUBLIC {
        trace_lde[c] = f.shifted_domain.fft(&f.domain.ifft(&pub_cols[c]));
    }
    let alpha = f.commit_trace(trace_lde);
    let z = f.commit_quotient(vec![Ext::zero(); lde]);
    for c in 0..NUM_PUBLIC {
        tau[c] = z.eval_base_at_ext(&f.domain.ifft(&pub_cols[c]));
    }

    // 2. With q = 0 the verifier needs C(z) = 0; honestly C(tau) = D != 0.
    let w = weights(alpha);
    let d = combined_constraint(&f.p, &tau, &w);
    assert!(!d.is_zero());

    // 3. Shifting a-cell s by delta changes (a - v^3) by delta and (y - a^2 v) by -delta^2 v.
    let vs = sbox_inputs(&f.p, &tau);
    let delta = |o: usize| {
        Ext::new(std::array::from_fn(|k| {
            if k > 0 && (o >> (k - 1)) & 1 == 1 { BabyBear::new(DELTA as u64) } else { BabyBear::zero() }
        }))
    };
    let options: Vec<[V; 8]> = (0..2 * SBOXES)
        .map(|s| {
            std::array::from_fn(|o| {
                let dl = delta(o);
                to_v(w[2 * s] * dl - w[2 * s + 1] * dl * dl * vs[s])
            })
        })
        .collect();
    assert!(options.len() >= CELLS_USED);
    let target = to_v(Ext::zero() - d);
    let choice = ktree::solve(&options, target).expect("no k-tree solution; rerun with another seed");

    // 4. Send shifted coordinates as DELTA + p: the constraint check sees DELTA, DEEP sees 0 = tau.
    let mut ood = tau.clone();
    for (s, &o) in choice.iter().enumerate() {
        if o == 0 {
            continue;
        }
        let col = a_cell_column(s);
        let mut c = ood[col].c;
        for k in 1..4 {
            if (o >> (k - 1)) & 1 == 1 {
                c[k] = BabyBear { value: DELTA + P }; // non-canonical encoding of DELTA
            }
        }
        ood[col] = Ext::new(c);
    }
    assert!(combined_constraint(&f.p, &ood, &w).is_zero(), "verifier-side C(z) is not zero");

    // 5. Honest DEEP + FRI over the committed polynomials and their true values tau.
    let q_z = Ext::zero();
    f.send_ood(ood, q_z);
    let layer0 = f.honest_deep(&tau, q_z);
    let mut proof = f.finish(layer0);
    proof.num_auths = records.len();

    assert!(!verify(&proof, &records), "forged proof accepted");
}

/// The raw arithmetic still panics on this encoding in debug builds; `verify` now rejects it first.
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "overflow")]
fn noncanonical_ood_value_panics_debug_verifier() {
    let encoded = Ext::new([BabyBear::zero(), BabyBear { value: DELTA + P }, BabyBear::zero(), BabyBear::zero()]);
    let _ = Ext::zero() - encoded; // the verifier's DEEP subtraction
}

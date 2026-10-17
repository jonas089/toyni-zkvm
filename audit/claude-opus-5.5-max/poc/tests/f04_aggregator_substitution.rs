//! AUTH-04: an aggregator that learned x proves its own message (see REPORT.md).

use auth_air::air::{h1, h2, AuthRecord};
use auth_air::poseidon1::Poseidon1;
use auth_air::prover::prove;
use auth_air::verifier::verify;
use rand::SeedableRng;
use toyni::babybear::BabyBear;

#[test]
fn aggregator_who_learned_x_authorizes_its_own_message() {
    let p = Poseidon1::new();
    let mut rng = rand::rngs::StdRng::seed_from_u64(0xF04);
    let mut r = |_| BabyBear::random(&mut rng);
    let x: [BabyBear; 4] = std::array::from_fn(&mut r);
    let anchor = h1(&p, x);

    // What the user committed to and revealed to the aggregator.
    let m: [BabyBear; 8] = std::array::from_fn(&mut r);
    let next = h1(&p, std::array::from_fn(&mut r));
    let _users_c = h2(&p, m, x, next);

    // The aggregator's substitute: its own message and its own next anchor.
    let m_evil: [BabyBear; 8] = std::array::from_fn(&mut r);
    let next_evil = h1(&p, std::array::from_fn(&mut r));
    let c_evil = h2(&p, m_evil, x, next_evil);
    let record = AuthRecord { anchor, m: m_evil, next: next_evil, c: c_evil };

    let proof = prove(&[record], &[x]);
    assert!(verify(&proof, &[record]));
}

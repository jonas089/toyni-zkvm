//! `auth-bench <num_auths> [repeats]`: prove and verify random batches.

use std::time::Instant;

use auth_air::air::{h1, h2, AuthRecord, NUM_COLS};
use auth_air::poseidon1::Poseidon1;
use auth_air::prover::{prove, BLOWUP};
use auth_air::verifier::verify;
use toyni::babybear::BabyBear;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(256);
    let repeats: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1);

    let p = Poseidon1::new();
    let mut rng = rand::thread_rng();
    let mut r = |_| BabyBear::random(&mut rng);
    let (records, secrets): (Vec<AuthRecord>, Vec<[BabyBear; 4]>) = (0..n)
        .map(|_| {
            let x: [BabyBear; 4] = std::array::from_fn(&mut r);
            let m: [BabyBear; 8] = std::array::from_fn(&mut r);
            let next = h1(&p, std::array::from_fn(&mut r));
            (AuthRecord { anchor: h1(&p, x), m, next, c: h2(&p, m, x, next) }, x)
        })
        .unzip();

    for rep in 0..repeats {
        let t = Instant::now();
        let proof = prove(&records, &secrets);
        let prove_s = t.elapsed().as_secs_f64();
        let t = Instant::now();
        let ok = verify(&proof, &records);
        let verify_s = t.elapsed().as_secs_f64();
        assert!(ok, "proof failed to verify");
        let cells = (proof.trace_len * NUM_COLS) as f64;
        println!(
            "run {rep}: auths={n} rows={} cols={NUM_COLS} lde={} | prove {prove_s:.2}s verify {verify_s:.3}s | {:.1} auths/s, {:.2}M trace cells/s",
            proof.trace_len,
            proof.trace_len * BLOWUP,
            n as f64 / prove_s,
            cells / prove_s / 1e6,
        );
    }
}

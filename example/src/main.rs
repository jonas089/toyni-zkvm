//! UTXO payments on the auth engine with an in-memory chain and one trusted sequencer.
//! Run: `cargo run --release -p utxo-example`. See README.md for the design.

mod chain;
mod sequencer;
mod utxo;

use auth_air::poseidon1::Poseidon1;
use toyni::babybear::BabyBear;

use chain::Chain;
use sequencer::Sequencer;
use utxo::{envelope, lock, new_secret, tag, Lock, Transfer};

fn balances(chain: &Chain, owners: &[(&str, &[Lock])]) {
    for (name, locks) in owners {
        let total: u64 = locks.iter().map(|l| chain.balance(*l)).sum();
        println!("    {name}: {total}");
    }
}

fn main() {
    let p = Poseidon1::new();
    let mut rng = rand::thread_rng();
    let mut chain = Chain::new(&p);
    let mut seq = Sequencer::new();

    let (alice0, alice1, alice2) = (new_secret(&mut rng), new_secret(&mut rng), new_secret(&mut rng));
    let (bob0, bob1, bob2) = (new_secret(&mut rng), new_secret(&mut rng), new_secret(&mut rng));
    let (carol0, carol1) = (new_secret(&mut rng), new_secret(&mut rng));
    let alice = [lock(&p, alice0), lock(&p, alice1), lock(&p, alice2)];
    let bob = [lock(&p, bob0), lock(&p, bob1), lock(&p, bob2)];
    let carol = [lock(&p, carol0), lock(&p, carol1)];
    let owners: [(&str, &[Lock]); 3] = [("alice", &alice), ("bob", &bob), ("carol", &carol)];

    chain.mint(alice[0], 100);
    chain.mint(carol[0], 50);
    println!("genesis");
    balances(&chain, &owners);

    // A griefer posts junk for Alice's lock first. It has no valid tag, so it is skipped.
    let junk = std::array::from_fn(|_| BabyBear::random(&mut rng));
    chain.post_envelope(alice[0], junk, junk);

    // Step 1: commit. Alice and Carol post envelopes; nobody has seen their secrets yet.
    let pay_bob = Transfer { to: bob[0], amount: 30, change: 70 };
    let c = envelope(&p, alice0, &pay_bob, alice[1]);
    chain.post_envelope(alice[0], c, tag(&p, alice0, &c));
    let carol_pays = Transfer { to: bob[1], amount: 50, change: 0 };
    let c = envelope(&p, carol0, &carol_pays, carol[1]);
    chain.post_envelope(carol[0], c, tag(&p, carol0, &c));

    // Step 2: reveal, once the envelopes are final.
    seq.submit(&chain, &pay_bob, alice0, alice[1]).unwrap();
    seq.submit(&chain, &carol_pays, carol0, carol[1]).unwrap();

    // Someone who saw alice0 posts a valid envelope that redirects her coin. It is later than hers.
    let mallory = lock(&p, new_secret(&mut rng));
    let steal = Transfer { to: mallory, amount: 100, change: 0 };
    let c = envelope(&p, alice0, &steal, mallory);
    chain.post_envelope(alice[0], c, tag(&p, alice0, &c));
    println!("redirect with leaked alice0: {:?}", seq.submit(&chain, &steal, alice0, mallory));

    println!("batch 1: {} spends proven and applied", seq.seal(&mut chain).unwrap());
    balances(&chain, &owners);

    // A spent lock cannot be opened again.
    println!("replay alice0: {:?}", seq.submit(&chain, &pay_bob, alice0, alice[1]));

    // Bob pays 10 to a fresh lock of Alice's, change 20 to his next lock.
    let bob_pays = Transfer { to: alice[2], amount: 10, change: 20 };
    let c = envelope(&p, bob0, &bob_pays, bob[2]);
    chain.post_envelope(bob[0], c, tag(&p, bob0, &c));
    seq.submit(&chain, &bob_pays, bob0, bob[2]).unwrap();
    println!("batch 2: {} spend proven and applied", seq.seal(&mut chain).unwrap());
    balances(&chain, &owners);
}

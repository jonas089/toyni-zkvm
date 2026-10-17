//! A coin sits under a one-time lock `H1(x)`. Spending it reveals `x` once; the message pays
//! `amount` to `to` and returns `change` to the spend's `next` lock.

use auth_air::air::{h1, h2};
use auth_air::poseidon1::Poseidon1;
use rand::Rng;
use toyni::babybear::BabyBear;

pub type Secret = [BabyBear; 4];
pub type Lock = [BabyBear; 4];
pub type Envelope = [BabyBear; 8];
pub type Tag = [BabyBear; 8];

#[derive(Clone, Copy, Debug)]
pub struct Transfer {
    pub to: Lock,
    pub amount: u64,
    pub change: u64,
}

impl Transfer {
    pub fn encode(&self) -> [BabyBear; 8] {
        let [a, b, c, d] = self.to;
        [a, b, c, d, BabyBear::new(self.amount), BabyBear::new(self.change), BabyBear::zero(), BabyBear::zero()]
    }

    pub fn decode(m: &[BabyBear; 8]) -> Option<Self> {
        (m[6].is_zero() && m[7].is_zero()).then(|| Transfer {
            to: [m[0], m[1], m[2], m[3]],
            amount: m[4].value as u64,
            change: m[5].value as u64,
        })
    }
}

pub fn new_secret(rng: &mut impl Rng) -> Secret {
    std::array::from_fn(|_| BabyBear::random(&mut *rng))
}

pub fn lock(p: &Poseidon1, x: Secret) -> Lock {
    h1(p, x)
}

/// `c = H2(m, x, next)`: seals the transfer and the change lock under `x`.
pub fn envelope(p: &Poseidon1, x: Secret, t: &Transfer, next: Lock) -> Envelope {
    h2(p, t.encode(), x, next)
}

/// `t = H2(c, x, domain)`: only the holder of `x` can produce it before `x` is revealed.
pub fn tag(p: &Poseidon1, x: Secret, c: &Envelope) -> Tag {
    h2(p, *c, x, [BabyBear::new(0x7461_6700); 4])
}

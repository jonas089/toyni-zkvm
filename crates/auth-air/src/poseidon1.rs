//! Textbook Poseidon1-BabyBear-16 (x^7, 8 full + 13 partial rounds), equal to Plonky3's
//! `default_babybear_poseidon1_16()`. Round: add constants, S-box, dense MDS.
//! https://github.com/Plonky3/Plonky3/blob/a21e3ed42905040ad49c519e402f018381c12d0c/poseidon1/src/lib.rs#L15-L33

use std::ops::{Add, Mul, Sub};

use toyni::babybear::BabyBear;
use toyni::ext::Ext;

use crate::constants::{MDS_ROW_16, RC_16};

pub const WIDTH: usize = 16;
pub const HALF_FULL_ROUNDS: usize = 4;
pub const PARTIAL_ROUNDS: usize = 13;
pub const ROUNDS: usize = 2 * HALF_FULL_ROUNDS + PARTIAL_ROUNDS;
/// 16 per full round, 1 per partial round.
pub const SBOXES: usize = 2 * HALF_FULL_ROUNDS * WIDTH + PARTIAL_ROUNDS;

/// BabyBear for hashing and the trace, Ext for checks at the OOD point.
pub trait AirField:
    Copy + Add<Output = Self> + Sub<Output = Self> + Mul<Output = Self> + From<BabyBear>
{
}
impl AirField for BabyBear {}
impl AirField for Ext {}

/// Rounds 0..4 and 17..21 are full, 4..17 partial.
pub fn is_full_round(round: usize) -> bool {
    round < HALF_FULL_ROUNDS || round >= HALF_FULL_ROUNDS + PARTIAL_ROUNDS
}

#[derive(Clone)]
pub struct Poseidon1 {
    rc: [[BabyBear; WIDTH]; ROUNDS],
    mds: [[BabyBear; WIDTH]; WIDTH],
}

impl Default for Poseidon1 {
    fn default() -> Self {
        Self::new()
    }
}

impl Poseidon1 {
    pub fn new() -> Self {
        let rc = RC_16.map(|row| row.map(BabyBear::from_u32));
        // https://github.com/Plonky3/Plonky3/blob/a21e3ed42905040ad49c519e402f018381c12d0c/mds/src/util.rs#L52-L62
        let col: [BabyBear; WIDTH] =
            std::array::from_fn(|i| BabyBear::from_u32(MDS_ROW_16[(WIDTH - i) % WIDTH]));
        // https://github.com/Plonky3/Plonky3/blob/a21e3ed42905040ad49c519e402f018381c12d0c/poseidon1/src/utils.rs#L77-L80
        let mds = std::array::from_fn(|i| std::array::from_fn(|j| col[(WIDTH + i - j) % WIDTH]));
        Self { rc, mds }
    }

    /// Shared by hashing, witness generation and constraint evaluation; `sbox` is
    /// called for every S-box in order.
    pub fn permute_with<F: AirField>(
        &self,
        mut state: [F; WIDTH],
        mut sbox: impl FnMut(F) -> F,
    ) -> [F; WIDTH] {
        for round in 0..ROUNDS {
            for i in 0..WIDTH {
                state[i] = state[i] + F::from(self.rc[round][i]);
            }
            if is_full_round(round) {
                for s in state.iter_mut() {
                    *s = sbox(*s);
                }
            } else {
                state[0] = sbox(state[0]);
            }
            state = std::array::from_fn(|i| {
                let mut acc = F::from(BabyBear::zero());
                for j in 0..WIDTH {
                    acc = acc + F::from(self.mds[i][j]) * state[j];
                }
                acc
            });
        }
        state
    }

    pub fn permute(&self, state: [BabyBear; WIDTH]) -> [BabyBear; WIDTH] {
        self.permute_with(state, |x| {
            let x3 = x * x * x;
            x3 * x3 * x
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_baby_bear::default_babybear_poseidon1_16;
    use p3_field::{PrimeCharacteristicRing, PrimeField32};
    use p3_symmetric::Permutation;
    use rand::{Rng, SeedableRng};

    /// https://github.com/Plonky3/Plonky3/blob/a21e3ed42905040ad49c519e402f018381c12d0c/baby-bear/src/poseidon1.rs#L487-L502
    pub const OFFICIAL_INPUT: [u32; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
    pub const OFFICIAL_OUTPUT: [u32; 16] = [
        0x1c054a3c, 0x4d897543, 0x4f6d849c, 0x22c40722, 0x27f28fcc, 0x12630ff8, 0x0b6a636e,
        0x540fb34e, 0x3fb75b3b, 0x0fff080e, 0x6c933709, 0x0fcfaae1, 0x6dbe9950, 0x214714db,
        0x4b965dbe, 0x40463a0a,
    ];

    #[test]
    fn official_test_vector() {
        let out = Poseidon1::new().permute(OFFICIAL_INPUT.map(BabyBear::from_u32));
        assert_eq!(out.map(|v| v.value), OFFICIAL_OUTPUT);
    }

    #[test]
    fn matches_plonky3_on_random_inputs() {
        let ours = Poseidon1::new();
        let theirs = default_babybear_poseidon1_16();
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let input: [u32; 16] = std::array::from_fn(|_| rng.gen_range(0..BabyBear::PRIME));
            let mut p3_state = input.map(p3_baby_bear::BabyBear::from_u32);
            theirs.permute_mut(&mut p3_state);
            let out = ours.permute(input.map(BabyBear::from_u32));
            assert_eq!(out.map(|v| v.value), p3_state.map(|v| v.as_canonical_u32()));
        }
    }
}

//! One row per authorization: H1(x) == anchor, H2(m, x, next) == c, x private.
//! Columns: public [0..24), x [24..28), then H1 and H2 S-box cells (a = v^3, y = a^2 v),
//! so every constraint has degree 3. No transition constraints.

use toyni::babybear::BabyBear;

use crate::poseidon1::{AirField, Poseidon1, SBOXES, WIDTH};

pub const ANCHOR: usize = 0;
pub const M: usize = 4;
pub const NEXT: usize = 12;
pub const C: usize = 16;
pub const NUM_PUBLIC: usize = 24;
pub const X: usize = 24;
pub const PERM_CELLS: usize = 2 * SBOXES;
pub const H1_CELLS: usize = 28;
pub const H2_CELLS: usize = H1_CELLS + PERM_CELLS;
pub const NUM_COLS: usize = H2_CELLS + PERM_CELLS;
pub const NUM_CONSTRAINTS: usize = 2 * 2 * SBOXES + 4 + 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthRecord {
    pub anchor: [BabyBear; 4],
    pub m: [BabyBear; 8],
    pub next: [BabyBear; 4],
    pub c: [BabyBear; 8],
}

impl AuthRecord {
    pub fn public_values(&self) -> [BabyBear; NUM_PUBLIC] {
        let mut v = [BabyBear::zero(); NUM_PUBLIC];
        v[ANCHOR..ANCHOR + 4].copy_from_slice(&self.anchor);
        v[M..M + 8].copy_from_slice(&self.m);
        v[NEXT..NEXT + 4].copy_from_slice(&self.next);
        v[C..C + 8].copy_from_slice(&self.c);
        v
    }
}

fn h1_input<F: AirField>(x: [F; 4]) -> [F; WIDTH] {
    let zero = F::from(BabyBear::zero());
    std::array::from_fn(|i| if i < 4 { x[i] } else { zero })
}

fn h2_input<F: AirField>(m: [F; 8], x: [F; 4], next: [F; 4]) -> [F; WIDTH] {
    std::array::from_fn(|i| match i {
        0..8 => m[i],
        8..12 => x[i - 8],
        _ => next[i - 12],
    })
}

pub fn h1(p: &Poseidon1, x: [BabyBear; 4]) -> [BabyBear; 4] {
    let out = p.permute(h1_input(x));
    std::array::from_fn(|i| out[i])
}

pub fn h2(p: &Poseidon1, m: [BabyBear; 8], x: [BabyBear; 4], next: [BabyBear; 4]) -> [BabyBear; 8] {
    let out = p.permute(h2_input(m, x, next));
    std::array::from_fn(|i| out[i])
}

/// Padding row: the valid authorization with x = m = next = 0.
pub fn padding(p: &Poseidon1) -> (AuthRecord, [BabyBear; 4]) {
    let x = [BabyBear::zero(); 4];
    let m = [BabyBear::zero(); 8];
    let next = [BabyBear::zero(); 4];
    let rec = AuthRecord { anchor: h1(p, x), m, next, c: h2(p, m, x, next) };
    (rec, x)
}

/// Panics if (rec, x) is not a valid authorization.
pub fn trace_row(p: &Poseidon1, rec: &AuthRecord, x: [BabyBear; 4]) -> Vec<BabyBear> {
    let mut row = Vec::with_capacity(NUM_COLS);
    row.extend_from_slice(&rec.public_values());
    row.extend_from_slice(&x);
    let mut sbox = |v: BabyBear| {
        let a = v * v * v;
        let y = a * a * v;
        row.push(a);
        row.push(y);
        y
    };
    let out1 = p.permute_with(h1_input(x), &mut sbox);
    let out2 = p.permute_with(h2_input(rec.m, x, rec.next), &mut sbox);
    assert!(out1[..4] == rec.anchor, "H1(x) != anchor");
    assert!(out2[..8] == rec.c, "H2(m, x, next) != c");
    assert_eq!(row.len(), NUM_COLS);
    row
}

/// Calls `emit` for each constraint in a fixed order; all are zero iff the row is valid.
pub fn eval_constraints<F: AirField>(p: &Poseidon1, row: &[F], mut emit: impl FnMut(F)) {
    debug_assert_eq!(row.len(), NUM_COLS);
    let get = |start: usize| -> [F; 4] { std::array::from_fn(|i| row[start + i]) };
    let anchor = get(ANCHOR);
    let m: [F; 8] = std::array::from_fn(|i| row[M + i]);
    let next = get(NEXT);
    let c: [F; 8] = std::array::from_fn(|i| row[C + i]);
    let x = get(X);

    let mut check_perm = |input: [F; WIDTH], cells_start: usize| -> [F; WIDTH] {
        let mut k = cells_start;
        p.permute_with(input, |v| {
            let a = row[k];
            let y = row[k + 1];
            k += 2;
            emit(a - v * v * v);
            emit(y - a * a * v);
            y
        })
    };
    let out1 = check_perm(h1_input(x), H1_CELLS);
    let out2 = check_perm(h2_input(m, x, next), H2_CELLS);
    for i in 0..4 {
        emit(out1[i] - anchor[i]);
    }
    for i in 0..8 {
        emit(out2[i] - c[i]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{Rng, SeedableRng};

    fn rand_elems<const N: usize>(rng: &mut impl Rng) -> [BabyBear; N] {
        std::array::from_fn(|_| BabyBear::random(rng))
    }

    #[test]
    fn honest_row_satisfies_all_constraints() {
        let p = Poseidon1::new();
        let mut rng = rand::rngs::StdRng::seed_from_u64(1);
        for _ in 0..20 {
            let x = rand_elems::<4>(&mut rng);
            let m = rand_elems::<8>(&mut rng);
            let next = rand_elems::<4>(&mut rng);
            let rec = AuthRecord { anchor: h1(&p, x), m, next, c: h2(&p, m, x, next) };
            let row = trace_row(&p, &rec, x);
            let mut n = 0;
            eval_constraints(&p, &row, |v| {
                assert!(v.is_zero());
                n += 1;
            });
            assert_eq!(n, NUM_CONSTRAINTS);
        }
    }

    #[test]
    fn any_tampered_cell_violates_a_constraint() {
        let p = Poseidon1::new();
        let (rec, x) = padding(&p);
        let row = trace_row(&p, &rec, x);
        let mut rng = rand::rngs::StdRng::seed_from_u64(2);
        for col in 0..NUM_COLS {
            let mut bad = row.clone();
            bad[col] = bad[col] + BabyBear::new(rng.gen_range(1..1000));
            let mut violated = false;
            eval_constraints(&p, &bad, |v| violated |= !v.is_zero());
            assert!(violated, "changing column {col} went unnoticed");
        }
    }
}

//! AIR for one authorization per row: H1(x) == anchor and H2(m, x, next) == c, x private.
//!
//! Trace layout (`Row`, 592 columns):
//!
//! | columns      | cells          | kind    | meaning                                  |
//! |--------------|----------------|---------|------------------------------------------|
//! | `[0, 4)`     | `anchor`       | public  | must equal H1(x)[0..4]                   |
//! | `[4, 12)`    | `m`            | public  | message                                  |
//! | `[12, 16)`   | `next`         | public  | next anchor                              |
//! | `[16, 24)`   | `c`            | public  | must equal H2(m, x, next)[0..8]          |
//! | `[24, 28)`   | `x`            | witness | secret preimage                          |
//! | `[28, 310)`  | `h1` S-boxes   | witness | (cube, out) for each of H1's 141 S-boxes |
//! | `[310, 592)` | `h2` S-boxes   | witness | (cube, out) for each of H2's 141 S-boxes |
//!
//! Poseidon is linear except for its S-boxes v -> v^7. The trace stores `cube = v^3` and
//! `out = cube^2 * v` for each S-box, so every constraint has degree 3. There are no
//! transition constraints: rows are independent. See `constraints` for the full list.

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
/// Two per S-box in each hash, plus 4 anchor and 8 commitment equalities.
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

/// The two trace cells of one S-box with input v: `cube = v^3`, `out = cube^2 * v = v^7`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SboxCells<F> {
    pub cube: F,
    pub out: F,
}

impl SboxCells<BabyBear> {
    pub fn compute(v: BabyBear) -> Self {
        let cube = v * v * v;
        Self { cube, out: cube * cube * v }
    }
}

/// One trace row with every cell named. `from_cells` / `to_cells` fix the column order.
#[derive(Clone, Copy, Debug)]
pub struct Row<F> {
    pub anchor: [F; 4],
    pub m: [F; 8],
    pub next: [F; 4],
    pub c: [F; 8],
    pub x: [F; 4],
    pub h1: [SboxCells<F>; SBOXES],
    pub h2: [SboxCells<F>; SBOXES],
}

impl<F: Copy> Row<F> {
    pub fn from_cells(cells: &[F]) -> Self {
        assert_eq!(cells.len(), NUM_COLS);
        let sboxes = |start: usize| -> [SboxCells<F>; SBOXES] {
            std::array::from_fn(|s| SboxCells { cube: cells[start + 2 * s], out: cells[start + 2 * s + 1] })
        };
        Row {
            anchor: std::array::from_fn(|i| cells[ANCHOR + i]),
            m: std::array::from_fn(|i| cells[M + i]),
            next: std::array::from_fn(|i| cells[NEXT + i]),
            c: std::array::from_fn(|i| cells[C + i]),
            x: std::array::from_fn(|i| cells[X + i]),
            h1: sboxes(H1_CELLS),
            h2: sboxes(H2_CELLS),
        }
    }

    pub fn to_cells(&self) -> Vec<F> {
        let mut cells = Vec::with_capacity(NUM_COLS);
        cells.extend_from_slice(&self.anchor);
        cells.extend_from_slice(&self.m);
        cells.extend_from_slice(&self.next);
        cells.extend_from_slice(&self.c);
        cells.extend_from_slice(&self.x);
        for s in self.h1.iter().chain(&self.h2) {
            cells.push(s.cube);
            cells.push(s.out);
        }
        cells
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

/// Hashes `input` and records the cells of every S-box along the way.
fn hash_with_cells(p: &Poseidon1, input: [BabyBear; WIDTH]) -> ([SboxCells<BabyBear>; SBOXES], [BabyBear; WIDTH]) {
    let mut cells = Vec::with_capacity(SBOXES);
    let out = p.permute_with(input, |v| {
        let s = SboxCells::compute(v);
        cells.push(s);
        s.out
    });
    (cells.try_into().unwrap(), out)
}

/// Witness row for (rec, x). Panics if (rec, x) is not a valid authorization.
pub fn witness_row(p: &Poseidon1, rec: &AuthRecord, x: [BabyBear; 4]) -> Row<BabyBear> {
    let (h1, out1) = hash_with_cells(p, h1_input(x));
    let (h2, out2) = hash_with_cells(p, h2_input(rec.m, x, rec.next));
    assert!(out1[..4] == rec.anchor, "H1(x) != anchor");
    assert!(out2[..8] == rec.c, "H2(m, x, next) != c");
    Row { anchor: rec.anchor, m: rec.m, next: rec.next, c: rec.c, x, h1, h2 }
}

/// `witness_row` flattened into columns.
pub fn trace_row(p: &Poseidon1, rec: &AuthRecord, x: [BabyBear; 4]) -> Vec<BabyBear> {
    witness_row(p, rec, x).to_cells()
}

/// Every constraint of one row, in this order; the row is valid iff all are zero:
///
/// 1. H1 S-boxes: `cube - v^3` and `out - cube^2 * v`, where v is the S-box input obtained by
///    replaying Poseidon on (x, 0, ..., 0) with the trace's S-box outputs.
/// 2. H2 S-boxes: the same, replaying Poseidon on (m, x, next).
/// 3. `H1(x)[i] - anchor[i]` for i in 0..4.
/// 4. `H2(m, x, next)[i] - c[i]` for i in 0..8.
///
/// Generic over the field: the prover evaluates it on BabyBear rows of the LDE, the verifier on
/// the Ext row opened at the out-of-domain point.
pub fn constraints<F: AirField>(p: &Poseidon1, row: &Row<F>) -> Vec<F> {
    let (h1_inputs, h1_out) = p.replay(h1_input(row.x), &row.h1.map(|s| s.out));
    let (h2_inputs, h2_out) = p.replay(h2_input(row.m, row.x, row.next), &row.h2.map(|s| s.out));

    let mut constraints = Vec::with_capacity(NUM_CONSTRAINTS);
    let sboxes = h1_inputs.iter().zip(&row.h1).chain(h2_inputs.iter().zip(&row.h2));
    for (&v, s) in sboxes {
        constraints.push(s.cube - v * v * v);
        constraints.push(s.out - s.cube * s.cube * v);
    }
    for i in 0..4 {
        constraints.push(h1_out[i] - row.anchor[i]);
    }
    for i in 0..8 {
        constraints.push(h2_out[i] - row.c[i]);
    }
    debug_assert_eq!(constraints.len(), NUM_CONSTRAINTS);
    constraints
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{Rng, SeedableRng};

    fn rand_elems<const N: usize>(rng: &mut impl Rng) -> [BabyBear; N] {
        std::array::from_fn(|_| BabyBear::random(rng))
    }

    #[test]
    fn row_round_trips_through_cells() {
        let p = Poseidon1::new();
        let (rec, x) = padding(&p);
        let cells = trace_row(&p, &rec, x);
        assert_eq!(cells.len(), NUM_COLS);
        assert_eq!(Row::from_cells(&cells).to_cells(), cells);
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
            let cs = constraints(&p, &witness_row(&p, &rec, x));
            assert_eq!(cs.len(), NUM_CONSTRAINTS);
            assert!(cs.iter().all(|c| c.is_zero()));
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
            let cs = constraints(&p, &Row::from_cells(&bad));
            assert!(cs.iter().any(|c| !c.is_zero()), "changing column {col} went unnoticed");
        }
    }
}

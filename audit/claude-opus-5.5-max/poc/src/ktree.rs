//! Wagner k-tree (32 lists x 2^21, 5 merge levels) for subset-sum over F_p^4.

use rayon::prelude::*;

use crate::P;

pub type V = [u32; 4];

const GROUPS: usize = 32;
const CELLS_PER_GROUP: usize = 7;
pub const CELLS_USED: usize = GROUPS * CELLS_PER_GROUP;

fn add(a: V, b: V) -> V {
    std::array::from_fn(|i| ((a[i] as u64 + b[i] as u64) % P as u64) as u32)
}

fn sub(a: V, b: V) -> V {
    std::array::from_fn(|i| ((a[i] as u64 + P as u64 - b[i] as u64) % P as u64) as u32)
}

struct Merged {
    vals: Vec<V>,
    left: Vec<u32>,
    right: Vec<u32>,
}

/// One merge condition: optionally coordinate `exact` must cancel exactly, and
/// coordinate `ic` must land in [-bound, bound] (centered mod p).
struct Cond {
    exact: Option<usize>,
    ic: usize,
    bound: u32,
}

fn ranges(center: u32, bound: u32) -> Vec<(u32, u32)> {
    if bound >= P / 2 {
        return vec![(0, P - 1)];
    }
    let lo = (center as u64 + P as u64 - bound as u64) % P as u64;
    let hi = (center as u64 + bound as u64) % P as u64;
    if lo <= hi { vec![(lo as u32, hi as u32)] } else { vec![(lo as u32, P - 1), (0, hi as u32)] }
}

fn merge(a: &[V], b: &[V], cond: &Cond, cap: usize) -> Merged {
    let key1 = |v: &V| cond.exact.map(|e| v[e]).unwrap_or(0);
    let mut sorted: Vec<(u32, u32, u32)> =
        b.iter().enumerate().map(|(i, v)| (key1(v), v[cond.ic], i as u32)).collect();
    sorted.par_sort_unstable();
    let out: Vec<(V, u32, u32)> = a
        .par_iter()
        .enumerate()
        .flat_map_iter(|(ia, va)| {
            let want1 = cond.exact.map(|e| (P - va[e]) % P).unwrap_or(0);
            let lo1 = sorted.partition_point(|t| t.0 < want1);
            let hi1 = sorted.partition_point(|t| t.0 <= want1);
            let slice = &sorted[lo1..hi1];
            let center = (P - va[cond.ic]) % P;
            let mut found = Vec::new();
            for (lo, hi) in ranges(center, cond.bound) {
                let s = slice.partition_point(|t| t.1 < lo);
                let e = slice.partition_point(|t| t.1 <= hi);
                for t in &slice[s..e] {
                    found.push((add(*va, b[t.2 as usize]), ia as u32, t.2));
                }
            }
            found
        })
        .collect();
    let take = out.len().min(cap);
    Merged {
        vals: out[..take].iter().map(|t| t.0).collect(),
        left: out[..take].iter().map(|t| t.1).collect(),
        right: out[..take].iter().map(|t| t.2).collect(),
    }
}

/// `options[c]` are the 8 vectors cell `c` can contribute (index 0 should be
/// the zero vector). Returns one option index per cell for the first
/// `CELLS_USED` cells (the rest are left at option 0), or None.
pub fn solve(options: &[[V; 8]], target: V) -> Option<Vec<u8>> {
    assert!(options.len() >= CELLS_USED);
    // Level 0: every option combination of each group of 7 cells. Combination
    // id = base-8 digits, first cell most significant.
    let level0: Vec<Vec<V>> = (0..GROUPS)
        .into_par_iter()
        .map(|g| {
            let mut list: Vec<V> = vec![if g == 0 { sub([0; 4], target) } else { [0; 4] }];
            for c in 0..CELLS_PER_GROUP {
                let opts = &options[g * CELLS_PER_GROUP + c];
                let mut next = Vec::with_capacity(list.len() * 8);
                for v in &list {
                    for o in opts {
                        next.push(add(*v, *o));
                    }
                }
                list = next;
            }
            list
        })
        .collect();

    // Each merge keeps a 1/L fraction of the L^2 pairs, so list sizes stay ~L.
    let p = P as f64;
    let l = (1u64 << 21) as f64;
    // coord0 into [-b1, b1]
    let b1 = (p / l / 2.0) as u32;
    // coord0 exact (prob 1/(2b1+1)) and coord1 into [-b2, b2]
    let b2 = ((2 * b1 + 1) as f64 * p / l / 2.0) as u32;
    // coord1 exact (prob 1/(2b2+1)) and coord2 into [-b3, b3]
    let b3 = ((2 * b2 + 1) as f64 * p / l / 2.0) as u32;
    // coord2 of the sum (spread 2b3+1) into [-b4, b4]
    let b4 = ((2 * b3 + 1) as f64 / l / 2.0) as u32;
    eprintln!("[ktree] bounds b1={b1} b2={b2} b3={b3} b4={b4}");
    let conds = [
        Cond { exact: None, ic: 0, bound: b1 },
        Cond { exact: Some(0), ic: 1, bound: b2 },
        Cond { exact: Some(1), ic: 2, bound: b3 },
        Cond { exact: None, ic: 2, bound: b4 },
        Cond { exact: Some(2), ic: 3, bound: 0 },
    ];
    let cap = 1usize << 23;

    let mut levels: Vec<Merged> = Vec::new();
    for (li, cond) in conds.iter().enumerate() {
        let lists: Vec<&[V]> = if li == 0 {
            level0.iter().map(|v| v.as_slice()).collect()
        } else {
            let prev_start = levels.len() - (GROUPS >> li);
            levels[prev_start..].iter().map(|m| m.vals.as_slice()).collect()
        };
        let merged: Vec<Merged> =
            (0..lists.len() / 2).map(|j| merge(lists[2 * j], lists[2 * j + 1], cond, cap)).collect();
        eprintln!(
            "[ktree] level {}: {} lists, sizes {:?}",
            li + 1,
            merged.len(),
            merged.iter().map(|m| m.vals.len()).collect::<Vec<_>>()
        );
        levels.extend(merged);
    }

    // levels holds 16 + 8 + 4 + 2 + 1 lists; the last one holds solutions.
    let root = levels.last().unwrap();
    let e = root.vals.iter().position(|v| *v == [0; 4])?;

    // Walk back down: list j at merge level l came from lists 2j, 2j+1 of level l-1.
    let offsets = [0usize, 16, 24, 28, 30];
    let mut choice = vec![0u8; options.len()];
    let mut stack = vec![(4usize, 0usize, e as u32)];
    while let Some((lvl, j, idx)) = stack.pop() {
        let m = &levels[offsets[lvl] + j];
        let (l, r) = (m.left[idx as usize], m.right[idx as usize]);
        if lvl == 0 {
            for (g, id) in [(2 * j, l), (2 * j + 1, r)] {
                for c in 0..CELLS_PER_GROUP {
                    let digit = (id >> (3 * (CELLS_PER_GROUP - 1 - c))) & 7;
                    choice[g * CELLS_PER_GROUP + c] = digit as u8;
                }
            }
        } else {
            stack.push((lvl - 1, 2 * j, l));
            stack.push((lvl - 1, 2 * j + 1, r));
        }
    }
    let total = choice.iter().enumerate().fold([0; 4], |acc, (c, &o)| add(acc, options[c][o as usize]));
    assert_eq!(total, target, "k-tree backtracking produced a wrong sum");
    Some(choice)
}

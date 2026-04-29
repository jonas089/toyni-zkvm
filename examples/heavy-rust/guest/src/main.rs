#![no_std]
#![no_main]

zkvm_guest::entry!(main);

const ITERATIONS: u32 = 150_000;

fn main() {
    let seed: u32 = zkvm_guest::read();
    let mut acc: u32 = seed.wrapping_add(1);

    let mut i: u32 = 0;
    while i < ITERATIONS {
        acc = acc.wrapping_mul(1664525).wrapping_add(1013904223);
        acc ^= i;
        i = i.wrapping_add(1);
    }

    zkvm_guest::commit(acc);
}

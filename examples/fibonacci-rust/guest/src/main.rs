#![no_std]
#![no_main]

zkvm_guest::entry!(main);

fn main() {
    let n: u32 = zkvm_guest::read();

    let mut a: u32 = 0;
    let mut b: u32 = 1;
    for _ in 0..n {
        let t = a.wrapping_add(b);
        a = b;
        b = t;
    }

    zkvm_guest::commit(b);
}

//! Guest-side library for programs running inside the ZKVM.
//!
//! Provides I/O primitives and an entry point macro for `#[no_std]` RISC-V guest programs.
//!
//! # Usage
//! ```ignore
//! #![no_std]
//! #![no_main]
//!
//! zkvm_guest::entry!(main);
//!
//! fn main() {
//!     let n: u32 = zkvm_guest::read();
//!     let result = n * 2;
//!     zkvm_guest::commit(result);
//! }
//! ```

#![no_std]

/// Input tape base address in VM memory.
const INPUT_TAPE_ADDR: u32 = 0x0020_0000;
/// Output tape base address in VM memory.
const OUTPUT_TAPE_ADDR: u32 = 0x0030_0000;

/// Global read cursor (starts after the public input count word).
static mut READ_CURSOR: u32 = INPUT_TAPE_ADDR + 4;
/// Global output count.
static mut OUTPUT_COUNT: u32 = 0;

/// Read a `u32` value from the input tape.
///
/// Reads sequentially: first call returns the first public input,
/// second call returns the second, etc. After public inputs are
/// exhausted, reads continue into private inputs (skipping the
/// private count word automatically).
#[inline(never)]
pub fn read() -> u32 {
    unsafe {
        let ptr = READ_CURSOR as *const u32;
        let val = ptr.read_volatile();
        READ_CURSOR += 4;
        val
    }
}

/// Write a `u32` value to the output tape.
///
/// Each call appends one word and increments the output count.
#[inline(never)]
pub fn commit(val: u32) {
    unsafe {
        OUTPUT_COUNT += 1;
        // Write count at offset 0
        (OUTPUT_TAPE_ADDR as *mut u32).write_volatile(OUTPUT_COUNT);
        // Write value at offset 4 * count
        let addr = OUTPUT_TAPE_ADDR + OUTPUT_COUNT * 4;
        (addr as *mut u32).write_volatile(val);
    }
}

/// Define the guest program entry point.
///
/// This macro generates `_start` (the ELF entry point) and a panic handler.
/// The provided function is called as the guest's main logic.
///
/// # Example
/// ```ignore
/// zkvm_guest::entry!(main);
///
/// fn main() {
///     let x: u32 = zkvm_guest::read();
///     zkvm_guest::commit(x + 1);
/// }
/// ```
#[macro_export]
macro_rules! entry {
    ($path:path) => {
        #[unsafe(no_mangle)]
        pub extern "C" fn _start() -> ! {
            let f: fn() = $path;
            f();
            unsafe { core::arch::asm!("ecall", options(noreturn)) }
        }

        #[panic_handler]
        fn _panic(_info: &core::panic::PanicInfo) -> ! {
            unsafe { core::arch::asm!("ebreak", options(noreturn)) }
        }
    };
}

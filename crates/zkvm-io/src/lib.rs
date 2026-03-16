#![cfg_attr(not(feature = "std"), no_std)]

// ZKVM I/O tape API.
// Provides deterministic input/output for programs running inside the ZKVM.

/// Address where the input tape starts in VM memory.
pub const INPUT_TAPE_ADDR: u32 = 0x0020_0000;
/// Address where the output buffer starts in VM memory.
pub const OUTPUT_TAPE_ADDR: u32 = 0x0030_0000;
/// Maximum input/output size in bytes.
pub const MAX_IO_SIZE: u32 = 0x0010_0000; // 1 MiB

/// Input tape layout:
///   [0..4]   : number of public input words (u32)
///   [4..4+4n]: public input words
///   [4+4n..] : private input words (prefixed with count)

/// Initialize the input tape in VM memory with public and private inputs.
#[cfg(feature = "std")]
pub fn init_input_tape(
    mem: &mut zkvm_core::memory::Memory,
    public_inputs: &[u32],
    private_inputs: &[u32],
) {
    let mut offset = INPUT_TAPE_ADDR;

    // Write public input count and values
    mem.write_bytes_no_log(offset, &(public_inputs.len() as u32).to_le_bytes());
    offset += 4;
    for &val in public_inputs {
        mem.write_bytes_no_log(offset, &val.to_le_bytes());
        offset += 4;
    }

    // Write private input count and values
    mem.write_bytes_no_log(offset, &(private_inputs.len() as u32).to_le_bytes());
    offset += 4;
    for &val in private_inputs {
        mem.write_bytes_no_log(offset, &val.to_le_bytes());
        offset += 4;
    }
}

/// Read the output buffer from VM memory.
#[cfg(feature = "std")]
pub fn read_outputs(mem: &zkvm_core::memory::Memory) -> Vec<u32> {
    let count = mem.peek_word(OUTPUT_TAPE_ADDR) as usize;
    let mut outputs = Vec::with_capacity(count);
    for i in 0..count {
        let addr = OUTPUT_TAPE_ADDR + 4 + (i as u32) * 4;
        outputs.push(mem.peek_word(addr));
    }
    outputs
}

#[cfg(feature = "std")]
pub use zkvm_core;

#[cfg(feature = "std")]
#[cfg(test)]
mod tests {
    use super::*;
    use zkvm_core::memory::Memory;

    #[test]
    fn test_input_tape_roundtrip() {
        let mut mem = Memory::new(1 << 24);
        let public = vec![1u32, 2, 3];
        let private = vec![42u32, 99];
        init_input_tape(&mut mem, &public, &private);

        // Read back public inputs
        let count = mem.peek_word(INPUT_TAPE_ADDR);
        assert_eq!(count, 3);
        assert_eq!(mem.peek_word(INPUT_TAPE_ADDR + 4), 1);
        assert_eq!(mem.peek_word(INPUT_TAPE_ADDR + 8), 2);
        assert_eq!(mem.peek_word(INPUT_TAPE_ADDR + 12), 3);

        // Read back private inputs
        let priv_offset = INPUT_TAPE_ADDR + 4 + 3 * 4;
        let priv_count = mem.peek_word(priv_offset);
        assert_eq!(priv_count, 2);
        assert_eq!(mem.peek_word(priv_offset + 4), 42);
        assert_eq!(mem.peek_word(priv_offset + 8), 99);
    }
}

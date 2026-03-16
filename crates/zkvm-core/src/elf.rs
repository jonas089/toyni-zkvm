/// Minimal ELF loader for RV32I flat binaries.
/// Supports loading .text and .rodata segments into VM memory.

use crate::memory::Memory;

/// ELF magic number.
const ELF_MAGIC: [u8; 4] = [0x7f, b'E', b'L', b'F'];

/// Load a RISC-V ELF binary into memory.
/// Returns the entry point address.
pub fn load_elf(elf_bytes: &[u8], mem: &mut Memory) -> Result<u32, String> {
    if elf_bytes.len() < 52 {
        return Err("ELF too small".into());
    }
    if elf_bytes[0..4] != ELF_MAGIC {
        return Err("Not an ELF file".into());
    }

    // Check ELF32
    let ei_class = elf_bytes[4];
    if ei_class != 1 {
        return Err("Expected ELF32".into());
    }

    // Check little-endian
    let ei_data = elf_bytes[5];
    if ei_data != 1 {
        return Err("Expected little-endian".into());
    }

    let entry = u32_le(&elf_bytes[24..28]);
    let phoff = u32_le(&elf_bytes[28..32]) as usize;
    let phentsize = u16_le(&elf_bytes[42..44]) as usize;
    let phnum = u16_le(&elf_bytes[44..46]) as usize;

    for i in 0..phnum {
        let off = phoff + i * phentsize;
        if off + phentsize > elf_bytes.len() {
            return Err("Program header out of bounds".into());
        }
        let ph = &elf_bytes[off..off + phentsize];

        let p_type = u32_le(&ph[0..4]);
        // PT_LOAD = 1
        if p_type != 1 {
            continue;
        }

        let p_offset = u32_le(&ph[4..8]) as usize;
        let p_vaddr = u32_le(&ph[8..12]);
        let p_filesz = u32_le(&ph[16..20]) as usize;
        let p_memsz = u32_le(&ph[20..24]) as usize;

        // Load file content
        if p_filesz > 0 {
            let end = p_offset + p_filesz;
            if end > elf_bytes.len() {
                return Err(format!(
                    "Segment data out of bounds: offset={}, filesz={}",
                    p_offset, p_filesz
                ));
            }
            mem.write_bytes_no_log(p_vaddr, &elf_bytes[p_offset..end]);
        }

        // Zero-fill BSS (memsz > filesz)
        if p_memsz > p_filesz {
            let bss_start = p_vaddr + p_filesz as u32;
            let bss_len = p_memsz - p_filesz;
            let zeros = vec![0u8; bss_len];
            mem.write_bytes_no_log(bss_start, &zeros);
        }
    }

    Ok(entry)
}

/// Load a flat binary (raw instruction words) into memory at a given address.
/// Returns the entry point (= base address).
pub fn load_flat_binary(code: &[u8], base_addr: u32, mem: &mut Memory) -> u32 {
    mem.write_bytes_no_log(base_addr, code);
    base_addr
}

fn u16_le(b: &[u8]) -> u16 {
    u16::from_le_bytes([b[0], b[1]])
}

fn u32_le(b: &[u8]) -> u32 {
    u32::from_le_bytes([b[0], b[1], b[2], b[3]])
}

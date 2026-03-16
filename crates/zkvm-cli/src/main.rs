/// ZKVM CLI: build, prove, and verify RISC-V programs.

use sha2::{Digest, Sha256};
use std::env;
use std::fs;
use std::process;

use zkvm_core::cpu::Cpu;
use zkvm_core::memory::Memory;
use zkvm_prover::ZkvmProver;
use zkvm_verifier::ZkvmVerifier;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: zkvm-cli <command> [options]");
        eprintln!("Commands:");
        eprintln!("  prove  <binary> [--cuda]  - Run VM and generate proof");
        eprintln!("  verify <binary>           - Verify a proof");
        process::exit(1);
    }

    match args[1].as_str() {
        "prove" => cmd_prove(&args[2..]),
        "verify" => cmd_verify(&args[2..]),
        other => {
            eprintln!("Unknown command: {}", other);
            process::exit(1);
        }
    }
}

fn cmd_prove(args: &[String]) {
    if args.is_empty() {
        eprintln!("Usage: zkvm-cli prove <binary> [--cuda]");
        process::exit(1);
    }

    let binary_path = &args[0];
    let use_cuda = args.iter().any(|a| a == "--cuda");

    let code = fs::read(binary_path).unwrap_or_else(|e| {
        eprintln!("Failed to read {}: {}", binary_path, e);
        process::exit(1);
    });

    // Load and run
    let mut mem = Memory::new(1 << 24);
    let entry = zkvm_core::elf::load_elf(&code, &mut mem).unwrap_or_else(|e| {
        eprintln!("ELF load failed: {}. Trying flat binary.", e);
        zkvm_core::elf::load_flat_binary(&code, 0x1000, &mut mem)
    });

    eprintln!("Entry point: 0x{:08x}", entry);
    let mut cpu = Cpu::new(entry);
    let mut trace = cpu.run(&mut mem, 1 << 20);
    eprintln!(
        "Execution finished: {} cycles, halt={:?}",
        trace.len(),
        cpu.halt_reason
    );

    // Read outputs
    let outputs = zkvm_io::read_outputs(&mem);
    eprintln!("Public outputs: {:?}", outputs);

    // Pad and convert to columns
    trace.pad_to_power_of_two();

    // Extract program ROM and compute hash
    let mut program_rom = extract_program_rom(&code);
    program_rom.sort_by_key(|&(a, _)| a);
    program_rom.dedup_by_key(|e| e.0);
    let program_hash = hash_program_rom(&program_rom);

    let num_real_steps = trace.num_real_steps;
    let n = trace.rows.len();
    let padding_start_pc = if num_real_steps < n { trace.rows[num_real_steps].pc } else { 0 };

    trace.prepare_sorted_tables(&program_rom);
    let columns = trace.to_columns();

    // Prove
    eprintln!("Generating proof (use_gpu={})...", use_cuda);
    let prover = ZkvmProver::new(
        columns, program_hash, vec![], outputs.clone(), entry,
        program_rom, padding_start_pc, num_real_steps,
    );
    let proof = prover.prove(use_cuda);
    eprintln!("Proof generated. Trace length: {}", proof.trace_len);

    // Verify immediately
    let verifier = ZkvmVerifier;
    let ok = verifier.verify(&proof);
    if ok {
        eprintln!("Proof VERIFIED successfully.");
    } else {
        eprintln!("Proof FAILED verification!");
        process::exit(1);
    }
}

fn extract_program_rom(elf_bytes: &[u8]) -> Vec<(u32, u32)> {
    let mut table = Vec::new();
    if elf_bytes.len() < 52 || elf_bytes[0..4] != [0x7f, b'E', b'L', b'F'] {
        return table;
    }
    let phoff = u32::from_le_bytes([elf_bytes[28], elf_bytes[29], elf_bytes[30], elf_bytes[31]]) as usize;
    let phentsize = u16::from_le_bytes([elf_bytes[42], elf_bytes[43]]) as usize;
    let phnum = u16::from_le_bytes([elf_bytes[44], elf_bytes[45]]) as usize;
    for i in 0..phnum {
        let off = phoff + i * phentsize;
        if off + phentsize > elf_bytes.len() { break; }
        let ph = &elf_bytes[off..off + phentsize];
        let p_type = u32::from_le_bytes([ph[0], ph[1], ph[2], ph[3]]);
        if p_type != 1 { continue; }
        let p_offset = u32::from_le_bytes([ph[4], ph[5], ph[6], ph[7]]) as usize;
        let p_vaddr = u32::from_le_bytes([ph[8], ph[9], ph[10], ph[11]]);
        let p_filesz = u32::from_le_bytes([ph[16], ph[17], ph[18], ph[19]]) as usize;
        let p_flags = u32::from_le_bytes([ph[24], ph[25], ph[26], ph[27]]);
        if p_flags & 1 == 0 { continue; }
        let end = (p_offset + p_filesz).min(elf_bytes.len());
        let data = &elf_bytes[p_offset..end];
        for (j, chunk) in data.chunks_exact(4).enumerate() {
            let addr = p_vaddr + (j as u32) * 4;
            let instr = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
            table.push((addr, instr));
        }
    }
    table
}

fn hash_program_rom(rom: &[(u32, u32)]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for &(addr, instr) in rom {
        hasher.update(addr.to_le_bytes());
        hasher.update(instr.to_le_bytes());
    }
    hasher.finalize().into()
}

fn cmd_verify(args: &[String]) {
    if args.is_empty() {
        eprintln!("Usage: zkvm-cli verify <binary>");
        eprintln!("(Re-runs prove + verify for now; serialized proofs coming in v2)");
        process::exit(1);
    }
    // For v1, just re-run the prove path which includes verification
    cmd_prove(args);
}

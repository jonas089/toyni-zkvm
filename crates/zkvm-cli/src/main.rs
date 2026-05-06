//! `zkvm-cli prove <file.mini|file.asm> [-i N N N ...] [--cuda]`
//!
//! Compiles the program (mini -> asm -> instructions; or asm directly),
//! runs the VM, builds the trace, generates a STARK proof and verifies it.

mod asm;
mod mini;

use std::env;
use std::fs;
use std::process;

use zkvm_core::{build_columns, hash_program, run, Instruction};
use zkvm_prover::ZkvmProver;
use zkvm_verifier::ZkvmVerifier;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: zkvm-cli prove <file.mini|file.asm> [-i N N N ...] [--cuda]");
        process::exit(1);
    }
    match args[1].as_str() {
        "prove" => cmd_prove(&args[2..]),
        other => { eprintln!("unknown command: {}", other); process::exit(1); }
    }
}

fn cmd_prove(args: &[String]) {
    let path = &args[0];
    let mut public_inputs: Vec<u32> = Vec::new();
    let mut use_cuda = false;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--cuda" => { use_cuda = true; i += 1; }
            "-i" => {
                i += 1;
                while i < args.len() && !args[i].starts_with("--") && args[i] != "-i" {
                    let v: u64 = args[i].parse().expect("bad public input");
                    public_inputs.push((v % zkvm_core::P as u64) as u32);
                    i += 1;
                }
            }
            other => { eprintln!("unknown flag: {}", other); process::exit(1); }
        }
    }

    let src = fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("failed to read {}: {}", path, e);
        process::exit(1);
    });

    let asm_src = if path.ends_with(".mini") {
        eprintln!("[cli] compiling mini -> asm");
        match mini::compile(&src) {
            Ok(s) => s,
            Err(e) => { eprintln!("mini compile error: {}", e); process::exit(1); }
        }
    } else {
        src
    };
    if env::var("ZKVM_DUMP_ASM").is_ok() {
        eprintln!("--- ASM ---\n{}---", asm_src);
    }

    let program: Vec<Instruction> = match asm::assemble(&asm_src) {
        Ok(p) => p,
        Err(e) => { eprintln!("assemble error: {}", e); process::exit(1); }
    };
    eprintln!("[cli] program: {} instructions", program.len());

    let max_steps = 1usize << 20;
    let (records, outputs) = match run(&program, &public_inputs, max_steps) {
        Ok(r) => r,
        Err(e) => { eprintln!("run error: {}", e); process::exit(1); }
    };
    eprintln!("[cli] executed {} cycles, outputs={:?}", records.len(), outputs);

    let (columns, _n_real) = build_columns(&records, &program, &public_inputs, &outputs);
    let program_hash = hash_program(&program);
    let program_rom: Vec<(u32, u32, u32, u32, u32)> = program.iter().enumerate()
        .map(|(i, ins)| (i as u32, ins.op as u32, ins.a, ins.b, ins.c))
        .collect();

    eprintln!("[cli] generating proof (cuda={})...", use_cuda);
    let prover = ZkvmProver::new(
        columns,
        program_hash,
        public_inputs.clone(),
        outputs.clone(),
        0, // entry_pc
        program_rom,
    );
    let proof = prover.prove(use_cuda);

    eprintln!("[cli] verifying proof...");
    let verifier = ZkvmVerifier;
    if verifier.verify(&proof) {
        eprintln!("[cli] proof VERIFIED. trace_len={}, outputs={:?}", proof.trace_len, proof.public_outputs);
    } else {
        eprintln!("[cli] proof FAILED verification");
        process::exit(1);
    }
}

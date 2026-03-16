/// Host-side SDK for loading, executing, and proving ZKVM guest programs.

use sha2::{Digest, Sha256};
use zkvm_core::cpu::Cpu;
use zkvm_core::elf;
use zkvm_core::memory::Memory;
use zkvm_prover::{ZkvmProof, ZkvmProver};
use zkvm_verifier::ZkvmVerifier;

/// A proven execution receipt containing the proof and public outputs.
pub struct Receipt {
    pub proof: ZkvmProof,
    pub outputs: Vec<u32>,
}

impl Receipt {
    /// Verify the proof.
    pub fn verify(&self) -> bool {
        let verifier = ZkvmVerifier;
        verifier.verify(&self.proof)
    }
}

/// Builder for configuring and running a guest program proof.
pub struct ProverBuilder {
    elf_bytes: Vec<u8>,
    public_inputs: Vec<u32>,
    private_inputs: Vec<u32>,
    cycle_limit: u32,
}

impl ProverBuilder {
    /// Create a new builder from an ELF binary.
    pub fn from_elf(elf_bytes: &[u8]) -> Self {
        Self {
            elf_bytes: elf_bytes.to_vec(),
            public_inputs: Vec::new(),
            private_inputs: Vec::new(),
            cycle_limit: 1 << 20,
        }
    }

    /// Add a public input value.
    pub fn add_input(&mut self, val: u32) -> &mut Self {
        self.public_inputs.push(val);
        self
    }

    /// Add a private (witness) input value.
    pub fn add_private_input(&mut self, val: u32) -> &mut Self {
        self.private_inputs.push(val);
        self
    }

    /// Set the maximum cycle count (default: 1M).
    pub fn set_cycle_limit(&mut self, limit: u32) -> &mut Self {
        self.cycle_limit = limit;
        self
    }

    /// Execute the guest program and generate a STARK proof.
    pub fn prove(&self) -> Receipt {
        // Set up memory (16 MiB)
        let mut mem = Memory::new(1 << 24);

        // Load ELF
        let entry_pc = elf::load_elf(&self.elf_bytes, &mut mem)
            .expect("Failed to load ELF");

        // Initialize input tape
        zkvm_io::init_input_tape(&mut mem, &self.public_inputs, &self.private_inputs);

        // Run the VM
        let mut cpu = Cpu::new(entry_pc);
        let mut trace = cpu.run(&mut mem, self.cycle_limit);

        if !cpu.halted {
            panic!("Guest program did not halt within {} cycles", self.cycle_limit);
        }

        // Read outputs
        let outputs = zkvm_io::read_outputs(&mem);

        // Prepare trace for proving
        trace.pad_to_power_of_two();

        // Build program ROM from ELF code section
        let mut program_rom = extract_program_table(&self.elf_bytes);
        program_rom.sort_by_key(|&(a, _)| a);
        program_rom.dedup_by_key(|e| e.0);

        // Hash the program ROM (not the ELF) for verifier binding
        let program_hash = hash_program_rom(&program_rom);

        // Compute padding start PC
        let num_real_steps = trace.num_real_steps;
        let n = trace.rows.len();
        let padding_start_pc = if num_real_steps < n {
            trace.rows[num_real_steps].pc
        } else {
            0
        };

        trace.prepare_sorted_tables(&program_rom);

        let columns = trace.to_columns();

        // Validate main trace constraints
        zkvm_air::validate_trace(&columns)
            .expect("Trace validation failed");

        // Validate full trace with accumulators (pre-check before proving)
        {
            use toyni::babybear::BabyBear;
            let gammas: [BabyBear; 4] = [
                BabyBear::new(12345), BabyBear::new(23456),
                BabyBear::new(34567), BabyBear::new(45678),
            ];
            let alphas: [BabyBear; 4] = [
                BabyBear::new(56789), BabyBear::new(67890),
                BabyBear::new(78901), BabyBear::new(89012),
            ];
            let accum_columns = zkvm_air::permutation::compute_accumulators(&columns, &gammas, &alphas);
            zkvm_air::validate_full_trace(&columns, &accum_columns, &gammas, &alphas)
                .expect("Full trace validation failed");
        }

        // Generate proof
        let prover = ZkvmProver::new(
            columns,
            program_hash,
            self.public_inputs.clone(),
            outputs.clone(),
            entry_pc,
            program_rom,
            padding_start_pc,
            num_real_steps,
        );
        let proof = prover.prove(false);

        Receipt { proof, outputs }
    }
}

/// Extract (address, instruction) pairs from an ELF binary for the program table.
fn extract_program_table(elf_bytes: &[u8]) -> Vec<(u32, u32)> {
    let mut table = Vec::new();

    if elf_bytes.len() < 52 || elf_bytes[0..4] != [0x7f, b'E', b'L', b'F'] {
        return table;
    }

    let phoff = u32::from_le_bytes([elf_bytes[28], elf_bytes[29], elf_bytes[30], elf_bytes[31]]) as usize;
    let phentsize = u16::from_le_bytes([elf_bytes[42], elf_bytes[43]]) as usize;
    let phnum = u16::from_le_bytes([elf_bytes[44], elf_bytes[45]]) as usize;

    for i in 0..phnum {
        let off = phoff + i * phentsize;
        if off + phentsize > elf_bytes.len() {
            break;
        }
        let ph = &elf_bytes[off..off + phentsize];

        let p_type = u32::from_le_bytes([ph[0], ph[1], ph[2], ph[3]]);
        if p_type != 1 { // PT_LOAD
            continue;
        }

        let p_offset = u32::from_le_bytes([ph[4], ph[5], ph[6], ph[7]]) as usize;
        let p_vaddr = u32::from_le_bytes([ph[8], ph[9], ph[10], ph[11]]);
        let p_filesz = u32::from_le_bytes([ph[16], ph[17], ph[18], ph[19]]) as usize;
        let p_flags = u32::from_le_bytes([ph[24], ph[25], ph[26], ph[27]]);

        // PF_X = 1 (executable segment)
        if p_flags & 1 == 0 {
            continue;
        }

        // Extract instructions (4 bytes each)
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

/// Hash the program ROM table (sorted addr/instr pairs) for verifier binding.
fn hash_program_rom(rom: &[(u32, u32)]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for &(addr, instr) in rom {
        hasher.update(addr.to_le_bytes());
        hasher.update(instr.to_le_bytes());
    }
    hasher.finalize().into()
}

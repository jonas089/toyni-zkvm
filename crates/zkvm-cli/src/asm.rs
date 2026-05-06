//! Assembler for the small custom VM.
//!
//! Grammar (one instruction per line, comments with `;`, labels end with `:`):
//!
//!   ADD   rd, ra, rb
//!   SUB   rd, ra, rb
//!   MUL   rd, ra, rb
//!   IMM   rd, K          (K is a decimal field-element literal)
//!   LOAD  rd, ra
//!   STORE ra, rb
//!   JMP   label
//!   JZ    ra, label
//!   READ  rd
//!   WRITE ra
//!   HALT
//!   MOV   rd, rs         (pseudo: ADD rd, rs, r0)

use std::collections::HashMap;

use zkvm_core::{Instruction, Opcode};

pub fn assemble(src: &str) -> Result<Vec<Instruction>, String> {
    // Two-pass: first pass collects label addresses, second pass emits code.
    let lines: Vec<(usize, &str)> = src
        .lines()
        .enumerate()
        .map(|(i, l)| (i + 1, l.split(';').next().unwrap().trim()))
        .filter(|(_, l)| !l.is_empty())
        .collect();

    let mut labels: HashMap<String, u32> = HashMap::new();
    let mut pc: u32 = 0;
    let mut body: Vec<(usize, &str)> = Vec::new();
    for &(lineno, l) in &lines {
        if let Some(name) = l.strip_suffix(':') {
            if labels.insert(name.trim().to_string(), pc).is_some() {
                return Err(format!("line {}: duplicate label '{}'", lineno, name));
            }
        } else {
            body.push((lineno, l));
            pc += 1;
        }
    }

    let mut out = Vec::new();
    for (lineno, l) in body {
        out.push(parse_line(l, &labels).map_err(|e| format!("line {}: {}", lineno, e))?);
    }
    Ok(out)
}

fn parse_reg(s: &str) -> Result<u32, String> {
    let s = s.trim();
    if !s.starts_with('r') {
        return Err(format!("expected register (e.g. r0..r7), got '{}'", s));
    }
    let n: u32 = s[1..].parse().map_err(|_| format!("bad register '{}'", s))?;
    if n >= 8 { return Err(format!("register out of range: r{}", n)); }
    Ok(n)
}

fn parse_imm_or_label(s: &str, labels: &HashMap<String, u32>) -> Result<u32, String> {
    let s = s.trim();
    if let Some(&p) = labels.get(s) { return Ok(p); }
    s.parse::<u64>()
        .map(|v| (v % zkvm_core::P as u64) as u32)
        .map_err(|_| format!("bad immediate / unknown label '{}'", s))
}

fn parse_line(line: &str, labels: &HashMap<String, u32>) -> Result<Instruction, String> {
    let mut parts = line.splitn(2, char::is_whitespace);
    let mnemonic = parts.next().ok_or("empty line")?.to_uppercase();
    let rest = parts.next().unwrap_or("").trim();
    let args: Vec<&str> = if rest.is_empty() { Vec::new() } else { rest.split(',').collect() };

    let need = |n: usize| {
        if args.len() != n { return Err(format!("{} expects {} arg(s), got {}", mnemonic, n, args.len())); }
        Ok(())
    };

    Ok(match mnemonic.as_str() {
        "ADD" => { need(3)?;
            Instruction { op: Opcode::Add, a: parse_reg(args[0])?, b: parse_reg(args[1])?, c: parse_reg(args[2])? }
        }
        "SUB" => { need(3)?;
            Instruction { op: Opcode::Sub, a: parse_reg(args[0])?, b: parse_reg(args[1])?, c: parse_reg(args[2])? }
        }
        "MUL" => { need(3)?;
            Instruction { op: Opcode::Mul, a: parse_reg(args[0])?, b: parse_reg(args[1])?, c: parse_reg(args[2])? }
        }
        "IMM" => { need(2)?;
            Instruction { op: Opcode::Imm, a: parse_reg(args[0])?, b: parse_imm_or_label(args[1], labels)?, c: 0 }
        }
        "LOAD" => { need(2)?;
            Instruction { op: Opcode::Load, a: parse_reg(args[0])?, b: parse_reg(args[1])?, c: 0 }
        }
        "STORE" => { need(2)?;
            Instruction { op: Opcode::Store, a: parse_reg(args[0])?, b: parse_reg(args[1])?, c: 0 }
        }
        "JMP" => { need(1)?;
            Instruction { op: Opcode::Jmp, a: parse_imm_or_label(args[0], labels)?, b: 0, c: 0 }
        }
        "JZ" => { need(2)?;
            Instruction { op: Opcode::Jz, a: parse_reg(args[0])?, b: parse_imm_or_label(args[1], labels)?, c: 0 }
        }
        "READ" => { need(1)?;
            Instruction { op: Opcode::Read, a: parse_reg(args[0])?, b: 0, c: 0 }
        }
        "WRITE" => { need(1)?;
            Instruction { op: Opcode::Write, a: parse_reg(args[0])?, b: 0, c: 0 }
        }
        "HALT" => { need(0)?;
            Instruction { op: Opcode::Halt, a: 0, b: 0, c: 0 }
        }
        "MOV" => { need(2)?;
            // MOV rd, rs => ADD rd, rs, r0
            Instruction { op: Opcode::Add, a: parse_reg(args[0])?, b: parse_reg(args[1])?, c: 0 }
        }
        other => return Err(format!("unknown mnemonic '{}'", other)),
    })
}

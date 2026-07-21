//! Both engines: a valid proof verifies, and tampering is rejected.

use toyni::field::Field;
use toyni::{CircleEngine, ClassicalEngine, Engine};
use zkvm_core::{build_columns, hash_program, run, Instruction, Opcode, P, P_M31};
use zkvm_prover::ZkvmProver;
use zkvm_verifier::verify;

fn program() -> Vec<Instruction> {
    // r1 = 5; write r1; halt.
    vec![
        Instruction { op: Opcode::Imm, a: 1, b: 5, c: 0 },
        Instruction { op: Opcode::Write, a: 1, b: 0, c: 0 },
        Instruction { op: Opcode::Halt, a: 0, b: 0, c: 0 },
    ]
}

fn roundtrip<E: Engine + Clone>(p: u32) {
    let prog = program();
    let (records, outputs) = run(&prog, &[], 1 << 20, p).unwrap();
    let (columns, _) = build_columns::<E::Base>(&records, &prog, &[], &outputs);
    let hash = hash_program(&prog);
    let rom: Vec<_> = prog
        .iter()
        .enumerate()
        .map(|(i, ins)| (i as u32, ins.op as u32, ins.a, ins.b, ins.c))
        .collect();
    let proof = ZkvmProver::<E>::new(columns, hash, vec![], outputs, 0, rom).prove();

    // Honest proof verifies.
    assert!(verify::<E>(&proof, &hash, 0), "{}: honest proof rejected", E::label());
    // Wrong program hash / entry pc rejected.
    let mut bad_hash = hash;
    bad_hash[0] ^= 0xff;
    assert!(!verify::<E>(&proof, &bad_hash, 0), "{}: wrong hash accepted", E::label());
    assert!(!verify::<E>(&proof, &hash, 1), "{}: wrong entry_pc accepted", E::label());

    // Tamper the out-of-domain quotient value → OOD identity fails.
    let mut p1 = proof.clone();
    p1.q_z = p1.q_z + E::Ext::ONE;
    assert!(!verify::<E>(&p1, &hash, 0), "{}: tampered q_z accepted", E::label());

    // Tamper a committed trace root → Merkle openings fail.
    let mut p2 = proof.clone();
    p2.trace_root[0] ^= 0xff;
    assert!(!verify::<E>(&p2, &hash, 0), "{}: tampered trace root accepted", E::label());

    // Tamper an out-of-domain trace value → identity / DEEP fails.
    let mut p3 = proof.clone();
    p3.trace_at_z[0] = p3.trace_at_z[0] + E::Ext::ONE;
    assert!(!verify::<E>(&p3, &hash, 0), "{}: tampered ood trace accepted", E::label());
}


#[test]
fn classical_soundness() {
    roundtrip::<ClassicalEngine>(P);
}

#[test]
fn circle_soundness() {
    roundtrip::<CircleEngine>(P_M31);
}

/// AIR (Algebraic Intermediate Representation) for the RISC-V ZKVM.
///
/// Defines polynomial constraints for each opcode class, register updates,
/// PC transitions, memory consistency, and permutation arguments.

pub mod bitwise;
pub mod constraints;
pub mod permutation;

use toyni::babybear::BabyBear;
use zkvm_core::trace::{col, NUM_TRACE_COLS};
use zkvm_core::cpu::NUM_OPCODE_CLASSES;

/// A single row of field-element trace values, used during constraint evaluation.
#[derive(Clone)]
pub struct TraceView {
    pub vals: Vec<BabyBear>,
}

impl TraceView {
    pub fn col(&self, idx: usize) -> BabyBear {
        self.vals[idx]
    }

    pub fn sel(&self, class: usize) -> BabyBear {
        self.vals[col::OPCODE_SEL_START + class]
    }
}

/// Evaluate all main trace transition constraints at a single point.
/// Does NOT include accumulator constraints (those need separate evaluation).
pub fn eval_transition_constraints(curr: &TraceView, next: &TraceView) -> Vec<BabyBear> {
    let mut constraints = Vec::new();

    // 1. Clock increments by 1
    constraints.push(next.col(col::CLK) - curr.col(col::CLK) - BabyBear::one());

    // 2. PC transition: next row's PC must equal current row's next_pc
    // Exempt when current row is halted (execution has stopped, PC can jump to padding)
    let not_halted = BabyBear::one() - curr.col(col::IS_HALTED);
    constraints.push(not_halted * (next.col(col::PC) - curr.col(col::NEXT_PC)));

    // 3. Opcode selectors sum to 1
    let mut sel_sum = BabyBear::zero();
    for i in 0..NUM_OPCODE_CLASSES {
        sel_sum = sel_sum + curr.sel(i);
    }
    constraints.push(sel_sum - BabyBear::one());

    // 4. ALU constraints
    constraints.extend(constraints::alu_constraints(curr));

    // 5. PC update constraints
    constraints.extend(constraints::pc_constraints(curr));

    // 6. Memory flag constraints
    constraints.extend(constraints::memory_flag_constraints(curr));

    // 7. Bitwise constraints
    constraints.extend(bitwise::bitwise_constraints(curr));

    // 8. Shift constraints
    constraints.extend(bitwise::shift_constraints(curr));

    // 9. Memory address computation
    constraints.extend(constraints::mem_addr_constraints(curr));

    // 10. JALR target masking
    constraints.extend(constraints::jalr_constraints(curr));

    // 11. Branch condition constraints
    constraints.extend(constraints::branch_condition_constraints(curr));

    // 12. Range check limb reconstruction
    constraints.extend(range_check_reconstruction_constraints(curr));

    // 13. Selector boolean constraints
    constraints.extend(constraints::selector_boolean_constraints(curr));

    // 14. x0 register constraints
    constraints.extend(constraints::x0_register_constraints(curr));

    // 15. Store value constraints
    constraints.extend(constraints::store_val_constraints(curr));

    // 16. Load value constraints - DISABLED: requires CPU to decompose mem_val into BITS_A
    // TODO: Either simplify constraints or update CPU to populate BITS_A for loads
    // constraints.extend(constraints::load_val_constraints(curr));

    // 17. Instruction decoding constraints
    constraints.extend(constraints::instruction_decoding_constraints(curr));

    // 18. Halting condition constraints
    constraints.extend(constraints::halting_constraints(curr, next));

    constraints
}

/// Number of main trace transition constraints (excluding accumulator).
pub fn num_transition_constraints() -> usize {
    let dummy = TraceView {
        vals: vec![BabyBear::zero(); NUM_TRACE_COLS],
    };
    eval_transition_constraints(&dummy, &dummy).len()
}

/// Total number of constraints including accumulators.
pub fn num_total_constraints() -> usize {
    num_transition_constraints() + permutation::num_accum_constraints()
}

/// Range check limb reconstruction: val = lo + hi * 65536 for each of 8 values.
fn range_check_reconstruction_constraints(curr: &TraceView) -> Vec<BabyBear> {
    let mut constraints = Vec::new();
    let c64k = BabyBear::new(65536);

    // 8 values: rs1, rs2, rd, imm, mem_addr, mem_val, next_pc, pc
    let value_cols = [
        col::RS1_VAL, col::RS2_VAL, col::RD_VAL, col::IMM,
        col::MEM_ADDR, col::MEM_VAL, col::NEXT_PC, col::PC,
    ];

    for (j, &val_col) in value_cols.iter().enumerate() {
        let lo = curr.col(col::LIMB_START + j * 2);
        let hi = curr.col(col::LIMB_START + j * 2 + 1);
        let val = curr.col(val_col);
        constraints.push(val - lo - hi * c64k);
    }

    constraints
}

/// Validate main trace transition constraints (without accumulators).
pub fn validate_trace(columns: &[Vec<BabyBear>]) -> Result<(), String> {
    let n = columns[0].len();
    for row in 0..n - 1 {
        let curr = TraceView {
            vals: columns.iter().map(|c| c[row]).collect(),
        };
        let next = TraceView {
            vals: columns.iter().map(|c| c[row + 1]).collect(),
        };
        let cvals = eval_transition_constraints(&curr, &next);
        let constraint_names = [
            "CLK", "PC", "Selector sum",
            // Add more names as needed, or use batch names
        ];
        for (j, &cv) in cvals.iter().enumerate() {
            if !cv.is_zero() {
                let name = if j < constraint_names.len() {
                    constraint_names[j]
                } else {
                    "unknown"
                };
                return Err(format!(
                    "Constraint {} ({}) violated at row {}: value = {} (mod p = {})",
                    j, name, row, cv.value, (cv.value as i64) - 2013265921
                ));
            }
        }
    }
    Ok(())
}

/// Validate all constraints including permutation accumulators.
pub fn validate_full_trace(
    columns: &[Vec<BabyBear>],
    accum_columns: &[Vec<BabyBear>],
    gammas: &[BabyBear; 4],
    alphas: &[BabyBear; 4],
) -> Result<(), String> {
    validate_trace(columns)?;

    let n = columns[0].len();
    // Check all accumulator constraints for rows 0..n-2 (all constraints hold)
    for row in 0..n - 1 {
        let curr = TraceView {
            vals: columns.iter().map(|c| c[row]).collect(),
        };
        let next = TraceView {
            vals: columns.iter().map(|c| c[row + 1]).collect(),
        };
        let curr_acc: Vec<BabyBear> = accum_columns.iter().map(|c| c[row]).collect();
        let next_acc: Vec<BabyBear> = accum_columns.iter().map(|c| c[row + 1]).collect();
        let cvals = permutation::eval_accum_constraints(
            &curr, &next, &curr_acc, &next_acc, gammas, alphas,
        );
        for (j, &cv) in cvals.iter().enumerate() {
            if !cv.is_zero() {
                return Err(format!(
                    "Accumulator constraint {} violated at row {}: value = {}",
                    j, row, cv.value
                ));
            }
        }
    }

    // Check wrap-around constraints at last row (next = first row)
    // Only wrap-around constraints must hold here (grand product + LogUp transitions).
    // Sorted table constraints are excepted at the last row.
    {
        let last = n - 1;
        let curr = TraceView {
            vals: columns.iter().map(|c| c[last]).collect(),
        };
        let next = TraceView {
            vals: columns.iter().map(|c| c[0]).collect(),
        };
        let curr_acc: Vec<BabyBear> = accum_columns.iter().map(|c| c[last]).collect();
        let next_acc: Vec<BabyBear> = accum_columns.iter().map(|c| c[0]).collect();
        let cvals = permutation::eval_accum_constraints(
            &curr, &next, &curr_acc, &next_acc, gammas, alphas,
        );
        for (j, &cv) in cvals.iter().enumerate() {
            if permutation::is_wrap_constraint(j) && !cv.is_zero() {
                return Err(format!(
                    "Wrap-around constraint {} violated at last row: value = {}",
                    j, cv.value
                ));
            }
        }
    }

    Ok(())
}

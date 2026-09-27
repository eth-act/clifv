import FVTest.Isle.Toy

/-!
# Interpreter vs. Cranelift: which rules fire

For each function of `FVTest/Isle/oracle/cases.clif`, the toy embedding (`FVTest/Isle/Toy.lean`)
runs `lower` on the function's instructions in the order Cranelift's lowering driver visits
them (last instruction first; an `iconst` folded into its user's immediate is dead and not
lowered), and the resulting trace must equal, line for line, what a `trace-log` build of
cranelift-codegen 0.136.1 prints for the same function (`FVTest/Isle/oracle/cases.trace`,
produced by `rust/crates/isle2lean/oracle`). Every case runs with `checkOverlap := true`, so
no two rules of the same priority matched along the way.

The instruction order and dead-instruction skipping come from the oracle, not from a model of
the driver.
-/

namespace Isle.Toy.Test
open Isle Isle.Aarch64 Isle.Toy

/-- `(function name, toy function, instructions to lower in driver order)`. -/
def cases : List (String × St × List Nat) := [
  ("%iadd_iconst_left",
    mkFunc ["I64"] [(iconstInst 5, some "I64"), (binaryInst "Iadd" 1 0, some "I64"),
      (returnInst [2], none)], [2, 1]),
  ("%iadd_iconst_right_shifted",
    mkFunc ["I32"] [(iconstInst 0x5000, some "I32"), (binaryInst "Iadd" 0 1, some "I32"),
      (returnInst [2], none)], [2, 1]),
  ("%iadd_regs_i8",
    mkFunc ["I8", "I8"] [(binaryInst "Iadd" 0 1, some "I8"), (returnInst [2], none)], [1, 0]),
  ("%icmp_slt_i64",
    mkFunc ["I64", "I64"] [(icmpInst "SignedLessThan" 0 1, some "I8"), (returnInst [2], none)],
    [1, 0]),
  ("%icmp_ult_imm_i32",
    mkFunc ["I32"] [(iconstInst 7, some "I32"), (icmpInst "UnsignedLessThan" 0 1, some "I8"),
      (returnInst [2], none)], [2, 1])]

/-- Split oracle output into `(function name, trace lines)` sections. -/
def sections (s : String) : List (String × List String) :=
  let lines := (s.splitOn "\n").filter (· ≠ "")
  let (done, cur) := lines.foldl (init := ([], none))
    fun (done, cur) l =>
      if l.startsWith "function " then
        (match cur with | some c => done ++ [c] | none => done, some ((l.drop 9).toString, []))
      else match cur with
        | some (n, ls) => (done, some (n, ls ++ [l]))
        | none => (done, none)
  match cur with | some c => done ++ [c] | none => done

def check : IO Unit := do
  let oracle := sections (← IO.FS.readFile "FVTest/Isle/oracle/cases.trace")
  unless oracle.length == cases.length do
    throw (IO.userError s!"oracle has {oracle.length} functions, expected {cases.length}")
  for (name, st, insts) in cases do
    let some expected := oracle.lookup name
      | throw (IO.userError s!"{name}: not in oracle output")
    match lowerInsts st insts { checkOverlap := true } with
    | .error e => throw (IO.userError s!"{name}: {repr e}")
    | .ok (tr, _) =>
      let got := traceLines tr
      unless got == expected do
        throw (IO.userError s!"{name}: trace mismatch\n got: {got}\n expected: {expected}")
      IO.println s!"{name}: {got.length} rules match: {program.ruleNames tr}"

#eval check

-- The instruction selected for `iadd (iconst 5) v0` at i64: `add x3, x0, #5`.
#guard match lowerInsts (cases[0]!.2.1) [1] with
  | .ok (_, st) => st.emitted.toList ==
      [dataVal "MInst.AluRRImm12" [enumVal "ALUOp.Add", enumVal "OperandSize.Size64", .reg 3,
        .reg 0, .prim "Imm12" [.int 5, .bool false]]]
  | .error _ => false

-- Without overlap checking the same rules are chosen.
#guard cases.all fun (_, st, insts) =>
  match lowerInsts st insts, lowerInsts st insts { checkOverlap := true } with
  | .ok (a, _), .ok (b, _) => a == b
  | _, _ => false

-- Running out of fuel is reported, not a wrong answer.
#guard match lowerInsts (cases[0]!.2.1) [1] { fuel := 5 } with
  | .error .outOfFuel => true
  | _ => false

-- An instruction the toy does not model aborts with `unmodeled`, never "no rule".
#guard match lowerInsts (mkFunc ["I64"] [(binaryInst "Udiv" 0 0, some "I64")]) [0] with
  | .error (.unmodeled _) => true
  | _ => false

-- Every rule fired in the oracle cases is in the emitter-subset closure.
#guard cases.all fun (_, st, insts) =>
  match lowerInsts st insts with
  | .ok (tr, _) => tr.all fun r => Closure.rules.any (·.rule == r)
  | .error _ => false

-- `lower` is partial: an instruction no rule handles yields `none` and fires nothing.
#guard match Interp.run program sem {} "lower" [.inst 0]
    (mkFunc ["I64"] [(binaryInst "Iconst" 0 0, some "I64")]) with
  | .ok r => r.value.isNone && r.trace.isEmpty
  | .error _ => false

-- `operand_size` is total: no rule for `I128` is the generated code's panic.
#guard match Interp.run program sem {} "operand_size" [.ty "I128"] (mkFunc [] []) with
  | .error (.noRule "operand_size") => true
  | _ => false

-- ... and for `I32` it picks `operand_size_32` without touching the state.
#guard match Interp.run program sem {} "operand_size" [.ty "I32"] (mkFunc [] []) with
  | .ok r => r.value == some (enumVal "OperandSize.Size32") && program.ruleNames r.trace == ["rule_inst_1592"]
  | .error _ => false

end Isle.Toy.Test

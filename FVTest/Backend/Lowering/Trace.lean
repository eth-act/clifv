import FV.Backend
import FV.Opt.Legalize128Pass

/-!
# Instruction-selection diagnostics

`lean-backend-lowering-trace INPUT.clif OUTPUT.json` records initial value registers,
selected VCode, fired rules, and the prepared allocator input. It does not allocate or
emit code and does not change the compiler's lowering/checking path. Give it the
stock-effective Lean input from a settings-matched comparison to inspect that case.

The input is legalized exactly as in `lean-backend`; the report records this fact and
the legalization validator's results. These are structural diagnostics, not a
semantic-equivalence verdict or a replacement for the stock configuration receipt.
-/

namespace LoweringTrace

open Backend Lean

def regJson (r : Reg) : Json := toJson ((repr r).pretty)

def codeJson (vc : VCode) : Json := Json.mkObj [
  ("name", toJson vc.name),
  ("classes", toJson (vc.classes.map fun c => (repr c).pretty)),
  ("slot_bytes", toJson vc.slotBytes),
  ("outgoing_bytes", toJson vc.outgoing),
  ("rule_ids", toJson vc.rulesFired),
  ("rule_names", toJson (Isle.Aarch64.program.ruleNames vc.rulesFired.toList)),
  ("blocks", Json.arr (vc.blocks.map fun b => Json.mkObj [
    ("label", toJson b.label),
    ("params", Json.arr (b.params.map regJson)),
    ("branch_args", Json.arr (b.branchArgs.map regJson)),
    ("instructions", toJson (b.insts.map fun i => (repr i).pretty))]))]

/-- The current driver's checker replay, including each instruction's temporary range.
The checker independently reconstructs these calls; this is not an instrumented compiler. -/
def replayJson (f : Clif.Function) (ctx : Ctx) (initial : LState) : Except String Json := do
  let some blocks := Proof.Driver.lowBlocks f (Proof.Driver.stmtCall ctx)
      (Proof.Driver.termCallF ctx) (Proof.Driver.tryCallF ctx) 0 f.blocks initial f.blocks.length
    | throw "lowering checker replay failed"
  let mut calls := #[]
  for (b, bi) in blocks.zipIdx do
    for (s, j) in b.sl.zipIdx do
      let (_, _, rules) ← runTerm ctx "lower" [.inst (b.start + j)] s.st
      calls := calls.push (Json.mkObj [
        ("block_index", toJson bi), ("inst_index", toJson (b.start + j)),
        ("kind", toJson "statement"),
        ("first_temp", toJson s.st.nextVreg), ("next_temp", toJson s.st'.nextVreg),
        ("result_regs", toJson (s.rss.map fun rs => rs.map regJson)),
        ("rule_ids", toJson rules),
        ("instructions", toJson (s.st'.emitted.map fun i => (repr i).pretty))])
    calls := calls.push (Json.mkObj [
      ("block_index", toJson bi), ("inst_index", toJson (b.start + b.sl.length)),
      ("kind", toJson "terminator"),
      ("first_temp", toJson b.tst.nextVreg), ("next_temp", toJson b.tst'.nextVreg),
      ("targets", toJson b.targets),
      ("instructions", toJson (b.tst'.emitted.map fun i => (repr i).pretty))])
  pure (Json.arr calls)

def snapshot (f : Clif.Function) : Except String Json := do
  let (ctx, ranges, initial) ← buildCtx f
  let selected ← lowerFunction f
  let prepared ← prepare selected
  let replay ← replayJson f ctx initial
  let allocator ← match Json.parse (← vcodeJson prepared) with
    | .ok j => pure j
    | .error e => throw s!"invalid allocator JSON: {e}"
  let values := ctx.valReg.toList.zipIdx |>.filterMap fun (r, value) =>
    r.map fun reg => Json.mkObj [
      ("value", toJson value), ("reg", regJson reg),
      ("def_inst", toJson ((ctx.valDef[value]?).join))]
  pure (Json.mkObj [
    ("initial_next_vreg", toJson initial.nextVreg),
    ("value_regs", toJson values),
    ("source_blocks", toJson (f.blocks.map (·.id))),
    ("instruction_ranges", toJson (ranges.map fun (start, stop) => #[start, stop])),
    ("checker_replay", replay),
    ("selected", codeJson selected), ("prepared", codeJson prepared),
    ("allocator_input", allocator)])

def run (input output : String) : IO UInt32 := do
  let source ← IO.FS.readFile input
  let legalized := Opt.Legalize128.parsedFile128 (Clif.parseFile source)
  let rows := legalized.file.funcs.map fun parsed =>
    let result := match parsed.func with
      | .ok f => snapshot f
      | .error e => .error e.toString
    match result with
    | .ok report => Json.mkObj [
        ("name", toJson parsed.name), ("status", toJson "lowered"), ("lowering", report)]
    | .error reason => Json.mkObj [
        ("name", toJson parsed.name), ("status", toJson "unsupported"),
        ("reason", toJson reason)]
  let report := Json.mkObj [
    ("schema", toJson (1 : Nat)), ("input", toJson input),
    ("legalization_accepted", toJson legalized.accepted),
    ("legalization_unverified", toJson legalized.unverified),
    ("functions", toJson rows)]
  IO.FS.writeFile output (report.pretty ++ "\n")
  return 0

end LoweringTrace

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] => LoweringTrace.run input output
  | _ =>
    IO.eprintln "usage: lean-backend-lowering-trace INPUT.clif OUTPUT.json"
    return 2

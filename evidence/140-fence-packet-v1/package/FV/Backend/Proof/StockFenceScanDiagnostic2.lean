import FV.Backend.Lowering.Stock

namespace Backend.Stock.Proof
open Backend
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] emitInstruction commitOpportunistic

/-- A successful mandatory, unsunk nonterminator scan is an actual emission. -/
theorem stock_mandatory_scan_emission {ctx : Ctx} {block i ti : Nat} {branch : Bool}
    {input : State} {output : Scan}
    (unsunk : input.sunk[i]! = false) (different : i ≠ ti)
    (mandatory : ctx.insts[i]!.clif.any mustLower = true)
    (actual : scanInstruction ctx block i ti branch input = .ok output) :
    ∃ emission, emitInstruction ctx i (scanState input i) = .ok emission ∧
      output = emission.scan block i (scanState input i) := by
  have notTerm : (i == ti) = false := by simp [different]
  unfold scanInstruction at actual
  dsimp only at actual
  simp only [unsunk,Bool.false_eq_true,ite_false,notTerm,Bool.false_and,
    mandatory,Bool.not_true,Bool.and_false] at actual
  fail "PREFIX: simplification completed"
end Backend.Stock.Proof

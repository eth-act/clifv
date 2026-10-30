import FV.Backend.Proof.StockPolicy
import FV.Backend.Proof.IselCtlTry
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
attribute [local irreducible] Isle.Aarch64.program
/-- The extension encoded in the actual narrow comparison preserves the
complete Stock state and uses the original source width and signedness. -/
theorem stock_cmp_narrow_extend_op {p : Program} (hp : Data p) (ctx : Ctx)
    (signed half : Bool) (st : State) (tr : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) {} (n+20) 84 657
      [.ty (.int (if half then 16 else 8)),.data 56 (if signed then 2 else 1) []]).run (st,tr) =
      .ok (some (.data 84 (if signed then (if half then 5 else 4) else (if half then 1 else 0)) []),
        st,tr.push (if signed then (if half then rule_inst_5265.id else rule_inst_5264.id)
          else (if half then rule_inst_5267.id else rule_inst_5266.id))) := by
  have p8 : (Stock.sem ctx).prim 14 "I8" = some (.ty (.int 8)) := rfl
  have p16 : (Stock.sem ctx).prim 14 "I16" = some (.ty (.int 16)) := rfl
  have eq : ∀ a b,(Stock.sem ctx).eq a b = (a == b) := fun _ _ => rfl
  have mk : ∀ t k vs,(Stock.sem ctx).mkData t k vs = .data t k vs := fun _ _ _ => rfl
  have unData : ∀ ty k vs,(Stock.sem ctx).unData ty (.data ty k vs) = some (k,vs) := by
    intro ty k vs
    change (if ty == ty then some (k,vs) else none) = some (k,vs)
    simp
  have ne816 : (V.ty (.int 8) == V.ty (.int 16)) = false := by decide
  have ne168 : (V.ty (.int 16) == V.ty (.int 8)) = false := by decide
  cases hp
  cases signed <;> cases half
  all_goals isel_eval [*, isel_monad,rule_inst_5264,rule_inst_5265,rule_inst_5266,rule_inst_5267,reduceCtorEq]
/-- All four actual narrow extensions have successful, state-preserving runs. -/
theorem stock_cmp_narrow_extend_op_witness (signed half : Bool) :
    ∃ out trace,(applyTerm program (Stock.sem sinkCtx) {} 1000 84 657
      [.ty (.int (if half then 16 else 8)),.data 56 (if signed then 2 else 1) []]).run
      (sinkState,#[]) = .ok (some out,sinkState,trace) :=
  ⟨_,_,stock_cmp_narrow_extend_op data_program sinkCtx signed half sinkState #[] 980⟩
end Backend.Stock.Proof.ScalarCmp

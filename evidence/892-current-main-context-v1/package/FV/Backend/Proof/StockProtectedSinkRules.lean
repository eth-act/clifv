import FV.Backend.Proof.StockSinkTargetBinding
import FV.Backend.Proof.StockSinkRuleRhs
import FV.Backend.Proof.StockSinkRuleSyntax

namespace Backend.Stock.Proof.SinkRules
open Backend.Proof Isle Isle.Interp Isle.Aarch64 Isle.Interp.RuleFrame
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- This local slot property permits loads at every other source position. -/
def NoLoadAt (ctx : Ctx) (i : Nat) : Prop :=
  ∀ info,ctx.insts[i]? = some info → ∀ fmt fields,fmt = 16 ∨ fmt = 17 →
    (Backend.sem ctx).unData 152 info.data ≠ some (fmt,fields)

/-- Actual helper matching cannot bind a protected non-load slot as its sink target. -/
theorem pattern_sink_target_other {ctx : Ctx} {slot : Nat}
    (safe : NoLoadAt ctx slot) {st matched : State}
    {tr tr' : Array RuleId} {bound : Isle.Interp.Env V} {fuel : Nat} {vs : List V}
    (atomic : Bool)
    (run : (matchRule program (Stock.sem ctx) {} fuel
      (if atomic then rule_inst_3905 else rule_inst_4203) vs).run (st,tr) =
        .ok (some bound,matched,tr')) :
    ∃ i,matched = st ∧ tr' = tr ∧ slot ≠ i ∧
      bound[if atomic then 1 else 3]? = some (some (.inst i)) := by
  obtain ⟨i,info,fields,state,trace,found,format,binding⟩ := pattern_sink_target atomic run
  refine ⟨i,state,trace,?_,binding⟩
  intro same
  subst i
  apply safe info found (if atomic then 17 else 16) fields ?_ format
  cases atomic <;> simp

/-- Complete RHS execution preserves the protected slot, including partial-result paths.
The target and binding follow from the actual match; no sink-call receipt is a premise. -/
theorem pattern_sink_rule_frame {ctx : Ctx} {slot : Nat}
    (safe : NoLoadAt ctx slot) {st matched next : State}
    {tr tr' tr'' : Array RuleId} {bound : Isle.Interp.Env V} {n fuel : Nat}
    {vs : List V} {out : Option V}
    (frames : ∀ m,m < n → CtorFreeAt program (Stock.sem ctx) {} blocked
      (fun a b => b.sunk[slot]! = a.sunk[slot]!) m)
    (atomic : Bool)
    (matchedRun : (matchRule program (Stock.sem ctx) {} fuel
      (if atomic then rule_inst_3905 else rule_inst_4203) vs).run (st,tr) =
        .ok (some bound,matched,tr'))
    (rhsRun : (evalExpr program (Stock.sem ctx) {} n
      (if atomic then rule_inst_3905 else rule_inst_4203).rhs bound).run (matched,tr') =
        .ok (out,next,tr'')) : next.sunk[slot]! = st.sunk[slot]! := by
  obtain ⟨i,rfl,rfl,different,binding⟩ := pattern_sink_target_other safe atomic matchedRun
  have guards : termCtorFree program blocked = (fun t => t != 236) := funext term_guard
  cases atomic with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte,rule_inst_4203] at rhsRun binding
    apply sink_let_other frames binding different ?_ rhsRun
    rw [exprCtorFree,guards]
    decide +kernel
  | true =>
    simp only [↓reduceIte,rule_inst_3905] at rhsRun binding
    apply sink_let_other frames binding different ?_ rhsRun
    rw [exprCtorFree,guards]
    decide +kernel

end Backend.Stock.Proof.SinkRules

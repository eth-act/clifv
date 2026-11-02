import FV.Backend.Proof.IselCovForm
import FV.Backend.Proof.StockExtendRequests
import FV.Backend.Proof.StockOverflowPatterns
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem ext_fits32 (ctx : Ctx) (st : LState) :
    externExtract ctx T.fits_in_32 (.ty (.int 32)) st = .ok [.ty (.int 32)] := rfl
private def Nonzero32Outcome (p : Program) (ctx : Ctx) (fuel x : Nat)
    (st : State) (tr : Array RuleId) (out : V) (next : State) (trace : Array RuleId) : Prop :=
  ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel rule_inst_4977.rhs #[some (.ty (.int 32)),some (.value x)]).run
    (st,tr) = .ok (some out,next,rhsTrace) ∧ trace = rhsTrace.push rule_inst_4977.id
attribute [local irreducible] Nonzero32Outcome
private theorem outcome_elim {p : Program} {ctx : Ctx} {fuel x : Nat}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (h : Nonzero32Outcome p ctx fuel x st tr out next trace) :
    ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel rule_inst_4977.rhs #[some (.ty (.int 32)),some (.value x)]).run
      (st,tr) = .ok (some out,next,rhsTrace) ∧ trace = rhsTrace.push rule_inst_4977.id := by
  unfold Nonzero32Outcome at h
  exact h
private def Nonzero32Matches (p : Program) (ctx : Ctx) (x : Nat) : Prop :=
  ∀ st tr n,(matchRule p (Stock.sem ctx) {} (n+10) rule_inst_4977 [.value x]).run (st,tr) =
    .ok (some ((#[none,none].setIfInBounds 1 (some (.value x))).setIfInBounds 0 (some (.ty (.int 32)))),st,tr)
attribute [local irreducible] Nonzero32Matches
private theorem nonzero_match {p : Program} (hp : Data p) (ctx : Ctx) {x : Nat}
    (typed : ctx.valueType? x = some (.int 32)) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+10) rule_inst_4977 [.value x]).run (st,tr) =
      .ok (some ((#[none,none].setIfInBounds 1 (some (.value x))).setIfInBounds 0 (some (.ty (.int 32)))),st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  cases hp
  isel_eval [*,rule_inst_4977,sem_extract,sem_unData,sem_eq,sem_prim,CTy.ofName?,ext_fits32]
  rfl
private theorem second_absent {ctx : Ctx} {x : Nat} (parameter : ctx.defInst? x = none)
    {st : LState} {fs : List V} (h : externExtract ctx T.is_second_result (.value x) st = .ok fs) : False := by
  obtain ⟨j,info,defined,found,second,fields⟩ := (ext_is_second_result_iff ctx st x fs).mp h
  rw [parameter] at defined
  cases defined
private theorem overflow_absurd {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {r : Rule} {x fuel : Nat} {st : State} {tr : Array RuleId}
    {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (member : r ∈ overflowFlagsRules)
    (matched : (matchRule program (Stock.sem ctx) {} fuel r [.value x]).run (st,tr) = .ok (some env,after)) : False :=
  (stock_overflow_flags_rule_unreachable inv (st,tr) x member {} fuel env after) matched
/-- A real nonzero helper call on an original32-bit source selects its actual
register RHS. Higher overflow look-through follows the original mapped source invariant; incompatible widths are excluded. The earlier parameter-only variant remains unchanged. -/
theorem stock_cmp_original_nonzero32_selected {f : Clif.Function} (ctx : Ctx) (inv : MappedCtxInv f ctx)
    {x fuel : Nat} (enough : 200 ≤ fuel) (typed : ctx.valueType? x = some (.int 32))
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 123 651 [.value x] (st,tr) out (next,trace)) :
    ∃ rhsTrace,(evalExpr program (Stock.sem ctx) {} fuel rule_inst_4977.rhs #[some (.ty (.int 32)),some (.value x)]).run
      (st,tr) = .ok (some out,next,rhsTrace) ∧ trace = rhsTrace.push rule_inst_4977.id := by
  suffices h : Nonzero32Outcome program ctx fuel x st tr out next trace by exact outcome_elim h
  have hp : Data program := data_program
  have hp' := hp
  have hc : ({} : Config).checkOverlap = false := rfl
  have lookup := fun q => ext_value_type ctx q typed
  have matches32 : Nonzero32Matches program ctx x := by
    unfold Nonzero32Matches
    exact fun q t n => nonzero_match hp' ctx typed q t n
  stock_split hp hc run 651
  all_goals try (
    exfalso
    apply overflow_absurd inv (matched := hm)
    decide +kernel)
  all_goals isel_inv [*,rule_inst_4977,rule_inst_4979,rule_inst_4983,rule_inst_4988,
    rule_inst_4993,rule_inst_5013,rule_inst_5032,rule_inst_5049,rule_inst_5058,
    rule_inst_5077,rule_inst_5094,sem_extract,sem_unData,sem_eq,sem_prim,CTy.ofName?,ext_fits32] at hm
  all_goals simp only [typed,Option.some.injEq,reduceCtorEq] at *
  all_goals isel_destruct <;> subst_vars
  all_goals try (simp [CTy.bits,CTy.isInt,CTy.ofName?] at *)
  all_goals unfold Nonzero32Outcome
  all_goals exact ⟨_,by
    have envEq : ((Array.replicate 2 none : Isle.Interp.Env V).setIfInBounds 1 (some (.value x))).setIfInBounds 0 (some (.ty (.int 32))) =
        #[some (.ty (.int 32)),some (.value x)] := by
      apply Array.toList_inj.mp
      simp [Array.toList_setIfInBounds,List.set,List.replicate]
    simpa only [envEq] using he,rfl⟩
end Backend.Stock.Proof.ScalarCmp

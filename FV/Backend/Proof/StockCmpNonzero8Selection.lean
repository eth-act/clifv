import FV.Backend.Proof.IselCovForm
import FV.Backend.Proof.StockExtendRequests
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
private def Nonzero8Outcome (p : Program) (ctx : Ctx) (fuel x : Nat)
    (st : State) (tr : Array RuleId) (out : V) (next : State) (trace : Array RuleId) : Prop :=
  ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel rule_inst_4988.rhs #[some (.value x)]).run
    (st,tr) = .ok (some out,next,rhsTrace) ∧ trace = rhsTrace.push rule_inst_4988.id
attribute [local irreducible] Nonzero8Outcome
private theorem outcome_elim {p : Program} {ctx : Ctx} {fuel x : Nat}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (h : Nonzero8Outcome p ctx fuel x st tr out next trace) :
    ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel rule_inst_4988.rhs #[some (.value x)]).run
      (st,tr) = .ok (some out,next,rhsTrace) ∧ trace = rhsTrace.push rule_inst_4988.id := by
  unfold Nonzero8Outcome at h
  exact h
private def Nonzero8Matches (p : Program) (ctx : Ctx) (x : Nat) : Prop :=
  ∀ st tr n,(matchRule p (Stock.sem ctx) {} (n+10) rule_inst_4988 [.value x]).run (st,tr) =
    .ok (some (#[none].setIfInBounds 0 (some (.value x))),st,tr)
attribute [local irreducible] Nonzero8Matches
private theorem nonzero_match {p : Program} (hp : Data p) (ctx : Ctx) {x : Nat}
    (typed : ctx.valueType? x = some (.int 8)) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+10) rule_inst_4988 [.value x]).run (st,tr) =
      .ok (some (#[none].setIfInBounds 0 (some (.value x))),st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  cases hp
  isel_eval [*,rule_inst_4988,sem_extract,sem_unData,sem_eq,sem_prim,CTy.ofName?]
  have arrayEq : (Array.replicate 1 none : Isle.Interp.Env V) = #[none] := by
    apply Array.toList_inj.mp
    simp [List.replicate]
  rw [arrayEq]
private theorem second_absent {ctx : Ctx} {x : Nat} (parameter : ctx.defInst? x = none)
    {st : LState} {fs : List V} (h : externExtract ctx T.is_second_result (.value x) st = .ok fs) : False := by
  obtain ⟨j,info,defined,found,second,fields⟩ := (ext_is_second_result_iff ctx st x fs).mp h
  rw [parameter] at defined
  cases defined
private theorem rejected_prefix {p : Program} {ctx : Ctx} {x : Nat}
    {st : State} {tr : Array RuleId} {pre : List Rule}
    (match8 : Nonzero8Matches p ctx x)
    (failed : ∀ r ∈ pre,∃ m after,(matchRule p (Stock.sem ctx) {} (m+20) r [.value x]).run
      (st,tr) = .ok (none,after)) (member : rule_inst_4988 ∈ pre) : False := by
  obtain ⟨m,after,run⟩ := failed _ member
  unfold Nonzero8Matches at match8
  have forward := match8 st tr (m+10)
  have gas : m+10+10=m+20 := by omega
  rw [gas] at forward
  rw [forward] at run
  cases run
/-- A real nonzero helper call on an original8-bit parameter selects its actual
register RHS. Higher second-result look-through and incompatible widths are excluded. -/
theorem stock_cmp_parameter_nonzero8_selected {p : Program} (hp : Data p) (ctx : Ctx)
    {x fuel : Nat} (enough : 200 ≤ fuel) (typed : ctx.valueType? x = some (.int 8))
    (parameter : ctx.defInst? x = none) {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} fuel 123 651 [.value x] (st,tr) out (next,trace)) :
    ∃ rhsTrace,(evalExpr p (Stock.sem ctx) {} fuel rule_inst_4988.rhs #[some (.value x)]).run
      (st,tr) = .ok (some out,next,rhsTrace) ∧ trace = rhsTrace.push rule_inst_4988.id := by
  suffices h : Nonzero8Outcome p ctx fuel x st tr out next trace by exact outcome_elim h
  have hp' := hp
  have hc : ({} : Config).checkOverlap = false := rfl
  have lookup := fun q => ext_value_type ctx q typed
  have match8 : Nonzero8Matches p ctx x := by
    unfold Nonzero8Matches
    exact fun q t n => nonzero_match hp' ctx typed q t n
  stock_split hp hc run 651
  all_goals try (
    exfalso
    apply rejected_prefix (st := st) (tr := tr) match8 hpre
    decide +kernel)
  all_goals isel_inv [*,rule_inst_4977,rule_inst_4979,rule_inst_4983,rule_inst_4988,
    rule_inst_4993,rule_inst_5013,rule_inst_5032,rule_inst_5049,rule_inst_5058,
    rule_inst_5077,rule_inst_5094,sem_extract,sem_unData,sem_eq,sem_prim,CTy.ofName?] at hm
  all_goals simp only [typed,parameter,Option.some.injEq,reduceCtorEq] at *
  all_goals isel_destruct <;> subst_vars
  all_goals try (
    exfalso
    apply second_absent parameter
    assumption)
  all_goals try (simp [CTy.bits,CTy.isInt,CTy.ofName?] at *)
  all_goals unfold Nonzero8Outcome
  all_goals exact ⟨_,by simpa only [Array.setIfInBounds] using he,rfl⟩
end Backend.Stock.Proof.ScalarCmp

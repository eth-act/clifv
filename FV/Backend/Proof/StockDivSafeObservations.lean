import FV.Backend.Proof.StockExtendRequests
import FV.Backend.Proof.StockDivImmValues
import FV.Backend.Proof.StockDivSafeMatch
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem ext_reg {ctx : Ctx} {x to : Nat} {sg : Bool} {pass : List CTy}
    {s next : State} {out : V} (shape : ScalarShift.MappedExtOut ctx x sg to pass s next out) :
    ∃ r,out = .reg r := by
  obtain ⟨t,typed,safe,r,mapped,form⟩ := shape
  rcases form with ⟨_,equal,_⟩ | ⟨_,_,equal,_⟩
  · exact ⟨r,equal⟩
  · exact ⟨_,equal⟩
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_prim (ctx : Ctx) : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
/-- Every successful real immediate call returns a fresh result register;
this observation uses standard-only machine contracts for all five rules. -/
theorem stock_div_imm_reg {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {n w e : Nat} (enough : 39 ≤ n)
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (extension : e = 0 ∨ e = 1)
    {i : Int} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg n 27 553 (immArgs w e i) (st,tr) out (next,trace)) :
    ∃ d,out = .reg (.vreg d .int) ∧ st.base.nextVreg ≤ d := by
  obtain ⟨k,fuelEq⟩ : ∃ k,n+1=k+40 := ⟨n-39,by omega⟩
  unfold ApplyInternal at run
  rw [fuelEq] at run
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨frame,ms,d,output,shape,value⟩ := stock_div_imm_values hp ctx hc self width extension run
  exact ⟨d,output,shape.res⟩
def SafeSdivReceipt (p : Program) (ctx : Ctx) (wide : Bool) (n x w : Nat) (i v : Int)
    (st next : State) (tr : Array RuleId) (out : V) : Prop :=
  ∃ rx ry s1 s2 t1 t2,
    ScalarShift.MappedExtOut ctx x true (if wide then 64 else 32)
      (if wide then [.int 64] else [.int 32,.int 64]) st s1 (.reg rx) ∧
    (applyTerm p (Stock.sem ctx) {} (n+44) 27 (if wide then 557 else 555) [.value x]).run (st,tr) =
      .ok (some (.reg rx),s1,t1) ∧
    (applyTerm p (Stock.sem ctx) {} (n+43) 27 553 (immArgs w 0 v)).run (s1,t1) =
      .ok (some (.reg ry),s2,t2) ∧
    out = .regsVec [[(s2.base.fresh .int).1]] ∧ next = quotientState true w s2 rx ry
/-- The actual wide safe signed RHS derives guarded preparation and real
constant materialization, without a supplied helper execution certificate. -/
theorem stock_div_sdiv_safe_wide_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {n x : Nat} {i v : Int} (enough : 120 ≤ n)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+50) rule_lower_1163.rhs (safeWideEnv x i v)).run
      (st,tr) = .ok (some out,next,trace)) : SafeSdivReceipt p ctx true n x 64 i v st next tr out := by
  have hp' := hp
  have original := run
  cases hp
  isel_inv [*,safeWideEnv,rule_lower_1163,sem_ctor,sem_prim,sem_mkData] at run
  all_goals isel_destruct <;> subst_vars
  obtain ⟨first⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 557 [.value x] (st,tr) _ _) := ⟨by assumption⟩
  have extended := ScalarShift.stock_sext64_out hp' (ctx := ctx) (cfg := {}) rfl (h := first) (by omega)
  obtain ⟨rx,firstOutput⟩ := ext_reg extended
  subst_vars
  obtain ⟨literal⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 553 (immArgs 64 0 v) _ _ _) := ⟨by assumption⟩
  obtain ⟨d,output,bound⟩ := stock_div_imm_reg hp' ctx (cfg := {}) rfl (run := literal) (by omega) (by decide) (by decide)
  subst_vars
  unfold ApplyInternal at first literal
  obtain ⟨expectedTrace,expected⟩ := stock_div_sdiv_safe_wide_from_parts hp' ctx st tr n first literal
  rw [original] at expected
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at expected
  unfold SafeSdivReceipt
  exact ⟨rx,_,_,_,_,_,extended,first,literal,expected.1,expected.2.1⟩
theorem stock_div_sdiv_safe_narrow_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {n x w : Nat} {i v : Int} (enough : 120 ≤ n) (width : w = 8 ∨ w = 16 ∨ w = 32)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+50) rule_lower_1167.rhs (safeNarrowEnv w x i v)).run
      (st,tr) = .ok (some out,next,trace)) : SafeSdivReceipt p ctx false n x w i v st next tr out := by
  have hp' := hp
  have original := run
  cases hp
  isel_inv [*,safeNarrowEnv,rule_lower_1167,sem_ctor,sem_prim,sem_mkData] at run
  all_goals isel_destruct <;> subst_vars
  obtain ⟨first⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 555 [.value x] (st,tr) _ _) := ⟨by assumption⟩
  have extended := ScalarShift.stock_sext32_out hp' (ctx := ctx) (cfg := {}) rfl (h := first) (by omega)
  obtain ⟨rx,firstOutput⟩ := ext_reg extended
  subst_vars
  obtain ⟨literal⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 553 (immArgs w 0 v) _ _ _) := ⟨by assumption⟩
  obtain ⟨d,output,bound⟩ := stock_div_imm_reg hp' ctx (cfg := {}) rfl (run := literal) (by omega) (by omega) (by decide)
  subst_vars
  unfold ApplyInternal at first literal
  obtain ⟨expectedTrace,expected⟩ := stock_div_sdiv_safe_narrow_from_parts hp' ctx (by omega) st tr n first literal
  rw [original] at expected
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at expected
  unfold SafeSdivReceipt
  exact ⟨rx,_,_,_,_,_,extended,first,literal,expected.1,expected.2.1⟩
end Backend.Stock.Proof.ScalarDiv

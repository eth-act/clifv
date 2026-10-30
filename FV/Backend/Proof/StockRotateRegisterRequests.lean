import FV.Backend.Proof.StockExtendRequests
import FV.Backend.Proof.StockShiftRequests
import FV.Backend.Proof.StockRotateNarrowRoots
namespace Backend.Stock.Proof.ScalarRotate
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
section Numbers
attribute [local semireducible] Isle.Aarch64.program
private theorem zero (ctx : Ctx) : (Stock.sem ctx).int 6 0 = .int 0 := rfl
end Numbers
private theorem zero_reg (ctx : Ctx) (st : State) :
    Stock.externCtor ctx T.zero_reg [] st = .ok (.reg .xzr,st) := by
  rw [stock_ctor_baseOnly ctx T.zero_reg _ st (by decide)]; rfl
private theorem get_reg (ctx : Ctx) (st : State) (r : Reg) :
    Stock.externCtor ctx T.value_regs_get [.regs [r],.int 0] st = .ok (.reg r,st) := by
  rw [stock_ctor_baseOnly ctx T.value_regs_get _ st (by decide)]; rfl
/-- Successful wide register rotation derives both guarded mapped source
requests; the preliminary negation cannot change the sunk-definition guard. -/
theorem stock_rotate_wide_register_requests {p : Program} (hp : Data p) (ctx : Ctx) (left wide : Bool)
    {x y n : Nat} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+60) (rotateWideRule left wide).rhs
      (rotateWideEnv left x y)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧
      (∃ rx,ctx.valueReg? x = some rx) ∧ ∃ ry,ctx.valueReg? y = some ry := by
  have hp' := hp
  have zeroReg := fun q => zero_reg ctx q
  have get := fun q r => get_reg ctx q r
  cases hp
  cases left <;> cases wide
  all_goals
    isel_inv [*,rotateWideRule,rotateWideEnv,rule_lower_1791,rule_lower_1797,
      rule_lower_1844,rule_lower_1848,sem_ctor,sem_prim,zero,stock_put_in_reg_iff,
      ScalarShift.stock_shift_put_in_regs_iff] at run
    all_goals simp only [stock_put_in_reg_iff,ScalarShift.stock_shift_put_in_regs_iff,
      ExtResult.ok.injEq,Prod.mk.injEq] at *
    all_goals isel_destruct <;> subst_vars
  all_goals simp only [zero_reg,get_reg,ExtResult.ok.injEq,Prod.mk.injEq] at *
  all_goals isel_destruct <;> subst_vars
  all_goals first
    | (exact ⟨‹DemandAllowed ctx st x›,‹DemandAllowed ctx (st.mark x) y›,⟨_,‹ctx.valueReg? x = some _›⟩,⟨_,‹ctx.valueReg? y = some _›⟩⟩)
    | (have call : ApplyInternal p (Stock.sem ctx) {} (n+55) 27 437 ?_ ?_ ?_ ?_ := by assumption
       have guard := stock_rotate_pure_sunk hp' ctx (cfg := {}) rfl
         (t := 437) (by decide) call
       have safe : DemandAllowed ctx st x := by
         intro i defined
         have actual := ‹DemandAllowed ctx _ x› i defined
         simpa only [guard,State.mark] using actual
       exact ⟨safe,‹DemandAllowed ctx st y›,⟨_,‹ctx.valueReg? x = some _›⟩,⟨_,‹ctx.valueReg? y = some _›⟩⟩)
/-- Narrow register success derives source typing and both demand guards from
actual extension and count-negation calls and original frame consistency. -/
theorem stock_rotate_narrow_register_requests {p : Program} (hp : Data p) (ctx : Ctx) (left : Bool)
    {w x y n : Nat} (width : w = 8 ∨ w = 16)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {ty : Clif.Ty} (same : ty.width = w)
    {u : BitVec ty.width} (getX : fr.getAs x ty = .ok u)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+160) (rotateNarrowRule left false).rhs
      (rotateNarrowEnv left w x y)).run (st,tr) = .ok (some out,next,trace)) :
    ctx.valueType? x = some (.int w) ∧ DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧
      (∃ rx,ctx.valueReg? x = some rx) ∧ ∃ ry,ctx.valueReg? y = some ry := by
  have hp' := hp
  cases hp
  cases left
  all_goals
    isel_inv [*,rotateNarrowRule,rotateNarrowEnv,rule_lower_1772,rule_lower_1840,
      sem_ctor,sem_prim,zero,stock_put_in_reg_iff,ScalarShift.stock_shift_put_in_regs_iff] at run
    all_goals simp only [stock_put_in_reg_iff,ScalarShift.stock_shift_put_in_regs_iff,
      ExtResult.ok.injEq,Prod.mk.injEq] at *
    all_goals isel_destruct <;> subst_vars
  all_goals simp only [zero_reg,get_reg,ExtResult.ok.injEq,Prod.mk.injEq] at *
  all_goals isel_destruct <;> subst_vars
  all_goals
    have extCall : ApplyInternal p (Stock.sem ctx) {} ?_ 27 556 [.value x] ?_ ?_ ?_ := by assumption
    have shape := ScalarShift.stock_zext32_out hp' (ctx := ctx) (cfg := {}) rfl (by omega) extCall
    obtain ⟨t,typed,safeX,rx,mapX,form⟩ := shape
    have typeEq : t = .int ty.width := by
      have h := (dfg.2 x t ⟨ty,u⟩ typed (getAs_ok getX)).symm
      exact h.trans (ofClif_int_width (ty := ty) (isInt_of_width_lt_32 (by omega)))
    rw [typeEq] at typed form
    rcases form with pass | extended
    · rcases pass with ⟨impossible,_,_⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false,CTy.int.injEq] at impossible
      rcases width with small | large <;> rcases impossible with bad | bad <;> omega
    · obtain ⟨_,_,_,extState⟩ := extended
      first
      | (have safeY : DemandAllowed ctx st y := by
           intro i defined
           have actual := ‹DemandAllowed ctx _ y› i defined
           simpa only [extState,State.mark] using actual
         exact ⟨typed,safeX,safeY,⟨rx,mapX⟩,⟨_,‹ctx.valueReg? y = some _›⟩⟩)
      | (have negCall : ApplyInternal p (Stock.sem ctx) {} ?_ 27 437 ?_ ?_ ?_ ?_ := by assumption
         have guard := stock_rotate_pure_sunk hp' ctx (cfg := {}) rfl (t := 437) (by decide) negCall
         have safe : DemandAllowed ctx st x := by
           intro i defined
           have actual := safeX i defined
           simpa only [guard,State.mark] using actual
         exact ⟨typed,safe,‹DemandAllowed ctx st y›,⟨rx,mapX⟩,⟨_,‹ctx.valueReg? y = some _›⟩⟩)
end Backend.Stock.Proof.ScalarRotate

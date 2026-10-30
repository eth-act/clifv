import FV.Backend.Proof.StockAluSelectedValues
import FV.Backend.Proof.StockHighMulNarrowRhs
import FV.Backend.Proof.StockExtendRequests
namespace Backend.Stock.Proof.ScalarHighMul
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

/-- Actual successful high-multiply widening calls expose their original source
request and complete state, without a caller-supplied mapping or safety fact. -/
theorem stock_highmul_extend_observed {p : Program} (hp : Data p) (ctx : Ctx)
    (signed : Bool) {cfg : Config} (hc : cfg.checkOverlap = false)
    {n x : Nat} (enough : 60 ≤ n) {s s' : State × Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg n 27 (if signed then 557 else 558)
      [.value x] s out s') :
    ScalarShift.MappedExtOut ctx x signed 64 [.int 64] s.1 s'.1 out := by
  cases signed
  · exact ScalarShift.stock_zext64_out hp hc enough run
  · exact ScalarShift.stock_sext64_out hp hc enough run

/-- Original frame typing and the original source getter force a narrow source
helper to widen, excluding the 64-bit pass-through alternative internally.

Compatibility boundary (S11b, #140): `int` cannot be derived from the run. The widening
helper's `fits_in_32` guard also admits an `f32` source, and `FrameTyped` then types `x` as
`.float 32`, so the conclusion `.int ty.width` holds only on the original integer domain.
Every caller takes `int` from `isInt_of_eTy` of the instruction's type. -/
theorem stock_highmul_narrow_request_observed {p : Program} (hp : Data p) (ctx : Ctx)
    (signed : Bool) {cfg : Config} (hc : cfg.checkOverlap = false)
    {n x : Nat} (enough : 60 ≤ n) {s s' : State × Array RuleId} {out : V}
    {fr : Clif.Frame} (typed : FrameTyped ctx fr) {ty : Clif.Ty} {u : BitVec ty.width}
    (get : fr.getAs x ty = .ok u) (width : ty.width ≤ 32) (int : ty.isInt = true)
    (run : ApplyInternal p (Stock.sem ctx) cfg n 27 (if signed then 557 else 558)
      [.value x] s out s') :
    ctx.valueType? x = some (.int ty.width) ∧ DemandAllowed ctx s.1 x ∧
      ∃ rx,ctx.valueReg? x = some rx ∧ out = .reg (s.1.base.fresh .int).1 ∧
        s'.1 = {s.1.mark x with base := extendBase s.1.base signed ty.width rx} := by
  obtain ⟨t,sourceType,safe,rx,mapped,alternatives⟩ :=
    stock_highmul_extend_observed hp ctx signed hc enough run
  have equal : t = .int ty.width :=
    (typed x t ⟨ty,u⟩ sourceType (getAs_ok get)).symm.trans (ofClif_int_width int)
  rw [equal] at sourceType alternatives
  refine ⟨sourceType,safe,rx,mapped,?_,?_⟩
  · rcases alternatives with pass | widened
    · have impossible : ty.width = 64 := CTy.int.inj (List.mem_singleton.mp pass.1)
      omega
    · exact widened.2.2.1
  · rcases alternatives with pass | widened
    · have impossible : ty.width = 64 := CTy.int.inj (List.mem_singleton.mp pass.1)
      omega
    · exact widened.2.2.2
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_prim (ctx : Ctx) : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl

/-- Both successful original narrow RHS requests derive their types, guards
and source mappings using the original typed frame. Compatibility boundary (S11b, #140):
original integer domain only, as for `stock_highmul_narrow_request_observed`. -/
theorem stock_highmul_narrow_requests {p : Program} (hp : Data p) (ctx : Ctx)
    (signed : Bool) {n x y : Nat} {ty : Clif.Ty} (width : ty.width ≤ 32) (int : ty.isInt = true)
    {fr : Clif.Frame} (typed : FrameTyped ctx fr) {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+100) (narrowRule signed).rhs
      (narrowEnv ty.width x y)).run (st,tr) = .ok (some out,next,trace)) :
    ctx.valueType? x = some (.int ty.width) ∧ ctx.valueType? y = some (.int ty.width) ∧
      DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧
      ∃ rx ry,ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry := by
  have hp' := hp
  cases hp
  cases signed
  all_goals
    isel_inv [*,narrowRule,narrowEnv,rule_lower_1059,rule_lower_1071,sem_ctor,sem_prim] at run
    all_goals isel_destruct <;> subst_vars
  ·
    have first := stock_highmul_narrow_request_observed hp' ctx false (cfg := {}) rfl
      (n := n+96) (by omega) typed getX width int
      (show ApplyInternal p (Stock.sem ctx) {} (n+96) 27 558 [.value x] (st,tr) _ _ from by assumption)
    obtain ⟨typeX,safeX,rx,mapX,outX,stateX⟩ := first
    have second := stock_highmul_narrow_request_observed hp' ctx false (cfg := {}) rfl
      (n := n+95) (by omega) typed getY width int
      (show ApplyInternal p (Stock.sem ctx) {} (n+95) 27 558 [.value y] _ _ _ from by assumption)
    obtain ⟨typeY,safeY,ry,mapY,outY,stateY⟩ := second
    rw [stateX] at safeY
    exact ⟨typeX,typeY,safeX,safeY,⟨rx,mapX⟩,⟨ry,mapY⟩⟩

  ·
    have first := stock_highmul_narrow_request_observed hp' ctx true (cfg := {}) rfl
      (n := n+96) (by omega) typed getX width int
      (show ApplyInternal p (Stock.sem ctx) {} (n+96) 27 557 [.value x] (st,tr) _ _ from by assumption)
    obtain ⟨typeX,safeX,rx,mapX,outX,stateX⟩ := first
    have second := stock_highmul_narrow_request_observed hp' ctx true (cfg := {}) rfl
      (n := n+95) (by omega) typed getY width int
      (show ApplyInternal p (Stock.sem ctx) {} (n+95) 27 557 [.value y] _ _ _ from by assumption)
    obtain ⟨typeY,safeY,ry,mapY,outY,stateY⟩ := second
    rw [stateX] at safeY
    exact ⟨typeX,typeY,safeX,safeY,⟨rx,mapX⟩,⟨ry,mapY⟩⟩
/-- Successful actual narrow RHS execution determines both original requests,
the output, and the complete four-write scheduling state. Compatibility boundary (S11b,
#140): original integer domain only, as for `stock_highmul_narrow_request_observed`. -/
theorem stock_highmul_narrow_observed {p : Program} (hp : Data p) (ctx : Ctx)
    (signed : Bool) {n x y : Nat} {ty : Clif.Ty} (width : ty.width ≤ 32) (int : ty.isInt = true)
    {fr : Clif.Frame} (typed : FrameTyped ctx fr) {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+100) (narrowRule signed).rhs
      (narrowEnv ty.width x y)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧
      ∃ rx ry,ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
        out = .regsVec [[((multiplyBase (extendBase (extendBase st.base signed ty.width rx)
          signed ty.width ry) (st.base.fresh .int).1
          ((extendBase st.base signed ty.width rx).fresh .int).1).fresh .int).1]] ∧
        next = {(st.mark x).mark y with base := narrowBase st.base signed ty.width rx ry} := by
  obtain ⟨typeX,typeY,safeX,safeY,rx,ry,mapX,mapY⟩ :=
    stock_highmul_narrow_requests hp ctx signed width int typed getX getY run
  obtain ⟨actualTrace,forward⟩ := stock_highmul_narrow_rhs hp ctx signed width
    typeX typeY mapX mapY st safeX safeY tr n
  rw [forward] at run
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
  obtain ⟨outEq,stateEq,_⟩ := run
  exact ⟨safeX,safeY,rx,ry,mapX,mapY,outEq.symm,stateEq.symm⟩
/-- Successful actual wide RHS execution derives both guarded source requests. -/
theorem stock_highmul_wide_requests {p : Program} (hp : Data p) (ctx : Ctx)
    (signed : Bool) {n x y : Nat} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+50) (wideRule signed).rhs
      (wideEnv x y)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧
      ∃ rx ry,ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry := by
  cases hp
  cases signed
  all_goals
    isel_inv [*,wideRule,wideEnv,rule_lower_1056,rule_lower_1068,sem_ctor,sem_prim,
      stock_put_in_reg_iff] at run
    all_goals simp only [stock_put_in_reg_iff] at *
    all_goals isel_destruct <;> subst_vars
    exact ⟨by assumption,by assumption,⟨_,by assumption⟩,⟨_,by assumption⟩⟩

/-- The real wide RHS receipt fixes output and full scheduling state. -/
theorem stock_highmul_wide_observed {p : Program} (hp : Data p) (ctx : Ctx)
    (signed : Bool) {n x y : Nat} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+50) (wideRule signed).rhs
      (wideEnv x y)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧
      ∃ rx ry,ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
        out = .regsVec [[(st.base.fresh .int).1]] ∧
        next = {(st.mark x).mark y with base := ((st.base.fresh .int).2.emit
          (.aluRRR (if signed then .sMulH else .uMulH) .size64 (st.base.fresh .int).1 rx ry))} := by
  obtain ⟨safeX,safeY,rx,ry,mapX,mapY⟩ := stock_highmul_wide_requests hp ctx signed run
  obtain ⟨actualTrace,forward⟩ := stock_highmul_wide_rhs hp ctx signed mapX mapY st safeX safeY tr n
  rw [forward] at run
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
  obtain ⟨outEq,stateEq,_⟩ := run
  exact ⟨safeX,safeY,rx,ry,mapX,mapY,outEq.symm,stateEq.symm⟩
end Backend.Stock.Proof.ScalarHighMul

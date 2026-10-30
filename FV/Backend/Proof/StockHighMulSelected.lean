import FV.Backend.Proof.StockHighMulSemantics
import FV.Backend.Proof.StockHighMulDispatch
import FV.Backend.Proof.StockHighMulRequests
namespace Backend.Stock.Proof.ScalarHighMul
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- The actual selected 64-bit source derives its root, guarded input requests,
output and complete scheduling state internally. -/
theorem stock_highmul_wide_selected {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (signed : Bool) {i x y : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (if signed then .smulhi else .umulhi) .i64 x y))
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧
      ∃ rx ry,ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
        out = .regsVec [[(st.base.fresh .int).1]] ∧
        next = {(st.mark x).mark y with base := ((st.base.fresh .int).2.emit
          (.aluRRR (if signed then .sMulH else .uMulH) .size64 (st.base.fresh .int).1 rx ry))} := by
  obtain ⟨_,data,type⟩ := stock_highmul_source_data inv signed source clif
  have chosen : selected.rule = wideRule signed := stock_selected_highmul_rule inv signed source clif selected
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+2 := ⟨selected.matchFuel-2,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq,stock_highmul_wide_match data_program ctx signed source type data st #[] m] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,stateEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [chosen,← envEq,← stateEq,← traceEq] at rhs
  change (evalExpr program (Stock.sem ctx) {} (999949+50) (wideRule signed).rhs
    (wideEnv x y)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
  exact stock_highmul_wide_observed data_program ctx signed rhs

/-- Actual narrow source selection determines both original typed requests and
all four writes, without a caller-selected root or typed helper certificate. -/
theorem stock_highmul_narrow_selected {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (signed : Bool) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (if signed then .smulhi else .umulhi) ty x y))
    (width : ty.width ≤ 32) {fr : Clif.Frame} (typed : FrameTyped ctx fr)
    {u v : BitVec ty.width} (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧
      ∃ rx ry,ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
        out = .regsVec [[((multiplyBase (extendBase (extendBase st.base signed ty.width rx)
          signed ty.width ry) (st.base.fresh .int).1
          ((extendBase st.base signed ty.width rx).fresh .int).1).fresh .int).1]] ∧
        next = {(st.mark x).mark y with base := narrowBase st.base signed ty.width rx ry} := by
  obtain ⟨_,data,type⟩ := stock_highmul_source_data inv signed source clif
  have int : ty.isInt = true := by
    have accepted := inv.instE i info _ source clif
    have supported : eTy ty = true := by
      cases signed <;> simpa [Compile.instE,Compile.binaryE,Compile.tyE,eTy] using accepted
    exact isInt_of_eTy supported
  have chosen := stock_selected_highmul_rule inv signed source clif selected
  simp only [highmulRule,show ty.width ≠ 64 by omega,ite_false] at chosen
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+2 := ⟨selected.matchFuel-2,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq,stock_highmul_narrow_match data_program ctx signed source type width data st #[] m] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,stateEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [chosen,← envEq,← stateEq,← traceEq] at rhs
  change (evalExpr program (Stock.sem ctx) {} (999899+100) (narrowRule signed).rhs
    (narrowEnv ty.width x y)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
  exact stock_highmul_narrow_observed data_program ctx signed width int typed getX getY rhs
/-- Actual wide source selection computes the original high product through
final aliases and preserves every other machine register. -/
theorem stock_highmul_wide_selected_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (signed : Bool) {i x y : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (if signed then .smulhi else .umulhi) .i64 x y))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {u v : BitVec 64}
    (getX : fr.getAs x .i64 = .ok u) (getY : fr.getAs y .i64 = .ok v)
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (nx ny : Nat) (ρ' : Nat → CV),
      ctx.valueReg? x = some (.vreg nx .int) ∧ ctx.valueReg? y = some (.vreg ny .int) ∧
      out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next = {(st.mark x).mark y with base := ((st.base.fresh .int).2.emit
        (.aluRRR (if signed then .sMulH else .uMulH) .size64 (.vreg st.base.nextVreg .int)
          (.vreg nx .int) (.vreg ny .int)))} ∧
      PRun F isem [(.aluRRR (if signed then .sMulH else .uMulH) .size64
        (.vreg st.base.nextVreg .int) (.vreg nx .int) (.vreg ny .int) : MInst).mapRegs
          (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨.i64,Clif.Sem.binary (if signed then .smulhi else .umulhi) u v⟩ (ρ' st.base.nextVreg) ∧
      ∀ n,n ≠ st.base.nextVreg → ρ' n = ρ n := by
  obtain ⟨safeX,safeY,rx,ry,mapX,mapY,outEq,stateEq⟩ := stock_highmul_wide_selected inv signed source clif selected
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapX
  obtain ⟨ny,rfl⟩ := inv.valueReg y ry mapY
  have inputs : ValuesHeld (fun k => k = x ∨ k = y) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    apply held.mono
    intro k operand
    rw [stateEq,Demanded]
    change ((st.mark x).mark y).demand[k]! ≠ 0
    rcases operand with operand | operand
    · subst k
      by_cases same : x = y
      · subst y
        rw [(mark_demand (st.mark x) x (by simpa only [State.mark,Array.size_modify] using extent x _ mapX)).1]
        omega
      · rw [mark_other (st.mark x) y x same,(mark_demand st x (extent x _ mapX)).1]
        omega
    · subst k
      rw [(mark_demand (st.mark x) y (by simpa only [State.mark,Array.size_modify] using extent y _ mapY)).1]
      omega
  obtain ⟨ρ',execution,value,kept⟩ := stock_highmul_wide_resolved refines signed bounded mapX mapY inputs getX getY
  exact ⟨nx,ny,ρ',mapX,mapY,outEq,stateEq,execution,value,kept⟩
end Backend.Stock.Proof.ScalarHighMul

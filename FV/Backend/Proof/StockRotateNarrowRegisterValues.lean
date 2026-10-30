import FV.Backend.Proof.StockSelectionReceipts
import FV.Backend.Proof.StockRotateMatch
import FV.Backend.Proof.StockRotateRegisterRequests
import FV.Backend.Proof.StockRotateNarrowRegisterSemantics
namespace Backend.Stock.Proof.ScalarRotate
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem narrow_register_match_width {ctx : Ctx} {left : Bool} {i w : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    {st : LState} {env env' : Isle.Interp.Env V}
    (matched : matchArgs program (Backend.sem ctx) st (rotateNarrowRule left false).args [.inst i] env = .ok (some env')) : w ≤ 16 := by
  have shape : ∃ q,(rotateNarrowRule left false).args =
      [.term 18 209 [.term 14 110 [.bind 14 0 (.wildcard 14)],q]] := by cases left <;> exact ⟨_,rfl⟩
  obtain ⟨q,shape⟩ := shape
  rw [shape] at matched
  obtain ⟨e1,root,_⟩ := matchArgs_cons_inv matched
  obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl root
  rw [Backend.Proof.sem_extract] at extracted
  have expected := ext_inst_data_value ctx st source
  rw [type,Option.getD_some] at expected
  rw [expected] at extracted
  cases extracted
  obtain ⟨e2,small,_⟩ := matchArgs_cons_inv patterns
  obtain ⟨fields,extracted,_⟩ := matchPat_extract_inv data_program.t110 term_110_kind rfl small
  rw [Backend.Proof.sem_extract,ext_fits_in_16] at extracted
  by_cases fits : w ≤ 16
  · exact fits
  · rw [if_neg fits] at extracted; cases extracted
private theorem requests_demanded (left : Bool) (st : State) (x y : Nat)
    (hx : x < st.demand.size) (hy : y < st.demand.size) :
    Demanded (rotateWideRequests left st x y) x ∧ Demanded (rotateWideRequests left st x y) y := by
  cases left
  · change Demanded ((st.mark x).mark y) x ∧ Demanded ((st.mark x).mark y) y
    have xNeeded := (demanded_mark_iff st x x hx).mpr (.inl rfl)
    have bound : y < (st.mark x).demand.size := by simpa only [State.mark,Array.size_modify] using hy
    exact ⟨(demanded_mark_iff (st.mark x) y x bound).mpr (.inr xNeeded),
      (demanded_mark_iff (st.mark x) y y bound).mpr (.inl rfl)⟩
  · change Demanded ((st.mark y).mark x) x ∧ Demanded ((st.mark y).mark x) y
    have yNeeded := (demanded_mark_iff st y y hy).mpr (.inl rfl)
    have bound : x < (st.mark y).demand.size := by simpa only [State.mark,Array.size_modify] using hx
    exact ⟨(demanded_mark_iff (st.mark y) x x bound).mpr (.inl rfl),
      (demanded_mark_iff (st.mark y) x y bound).mpr (.inr yNeeded)⟩
/-- Actual narrow register selection derives original source typing and both
requests and determines the complete actual output state. -/
theorem stock_rotate_selected_narrow_register_state {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (left : Bool) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.binary (rotateOp left) ty x y))
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u : BitVec ty.width} (getX : fr.getAs x ty = .ok u)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = rotateNarrowRule left false) :
    ∃ nx ny,(ty.width = 8 ∨ ty.width = 16) ∧ ctx.valueType? x = some (.int ty.width) ∧
      ctx.valueReg? x = some (.vreg nx .int) ∧ ctx.valueReg? y = some (.vreg ny .int) ∧
      out = .regsVec [[.vreg (rotateNarrowRootResult left st.base.nextVreg) .int]] ∧
      next = {rotateWideRequests left st x y with base := rotateNarrowRootBase left ty.width st.base (.vreg nx .int) (.vreg ny .int)} := by
  obtain ⟨width,data,type⟩ := stock_rotate_source_data inv left source clif
  have enough := selected.fuelBound
  have roots : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+10 := ⟨selected.matchFuel-10,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  obtain ⟨initial,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs] at args
  have physical := narrow_register_match_width source type args
  have supported : ty.width = 8 ∨ ty.width = 16 := by rcases width with h | h | h | h <;> omega
  have rootEq : rotateRule left false ty.width = rotateNarrowRule left false := by simp [rotateRule,supported]
  have expected := stock_rotate_register_match data_program ctx left width source type data st #[] m
  rw [rootEq] at expected
  rw [expected] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,middleEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [chosen,← envEq,← middleEq,← traceEq] at rhs
  have envEq' : rotateEnv left ty.width x y = rotateNarrowEnv left ty.width x y := by simp [rotateEnv,supported]
  rw [envEq'] at rhs
  change (evalExpr program (Stock.sem ctx) {} (999839+160) (rotateNarrowRule left false).rhs
    (rotateNarrowEnv left ty.width x y)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
  obtain ⟨typed,safeX,safeY,⟨rx,mapX⟩,ry,mapY⟩ := stock_rotate_narrow_register_requests
    data_program ctx left supported dfg rfl getX rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapX
  obtain ⟨ny,rfl⟩ := inv.valueReg y ry mapY
  obtain ⟨trace,forward⟩ := stock_rotate_narrow_rhs data_program ctx left supported mapX mapY typed st safeX safeY #[] 999839
  rw [forward] at rhs
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at rhs
  obtain ⟨outEq,nextEq,_⟩ := rhs
  exact ⟨nx,ny,supported,typed,mapX,mapY,outEq.symm,nextEq.symm⟩
/-- Selected narrow register roots compute original low bits and count through
final aliases. Retained composition supplies the internal write protection. -/
theorem stock_rotate_selected_narrow_register_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (left : Bool) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.binary (rotateOp left) ty x y))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u : BitVec ty.width} (getX : fr.getAs x ty = .ok u)
    {amount : Clif.Val} (getY : fr.regs y = some amount)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = rotateNarrowRule left false) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ v r,ctx.valueReg? v = some r → v < st.demand.size)
    (protectedX : ∀ a,ctx.valueReg? x = some (.vreg a .int) → left = true → aliasNum aliases a ≠ st.base.nextVreg)
    (protectedY : ∀ a,ctx.valueReg? y = some (.vreg a .int) → left = false → aliasNum aliases a ≠ st.base.nextVreg)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (nx ny : Nat) (ρ' : Nat → CV),(ty.width = 8 ∨ ty.width = 16) ∧
      ctx.valueReg? x = some (.vreg nx .int) ∧ ctx.valueReg? y = some (.vreg ny .int) ∧
      out = .regsVec [[.vreg (rotateNarrowRootResult left st.base.nextVreg) .int]] ∧
      next = {rotateWideRequests left st x y with base := rotateNarrowRootBase left ty.width st.base (.vreg nx .int) (.vreg ny .int)} ∧
      PRun F isem ((rotateNarrowRegisterCode left ty.width st.base.nextVreg nx ny).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,rotateWideBits left u amount.bits.toNat⟩ (ρ' (rotateNarrowRootResult left st.base.nextVreg)) ∧
      ∀ z,z < st.base.nextVreg ∨ st.base.nextVreg+rotateNarrowRegisterAlloc left ≤ z → ρ' z = ρ z := by
  obtain ⟨nx,ny,width,typed,mapX,mapY,output,nextEq⟩ := stock_rotate_selected_narrow_register_state
    inv left source clif dfg getX selected chosen
  have needed := requests_demanded left st x y (extent x _ mapX) (extent y _ mapY)
  have neededX : Demanded next x := by rw [nextEq]; exact needed.1
  have neededY : Demanded next y := by rw [nextEq]; exact needed.2
  have input := held.read neededX (getAs_ok getX) mapX
  have count := held.read neededY getY mapY
  obtain ⟨ρ',execution,value,kept⟩ := stock_rotate_narrow_register_resolved refines left width bounded
    (protectedX nx mapX) (protectedY ny mapY) input count
  exact ⟨nx,ny,ρ',width,mapX,mapY,output,nextEq,execution,value,kept⟩
end Backend.Stock.Proof.ScalarRotate

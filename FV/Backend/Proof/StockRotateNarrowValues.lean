import FV.Backend.Proof.StockRotateSelectedValues
namespace Backend.Stock.Proof.ScalarRotate
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem fresh_reg {aliases : Array (Option Nat)} {d : Nat} (bounded : aliases.size ≤ d) :
    Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int) = .vreg d .int := by
  rw [resolve_vreg]
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none; rw [Array.getElem?_eq_none bounded]; rfl
  change Reg.vreg (aliasNum aliases d) .int = _
  rw [fresh]
def rotateNarrowImmCode (left : Bool) (w d x amount : Nat) : List MInst :=
  [.extend (.vreg d .int) (.vreg x .int) false w 32,
   .aluRRImmShift .lsr .size32 (.vreg (d+1) .int) (.vreg d .int) (rotateImmediate left w amount),
   .aluRRImmShift .lsl .size32 (.vreg (d+2) .int) (.vreg d .int) (w-rotateImmediate left w amount),
   .aluRRR .orr .size32 (.vreg (d+3) .int) (.vreg (d+2) .int) (.vreg (d+1) .int)]
/-- Narrow immediate rotation executes the actual zero-extension/shifts/OR
through final aliases, independently of dirty upper source bits, preserving
all registers outside its complete four-register allocation. -/
theorem stock_rotate_narrow_imm_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (left : Bool) {ty : Clif.Ty} (width : ty.width = 8 ∨ ty.width = 16)
    {amount : Nat} (count : amount < ty.width) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    {d x : Nat} (bounded : aliases.size ≤ d) {u : BitVec ty.width}
    (held : VHolds ⟨ty,u⟩ (ρ (aliasNum aliases x))) :
    ∃ ρ',PRun F isem ((rotateNarrowImmCode left ty.width d x amount).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,rotateWideBits left u amount⟩ (ρ' (d+3)) ∧
      ∀ z,z < d ∨ d+4 ≤ z → ρ' z = ρ z := by
  have small : ty.width < 32 := by rcases width with h | h <;> omega
  have positive : 0 < ty.width := by rcases width with h | h <;> omega
  let a := rotateImmediate left ty.width amount
  have fits : a < ty.width := by
    cases left
    · exact count
    · exact Nat.mod_lt _ positive
  let low := (lo64 (ρ (aliasNum aliases x))).setWidth ty.width
  let r0 := resX .size32 (low.setWidth OperandSize.size32.bits)
  let q0 := upd ρ d r0
  let r1 := resX .size32 (opnd .size32 (q0 d) >>> a)
  let q1 := upd q0 (d+1) r1
  let r2 := resX .size32 (opnd .size32 (q1 d) <<< (ty.width-a))
  let q2 := upd q1 (d+2) r2
  let r3 := resX .size32 (opnd .size32 (q2 (d+2)) ||| opnd .size32 (q2 (d+1)))
  refine ⟨upd q2 (d+3) r3,?_,?_,?_⟩
  · simp only [rotateNarrowImmCode,List.map_cons,List.map_nil,MInst.mapRegs]
    rw [fresh_reg bounded,fresh_reg (by omega : aliases.size ≤ d+1),
      fresh_reg (by omega : aliases.size ≤ d+2),fresh_reg (by omega : aliases.size ≤ d+3),resolve_vreg]
    exact prun_rr refines rfl
      (fun _ => ispec_extend (width.elim (fun h => .inl h) (fun h => .inr (.inl h))) (.inl rfl) small)
      (prun_rr refines rfl (fun world => ispec_imm_shift_fb (.inr (.inl rfl))
        (by change a < 32; omega))
      (prun_rr refines rfl (fun world => ispec_imm_shift_fb (.inl rfl)
        (by change ty.width-a < 32; omega))
      (prun_rrr refines (operands_aluRRR _ _ _ _ _) (fun _ => ispec_orr_fb) (prun_nil _))))
  · rw [upd_same]
    change r3.setWidth ty.width = _
    dsimp only [r3,q2,q1,r2,r1,q0]
    simp only [upd_same,upd_ne_fb (by omega : d+1 ≠ d+2),upd_ne_fb (by omega : d ≠ d+1),opnd_resX]
    dsimp only [r0]
    rw [opnd_resX,resX_setWidth (by change ty.width ≤ 32; omega) (by decide)]
    have result := small_rot_fin width low fits
    change ((low.setWidth 32 <<< (ty.width-a)) ||| (low.setWidth 32 >>> a)).setWidth ty.width = _
    apply result.trans
    have input : low = u := by
      change (opnd .size64 (ρ (aliasNum aliases x))).setWidth ty.width = u
      rw [opnd_setWidth (by change ty.width ≤ 64; omega) (by decide)]
      exact held
    rw [input]
    cases left
    · simp only [a,rotateImmediate,rotateWideBits,Bool.false_eq_true,ite_false,Nat.mod_eq_of_lt count]
    · simp only [a,rotateImmediate,rotateWideBits,ite_true]
      apply rotr_neg positive
      simp only [Nat.mod_mod,Nat.mod_eq_of_lt count]
  · intro z outside
    simp only [q2,q1,q0,upd,show z ≠ d by omega,show z ≠ d+1 by omega,
      show z ≠ d+2 by omega,show z ≠ d+3 by omega,ite_false]
private theorem narrow_match_width {ctx : Ctx} {left : Bool} {i w : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    {st : LState} {env env' : Isle.Interp.Env V}
    (matched : matchArgs program (Backend.sem ctx) st (rotateNarrowRule left true).args [.inst i] env = .ok (some env')) : w ≤ 16 := by
  have shape : ∃ q,(rotateNarrowRule left true).args =
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
/-- Actual selected narrow immediate rotations derive width, source type,
original constant count and guarded mapped source internally, computing the
original low-bit value through final aliases with full four-write preservation. -/
theorem stock_rotate_selected_narrow_immediate_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (left : Bool) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.binary (rotateOp left) ty x y))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u : BitVec ty.width} (getX : fr.getAs x ty = .ok u)
    {amount : Clif.Val} (getY : fr.regs y = some amount)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = rotateNarrowRule left true) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ v r,ctx.valueReg? v = some r → v < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (nx count : Nat) (ρ' : Nat → CV),(ty.width = 8 ∨ ty.width = 16) ∧
      ctx.valueType? x = some (.int ty.width) ∧ ctx.valueReg? x = some (.vreg nx .int) ∧
      count = amount.bits.toNat % ty.width ∧ count < ty.width ∧
      out = .regsVec [[.vreg (st.base.nextVreg+3) .int]] ∧
      next = {st.mark x with base := rotateNarrowImmRootBase left ty.width st.base (.vreg nx .int) count} ∧
      PRun F isem ((rotateNarrowImmCode left ty.width st.base.nextVreg nx count).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,rotateWideBits left u amount.bits.toNat⟩ (ρ' (st.base.nextVreg+3)) ∧
      ∀ z,z < st.base.nextVreg ∨ st.base.nextVreg+4 ≤ z → ρ' z = ρ z := by
  obtain ⟨width,data,type⟩ := stock_rotate_source_data inv left source clif
  have enough := selected.fuelBound
  have roots : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+20 := ⟨selected.matchFuel-20,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  obtain ⟨initial,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs] at args
  have small := narrow_match_width source type args
  have narrow : ty.width = 8 ∨ ty.width = 16 := by rcases width with h | h | h | h <;> omega
  have rootEq : rotateRule left true ty.width = rotateNarrowRule left true := by simp only [rotateRule,narrow,ite_true]
  rw [← rootEq] at matched
  obtain ⟨j,literal,constantTy,bits,c,count,defined,found,original,value,envEq,middleEq,countEq,countBound⟩ :=
    stock_rotate_immediate_receipts data_program inv left dfg width source type data getY matched
  have rhs := selected.rhsRun
  rw [chosen,envEq,middleEq] at rhs
  simp only [rotateImmediateEnv,narrow,ite_true] at rhs
  change (evalExpr program (Stock.sem ctx) {} (999859+140) (rotateNarrowRule left true).rhs
    (env4 (.ty (.int ty.width)) (.value x) (.int c) (.op (.immShift count)))).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
  obtain ⟨typed,safe,rx,mapped⟩ := stock_rotate_narrow_immediate_requests data_program ctx left narrow dfg rfl getX rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapped
  obtain ⟨trace,forward⟩ := stock_rotate_narrow_imm_rhs data_program ctx left narrow countBound c mapped typed st safe #[] 999859
  rw [forward] at rhs
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at rhs
  obtain ⟨outEq,nextEq,_⟩ := rhs
  have input := held.read (by
      rw [← nextEq,Demanded]
      change (st.mark x).demand[x]! ≠ 0
      rw [(mark_demand st x (extent x _ mapped)).1]; omega) (getAs_ok getX) mapped
  obtain ⟨ρ',execution,result,kept⟩ := stock_rotate_narrow_imm_resolved refines left narrow countBound bounded input
  refine ⟨nx,count,ρ',narrow,typed,mapped,countEq,countBound,outEq.symm,nextEq.symm,execution,?_,kept⟩
  simpa only [countEq,rotateWideBits,Nat.mod_mod] using result
end Backend.Stock.Proof.ScalarRotate

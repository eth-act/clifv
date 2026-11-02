import FV.Backend.Proof.StockSelectionReceipts
import FV.Backend.Proof.StockRotateMatch
import FV.Backend.Proof.StockRotateRegisterRequests
namespace Backend.Stock.Proof.ScalarRotate
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem type_match {ctx : Ctx} {r : Rule} {name : String} {target i w : Nat} {q : Pattern}
    (args : r.args = [.term 18 209 [.constPrim 14 name,q]])
    (primitive : (Backend.sem ctx).prim 14 name = some (.ty (.int target)))
    {info : IInfo} (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    {st : LState} {env env' : Isle.Interp.Env V}
    (matched : matchArgs program (Backend.sem ctx) st r.args [.inst i] env = .ok (some env')) : w = target := by
  rw [args] at matched
  obtain ⟨first,head,_⟩ := matchArgs_cons_inv matched
  obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl head
  rw [Backend.Proof.sem_extract] at extracted
  have expected := ext_inst_data_value ctx st source
  rw [type,Option.getD_some] at expected
  rw [expected] at extracted
  cases extracted
  obtain ⟨middle,typeMatch,_⟩ := matchArgs_cons_inv patterns
  have eq : ∀ a b,(Backend.sem ctx).eq a b = (a == b) := fun _ _ => rfl
  simp only [matchPat.eq_5,primitive,eq] at typeMatch
  split at typeMatch
  · rename_i same
    have types := beq_iff_eq.mp same
    exact CTy.int.inj (V.ty.inj types)
  · cases typeMatch
private theorem wide_register_match_width {ctx : Ctx} {left wide : Bool} {i w : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    {st : LState} {env env' : Isle.Interp.Env V}
    (matched : matchArgs program (Backend.sem ctx) st (rotateWideRule left wide).args [.inst i] env = .ok (some env')) :
    w = rotateWidth wide := by
  cases left <;> cases wide
  · exact type_match (name := "I32") (target := 32) rfl rfl source type matched
  · exact type_match (name := "I64") (target := 64) rfl rfl source type matched
  · exact type_match (name := "I32") (target := 32) rfl rfl source type matched
  · exact type_match (name := "I64") (target := 64) rfl rfl source type matched
private theorem wide_register_value {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (left : Bool) {ty : Clif.Ty} (width : ty.width = 32 ∨ ty.width = 64)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {d x y : Nat}
    (bounded : aliases.size ≤ d) (protectedX : left = true → aliasNum aliases x ≠ d)
    {u : BitVec ty.width} (heldX : VHolds ⟨ty,u⟩ (ρ (aliasNum aliases x)))
    {amount : Clif.Val} (heldY : VHolds amount (ρ (aliasNum aliases y))) :
    ∃ ρ',PRun F isem ((rotateWideCode left (szOf ty.width) d x y).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,rotateWideBits left u amount.bits.toNat⟩ (ρ' (rotateWideResult left d)) ∧
      ∀ z,z < d ∨ d+rotateWideAlloc left ≤ z → ρ' z = ρ z := by
  rcases width with small | large
  · rcases (show ty = .i32 ∨ ty = .f32 by revert small; cases ty <;> simp [Clif.Ty.width])
      with rfl | rfl <;>
    simpa only [Clif.Ty.width,szOf,Nat.reduceLeDiff,ite_true,VHolds,OperandSize.bits] using
      stock_rotate_wide_resolved refines left .size32 bounded protectedX heldX heldY
  · rcases (show ty = .i64 ∨ ty = .f64 by revert large; cases ty <;> simp [Clif.Ty.width])
      with rfl | rfl <;>
    simpa only [Clif.Ty.width,szOf,Nat.reduceLeDiff,ite_false,VHolds,OperandSize.bits] using
      stock_rotate_wide_resolved refines left .size64 bounded protectedX heldX heldY
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
/-- Successful wide register selection determines the complete actual output
and state, independently of source machine values. -/
theorem stock_rotate_selected_wide_register_state {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (left wide : Bool) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.binary (rotateOp left) ty x y))
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = rotateWideRule left wide) :
    ∃ nx ny,ty.width = rotateWidth wide ∧ ctx.valueReg? x = some (.vreg nx .int) ∧
      ctx.valueReg? y = some (.vreg ny .int) ∧
      out = .regsVec [[.vreg (rotateWideResult left st.base.nextVreg) .int]] ∧
      next = {rotateWideRequests left st x y with base := rotateWideBase left wide st.base (.vreg nx .int) (.vreg ny .int)} := by
  obtain ⟨width,data,type⟩ := stock_rotate_source_data inv left source clif
  have enough := selected.fuelBound
  have roots : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+10 := ⟨selected.matchFuel-10,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  obtain ⟨initial,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs] at args
  have physical := wide_register_match_width source type args
  have supported : ty.width = 32 ∨ ty.width = 64 := by
    cases wide
    · exact .inl physical
    · exact .inr physical
  have narrow : ¬ (ty.width = 8 ∨ ty.width = 16) := by rcases supported with h | h <;> omega
  have rootEq : rotateRule left false ty.width = rotateWideRule left wide := by
    simp only [rotateRule,narrow,ite_false,ite_false]
    cases wide <;> simp [physical,rotateWidth]
  have expected := stock_rotate_register_match data_program ctx left width source type data st #[] m
  rw [rootEq] at expected
  rw [expected] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,middleEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [chosen,← envEq,← middleEq,← traceEq] at rhs
  have envEq' : rotateEnv left ty.width x y = rotateWideEnv left x y := by simp [rotateEnv,narrow]
  rw [envEq'] at rhs
  change (evalExpr program (Stock.sem ctx) {} (999939+60) (rotateWideRule left wide).rhs
    (rotateWideEnv left x y)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
  obtain ⟨safeX,safeY,⟨rx,mapX⟩,ry,mapY⟩ := stock_rotate_wide_register_requests data_program ctx left wide rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapX
  obtain ⟨ny,rfl⟩ := inv.valueReg y ry mapY
  obtain ⟨trace,forward⟩ := stock_rotate_wide_rhs data_program ctx left wide mapX mapY st safeX safeY #[] 999939
  rw [forward] at rhs
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at rhs
  obtain ⟨outEq,nextEq,_⟩ := rhs
  exact ⟨nx,ny,physical,mapX,mapY,outEq.symm,nextEq.symm⟩
/-- Actual wide register selection computes the original source value through
final aliases. The internal source-protection premise is discharged from
original availability by retained-record composition, not by a new input gate. -/
theorem stock_rotate_selected_wide_register_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (left wide : Bool) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.binary (rotateOp left) ty x y))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {u : BitVec ty.width} (getX : fr.getAs x ty = .ok u)
    {amount : Clif.Val} (getY : fr.regs y = some amount)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = rotateWideRule left wide) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ v r,ctx.valueReg? v = some r → v < st.demand.size)
    (protectedX : ∀ a,ctx.valueReg? x = some (.vreg a .int) → left = true → aliasNum aliases a ≠ st.base.nextVreg)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (nx ny : Nat) (ρ' : Nat → CV),ty.width = rotateWidth wide ∧
      ctx.valueReg? x = some (.vreg nx .int) ∧ ctx.valueReg? y = some (.vreg ny .int) ∧
      out = .regsVec [[.vreg (rotateWideResult left st.base.nextVreg) .int]] ∧
      next = {rotateWideRequests left st x y with base := rotateWideBase left wide st.base (.vreg nx .int) (.vreg ny .int)} ∧
      PRun F isem ((rotateWideCode left (szOf ty.width) st.base.nextVreg nx ny).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,rotateWideBits left u amount.bits.toNat⟩ (ρ' (rotateWideResult left st.base.nextVreg)) ∧
      ∀ z,z < st.base.nextVreg ∨ st.base.nextVreg+rotateWideAlloc left ≤ z → ρ' z = ρ z := by
  obtain ⟨width,data,type⟩ := stock_rotate_source_data inv left source clif
  have enough := selected.fuelBound
  have roots : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+10 := ⟨selected.matchFuel-10,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  obtain ⟨initial,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs] at args
  have physical := wide_register_match_width source type args
  have supported : ty.width = 32 ∨ ty.width = 64 := by
    cases wide
    · exact .inl physical
    · exact .inr physical
  have narrow : ¬ (ty.width = 8 ∨ ty.width = 16) := by rcases supported with h | h <;> omega
  have rootEq : rotateRule left false ty.width = rotateWideRule left wide := by
    simp only [rotateRule,narrow,ite_false,ite_false]
    cases wide <;> simp [physical,rotateWidth]
  have expected := stock_rotate_register_match data_program ctx left width source type data st #[] m
  rw [rootEq] at expected
  rw [expected] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,middleEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [chosen,← envEq,← middleEq,← traceEq] at rhs
  have envEq' : rotateEnv left ty.width x y = rotateWideEnv left x y := by simp [rotateEnv,narrow]
  rw [envEq'] at rhs
  change (evalExpr program (Stock.sem ctx) {} (999939+60) (rotateWideRule left wide).rhs
    (rotateWideEnv left x y)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
  obtain ⟨safeX,safeY,⟨rx,mapX⟩,ry,mapY⟩ := stock_rotate_wide_register_requests data_program ctx left wide rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapX
  obtain ⟨ny,rfl⟩ := inv.valueReg y ry mapY
  obtain ⟨trace,forward⟩ := stock_rotate_wide_rhs data_program ctx left wide mapX mapY st safeX safeY #[] 999939
  rw [forward] at rhs
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at rhs
  obtain ⟨outEq,nextEq,_⟩ := rhs
  have needed := requests_demanded left st x y (extent x _ mapX) (extent y _ mapY)
  have neededX : Demanded next x := by rw [← nextEq]; exact needed.1
  have neededY : Demanded next y := by rw [← nextEq]; exact needed.2
  have input := held.read neededX (getAs_ok getX) mapX
  have count := held.read neededY getY mapY
  obtain ⟨ρ',execution,result,kept⟩ := wide_register_value refines left supported bounded (protectedX nx mapX) input count
  exact ⟨nx,ny,ρ',physical,mapX,mapY,outEq.symm,nextEq.symm,execution,result,kept⟩
end Backend.Stock.Proof.ScalarRotate

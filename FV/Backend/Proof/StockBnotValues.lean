import FV.Backend.Proof.StockBnotSemantics
import FV.Backend.Proof.StockBnotMatch
import FV.Backend.Proof.StockSelectionReceipts

namespace Backend.Stock.Proof.Bnot
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem rhs_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (shifted : Bool) {ty : Clif.Ty} (width : ty.width ≤ 64)
    {fr : Clif.Frame} {x : Nat} {u : BitVec ty.width} (source : fr.getAs x ty = .ok u)
    {st next : State} {out : V} {trace : Array RuleId} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r, ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k)))
    {k : Int} {sh : ShiftOpAndAmt} (valid : shifted = true → sh.op = .lsl ∧ sh.amt < ty.width)
    (rhs : (evalExpr program (Stock.sem ctx) {} 999999 (rule shifted).rhs (env shifted ty.width x k sh)).run
      (st,#[]) = .ok (some out,next,trace)) :
    ∃ (mi : MInst) (ρ' : Nat → CV), out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next.base = (st.base.fresh .int).2.emit mi ∧
      PRun F isem [mi.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bnot (if shifted then u <<< sh.amt else u)⟩ (ρ' st.base.nextVreg) ∧
      ∀ n, n ≠ st.base.nextVreg → ρ' n = ρ n := by
  obtain ⟨safe,r,mapped,outputEq,stateEq⟩ := stock_bnot_rhs_observed data_program ctx shifted width
    (n := 999959) (k := k) (sh := sh) rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg x r mapped
  have needed : Demanded next x := by
    rw [stateEq]
    change (st.mark x).demand[x]! ≠ 0
    rw [(mark_demand st x (extent x _ mapped)).1]
    omega
  have operand : ValuesHeld (fun z => z = x) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    apply held.mono
    intro z equal
    subst z
    exact needed
  have baseEq := congrArg State.base stateEq
  cases shifted
  · obtain ⟨ρ',execution,value,kept⟩ := stock_bnot_base_resolved refines width bounded mapped operand source
    exact ⟨code false ty.width (.vreg st.base.nextVreg .int) (.vreg nx .int) sh,ρ',outputEq,baseEq,execution,value,kept⟩
  · obtain ⟨lsl,amount⟩ := valid rfl
    obtain ⟨ρ',execution,value,kept⟩ := stock_bnot_shift_resolved refines width bounded mapped operand source lsl amount
    exact ⟨code true ty.width (.vreg st.base.nextVreg .int) (.vreg nx .int) sh,ρ',outputEq,baseEq,execution,value,kept⟩

/-- Actual root selection and original source facts establish the original NOT
value for base and fused LSL forms, with fresh-only machine write preservation. -/
theorem stock_bnot_selected_root_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {i y : Nat} {ty : Clif.Ty} {info : IInfo}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .bnot ty y))
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u : BitVec ty.width} (get : fr.getAs y ty = .ok u)
    {st next : State} {out : V} {trace : List RuleId} (selected : LowerSelection ctx i st out next trace)
    (shifted : Bool) (chosen : selected.rule = rule shifted)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r, ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (mi : MInst) (ρ' : Nat → CV), out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next.base = (st.base.fresh .int).2.emit mi ∧
      PRun F isem [mi.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bnot u⟩ (ρ' st.base.nextVreg) ∧
      ∀ n, n ≠ st.base.nextVreg → ρ' n = ρ n := by
  obtain ⟨width,data,type⟩ := stock_bnot_data inv source clif
  have fuelBound := selected.fuelBound
  have count : (program.rulesOf T.lower.id).length ≤ 999987 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
  have enough : 10 ≤ selected.matchFuel := by omega
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+10 := ⟨selected.matchFuel-10,by omega⟩
  have matched := selected.matchedRun
  have rhs := selected.rhsRun
  rw [chosen,fuelEq] at matched
  rw [chosen] at rhs
  cases shifted
  · change (matchRule program (Stock.sem ctx) {} (m+10) rule_lower_1377 [.inst i]).run (st,#[]) = _ at matched
    rw [stock_bnot_base_match data_program ctx source type width data st #[] (m+8)] at matched
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
    obtain ⟨envEq,stateEq,traceEq⟩ := matched
    rw [← envEq,← stateEq,← traceEq] at rhs
    exact rhs_values inv refines false width get bounded extent held (k := 0) (sh := ⟨.lsl,0⟩)
      (by intro impossible; cases impossible) rhs
  · change (matchRule program (Stock.sem ctx) {} (m+10) rule_lower_1401 [.inst i]).run (st,#[]) = _ at matched
    obtain ⟨z,k,sh,previous,envEq,stateEq,sourceZ,lsl,amount,value⟩ := stock_bnot_shift_match_receipts
      data_program inv dfg width source type data get matched
    rw [envEq,stateEq] at rhs
    rw [value]
    exact rhs_values inv refines true width sourceZ bounded extent held (k := k) (sh := sh)
      (fun _ => ⟨lsl,amount⟩) rhs

end Backend.Stock.Proof.Bnot

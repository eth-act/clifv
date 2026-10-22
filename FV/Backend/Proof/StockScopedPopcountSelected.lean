import FV.Backend.Proof.StockScopedPopcountSemantics
import FV.Backend.Proof.StockPopcountMatch
namespace Backend.Stock.Proof.Popcount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
attribute [local irreducible] Isle.Aarch64.program

/-- Actual original source selection supplies request safety, retained output,
resolved execution and fresh-write preservation, without a chosen-root premise. -/
theorem selected_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .popcnt ty x))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {u : BitVec ty.width} (get : fr.getAs x ty = .ok u)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (nx : Nat) (ρ' : Nat → CV),ctx.valueReg? x = some (.vreg nx .int) ∧
      out = .regsVec [[.vreg (popcountResult ty.width st.base.nextVreg) .int]] ∧
      next = {st.mark x with base := popcountBase ty.width st.base (.vreg nx .int)} ∧
      PRun F isem ((popcountCode ty.width st.base.nextVreg nx).map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .popcnt u⟩ (ρ' (popcountResult ty.width st.base.nextVreg)) ∧
      ∀ n,n < st.base.nextVreg ∨ st.base.nextVreg+popcountAlloc ty.width ≤ n → ρ' n = ρ n := by
  obtain ⟨width,data,type⟩ := source_data inv source clif
  have chosen := selected_rule inv source clif selected
  have enough := selected.fuelBound
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+2 := ⟨selected.matchFuel-2,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq,popcount_match data_program ctx width source type data st #[] m] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,stateEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [chosen,← envEq,← stateEq,← traceEq] at rhs
  change (evalExpr program (Stock.sem ctx) {} (999799+200) (popcountRule ty.width).rhs
    (popcountEnv ty.width x)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
  obtain ⟨rx,safe,mapped,output,nextEq⟩ := rhs_observed data_program ctx width rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapped
  have inputHeld : ValuesHeld (fun z => z = x) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    apply held.mono
    intro z same; subst z
    rw [nextEq,Demanded]
    change (st.mark x).demand[x]! ≠ 0
    rw [(mark_demand st x (extent x _ mapped)).1]
    omega
  have input := inputHeld.read rfl (getAs_ok get) mapped
  obtain ⟨ρ',execution,value,kept⟩ := resolved refines width bounded input
  exact ⟨nx,ρ',mapped,output,nextEq,execution,value,kept⟩
end Backend.Stock.Proof.Popcount

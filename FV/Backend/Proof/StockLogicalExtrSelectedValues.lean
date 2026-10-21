import FV.Backend.Proof.StockLogicalExtrMatchedValues
import FV.Backend.Proof.StockSelectionReceipts

namespace Backend.Stock.Proof.LogicalExtr
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- The actual first-match lower call supplies EXTR's match environment, fuel
and RHS execution. Original operand values are obtained from source DFG; the
looked-through shifts need no separately materialized machine registers. -/
theorem selected_root_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (mirrored : Bool)
    {i x y : Nat} {ty : Clif.Ty} {info : IInfo}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary .bor ty x y))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u v : BitVec ty.width}
    (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.getAs y ty = .ok v)
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace)
    (chosen : selected.rule = extrRule mirrored)
    {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r, ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun z => ρ (aliasNum aliases z))) :
    ∃ (mi : MInst) (ρ' : Nat → CV),
      out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next.base = (st.base.fresh .int).2.emit mi ∧
      PRun F isem [mi.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size + 1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary .bor u v⟩ (ρ' st.base.nextVreg) ∧
      ∀ z, z ≠ st.base.nextVreg → ρ' z = ρ z := by
  have fuelBound := selected.fuelBound
  have count : (program.rulesOf T.lower.id).length ≤ 999977 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]
    decide +kernel
  have enough : 20 ≤ selected.matchFuel := by omega
  obtain ⟨m,fuelEq⟩ : ∃ m, selected.matchFuel = m + 20 :=
    ⟨selected.matchFuel - 20,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  have rhs := selected.rhsRun
  rw [chosen] at rhs
  exact matched_values data_program inv mirrored source clif refines dfg
    sourceX sourceY bounded extent held (n := 999939) matched rhs

end Backend.Stock.Proof.LogicalExtr

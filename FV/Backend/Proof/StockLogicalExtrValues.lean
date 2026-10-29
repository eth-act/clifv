module

public import FV.Backend.Proof.StockLogicalExtrSemantics
public import FV.Backend.Proof.StockLogicalExtrRhs
public import FV.Backend.Proof.StockValues

@[expose] public section

namespace Backend.Stock.Proof.LogicalExtr
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Actual RHS output, emitted instruction execution and source-word result,
with final aliases and the fresh-only write frame. -/
def ValueOut (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem) (ty : Clif.Ty)
    (u v : BitVec ty.width) (X Y : Nat) (st next : State) (out : V)
    (aliases : Array (Option Nat)) (ρ : Nat → CV) : Prop :=
  ∃ (mi : MInst) (ρ' : Nat → CV),
    out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
    next.base = (st.base.fresh .int).2.emit mi ∧
    PRun F isem [mi.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
    VHolds ⟨ty,(u <<< X) ||| (v >>> Y)⟩ (ρ' st.base.nextVreg) ∧
    ∀ z,z ≠ st.base.nextVreg → ρ' z = ρ z

private theorem marked (st : State) (x : Nat) (bound : x < st.demand.size) : Demanded (st.mark x) x := by
  rw [Demanded,(mark_demand st x bound).1]
  omega
private theorem twice_marked (st : State) (x y : Nat) (bx : x < st.demand.size) (by_ : y < st.demand.size) :
    Demanded ((st.mark x).mark y) x ∧ Demanded ((st.mark x).mark y) y := by
  have afterBound : y < (st.mark x).demand.size := by rw [(mark_demand st x bx).2.2]; exact by_
  exact ⟨(demanded_mark_iff (st.mark x) y x afterBound).mpr (Or.inr (marked st x bx)),
    marked (st.mark x) y afterBound⟩

/-- A successful actual EXTR RHS internally derives its integer mappings and
operand demands from the original held-values relation, then executes the real
two-word instruction. No caller-supplied register/request certificate is used. -/
theorem rhs_values {p : Program} (hp : Data p) {ctx : Ctx} (mirrored : Bool)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {ty : Clif.Ty} (width : ty.width = 32 ∨ ty.width = 64)
    {X Y : Int} (sum : X.toNat+Y.toNat = ty.width) (count : Y.toNat < ty.width)
    {x y n : Nat} {u v : BitVec ty.width} {fr : Clif.Frame}
    (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.getAs y ty = .ok v)
    {st next : State} {out : V} {tr trace : Array RuleId}
    {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun z => ρ (aliasNum aliases z)))
    (run : (evalExpr p (Stock.sem ctx) {} (n+60) (extrRule mirrored).rhs
      (extrEnv mirrored ty.width x X y Y)).run (st,tr) = .ok (some out,next,trace)) :
    ValueOut F isem ty u v X.toNat Y.toNat st next out aliases ρ := by
  have fits : Y < 64 := by rcases width with h | h <;> omega
  obtain ⟨safeX,safeY,rx,ry,mappedX,mappedY,outEq,stateEq⟩ := rhs_observed hp ctx mirrored width fits run
  have needed : Demanded next x ∧ Demanded next y := by
    rw [stateEq]
    exact twice_marked st x y (extent x rx mappedX) (extent y ry mappedY)
  obtain ⟨nx,mx,heldX⟩ := held x needed.1 ⟨ty,u⟩ (getAs_ok sourceX)
  obtain ⟨ny,my,heldY⟩ := held y needed.2 ⟨ty,v⟩ (getAs_ok sourceY)
  have rxEq := Option.some.inj (mappedX.symm.trans mx)
  have ryEq := Option.some.inj (mappedY.symm.trans my)
  subst rx ry
  have amount : (shiftFor ty.width Y.toNat).amt = Y.toNat := by unfold shiftFor; split <;> rfl
  obtain ⟨ρ',execution,value,kept⟩ := extr_resolved refines width
    (sh := shiftFor ty.width Y.toNat) bounded (by simpa only [amount] using sum)
    (by simpa only [amount] using count) heldX heldY
  refine ⟨.aluRRRShift .extr (szOf ty.width) (.vreg st.base.nextVreg .int)
    (.vreg nx .int) (.vreg ny .int) (shiftFor ty.width Y.toNat),ρ',outEq,?_,execution,?_,kept⟩
  · exact congrArg State.base stateEq
  · simpa only [amount] using value

end Backend.Stock.Proof.LogicalExtr

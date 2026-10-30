import FV.Backend.Proof.StockDivDivisorValues
import FV.Backend.Proof.StockDivBodyValues
import FV.Backend.Proof.StockDivSelected
import FV.Backend.Proof.StockDemandMono
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
def SourceDivisionOut (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem) (op : Clif.DivOp)
    (ty : Clif.Ty) (u v : BitVec ty.width) (st next : State) (out : V)
    (aliases : Array (Option Nat)) (ρ : Nat → CV) : Prop :=
  ∃ ms d,out = .regsVec [[.vreg d .int]] ∧ Frag st.base next.base ms ∧
    (st.base.nextVreg ≤ d ∧ d < next.base.nextVreg) ∧
    ∀ world,(∀ c,Clif.Sem.div op u v = .error c → TrapRun isem (ms.map (·.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world c) ∧
      (∀ q,Clif.Sem.div op u v = .ok q → Runs F isem (ms.map (·.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
        VHolds ⟨ty,q⟩ (ρ' d) ∧ ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k))
/-- Actual selected64-bit unsigned division composes its original mapped dividend,
real divisor/zero guard and quotient execution. Original source errors and normal
results are both preserved; noncapture is an internal record-availability fact. -/
theorem stock_div_udiv_wide_selected_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {id x y : Nat} {info : IInfo} (source : ctx.insts[id]? = some info)
    (clif : info.clif = some (.div .udiv .i64 x y))
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx id st out next rules)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u v : BitVec 64}
    (getX : fr.getAs x .i64 = .ok u) (getY : fr.getAs y .i64 = .ok v)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (idem : ∀ k,aliasNum aliases (aliasNum aliases k) = aliasNum aliases k)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k)))
    (outside : ∀ z key,ctx.valueReg? z = some (.vreg key .int) → (fr.regs z).isSome = true →
      aliasNum aliases key < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases key) :
    SourceDivisionOut F isem .udiv .i64 u v st next out aliases ρ := by
  have observed := stock_div_udiv_selected inv source clif selected
  simp only [Clif.Ty.width,ite_true] at observed
  obtain ⟨safeX,rx,ry,middle,middleTrace,mapX,divisor,output,finish⟩ := observed
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapX
  have heldMiddle : ValuesHeld (Demanded middle) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    intro z needed value lookup
    apply held z ?_ value lookup
    simpa only [finish,quotientState,Demanded] using needed
  have neededX : Demanded middle x := by
    have counts := stock_apply_demand_mono divisor x
    have marked := (mark_demand st x (extent x _ mapX)).1
    unfold Demanded
    rw [marked] at counts
    omega
  have inputX : DivOpnd false u (ρ (aliasNum aliases nx)) :=
    divOpnd_of_vholds64 rfl (heldMiddle.read neededX (getAs_ok getX) mapX)
  have markExtent : ∀ z r,ctx.valueReg? z = some r → z < (st.mark x).demand.size := by
    simpa only [State.mark,Array.size_modify] using extent
  obtain ⟨msY,ny,regY,fragmentY,locationY,divisorRun⟩ := stock_div_divisor_values data_program inv refines dfg getY
    (n := 999991) (by decide) (by decide) (by decide) divisor bounded idem markExtent heldMiddle
  have sameY : ry = .vreg ny .int := V.reg.inj regY
  subst ry
  let d := middle.base.nextVreg
  let qinst : MInst := .aluRRR .uDiv .size64 (.vreg d .int) (.vreg nx .int) (.vreg ny .int)
  have fragmentQ : Frag middle.base next.base [qinst] := by
    refine ⟨?_,?_,?_⟩
    · rw [finish]; simp [quotientState,LState.fresh,LState.emit,qinst,d,szOf]
    · rw [finish]; simp [quotientState,LState.fresh,LState.emit,d]
    · intro m member key defined
      simp only [List.mem_singleton] at member
      subst m
      change key ∈ [d] at defined
      simp only [List.mem_singleton] at defined
      subst key
      rw [finish]; simp [quotientState,LState.fresh,LState.emit,d]
  have fragment : Frag st.base next.base (msY ++ [qinst]) := fragmentY.append fragmentQ
  have fresh : st.base.nextVreg ≤ d := fragmentY.mono
  have upper : d < next.base.nextVreg := by rw [finish]; simp [quotientState,LState.fresh,LState.emit,d]
  unfold SourceDivisionOut
  refine ⟨_,d,output,fragment,⟨fresh,upper⟩,?_⟩
  intro world
  simp only [List.map_append,List.map_cons,List.map_nil]
  refine ⟨?_,?_⟩
  · intro c failed
    obtain ⟨zero,rfl⟩ := udiv_trap failed
    exact ((divisorRun world).1 zero).append
  · intro q success
    obtain ⟨nonzero,_⟩ := udiv_ok success
    refine Runs.append ((divisorRun world).2 nonzero) (fun ρ1 nextWorld ⟨inputY,keptY⟩ => ?_)
    have originalX : ρ1 (aliasNum aliases nx) = ρ (aliasNum aliases nx) := by
      apply keptY
      have range := outside x nx mapX (by rw [getAs_ok getX]; rfl)
      have mono := fragmentQ.mono
      change aliasNum aliases nx < st.base.nextVreg ∨ middle.base.nextVreg ≤ aliasNum aliases nx
      omega
    have preparedX : DivOpnd false u (ρ1 (aliasNum aliases nx)) := by rw [originalX]; exact inputX
    obtain ⟨ρ2,execution,value,keptQ⟩ := stock_div_quotient_source_values refines false (ty := .i64) (by decide) success
      (aliases := aliases) (ρ := ρ1) (a := nx) (b := ny) (d := d) (by omega) preparedX inputY
    apply prun_runs execution nextWorld
    intro _
    refine ⟨value,fun k range => ?_⟩
    rw [keptQ k (by omega)]
    apply keptY
    change k < st.base.nextVreg ∨ middle.base.nextVreg ≤ k
    have mono := fragmentQ.mono
    omega
end Backend.Stock.Proof.ScalarDiv

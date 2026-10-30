import FV.Backend.Proof.StockDivValueTransfer
import FV.Backend.Proof.StockDivUdivWideValues
import FV.Backend.Proof.StockDivDividendValues
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
theorem stock_div_udiv_narrow_selected_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {id x y : Nat} {ty : Clif.Ty} (narrow : ty.width ≤ 32) {info : IInfo} (source : ctx.insts[id]? = some info)
    (clif : info.clif = some (.div .udiv ty x y))
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx id st out next rules)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (idem : ∀ k,aliasNum aliases (aliasNum aliases k) = aliasNum aliases k)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k)))
    (outside : ∀ z key,ctx.valueReg? z = some (.vreg key .int) → (fr.regs z).isSome = true →
      aliasNum aliases key < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases key) :
    SourceDivisionOut F isem .udiv ty u v st next out aliases ρ := by
  have observed := stock_div_udiv_selected inv source clif selected
  simp only [show ¬ty.width = 64 from by omega,ite_false] at observed
  obtain ⟨rx,ry,prepared,preparedTrace,middle,middleTrace,shape,dividend,divisor,output,finish⟩ := observed
  have heldMiddle : ValuesHeld (Demanded middle) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    intro z needed value lookup
    apply held z ?_ value lookup
    simpa only [finish,quotientState,Demanded] using needed
  have heldPrepared : ValuesHeld (Demanded prepared) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    intro z needed value lookup
    apply heldMiddle z ?_ value lookup
    have counts := stock_apply_demand_mono divisor z
    unfold Demanded at *
    omega
  obtain ⟨msX,nx,ρ0,regX,fragmentX,locationX,executionX,inputX,keptX⟩ :=
    stock_div_extended_dividend_values data_program inv refines false false
      (n := 999992) (by decide) dfg getX narrow bounded extent heldPrepared dividend
  have sameX : rx = .vreg nx .int := V.reg.inj regX
  subst rx
  have preparedExtent : ∀ z r,ctx.valueReg? z = some r → z < prepared.demand.size := by
    intro z r mapped
    have counts := stock_apply_demand_mono dividend z
    have initial := extent z r mapped
    have sizes := Extent.apply_demand_size dividend
    omega
  have nextMono : middle.base.nextVreg ≤ next.base.nextVreg := by
    rw [finish]; simp [quotientState,LState.fresh,LState.emit]
  have middleMono := stock_apply_allocationLe divisor
  have heldAfterX : ValuesHeld (Demanded middle) ctx fr (fun k => ρ0 (aliasNum aliases k)) :=
    stock_div_held_interval_transfer (first := st.base.nextVreg) (last := prepared.base.nextVreg)
      heldMiddle ⟨Nat.le_refl _,Nat.le_trans middleMono.1 nextMono⟩
      (fun z key _ mapped present => outside z key mapped present) keptX
  have boundedPrepared : aliases.size ≤ prepared.base.nextVreg := Nat.le_trans bounded fragmentX.mono
  have widths := (stock_div_source_data inv .udiv source clif).1
  obtain ⟨msY,ny,regY,fragmentY,locationY,divisorRun⟩ := stock_div_divisor_values data_program inv refines dfg getY
    (n := 999991) (by decide) widths (by decide) divisor boundedPrepared idem preparedExtent heldAfterX
  have sameY : ry = .vreg ny .int := V.reg.inj regY
  subst ry
  let d := middle.base.nextVreg
  let qinst : MInst := .aluRRR .uDiv .size32 (.vreg d .int) (.vreg nx .int) (.vreg ny .int)
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
  have fragment : Frag st.base next.base (msX ++ (msY ++ [qinst])) :=
    fragmentX.append (fragmentY.append fragmentQ)
  have fresh : st.base.nextVreg ≤ d := Nat.le_trans fragmentX.mono fragmentY.mono
  have upper : d < next.base.nextVreg := by rw [finish]; simp [quotientState,LState.fresh,LState.emit,d]
  have sourceXOutside : aliasNum aliases nx < prepared.base.nextVreg ∨ middle.base.nextVreg ≤ aliasNum aliases nx := by
    rcases locationX with mapped | allocated
    · have range := outside x nx mapped (by rw [getAs_ok getX]; rfl)
      have lowerMono := fragmentX.mono
      omega
    · have fixed : aliasNum aliases nx = nx := by
        apply chaseF_none
        rw [Array.getElem?_eq_none (by omega)]
        rfl
      rw [fixed]
      exact Or.inl allocated.2
  unfold SourceDivisionOut
  refine ⟨_,d,output,fragment,⟨fresh,upper⟩,?_⟩
  intro world
  simp only [List.map_append,List.map_cons,List.map_nil]
  have preparation := prun_runs executionX world (P := fun ρ' _ => ρ' = ρ0) (fun _ => rfl)
  refine ⟨?_,?_⟩
  · intro c failed
    obtain ⟨zero,rfl⟩ := udiv_trap failed
    exact TrapRun.prefix preparation (fun ρ' nextWorld equal => by
      subst ρ'
      exact ((divisorRun nextWorld).1 zero).append)
  · intro q success
    obtain ⟨nonzero,_⟩ := udiv_ok success
    refine Runs.append preparation (fun ρ' nextWorld equal => ?_)
    subst ρ'
    refine Runs.append ((divisorRun nextWorld).2 nonzero) (fun ρ1 quotientWorld ⟨inputY,keptY⟩ => ?_)
    have preparedX : DivOpnd false u (ρ1 (aliasNum aliases nx)) := by
      rw [keptY _ sourceXOutside]; exact inputX
    obtain ⟨ρ2,execution,value,keptQ⟩ := stock_div_quotient_source_values refines false (ty := ty)
      widths success (aliases := aliases) (ρ := ρ1) (a := nx) (b := ny) (d := d)
      (by omega) preparedX inputY
    have size : szOf ty.width = .size32 := by simp [szOf,narrow]
    rw [size] at execution
    apply prun_runs execution quotientWorld
    intro _
    refine ⟨value,fun k range => ?_⟩
    have firstMono := fragmentX.mono
    have secondMono := fragmentY.mono
    rw [keptQ k (by omega)]
    rw [keptY k (by omega)]
    apply keptX
    have mono := fragmentY.mono
    omega
end Backend.Stock.Proof.ScalarDiv

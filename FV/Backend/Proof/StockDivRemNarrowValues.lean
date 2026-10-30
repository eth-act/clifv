import FV.Backend.Proof.StockDivValueTransfer
import FV.Backend.Proof.StockDivUdivWideValues
import FV.Backend.Proof.StockDivDividendValues
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
theorem stock_div_rem_narrow_selected_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (signed : Bool)
    {id x y : Nat} {ty : Clif.Ty} (narrow : ty.width ≤ 32) {info : IInfo} (source : ctx.insts[id]? = some info)
    (clif : info.clif = some (.div (if signed then .srem else .urem) ty x y))
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
    SourceDivisionOut F isem (if signed then .srem else .urem) ty u v st next out aliases ρ := by
  have observed := stock_div_rem_selected inv signed source clif selected
  simp only [show ¬ty.width = 64 from by omega,ite_false] at observed
  obtain ⟨rx,ry,prepared,preparedTrace,middle,middleTrace,shape,dividend,divisor,output,finish⟩ := observed
  have heldMiddle : ValuesHeld (Demanded middle) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    intro z needed value lookup
    apply held z ?_ value lookup
    simpa only [finish,remainderState,quotientState,Demanded] using needed
  have heldPrepared : ValuesHeld (Demanded prepared) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    intro z needed value lookup
    apply heldMiddle z ?_ value lookup
    have counts := stock_apply_demand_mono divisor z
    unfold Demanded at *
    omega
  obtain ⟨msX,nx,ρ0,regX,fragmentX,locationX,executionX,inputX,keptX⟩ :=
    stock_div_extended_dividend_values data_program inv refines signed false
      (n := 999995) (by decide) dfg getX narrow bounded extent heldPrepared dividend
  have sameX : rx = .vreg nx .int := V.reg.inj regX
  subst rx
  have preparedExtent : ∀ z r,ctx.valueReg? z = some r → z < prepared.demand.size := by
    intro z r mapped
    have counts := stock_apply_demand_mono dividend z
    have initial := extent z r mapped
    have sizes := Extent.apply_demand_size dividend
    omega
  have nextMono : middle.base.nextVreg ≤ next.base.nextVreg := by
    rw [finish]; simp [remainderState,quotientState,LState.fresh,LState.emit] <;> omega
  have middleMono := stock_apply_allocationLe divisor
  have heldAfterX : ValuesHeld (Demanded middle) ctx fr (fun k => ρ0 (aliasNum aliases k)) :=
    stock_div_held_interval_transfer (first := st.base.nextVreg) (last := prepared.base.nextVreg)
      heldMiddle ⟨Nat.le_refl _,Nat.le_trans middleMono.1 nextMono⟩
      (fun z key _ mapped present => outside z key mapped present) keptX
  have boundedPrepared : aliases.size ≤ prepared.base.nextVreg := Nat.le_trans bounded fragmentX.mono
  have widths := (stock_div_source_data inv (if signed then .srem else .urem) source clif).1
  obtain ⟨msY,ny,regY,fragmentY,locationY,divisorRun⟩ := stock_div_divisor_values data_program inv refines dfg getY
    (n := 999994) (by decide) widths (by cases signed <;> decide) divisor boundedPrepared idem preparedExtent heldAfterX
  have sameY : ry = .vreg ny .int := V.reg.inj regY
  subst ry
  let d := middle.base.nextVreg
  let quotient : MInst := .aluRRR (if signed then .sDiv else .uDiv) (szOf ty.width)
    (.vreg d .int) (.vreg nx .int) (.vreg ny .int)
  let multiply : MInst := .aluRRRR .mSub (szOf ty.width)
    (.vreg (d+1) .int) (.vreg d .int) (.vreg ny .int) (.vreg nx .int)
  have fragmentQ : Frag middle.base next.base [quotient,multiply] := by
    refine ⟨?_,?_,?_⟩
    · rw [finish]
      simp [remainderState,quotientState,LState.fresh,LState.emit,quotient,multiply,d ]
      rw [Array.push_eq_append,Array.push_eq_append,Array.append_assoc]
      rfl
    · rw [finish]; simp [remainderState,quotientState,LState.fresh,LState.emit,d] <;> omega
    · intro m member key defined
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · change key ∈ [d] at defined
        simp only [List.mem_singleton] at defined
        subst key
        rw [finish]; simp [remainderState,quotientState,LState.fresh,LState.emit,d] <;> omega
      · change key ∈ [d+1] at defined
        simp only [List.mem_singleton] at defined
        subst key
        rw [finish]; simp [remainderState,quotientState,LState.fresh,LState.emit,d] <;> omega
  have fragment : Frag st.base next.base (msX ++ (msY ++ [quotient,multiply])) :=
    fragmentX.append (fragmentY.append fragmentQ)
  have fresh : st.base.nextVreg ≤ d+1 := by
    have first := fragmentX.mono
    have second := fragmentY.mono
    omega
  have upper : d+1 < next.base.nextVreg := by
    rw [finish]; simp [remainderState,quotientState,LState.fresh,LState.emit,d] <;> omega
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
  refine ⟨_,d+1,output,fragment,⟨fresh,upper⟩,?_⟩
  intro world
  simp only [List.map_append,List.map_cons,List.map_nil]
  have preparation := prun_runs executionX world (P := fun ρ' _ => ρ' = ρ0) (fun _ => rfl)
  refine ⟨?_,?_⟩
  · intro c failed
    have trapped : v = 0#ty.width ∧ c = .intDivz := by
      cases signed
      · exact urem_trap failed
      · exact srem_trap failed
    obtain ⟨zero,rfl⟩ := trapped
    exact TrapRun.prefix preparation (fun ρ' nextWorld equal => by
      subst ρ'
      exact ((divisorRun nextWorld).1 zero).append)
  · intro q success
    have nonzero : v ≠ 0#ty.width := by
      cases signed
      · exact (urem_ok success).1
      · exact (srem_ok success).1
    refine Runs.append preparation (fun ρ' nextWorld equal => ?_)
    subst ρ'
    refine Runs.append ((divisorRun nextWorld).2 nonzero) (fun ρ1 quotientWorld ⟨inputY,keptY⟩ => ?_)
    have preparedX : DivOpnd signed u (ρ1 (aliasNum aliases nx)) := by
      rw [keptY _ sourceXOutside]; exact inputX
    have aliasFresh (key : Nat) (lower : st.base.nextVreg ≤ key) : aliasNum aliases key = key := by
      apply chaseF_none
      rw [Array.getElem?_eq_none (by omega)]
      rfl
    have outsideX : aliasNum aliases nx ≠ d := by
      rcases locationX with mapped | allocated
      · have interval := outside x nx mapped (by rw [getAs_ok getX]; rfl)
        have lower := fragmentX.mono
        have middleCount := fragmentY.mono
        have high : next.base.nextVreg = d+2 := by rw [finish]; rfl
        omega
      · rw [aliasFresh nx allocated.1]
        have middleCount := fragmentY.mono
        omega
    have outsideY : aliasNum aliases ny ≠ d := by
      rcases locationY with mapped | allocated
      · have interval := outside y ny mapped (by rw [getAs_ok getY]; rfl)
        have lower := fragmentX.mono
        have middleCount := fragmentY.mono
        have high : next.base.nextVreg = d+2 := by rw [finish]; rfl
        omega
      · rw [aliasFresh ny (Nat.le_trans fragmentX.mono allocated.1)]
        exact Nat.ne_of_lt allocated.2
    obtain ⟨ρ2,execution,value,keptQ⟩ := stock_div_remainder_source_values refines signed (ty := ty)
      widths success (aliases := aliases) (ρ := ρ1) (a := nx) (b := ny) (d := d)
      (by have first := fragmentX.mono; have second := fragmentY.mono <;> omega) outsideX outsideY preparedX (by cases signed <;> simpa using inputY)
    apply prun_runs execution quotientWorld
    intro _
    refine ⟨value,fun k range => ?_⟩
    have firstMono := fragmentX.mono
    have secondMono := fragmentY.mono
    have count : next.base.nextVreg = d+2 := by rw [finish]; rfl
    rw [keptQ k (by omega)]
    rw [keptY k (by omega)]
    apply keptX
    have mono := fragmentY.mono
    omega
end Backend.Stock.Proof.ScalarDiv

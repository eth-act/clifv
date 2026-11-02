import FV.Backend.Proof.StockDivDividendValues
import FV.Backend.Proof.StockDivValueTransfer
import FV.Backend.Proof.StockDivUdivWideValues
import FV.Backend.Proof.StockDivSourceOverflow
import FV.Backend.Proof.StockDivMinimumResolved
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem fragment_unique {st next : LState} {ms ms' : List MInst}
    (a : Frag st next ms) (b : Frag st next ms') : ms = ms' := by
  have same := congrArg Array.toList (a.emitted.symm.trans b.emitted)
  simp only [Array.toList_append,List.toList_toArray] at same
  exact List.append_cancel_left same
theorem stock_div_general_sdiv_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (wide : Bool)
    {id x y : Nat} {ty : Clif.Ty} (relation : if wide then ty.width = 64 else ty.width ≤ 32) {info : IInfo} (source : ctx.insts[id]? = some info)
    (clif : info.clif = some (.div .sdiv ty x y))
    {st next : State} {out : V} (general : GeneralSdivReceipt program ctx wide 999899 x y ty.width st next #[] out)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (idem : ∀ k,aliasNum aliases (aliasNum aliases k) = aliasNum aliases k)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k)))
    (outside : ∀ z key,ctx.valueReg? z = some (.vreg key .int) → (fr.regs z).isSome = true →
      aliasNum aliases key < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases key) :
    SourceDivisionOut F isem .sdiv ty u v st next out aliases ρ := by
  obtain ⟨rx,ry,check,s1,s2,s3,s4,t1,t2,t3,t4,shape,dividend,divisor,minimum,overflow,output,finish⟩ := general
  have widths := (stock_div_source_data inv .sdiv source clif).1
  have minimumForm := stock_div_intmin_observed data_program ctx rfl (n := 999993) (by decide) widths minimum
  have overflowForm := stock_div_overflow_observed data_program ctx rfl (n := 999992) (by decide) widths overflow
  have sameDemand : next.demand = s2.demand := by
    rw [finish,overflowForm.2,minimumForm.2]
    unfold quotientState
    dsimp only
    split <;> rfl
  have heldS2 : ValuesHeld (Demanded s2) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    intro z needed value lookup
    apply held z ?_ value lookup
    simpa only [Demanded,sameDemand] using needed
  have heldS1 : ValuesHeld (Demanded s1) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    intro z needed value lookup
    apply heldS2 z ?_ value lookup
    have counts := stock_apply_demand_mono divisor z
    unfold Demanded at *
    omega
  obtain ⟨msX,nx,ρ0,regX,fragmentX,locationX,executionX,inputX,keptX⟩ :=
    stock_div_extended_dividend_values data_program inv refines true wide (n := 999995) (by decide)
      dfg getX relation bounded extent heldS1 (by simpa only [ApplyInternal,ScalarShift.extTerm,ite_true] using dividend)
  have sameX : rx = .vreg nx .int := V.reg.inj regX
  subst rx
  have extentS1 : ∀ z r,ctx.valueReg? z = some r → z < s1.demand.size := by
    intro z r mapped
    rw [Extent.apply_demand_size dividend]
    exact extent z r mapped
  have frontier2 := (stock_apply_allocationLe divisor).1
  have frontier3 := (stock_apply_allocationLe minimum).1
  have frontier4 := (stock_apply_allocationLe overflow).1
  have frontier5 : s4.base.nextVreg ≤ next.base.nextVreg := by rw [finish]; simp [quotientState,LState.fresh,LState.emit]
  have frontier1 := fragmentX.mono
  have heldAfterX : ValuesHeld (Demanded s2) ctx fr (fun k => ρ0 (aliasNum aliases k)) :=
    stock_div_held_interval_transfer (first := st.base.nextVreg) (last := s1.base.nextVreg) heldS2
      ⟨Nat.le_refl _,by omega⟩ (fun z key _ mapped present => outside z key mapped present) keptX
  obtain ⟨msY,ny,regY,fragmentY,locationY,divisorRun⟩ := stock_div_divisor_values data_program inv refines
    dfg getY (n := 999994) (by decide) widths (by decide) divisor (by omega) idem extentS1 heldAfterX
  have sameY : ry = .vreg ny .int := V.reg.inj regY
  subst ry
  obtain ⟨msC,nc,_,regC,fragmentC,locationC,_,_,_⟩ := stock_div_minimum_source_values data_program ctx refines
    widths (n := ty.width) (fuel := 999993) (by decide) minimum (by omega) inputX
  have sameC : check = .vreg nc .int := V.reg.inj regC
  subst check
  let sz := szOf ty.width
  let i1 : MInst := .aluRRImm12 .addS sz .xzr (.vreg ny .int) ⟨1,false⟩
  let i2 : MInst := .ccmpImm sz (.vreg nc .int) 1 ⟨false,false,false,false⟩ .eq
  let i3 : MInst := .trapIf (.cond .vs) .intOvf
  have fragmentO : Frag s3.base s4.base (ovfCheck sz nc ny) := by
    rw [overflowForm.2]
    exact (Frag.emit_nodef s3.base (show vdefs i1 = [] from rfl)).append
      ((Frag.emit_nodef (s3.base.emit i1) (show vdefs i2 = [] from rfl)).append
        (Frag.emit_nodef ((s3.base.emit i1).emit i2) (show vdefs i3 = [] from rfl)))
  let d := s4.base.nextVreg
  let quotient : MInst := .aluRRR .sDiv sz (.vreg d .int) (.vreg nx .int) (.vreg ny .int)
  have fragmentQ : Frag s4.base next.base [quotient] := by
    refine ⟨?_,?_,?_⟩
    · rw [finish]; simp [quotientState,LState.fresh,LState.emit,quotient,d,sz]
    · exact frontier5
    · intro m member key defined
      have same := List.mem_singleton.mp member
      subst m
      change key ∈ [d] at defined
      have same := List.mem_singleton.mp defined
      subst key
      rw [finish]; simp [quotientState,LState.fresh,LState.emit,d]
  have fragment := fragmentX.append (fragmentY.append (fragmentC.append (fragmentO.append fragmentQ)))
  have fresh : st.base.nextVreg ≤ d := by omega
  have upper : d < next.base.nextVreg := by rw [finish]; simp [quotientState,LState.fresh,LState.emit,d]
  have aliasFresh (key : Nat) (lower : st.base.nextVreg ≤ key) : aliasNum aliases key = key := by
    apply chaseF_none
    rw [Array.getElem?_eq_none (by omega)]
    rfl
  have outsideX2 : aliasNum aliases nx < s1.base.nextVreg ∨ s2.base.nextVreg ≤ aliasNum aliases nx := by
    rcases locationX with mapped | allocated
    · have range := outside x nx mapped (by rw [getAs_ok getX]; rfl)
      omega
    · rw [aliasFresh nx allocated.1]
      exact Or.inl allocated.2
  have outsideX3 : aliasNum aliases nx < s2.base.nextVreg ∨ s3.base.nextVreg ≤ aliasNum aliases nx := by
    rcases locationX with mapped | allocated
    · have range := outside x nx mapped (by rw [getAs_ok getX]; rfl)
      omega
    · rw [aliasFresh nx allocated.1]
      omega
  have outsideY3 : aliasNum aliases ny < s2.base.nextVreg ∨ s3.base.nextVreg ≤ aliasNum aliases ny := by
    rcases locationY with mapped | allocated
    · have range := outside y ny mapped (by rw [getAs_ok getY]; rfl)
      omega
    · rw [aliasFresh ny (by omega)]
      exact Or.inl allocated.2
  have afterDivisor {ρ1 : Nat → CV} (keptY : ∀ k,k < s1.base.nextVreg ∨ s2.base.nextVreg ≤ k → ρ1 k = ρ0 k) :
      DivOpnd true u (ρ1 (aliasNum aliases nx)) := by rw [keptY _ outsideX2]; exact inputX
  have minExecution (ρ1 : Nat → CV) (preparedX : DivOpnd true u (ρ1 (aliasNum aliases nx))) :
      ∃ ρ2,PRun F isem (msC.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ1 ρ2 ∧
        (opnd sz (ρ2 (aliasNum aliases nc)) = BitVec.intMin sz.bits ↔ u = BitVec.intMin ty.width) ∧
        ∀ k,k < s2.base.nextVreg ∨ s3.base.nextVreg ≤ k → ρ2 k = ρ1 k := by
    obtain ⟨ms',nc',ρ2,reg,frag,loc,exec,reflected,kept⟩ := stock_div_minimum_source_values data_program ctx refines
      widths (fuel := 999993) (by decide) minimum (by omega) preparedX
    have checkEq := V.reg.inj (regC.symm.trans reg)
    have keyEq := (Reg.vreg.inj checkEq).1
    subst nc'
    have msEq := fragment_unique frag fragmentC
    subst ms'
    exact ⟨ρ2,exec,reflected,kept⟩
  unfold SourceDivisionOut
  refine ⟨_,d,output,fragment,⟨fresh,upper⟩,?_⟩
  intro world
  simp only [List.map_append,List.map_cons,List.map_nil]
  have preparation := prun_runs executionX world (P := fun ρ' _ => ρ' = ρ0) (fun _ => rfl)
  refine ⟨?_,?_⟩
  · intro c failed
    rcases sdiv_trap failed with ⟨zero,rfl⟩ | ⟨nonzero,minimumSource,minusOne,rfl⟩
    · exact TrapRun.prefix preparation (fun ρ' wd equal => by subst ρ'; exact ((divisorRun wd).1 zero).append)
    · refine TrapRun.prefix preparation (fun ρ' wd equal => ?_)
      subst ρ'
      refine TrapRun.prefix ((divisorRun wd).2 nonzero) (fun ρ1 wd1 ⟨inputY,keptY⟩ => ?_)
      obtain ⟨ρ2,exec,reflected,keptC⟩ := minExecution ρ1 (afterDivisor keptY)
      have divisor2 : DivOpnd true v (ρ2 (aliasNum aliases ny)) := by rw [keptC _ outsideY3]; exact inputY
      refine TrapRun.prefix (prun_runs exec wd1 (P := fun ρ' _ => ρ' = ρ2) (fun _ => rfl)) (fun ρ' wd2 equal => ?_)
      subst ρ'
      exact ((stock_div_overflow_source_resolved refines widths divisor2 reflected wd2).1 ⟨minimumSource,minusOne⟩).append
  · intro q success
    obtain ⟨nonzero,noOverflow,_⟩ := sdiv_ok success
    refine Runs.append preparation (fun ρ' wd equal => ?_)
    subst ρ'
    refine Runs.append ((divisorRun wd).2 nonzero) (fun ρ1 wd1 ⟨inputY,keptY⟩ => ?_)
    have preparedX := afterDivisor keptY
    obtain ⟨ρ2,exec,reflected,keptC⟩ := minExecution ρ1 preparedX
    have divisor2 : DivOpnd true v (ρ2 (aliasNum aliases ny)) := by rw [keptC _ outsideY3]; exact inputY
    have dividend2 : DivOpnd true u (ρ2 (aliasNum aliases nx)) := by rw [keptC _ outsideX3]; exact preparedX
    refine Runs.append (prun_runs exec wd1 (P := fun ρ' _ => ρ' = ρ2) (fun _ => rfl)) (fun ρ' wd2 equal => ?_)
    subst ρ'
    refine Runs.append ((stock_div_overflow_source_resolved refines widths divisor2 reflected wd2).2 noOverflow) (fun ρ' wd3 equal => ?_)
    subst ρ'
    obtain ⟨ρ3,quotientRun,value,keptQ⟩ := stock_div_quotient_source_values refines true (ty := ty) widths success
      (aliases := aliases) (ρ := ρ2) (a := nx) (b := ny) (d := d) (by omega) dividend2 divisor2
    apply prun_runs quotientRun wd3
    intro _
    refine ⟨value,fun k range => ?_⟩
    rw [keptQ k (by omega),keptC k (by omega),keptY k (by omega)]
    exact keptX k (by omega)
end Backend.Stock.Proof.ScalarDiv

import FV.Backend.Proof.StockSelectComparisonCompanionValues
import FV.Backend.Proof.StockSelectConditionReplacement
import FV.Backend.Proof.StockSelectConditionObserved
import FV.Backend.Proof.StockSelectCompanionFragment
import FV.Backend.Proof.StockDemandMono
import FV.Backend.Proof.StockDemandExtent
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
private theorem flag_unique {z : OperandSize → Nat → MInst} {raw : V} {a b : MInst} {ca cb : Cond}
    (left : CondFlag z raw a ca) (right : CondFlag z raw b cb) : a = b ∧ ca = cb := by
  rcases left with ⟨k,i,sz,rfl,hi,rfl,rfl⟩ | ⟨k,i,sz,rfl,hi,rfl,rfl⟩ | ⟨mi,rfl,hm⟩
  all_goals rcases right with ⟨k',i',sz',e,hi',rfl,rfl⟩ | ⟨k',i',sz',e,hi',rfl,rfl⟩ | ⟨mi',e,hm'⟩
  all_goals simp at e
  · obtain ⟨rfl,rfl⟩ := e
    rw [hi] at hi'; cases hi'
    exact ⟨rfl,rfl⟩
  · obtain ⟨rfl,rfl⟩ := e
    rw [hi] at hi'; cases hi'
    exact ⟨rfl,rfl⟩
  · obtain ⟨rfl,condition⟩ := e
    rw [hm] at hm'; cases hm'
    exact ⟨rfl,cond_idx_inj condition⟩
/-- The actual scalar comparison/select pair computes the original chosen
source value, including zero/inverted-zero and arbitrary comparison prefixes.
All source separation obligations are internal retained-availability obligations. -/
theorem stock_select_comparison_actual_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cty ty : Clif.Ty}
    (comparisonWidth : cty.width = 8 ∨ cty.width = 16 ∨ cty.width = 32 ∨ cty.width = 64)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (cc : Clif.IntCC) {fr : Clif.Frame} (dfg : DFGCons ctx fr) {a b x y : Nat}
    {av bv : BitVec cty.width} {u v : BitVec ty.width}
    (getA : fr.getAs a cty = .ok av) (getB : fr.getAs b cty = .ok bv)
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (typeA : ctx.valueType? a = some (.int cty.width))
    (typeB : ctx.valueType? b = some (.int cty.width))
    {emitFuel selectFuel : Nat} (enoughEmit : 300 ≤ emitFuel) (enoughSelect : 319 ≤ selectFuel)
    {st middle next : State} {tr emitTrace consumerStart trace : Array RuleId} {raw out : V}
    (empty : st.base.emitted = #[])
    (emitter : ApplyInternal program (Stock.sem ctx) {} emitFuel 123 652
      [.data 145 (ccIdx cc) [],.value a,.value b] (st,tr) raw (middle,emitTrace))
    (consumer : ApplyInternal program (Stock.sem ctx) {} selectFuel 22 659
      [.ty (.int ty.width),raw,.value x,.value y] (middle,consumerStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key)))
    (separatedB : ∀ key,ctx.valueReg? b = some (.vreg key .int) → aliasNum aliases key ≠ st.base.nextVreg)
    (outsideX : ∀ key,ctx.valueReg? x = some (.vreg key .int) →
      aliasNum aliases key < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases key)
    (outsideY : ∀ key,ctx.valueReg? y = some (.vreg key .int) →
      aliasNum aliases key < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases key) :
    ∃ d code,out = .regs [.vreg d .int] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base code ∧
      ∀ world,Runs F isem (code.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world
        (fun final _ => VHolds ⟨ty,if Clif.Sem.intcc cc av bv then u else v⟩ (final d) ∧
          ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → final k = ρ k) := by
  have shape := stock_select_comparison_condition_shape inv comparisonWidth cc typeA typeB enoughEmit emitter
  obtain ⟨booleanProducer,actualProducer,condition,rx,ry,booleanFlag,actualFlag,safeX,safeY,mapX,mapY,output,finish⟩ :=
    stock_select_decoded_condition_observed ctx shape width enoughSelect consumer
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapX
  obtain ⟨ny,rfl⟩ := inv.valueReg y ry mapY
  have monotone := stock_apply_demand_mono consumer
  have middleHeld : ValuesHeld (Demanded middle) ctx fr (fun key => ρ (aliasNum aliases key)) := by
    apply held.mono
    intro value needed
    have grows := monotone value
    change middle.demand[value]! ≠ 0 at needed
    change next.demand[value]! ≠ 0
    omega
  obtain ⟨producer',condition',booleanTrace,flag',noDefs,notAl,notNv,booleanCall,execution⟩ :=
    stock_select_comparison_companion_source_values inv comparisonWidth cc dfg getA getB typeA typeB enoughEmit
      emitter refines bounded extent middleHeld separatedB
  obtain ⟨producerEq,conditionEq⟩ := flag_unique flag' booleanFlag
  simp only [producerEq,conditionEq] at booleanCall execution noDefs notAl notNv
  obtain ⟨d,code,booleanOutput,lower,upper,fragment,runs⟩ := execution
  have equalD : d = middle.base.nextVreg := by
    simpa only [LState.fresh] using (Reg.vreg.inj (V.reg.inj booleanOutput)).1.symm
  subst d
  have actualNext : next.base = (((middle.base.fresh .int).2.emit actualProducer).emit
      (.csel (.vreg middle.base.nextVreg .int) (.vreg nx .int) (.vreg ny .int) condition)) := by rw [finish]; rfl
  have frontier : next.base.nextVreg = middle.base.nextVreg+1 := by rw [actualNext]; rfl
  have codeEq : code = middle.base.emitted.toList ++ [booleanProducer,.cset (.vreg middle.base.nextVreg .int) condition] := by
    simpa only [LState.fresh] using stock_select_companion_fragment_code empty fragment
  rw [codeEq] at runs fragment
  have demandSize := Extent.apply_demand_size emitter
  have extentMiddle : ∀ value r,ctx.valueReg? value = some r → value < middle.demand.size := by
    intro value r mapped
    rw [demandSize]
    exact extent value r mapped
  have neededX : Demanded next x := by
    have first := (mark_demand middle x (extentMiddle x _ mapX)).1
    have second := stock_ctor_demand_mono (stock_put_in_reg ctx (middle.mark x) y (.vreg ny .int) mapY safeY) x
    rw [finish]
    unfold Demanded
    simp only [State.mark] at first second ⊢
    omega
  have neededY : Demanded next y := by
    have bound : y < (middle.mark x).demand.size := by simpa only [State.mark,Array.size_modify] using extentMiddle y _ mapY
    have marked := (mark_demand (middle.mark x) y bound).1
    rw [finish]
    unfold Demanded
    simp only [State.mark] at marked ⊢
    omega
  have inputX := held.read neededX (getAs_ok getX) mapX
  have inputY := held.read neededY (getAs_ok getY) mapY
  let instructions := middle.base.emitted.toList ++ [actualProducer,
    MInst.csel (.vreg middle.base.nextVreg .int) (.vreg nx .int) (.vreg ny .int) condition]
  have noActualDefs := (actualFlag.shape cmpXzr_regs shape).2.2.1
  refine ⟨middle.base.nextVreg,instructions,output,lower,by omega,?_,?_⟩
  · constructor
    · rw [actualNext]
      apply Array.toList_inj.mp
      simp [LState.emit,LState.fresh,empty,instructions]
    · omega
    · intro inst member key defined
      simp only [instructions,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with leading | rfl | rfl
      · have range := fragment.defs inst (by simp [leading]) key defined
        simp only [LState.emit,LState.fresh] at range
        omega
      · rw [noActualDefs] at defined; cases defined
      · rw [vdefs_csel,List.mem_singleton] at defined
        subst key
        exact ⟨lower,by omega⟩
  · intro world
    apply stock_select_condition_producer_replacement (d := middle.base.nextVreg) (x := nx) (y := ny)
      (b := Clif.Sem.intcc cc av bv) (P := fun k => k < st.base.nextVreg ∨ next.base.nextVreg ≤ k)
      refines booleanFlag actualFlag ⟨notAl,notNv⟩
      (by omega : ty.width ≤ 64) (by omega : aliases.size ≤ middle.base.nextVreg)
      (by have h := outsideX nx mapX; omega) (by have h := outsideY ny mapY; omega)
      (by intro key outside; omega) (leading := middle.base.emitted.toList)
    apply (runs world).imp
    intro final _ _ post
    have ghostFrontier : ({middle with base := (((middle.base.fresh .int).2.emit booleanProducer).emit
        (.cset (middle.base.fresh .int).1 condition))} : State).base.nextVreg = next.base.nextVreg := by
      simp only [LState.fresh,LState.emit]
      omega
    rw [ghostFrontier] at post
    exact ⟨post.1,by rw [post.2 _ (outsideX nx mapX)]; exact inputX,
      by rw [post.2 _ (outsideY ny mapY)]; exact inputY,post.2⟩
end Backend.Stock.Proof.ScalarSelect

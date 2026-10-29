module

public import FV.Backend.Proof.PerEdgePreparedDriverSound
public import FV.Backend.Proof.PerEdgePrepareFacts
public import FV.Backend.Proof.StockPerEdgeAllocatorWitness
public import FV.Backend.Proof.StockPerEdgeM6Witness
public import FV.Backend.Proof.StockPerEdgeM6HaltWitness
public import FV.E2E.RegLevelDriverSem

@[expose] public section

namespace Backend.Stock.Proof.PreparedForwardWitness
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def function : Clif.Function := {
  name := "stock_per_successor_migration"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],term := .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩},
    {id := 1,params := [(31,.i64)],term := .ret [31]}, {id := 2,params := [(47,.i64)],term := .ret [47]}] }


private noncomputable def machineStep {W : Type} (vc : VCode) (sem : ISem CV W) (keep : Reg → CV → CV)
    (state : RFunc × MConf CV W) : RFunc × MConf CV W := by
  classical
  exact (state.1,if h : ∃ next,MStep vc sem keep state.1 state.2 next then Classical.choose h else state.2)

private theorem machine_realizes {W : Type} (vc : VCode) (rf : RFunc) (sem : ISem CV W)
    (keep : Reg → CV → CV) : Realizes vc rf sem keep (machineStep vc sem keep)
      (fun state conf => state = (rf,conf)) (fun _ => True) := by
  classical
  intro state conf next equal step
  subst state
  have existsStep : ∃ next,MStep vc sem keep rf conf next := ⟨next,step⟩
  refine ⟨1,Classical.choose existsStep,Classical.choose_spec existsStep,?_,fun _ _ => trivial⟩
  simp [machineStep,iterN,existsStep]

private def Observed : Prop := (do
  let result ← Stock.lower function
  let prepared ← prepareAt result.code result.edgeArgs
  pure (PerEdgePrep.prepCheckAt result.code result.edgeArgs prepared)).toOption = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
end Kernel

/-- A complete original-scope/dominated Stock conditional passes actual checked
preparation and checked spill lowering. Every original csem entry-return run is
realized by a deterministic successor selector over the actual allocated model,
with equal return/world and callee-saved parts. This is an allocated-model
non-vacuity witness; Arm instruction/byte realization is a later stage. -/
theorem stock_prepared_return_forward_witness : ∃ (result : Result) (prepared : EdgeVCode) (rf : RFunc) (af : AFunc),
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    prepareCheckedAt result.code result.edgeArgs = .ok prepared ∧
    allocResultAt prepared.code prepared.edges (.error "force indexed fallback") = .ok rf ∧
    lowerAllocAt prepared.code prepared.edges (.error "force indexed fallback") = .ok af ∧
    (prepared.code.name = result.code.name ∧ prepared.code.classes = result.code.classes ∧
      prepared.code.slotBytes = result.code.slotBytes ∧ prepared.code.outgoing = result.code.outgoing ∧
      prepared.code.rulesFired = result.code.rulesFired) ∧
    ∀ (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState) (ρ : Nat → CV) (m₀ : Loc → CV),
      Star (VStepAt result.code result.edgeArgs (csem F ctx X)) (VConf.init ρ w) (.ret [regVal w (.x 0)] w) ∧
      Star (VStepAt prepared.code prepared.edges (csem F ctx X)) (VConf.init ρ w) (.ret [regVal w (.x 0)] w) ∧
      (∃ n m,iterN (machineStep prepared.code (csem F ctx X) ckeep) n (rf,MConf.init rf m₀ w) =
        (rf,.ret [regVal w (.x 0)] m w) ∧
        ∀ r ∈ calleeSaved,ckeep r (m (.reg r)) = ckeep r (m₀ (.reg r))) ∧
      (∃ n b allocs items m world,
        iterN (machineStep prepared.code (csem F ctx X) ckeep) n (rf,MConf.init rf m₀ w) =
          (rf,.run ⟨b,.op 0 allocs :: items,m,world⟩)) := by
  obtain ⟨result,prepared,rf,af,run,scope,dominated,preparation,_,_,selected,accepted,lowered,lower,_⟩ :=
    PerEdgeAllocatorWitness.stock_per_edge_allocator_fallback_witness
  change Stock.lower function = .ok result at run
  change LowerScope function at scope
  change Dominated function at dominated
  have actual := observed
  unfold Observed at actual
  rw [run] at actual
  simp only [bind,Except.bind,preparation,pure,Except.pure,Except.toOption,Option.some.injEq] at actual
  have checked : prepareCheckedAt result.code result.edgeArgs = .ok prepared := by
    simp [prepareCheckedAt,preparation,actual]
  obtain ⟨result',run',_,_,_,sourceRun⟩ := PerEdgeM6Witness.stock_per_edge_m6_return_witness
  change Stock.lower function = .ok result' at run'
  rw [run] at run'
  cases run'
  refine ⟨result,prepared,rf,af,run,scope,dominated,checked,selected,lower,PerEdgePrep.prepareAt_fields preparation,?_⟩
  intro F ctx X w ρ m₀
  have source := (sourceRun F ctx X w ρ).2.1
  have dsem := (driverSem_csem F ctx X).toDriverSemG
  have preparedRun := PerEdgePrep.prep_ret dsem actual source
  have initial : ∀ rf',allocResultAt prepared.code prepared.edges (.error "force indexed fallback") = .ok rf' →
      lowerRFunc prepared.code rf' = .ok af → (rf,MConf.init rf m₀ w) = (rf',MConf.init rf' m₀ w) := by
    intro rf' same _
    rw [selected] at same
    cases same
    rfl
  obtain ⟨rf',n,m,chosen,_,executed,preserved,_⟩ := PerEdge.prepared_return_forward checked lower dsem ckeep
    (Q := fun rf' state conf => state = (rf',conf)) (T := fun _ => True)
    (fun rf' _ _ => machine_realizes prepared.code rf' (csem F ctx X) ckeep) initial source
  rw [selected] at chosen
  cases chosen
  have firstStep : ∃ v,VStepAt prepared.code prepared.edges (csem F ctx X) (VConf.init ρ w) v := by
    cases preparedRun with
    | step first rest => exact ⟨_,first⟩
  obtain ⟨v,first⟩ := firstStep
  obtain ⟨R,simulation,related,_⟩ := PerEdge.checkAlloc_sound prepared.code rf (csem F ctx X) ckeep accepted m₀ ρ w
  obtain ⟨n',b,allocs,items,m',world,operation,_⟩ := PerEdge.forward_op simulation
    (machine_realizes prepared.code rf (csem F ctx X) ckeep) first
    (MConf.init rf m₀ w).measure (MConf.init rf m₀ w) (rf,MConf.init rf m₀ w)
    (Nat.le_refl _) related rfl
  exact ⟨source,preparedRun,⟨n,m,executed,preserved⟩,n',b,allocs,items,m',world,operation⟩
private def trapFunction : Clif.Function := {
  name := "stock_trap_abi_contract",sig := {callConv := some .systemV}
  blocks := [{id := 0,term := .trap (.user 9)}] }
private def trapPipeline : Except String (Result × EdgeVCode × RFunc × AFunc) := do
  let result ← Stock.lower trapFunction
  let prepared ← prepareCheckedAt result.code result.edgeArgs
  let rf ← allocResultAt prepared.code prepared.edges (.error "force indexed fallback")
  let af ← lowerRFunc prepared.code rf
  pure (result,prepared,rf,af)
private def TrapObserved : Prop := trapPipeline.toOption.map (fun (q : Result × EdgeVCode × RFunc × AFunc) =>
  decide (q.1.code.blocks.size = 1 ∧ (q.1.code.blocks[0]!).insts = #[.udf (.user 9)])) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem trap_observed : TrapObserved := by unfold TrapObserved trapPipeline; decide +kernel
end Kernel
private theorem trap_dominated : Dominated trapFunction := by
  constructor
  · change ([] : List Nat).Nodup; decide
  · intro ctx ranges initial build bi block found
    cases bi with
    | zero =>
      simp [trapFunction] at found
      subst block
      constructor
      · intro j statement present; simp at present
      · intro y member; simp [abiTerm,Driver.termArgs] at member
    | succ bi => simp [trapFunction] at found
  · intro ctx ranges initial build tl x available notLocal y member
    cases tl <;> simp [parsOf,trapFunction]

/-- The complete original Stock trap passes actual checked preparation and
fallback lowering. Its source-coded trap and csem halt survive preparation,
and the selected allocated-model machine reaches the same halt/world. -/
theorem stock_prepared_halt_forward_witness : ∃ (result : Result) (prepared : EdgeVCode) (rf : RFunc) (af : AFunc),
    Stock.lower trapFunction = .ok result ∧ LowerScope trapFunction ∧ Dominated trapFunction ∧
    prepareCheckedAt result.code result.edgeArgs = .ok prepared ∧
    allocResultAt prepared.code prepared.edges (.error "force indexed fallback") = .ok rf ∧
    lowerAllocAt prepared.code prepared.edges (.error "force indexed fallback") = .ok af ∧
    Clif.step Clif.Env.empty {funcs := []}
      ⟨{func := trapFunction,regs := fun _ => none,slots := [],body := [],term := .trap (.user 9)},[],Clif.Mem.empty⟩ =
        .trapped (.user 9) ∧
    ∀ (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState) (ρ : Nat → CV) (m₀ : Loc → CV),
      Star (VStepAt result.code result.edgeArgs (csem F ctx X)) (VConf.init ρ w) (.halt w) ∧
      Star (VStepAt prepared.code prepared.edges (csem F ctx X)) (VConf.init ρ w) (.halt w) ∧
      PerEdgePrep.VTrapFromAt result.code result.edgeArgs (csem F ctx X) ⟨0,0,ρ,w⟩ (.user 9) ∧
      PerEdgePrep.VTrapFromAt prepared.code prepared.edges (csem F ctx X) ⟨0,0,ρ,w⟩ (.user 9) ∧
      ∃ n,iterN (machineStep prepared.code (csem F ctx X) ckeep) n (rf,MConf.init rf m₀ w) = (rf,.halt w) := by
  have actual := trap_observed
  unfold TrapObserved at actual
  cases done : trapPipeline with
  | error err => simp only [done,Except.toOption,Option.map_none] at actual; cases actual
  | ok q =>
    rw [done] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    obtain ⟨size,code⟩ := actual
    unfold trapPipeline at done
    obtain ⟨result,run,h⟩ := Except.bind_ok done
    obtain ⟨prepared,preparation,h⟩ := Except.bind_ok h
    obtain ⟨rf,selected,h⟩ := Except.bind_ok h
    obtain ⟨af,lowered,h⟩ := Except.bind_ok h
    cases h
    have lower : lowerAllocAt prepared.code prepared.edges (.error "force indexed fallback") = .ok af := by
      simp only [lowerAllocAt,selected,bind,Except.bind,lowered]
    obtain ⟨result',run',scope,_,sourceTrap,sourceRun⟩ := PerEdgeM6HaltWitness.stock_per_edge_m6_halt_witness
    change Stock.lower trapFunction = .ok result' at run'
    change LowerScope trapFunction at scope
    rw [run] at run'
    cases run'
    refine ⟨result,prepared,rf,af,run,scope,trap_dominated,preparation,selected,lower,sourceTrap,?_⟩
    intro F ctx X w ρ m₀
    have source := (sourceRun F ctx X w m₀ ρ).2
    have dsem := (driverSem_csem F ctx X).toDriverSemG
    have checked := (PerEdge.prepareCheckedAt_ok preparation).2
    have preparedRun := PerEdgePrep.prep_halt dsem checked source
    have placed : result.code.blocks[0]? = some result.code.blocks[0]! := by
      have bound : 0 < result.code.blocks.size := by rw [size]; decide
      simp [getElem!_def,Array.getElem?_eq_getElem bound]
    have observation : PerEdgePrep.VTrapFromAt result.code result.edgeArgs (csem F ctx X) ⟨0,0,ρ,w⟩ (.user 9) := by
      refine ⟨0,0,ρ,w,result.code.blocks[0]!,.udf (.user 9),#[],[],w,.refl _,placed,?_,rfl,rfl,rfl⟩
      rw [code]; rfl
    have preparedObservation := (PerEdgePrep.prep_sound dsem checked ρ w).2 (.user 9) observation
    have initial : ∀ rf',allocResultAt prepared.code prepared.edges (.error "force indexed fallback") = .ok rf' →
        lowerRFunc prepared.code rf' = .ok af → (rf,MConf.init rf m₀ w) = (rf',MConf.init rf' m₀ w) := by
      intro rf' same _
      rw [selected] at same
      cases same
      rfl
    obtain ⟨rf',n,chosen,_,executed,_⟩ := PerEdge.prepared_halt_forward preparation lower dsem ckeep
      (Q := fun rf' state conf => state = (rf',conf)) (T := fun _ => True)
      (fun rf' _ _ => machine_realizes prepared.code rf' (csem F ctx X) ckeep) initial source
    rw [selected] at chosen
    cases chosen
    exact ⟨source,preparedRun,observation,preparedObservation,n,executed⟩
end Backend.Stock.Proof.PreparedForwardWitness

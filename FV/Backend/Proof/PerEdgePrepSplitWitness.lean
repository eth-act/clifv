import FV.Backend.Proof.PerEdgePrepareSound
import FV.Backend.Proof.PerEdgePrepareWitness
import FV.E2E.RegLevelDriverSem
namespace Backend.Proof.PerEdgePrepSplitWitness
open Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private def code : VCode := {
  name := "indexed_prepare_split",classes := Array.replicate 196 .int,
  slotBytes := 0,outgoing := 0,rulesFired := #[],blocks := #[
    {label := 10,insts := #[.args [(.vreg 192 .int,.x 0),(.vreg 194 .int,.x 1)],
      .condBr 20 30 (.notZero (.vreg 192 .int) .size64)]},
    {label := 20,insts := #[.jump 30],params := #[.vreg 193 .int],branchArgs := #[.vreg 193 .int]},
    {label := 30,insts := #[.rets [(.vreg 195 .int,.x 0)]],params := #[.vreg 195 .int]},
    {label := 40,insts := #[.jump 50]}, {label := 50,insts := #[.udf (.user 7)]}] }
private def edges : Array (Array (Array Reg)) := #[
  #[#[.vreg 192 .int],#[.vreg 194 .int]],#[#[.vreg 193 .int]],#[],#[#[]],#[]]

private def registers (word : CV) (key : Nat) : CV := if key = 194 then word else 0
private def Observed : Prop := (prepareAt code edges).toOption.map
  (fun (p : EdgeVCode) => PerEdgePrep.prepCheckAt code edges p) = some true
private theorem observed : Observed := by unfold Observed; decide +kernel

/-- A genuine critical edge with a nonempty copy into a parameterized block
inhabits indexed preparation's one/two-step simulation and split-route decoder.
All filtering/splitting/RPO comes from actual prepareAt; the original selected
value is copied for every CV word and Arm world. -/
theorem per_edge_prepare_actual_split_step_witness (word : CV) (F : BitVec 64 → Prop)
    (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState) : ∃ (prepared : EdgeVCode) (target : Nat),
    prepareAt code edges = .ok prepared ∧ PerEdgePrep.prepCheckAt code edges prepared = true ∧
    sigmaOf code prepared.code 2 = some target ∧
    VStepAt code edges (csem F ctx X) (.run ⟨0,1,registers word,w⟩)
      (.run ⟨2,0,parCopyEnv (registers word) [195] [194],w⟩) ∧
    Star (VStepAt prepared.code prepared.edges (csem F ctx X)) (.run ⟨0,1,registers word,w⟩)
      (.run ⟨target,0,parCopyEnv (registers word) [195] [194],w⟩) ∧
    parCopyEnv (registers word) [195] [194] 195 = word := by
  obtain ⟨prepared,run,_,_,sourceCopy,_⟩ := PerEdgePrepareWitness.per_edge_prepare_split_copy_witness (registers word)
  change prepareAt code edges = .ok prepared at run
  change edgeEnvAt code edges 0 2 1 (registers word) = some (parCopyEnv (registers word) [195] [194]) at sourceCopy
  have actual := observed
  unfold Observed at actual
  rw [run] at actual
  simp only [Except.toOption,Option.map_some,Option.some.injEq] at actual
  have source : VStepAt code edges (csem F ctx X) (.run ⟨0,1,registers word,w⟩)
      (.run ⟨2,0,parCopyEnv (registers word) [195] [194],w⟩) := by
    refine VStepAt.step (vb := code.blocks[0]!) (i := .condBr 20 30 (.notZero (.vreg 192 .int) .size64))
      (ops := #[⟨192,.int,.use,.early,.reg⟩]) rfl rfl rfl (by rfl) (by decide) ?_
    simp [Operand.isDef,writeV]
    exact VNextAt.goto (by decide) (by change succOf code 0 1 = some 2; decide +kernel) sourceCopy
  obtain ⟨target,mapped,steps⟩ := PerEdgePrep.prep_entry_step (driverSem_csem F ctx X).toDriverSemG actual source
  exact ⟨prepared,target,run,actual,mapped,source,steps,by simp [parCopyEnv,registers]⟩
end Backend.Proof.PerEdgePrepSplitWitness

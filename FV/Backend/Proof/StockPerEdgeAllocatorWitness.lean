import FV.Backend.Proof.PerEdgeAllocDriverSound
import FV.Backend.Proof.StockPerEdgeCheckerWitness
namespace Backend.Stock.Proof.PerEdgeAllocatorWitness
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def function : Clif.Function := {
  name := "stock_per_successor_migration"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],term := .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩},
    {id := 1,params := [(31,.i64)],term := .ret [31]}, {id := 2,params := [(47,.i64)],term := .ret [47]}] }

private def pipeline : Except String (Result × EdgeVCode × RFunc × AFunc) := do
  let result ← Stock.lower function
  let prepared ← prepareAt result.code result.edgeArgs
  let rf ← allocResultAt prepared.code prepared.edges (.error "force indexed fallback")
  let af ← lowerRFunc prepared.code rf
  pure (result,prepared,rf,af)
private def Observed : Prop := pipeline.toOption.map (fun (q : Result × EdgeVCode × RFunc × AFunc) => decide (
  q.2.1.code.blocks.size = 3 ∧
  q.2.1.edges[0]? = some #[#[Reg.vreg 192 .int],#[Reg.vreg 192 .int]])) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed pipeline; decide +kernel
end Kernel

/-- The complete original conditional now prepares and lowers with the actual
checked indexed spill fallback, preserving its two nonempty outgoing vectors.
All driver-success proof roots are inhabited on this full Stock execution. -/
theorem stock_per_edge_allocator_fallback_witness : ∃ (result : Result) (prepared : EdgeVCode) (rf : RFunc) (af : AFunc),
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    prepareAt result.code result.edgeArgs = .ok prepared ∧
    prepared.edges[0]? = some #[#[Reg.vreg 192 .int],#[Reg.vreg 192 .int]] ∧
    rf = spillAllocAt prepared.code prepared.edges ∧
    allocResultAt prepared.code prepared.edges (.error "force indexed fallback") = .ok rf ∧
    checkAllocAt prepared.code prepared.edges rf = .ok () ∧
    lowerRFunc prepared.code rf = .ok af ∧
    lowerAllocAt prepared.code prepared.edges (.error "force indexed fallback") = .ok af ∧
    ∀ {V W : Type} (sem : ISem V W) (keep : Reg → V → V) (m : Loc → V) (ρ : Nat → V) (w : W),
      ∃ R,PerEdge.IsSimulation prepared.code rf sem keep prepared.edges R ∧
        R (MConf.init rf m w) (VConf.init ρ w) ∧
        ∀ {vals m' w' v},R (.ret vals m' w') v →
          ∀ r ∈ calleeSaved,keep r (m' (.reg r)) = keep r (m (.reg r)) := by
  obtain ⟨_,_,scope,dominated,_⟩ := PerEdgeCheckerWitness.stock_per_edge_checker_witness
  change LowerScope function at scope
  change Dominated function at dominated
  have actual := observed
  unfold Observed at actual
  cases run : pipeline with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok q =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    obtain ⟨size,vectors⟩ := actual
    unfold pipeline at run
    obtain ⟨result,lowered,h⟩ := Except.bind_ok run
    obtain ⟨prepared,prepare,h⟩ := Except.bind_ok h
    obtain ⟨rf,selected,h⟩ := Except.bind_ok h
    obtain ⟨af,allocated,h⟩ := Except.bind_ok h
    cases h
    have fallback : rf = spillAllocAt prepared.code prepared.edges := by
      have h := selected
      unfold allocResultAt checkedSpillAt at h
      obtain ⟨answer,_,same⟩ := Except.bind_ok h
      cases same
      rfl
    have final : lowerAllocAt prepared.code prepared.edges (.error "force indexed fallback") = .ok af := by
      simp only [lowerAllocAt,selected,bind,Except.bind,allocated]
    obtain ⟨rf',chosen,accepted,lower⟩ := PerEdge.lowerAllocAt_ok final
    rw [selected] at chosen
    cases chosen
    refine ⟨result,prepared,rf,af,lowered,scope,dominated,prepare,vectors,fallback,
      selected,accepted,allocated,final,?_⟩
    intro V W sem keep m ρ w
    obtain ⟨rf',chosen,_,simulation⟩ := PerEdge.lowerAllocAt_sound final sem keep
    rw [selected] at chosen
    cases chosen
    exact simulation m ρ w
end Backend.Stock.Proof.PerEdgeAllocatorWitness

import FV.Backend.Proof.PerEdgeAllocDriverSound
import FV.Backend.Proof.StockCriticalValuesWitness
namespace Backend.Stock.Proof.PerEdgeCriticalAllocatorWitness
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def reduce : Clif.Stmt := ⟨[17],.ireduce .i8 7⟩
private def function : Clif.Function := {
  name := "stock_critical_values_alias"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],body := [reduce],term := .brif 7 ⟨1,[17]⟩ ⟨1,[17]⟩},
    {id := 1,params := [(31,.i8)],term := .ret [31]}] }

private def pipeline : Except String (Result × EdgeVCode × RFunc × AFunc) := do
  let result ← Stock.lower function
  let prepared ← prepareAt result.code result.edgeArgs
  let rf ← allocResultAt prepared.code prepared.edges (.error "force indexed fallback")
  let af ← lowerRFunc prepared.code rf
  pure (result,prepared,rf,af)
private def Observed : Prop := pipeline.toOption.map (fun (q : Result × EdgeVCode × RFunc × AFunc) => decide (
  q.2.1.code.blocks.size = 4 ∧
  q.2.1.edges[0]? = some #[#[],#[]] ∧
  q.2.1.edges[1]? = some #[#[Reg.vreg 192 .int]] ∧
  q.2.1.edges[2]? = some #[#[Reg.vreg 192 .int]] ∧
  (q.2.1.code.blocks[1]!).label = 2)) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed pipeline; decide +kernel
end Kernel

/-- Complete critical-edge Stock lowering has synthetic blocks reordered by
prepareAt. Their actual outgoing vectors and alias-resolved source register
survive, and the checked indexed fallback lowers with complete M6 simulation. -/
theorem stock_per_edge_critical_allocator_fallback_witness : ∃ (result : Result) (prepared : EdgeVCode) (rf : RFunc) (af : AFunc),
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    prepareAt result.code result.edgeArgs = .ok prepared ∧
    prepared.edges[0]? = some #[#[],#[]] ∧
    prepared.edges[1]? = some #[#[Reg.vreg 192 .int]] ∧
    prepared.edges[2]? = some #[#[Reg.vreg 192 .int]] ∧
    (prepared.code.blocks[1]!).label = 2 ∧
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
  obtain ⟨_,_,_,_,_,scope,dominated,_⟩ := CriticalValuesWitness.stock_critical_selected_route_witness 0 0 (by decide)
  change LowerScope function at scope
  change Dominated function at dominated
  have actual := observed
  unfold Observed at actual
  cases run : pipeline with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok q =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    obtain ⟨size,vectors0,vectors1,vectors2,reordered⟩ := actual
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
    refine ⟨result,prepared,rf,af,lowered,scope,dominated,prepare,vectors0,vectors1,vectors2,reordered,fallback,
      selected,accepted,allocated,final,?_⟩
    intro V W sem keep m ρ w
    obtain ⟨rf',chosen,_,simulation⟩ := PerEdge.lowerAllocAt_sound final sem keep
    rw [selected] at chosen
    cases chosen
    exact simulation m ρ w
end Backend.Stock.Proof.PerEdgeCriticalAllocatorWitness

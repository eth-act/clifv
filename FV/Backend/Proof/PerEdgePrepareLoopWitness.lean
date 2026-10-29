module

public import FV.Backend.Proof.PerEdgePrepareLoopFacts
public import FV.Backend.Proof.PerEdgePrepareWitness

@[expose] public section

namespace Backend.Proof.PerEdgePrepLoopWitness
open Backend Backend.Proof.PerEdgePrep

private def preds : Array (Array Nat) := #[#[], #[0], #[0,1]]
private def successors : Array Nat := #[1,2]
private def targets : Array Label := #[20,30]
private def original : EdgeRow := #[#[.vreg 192 .int], #[.vreg 195 .int, .vreg 194 .int]]
private def previous : VBlock :=
  {label := 99, insts := #[.jump 40], branchArgs := #[.vreg 196 .int]}
private def initial : InnerState := (100, #[previous], #[#[previous.branchArgs]], original, #[])
private def inputs := (successors.zip targets).zipIdx
private def out := inputs.toList.foldl (innerStepAt preds) initial
private def first := innerStepAt preds initial ((1,20),0)

private def execute : Except String InnerState :=
  forIn inputs initial fun x st => do
    if preds[x.1.1]!.size > 1 then
      let args := st.2.2.2.1[x.2]!
      pure (.yield (st.1 + 1,
        st.2.1.push {label := st.1, insts := #[.jump x.1.2], branchArgs := args},
        st.2.2.1.push #[args], st.2.2.2.1.set! x.2 #[], st.2.2.2.2.push st.1))
    else pure (.yield (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.push x.1.2))

/-- A mixed direct/critical loop, starting with an existing synthetic edge,
inhabits every graph, monadic-normalization and copy-conservation root. The
split vector has two registers in reversed order; neither copy is empty. -/
theorem indexed_inner_loop_witness :
    execute = .ok out ∧
    graphState (innerStepAt preds first ((2,30),1)) =
      Prep.innerStep preds (graphState first) (2,30) ∧
    graphState out = (inputs.toList.map Prod.fst).foldl (Prep.innerStep preds) (graphState initial) ∧
    EdgeRowsAgree (innerStepAt preds first ((2,30),1)).2.1
      (innerStepAt preds first ((2,30),1)).2.2.1 ∧
    EdgeRowsAgree out.2.1 out.2.2.1 ∧
    out.2.1.size + 99 = out.1 ∧ Prep.EdgesOk 99 (out.2.1.map graphBlock) ∧
    CopyRoute out 0 20 #[.vreg 192 .int] ∧
    CopyRoute out 1 30 #[.vreg 195 .int, .vreg 194 .int] ∧
    out.2.2.2.2 = #[20,100] ∧ out.2.1[0]? = some previous ∧
    out.2.2.2.1 = #[#[.vreg 192 .int],#[]] ∧
    out.2.2.1[1]? = some #[#[.vreg 195 .int,.vreg 194 .int]] := by
  have paired : EdgeRowsAgree initial.2.1 initial.2.2.1 := by
    refine ⟨rfl, ?_⟩
    intro e b hb
    have bound := (Array.getElem?_eq_some_iff.mp hb).1
    have eq : e = 0 := by change e < 1 at bound; omega
    subst e
    change some previous = some b at hb
    cases hb
    rfl
  have firstPaired := innerStepAt_rows preds initial ((1,20),0) paired
  have facts := innerFoldAt_facts preds 99 inputs.toList initial (by decide +kernel)
    (by
      intro e he
      have eq : e = 0 := by simp only [Array.size_map] at he; change e < 1 at he; omega
      subst e
      exact ⟨40, by simp [initial, previous, graphBlock]⟩)
  have copies := innerFoldAt_copies preds successors targets original 100 #[previous]
    #[#[previous.branchArgs]] paired (by decide +kernel)
  refine ⟨innerForInAt_eq preds inputs initial, innerStepAt_graph preds first ((2,30),1),
    innerFoldAt_graph preds inputs.toList initial,
    innerStepAt_rows preds first ((2,30),1) firstPaired,
    innerFoldAt_rows preds inputs.toList initial paired, facts.1, facts.2.1,
    copies.2.2 0 20 _ rfl rfl, copies.2.2 1 30 _ rfl rfl, ?_⟩
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
  simp [out, inputs, successors, targets, initial, innerStepAt, preds]

/-- The actual filtering/splitting/RPO fixture supplies the normalized outer
execution with no extra loop certificate. Unreachable blocks disappear and the
fresh critical edge is placed by actual RPO. -/
theorem indexed_prepare_stages_witness :
    ∃ (vc : VCode) (edges : Array EdgeRow) (p : EdgeVCode),
      prepareAt vc edges = .ok p ∧ vc.blocks.size = 5 ∧
      p.code.blocks.map (·.label) = #[10,31,20,30] ∧
      ∃ (ss0 ps0 ss1 ps1 ss2 ps2 : Array (Array Nat)) (st : OuterState),
        vc.cfg = .ok (ss0,ps0) ∧
        ({vc with blocks := (keptAt vc edges ss0).map Prod.fst} : VCode).cfg = .ok (ss1,ps1) ∧
        forIn ((keptAt vc edges ss0).map Prod.fst).zipIdx
          (Prep.next0Of ((keptAt vc edges ss0).map Prod.fst), #[], #[], #[], #[])
          (outerStepAt ss1 ps1 ((keptAt vc edges ss0).map Prod.snd)) = .ok st ∧
        ({vc with blocks := st.2.1 ++ st.2.2.2.1} : VCode).cfg = .ok (ss2,ps2) ∧
        p = ⟨{vc with blocks := (rpo ss2).map fun i => (st.2.1 ++ st.2.2.2.1)[i]!},
          (rpo ss2).map fun i => (st.2.2.1 ++ st.2.2.2.2)[i]!⟩ := by
  obtain ⟨p,run,labels,_⟩ := PerEdgePrepareWitness.per_edge_prepare_split_copy_witness (fun _ => 0)
  exact ⟨_,_,p,run,rfl,labels,prepareAt_stages run⟩

end Backend.Proof.PerEdgePrepLoopWitness

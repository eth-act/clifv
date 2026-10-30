import FV.Backend.RegallocPerEdgePrepare
import FV.Backend.Proof.RegallocOperands
import FV.Backend.Proof.PerEdgeVCodeSem
namespace Backend.Proof.PerEdgePrepareWitness
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
private def Observed : Prop := (prepareAt code edges).toOption.map (fun (p : EdgeVCode) => decide (
  p.code.blocks.size = 4 ∧ p.code.blocks.map (·.label) = #[10,31,20,30] ∧
  (p.code.blocks[1]!).insts = #[.jump 30] ∧ (p.code.blocks[1]!).params = #[] ∧
  (p.code.blocks[3]!).params = #[.vreg 195 .int] ∧
  p.edges[0]? = some #[#[Reg.vreg 192 .int],#[]] ∧ p.edges[1]? = some #[#[Reg.vreg 194 .int]])) = some true
private theorem observed : Observed := by unfold Observed; decide +kernel

/-- Preparation really filters unreachable blocks, introduces a critical-edge
jump and reorders blocks. The split edge has an identity first copy followed by
the exact original selected copy, over arbitrary register values. -/
theorem per_edge_prepare_split_copy_witness (ρ : Nat → CV) : ∃ p : EdgeVCode,
    prepareAt code edges = .ok p ∧ p.code.blocks.map (·.label) = #[10,31,20,30] ∧
    (p.code.blocks[1]!).insts = #[.jump 30] ∧
    edgeEnvAt code edges 0 2 1 ρ = some (parCopyEnv ρ [195] [194]) ∧
    edgeEnvAt p.code p.edges 0 1 1 ρ = some ρ ∧
    edgeEnvAt p.code p.edges 1 3 0 ρ = some (parCopyEnv ρ [195] [194]) := by
  have actual := observed
  unfold Observed at actual
  cases run : prepareAt code edges with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok p =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    obtain ⟨size,labels,jump,empty,params,row0,row1⟩ := actual
    have one : p.code.blocks[1]? = some p.code.blocks[1]! := by
      have bound : 1 < p.code.blocks.size := by omega
      simp [getElem!_def,Array.getElem?_eq_getElem bound]
    have three : p.code.blocks[3]? = some p.code.blocks[3]! := by
      have bound : 3 < p.code.blocks.size := by omega
      simp [getElem!_def,Array.getElem?_eq_getElem bound]
    refine ⟨p,rfl,labels,jump,?_,?_,?_⟩
    · simp [edgeEnvAt,code,edges,vregNum,List.mapM_cons,parCopyEnv,Except.toOption]
    · simp [edgeEnvAt,one,empty,row0,vregNum,parCopyEnv,Except.toOption]
      rfl
    · exact edgeEnvAt_eq (ps := [195]) (xs := [194]) three (by simp [row1]) params (by decide) ρ
end Backend.Proof.PerEdgePrepareWitness

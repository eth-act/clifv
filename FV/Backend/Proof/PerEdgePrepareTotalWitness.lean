import FV.Backend.Proof.PerEdgePrepareInputTotal
import FV.Backend.Proof.StockPrepareInputs
import FV.Backend.Proof.StockPrepareCompleteWitness
import FV.Backend.Proof.PerEdgePrepareWitness

namespace Backend.Proof.PerEdgePrepTotalWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.PerEdgePrep

private def code : VCode := {
  name := "indexed_prepare_split",classes := Array.replicate 196 .int,
  slotBytes := 0,outgoing := 0,rulesFired := #[],blocks := #[
    {label := 10,insts := #[.args [(.vreg 192 .int,.x 0),(.vreg 194 .int,.x 1)],
      .condBr 20 30 (.notZero (.vreg 192 .int) .size64)]},
    {label := 20,insts := #[.jump 30],params := #[.vreg 193 .int],branchArgs := #[.vreg 193 .int]},
    {label := 30,insts := #[.rets [(.vreg 195 .int,.x 0)]],params := #[.vreg 195 .int]},
    {label := 40,insts := #[.jump 50]}, {label := 50,insts := #[.udf (.user 7)]}] }
private def edges : Array EdgeRow := #[
  #[#[.vreg 192 .int],#[.vreg 194 .int]],#[#[.vreg 193 .int]],#[],#[#[]],#[]]
private def succs : Array (Array Nat) := #[#[1,2],#[2],#[],#[4],#[]]
private def preds : Array (Array Nat) := #[#[],#[0],#[0,1],#[],#[3]]
private def kept : VCode := {code with blocks := #[code.blocks[0]!,code.blocks[1]!,code.blocks[2]!]}
private def keptSuccs : Array (Array Nat) := #[#[1,2],#[2],#[]]
private def keptPreds : Array (Array Nat) := #[#[],#[0],#[0,1]]
private def keptEdges : Array EdgeRow := #[edges[0]!,edges[1]!,edges[2]!]

private theorem cfg : code.cfg = .ok (succs,preds) := by
  have observed : code.cfg.toOption = some (succs,preds) := by decide +kernel
  cases run : code.cfg with
  | error err => simp [run,Except.toOption] at observed
  | ok pair =>
    rw [run] at observed
    simp only [Except.toOption,Option.some.injEq] at observed
    exact congrArg Except.ok observed

private theorem keptCfg : Prep.CfgSpec kept.blocks keptSuccs := by
  apply Prep.cfg_spec (vc := kept) (ps := keptPreds)
  have observed : kept.cfg.toOption = some (keptSuccs,keptPreds) := by decide +kernel
  cases run : kept.cfg with
  | error err => simp [run,Except.toOption] at observed
  | ok pair =>
    rw [run] at observed
    simp only [Except.toOption,Option.some.injEq] at observed
    exact congrArg Except.ok observed

private theorem rowArity : ∀ (b : Nat) (row : EdgeRow),edges[b]? = some row → row.size = succs[b]!.size := by
  intro b row atRow
  have bound := (Array.getElem?_eq_some_iff.mp atRow).1
  have cases : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by change b < 5 at bound; omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [edges] at atRow
    subst row
    decide +kernel

private theorem noEntry : ∀ b ∈ code.blocks.toList,∀ t,
    b.insts.back? = some t → code.blocks[0].label ∉ t.targets := by
  have observed : code.blocks.toList.all (fun b => match b.insts.back? with
    | some t => decide (10 ∉ t.targets) | none => true) = true := by decide +kernel
  intro b member t back
  have h := List.all_eq_true.mp observed b member
  rw [back] at h
  exact of_decide_eq_true h

/-- Conditional, jump-table and real TryCall handler/continuation retargeting
all inhabit the total gate with their original successor counts. -/
theorem retarget_total_witness :
    (∃ i', (MInst.condBr 20 30 (.notZero (.vreg 192 .int) .size64)).setTargets [40,50] = some i' ∧
      i'.targets = [40,50]) ∧
    (∃ i', (MInst.jtSequence 20 [30,40] (.vreg 192 .int) (.vreg 193 .int) (.vreg 194 .int)).setTargets
      [50,60,70] = some i' ∧ i'.targets = [50,60,70]) ∧
    (∃ i', (MInst.tryCall default {continuation := 20,handlers := [.tag 7 30,.default 40]}).setTargets
      [50,60,70] = some i' ∧ i'.targets = [50,60,70]) := by
  constructor
  · obtain ⟨i',run⟩ := setTargets_total (i := .condBr 20 30 (.notZero (.vreg 192 .int) .size64))
      (by decide +kernel) [40,50] rfl
    exact ⟨i',run,(Prep.setTargets_targets run).1⟩
  · constructor
    · obtain ⟨i',run⟩ := setTargets_total
        (i := .jtSequence 20 [30,40] (.vreg 192 .int) (.vreg 193 .int) (.vreg 194 .int))
        (by decide +kernel) [50,60,70] rfl
      exact ⟨i',run,(Prep.setTargets_targets run).1⟩
    · obtain ⟨i',run⟩ := setTargets_total
        (i := .tryCall default {continuation := 20,handlers := [.tag 7 30,.default 40]})
        (by decide +kernel) [50,60,70] rfl
      exact ⟨i',run,(Prep.setTargets_targets run).1⟩

/-- Totality produces the real splitting execution, complete copy/graph
invariant, valid generated targets and final split CFG without assuming success. -/
theorem splitting_total_witness :
    ∃ st,forIn kept.blocks.zipIdx (Prep.next0Of kept.blocks,#[],#[],#[],#[])
        (outerStepAt keptSuccs keptPreds keptEdges) = .ok st ∧
      OuterInv kept.blocks keptEdges (Prep.next0Of kept.blocks) kept.blocks.size st ∧
      EdgeTargets kept.blocks st.2.2.2.1 ∧
      (∃ first,outerStepAt keptSuccs keptPreds keptEdges (kept.blocks[0]!,0)
        (Prep.next0Of kept.blocks,#[],#[],#[],#[]) = .ok (.yield first)) ∧
      ∃ ss ps,({kept with blocks := st.2.1 ++ st.2.2.2.1} : VCode).cfg = .ok (ss,ps) := by
  obtain ⟨st,run,inv,targets⟩ := outerLoopAt_total_targets (outgoing := keptEdges) (ps := keptPreds) keptCfg
  have initial : OuterInv kept.blocks keptEdges (Prep.next0Of kept.blocks) 0
      (Prep.next0Of kept.blocks,#[],#[],#[],#[]) := by
    refine ⟨⟨by simp,?_,rfl,?_⟩,rfl,?_,?_⟩
    · intro e he; simp at he
    · intro j _ hj; simp at hj
    · exact ⟨rfl,fun e _ he => by simp at he⟩
    · intro j _ hj; simp at hj
  obtain ⟨first,firstRun,_⟩ := outerStepAt_total keptCfg (k := 0) (vb := kept.blocks[0]!) (by rfl) initial
  exact ⟨st,run,inv,targets,⟨first,firstRun⟩,
    split_cfg inv keptCfg (by unfold Prep.Lbls; decide +kernel) targets⟩

/-- The five-block fixture reaches raw and checked preparation by totality,
with no raw success premise. Its unreachable filtering, new critical edge and
RPO10/31/20/30 agree with the independent existing execution witness. -/
theorem raw_prepare_total_witness :
    ∃ prepared,prepareAt code edges = .ok prepared ∧ prepareCheckedAt code edges = .ok prepared ∧
      prepCheckAt code edges prepared = true ∧ prepared.code.blocks.map (·.label) = #[10,31,20,30] ∧
      ∃ ss ps,({code with blocks := Prep.keep code.blocks (reachable succs)} : VCode).cfg = .ok (ss,ps) ∧
        (ps[0]?.getD #[]).isEmpty = true ∧
        (((Prep.keep code.blocks (reachable succs))[0]?.map (fun b => b.params.isEmpty)).getD true) = true := by
  have nonempty : 0 < code.blocks.size := by decide +kernel
  have labels : Prep.Lbls code.blocks := by unfold Prep.Lbls; decide +kernel
  obtain ⟨prepared,run,checked,accepted⟩ := prepareCheckedAt_total cfg nonempty labels
    (by decide +kernel) rowArity rfl noEntry
  obtain ⟨reference,actual,labelled,_⟩ := PerEdgePrepareWitness.per_edge_prepare_split_copy_witness (fun _ => 0)
  change prepareAt code edges = .ok reference at actual
  rw [run] at actual
  cases actual
  obtain ⟨ss,ps,cfg'⟩ := kept_cfg cfg nonempty labels
  have entry := kept_entry cfg nonempty cfg' rfl noEntry
  exact ⟨prepared,run,checked,accepted,labelled,ss,ps,cfg',entry⟩

/-- The complete original-scope/dominated actual conditional Stock witness
inhabits dimensions derived from its real collector, traversal and resolver. -/
theorem stock_dimensions_witness :
    ∃ (f : Clif.Function) (result : Stock.Result),Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      0 < result.code.blocks.size ∧ result.edgeArgs.size = result.code.blocks.size ∧
      result.edgeArgs.size = result.order.nodes.size ∧
      ∀ (label : Nat) (row : Array (Array Reg)),result.edgeArgs[label]? = some row →
        row.size = result.order.successors[label]!.size := by
  obtain ⟨f,result,prepared,lowered,scope,dominated,_,nonempty,_⟩ :=
    Stock.Proof.PrepareCompleteWitness.stock_prepare_complete_return_witness
  exact ⟨f,result,lowered,scope,dominated,nonempty,Stock.Proof.stock_prepare_dimensions lowered⟩

end Backend.Proof.PerEdgePrepTotalWitness

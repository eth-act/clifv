module

public import FV.Backend.Proof.PerEdgeArgumentShape
public import FV.Backend.Proof.PerEdgeParameterShape
public import FV.Backend.Proof.PerEdgeSpillCopy

@[expose] public section

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Actual original-scope/SSA Stock preparation derives every outgoing vector's
virtual-int class and every target's virtual-int/distinct parameter shape. No
class/distinctness checker is added to the source acceptance conditions. -/
theorem stock_prepare_copy_metadata {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) :
    ∃ prepared,prepareAt result.code result.edgeArgs = .ok prepared ∧
      prepareCheckedAt result.code result.edgeArgs = .ok prepared ∧
      PerEdgePrep.prepCheckAt result.code result.edgeArgs prepared = true ∧
      (∀ (b j : Nat) (row : PerEdgePrep.EdgeRow) (args : Array Reg),
        prepared.edges[b]? = some row → row[j]? = some args → ArgumentShape args) ∧
      ∀ (b : Nat) (vb : VBlock),prepared.code.blocks[b]? = some vb → ParameterShape vb.params := by
  obtain ⟨prepared,raw,checked,accepted,params⟩ := stock_prepare_parameter_shape run scope ssa
  exact ⟨prepared,raw,checked,accepted,
    PerEdgePrep.prepareAt_argument_shape raw (stock_lower_outgoing_shape run),params⟩

/-- Actual two-phase symbolic-copy postcondition, including unaffected homes,
registers and save cells. Index zero is before the actual execution block's first instruction. -/
def SpillCopyPost (prepared : EdgeVCode) (args : Array Reg) (target : VBlock) (before : AState)
    (k : Nat) (after : AState) : Prop :=
  k = 0 ∧ after.size = stateSizeAt prepared.code prepared.edges ∧
  (∀ (i : Nat) (ar p : Reg),args[i]? = some ar → target.params[i]? = some p →
    after.get (spillHomeAt (spillHomesAt prepared.code prepared.edges) p.homeNum p.homeCls) =
      before.get (spillHomeAt (spillHomesAt prepared.code prepared.edges) ar.homeNum ar.homeCls)) ∧
  ∀ l,(∀ cl,l ≠ .reg (spillScratch cl)) →
    (∀ i cl,l ≠ .stack ((spillHomesAt prepared.code prepared.edges).size+i) cl) →
    (∀ p ∈ target.params.toList,l ≠ spillHomeAt (spillHomesAt prepared.code prepared.edges) p.homeNum p.homeCls) →
    after.get l = before.get l

/-- Actual Stock/prepared spill copies need no supplied class, distinctness,
spill-slot or before-terminator certificate. The original scope/SSA and real
preparation/allocation derive these internally. Selected graph-edge arity is
still an internal proof obligation, not a new accepted-source condition. -/
theorem stock_spillArgMovesAt_runs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {prepared : EdgeVCode} (raw : prepareAt result.code result.edgeArgs = .ok prepared)
    {c : CheckCtx} (allocated : c.rf = spillAllocAt prepared.code prepared.edges)
    {b j target execution : Nat} {row : PerEdgePrep.EdgeRow} {args : Array Reg} {vb tb : VBlock}
    (atRow : prepared.edges[b]? = some row) (atArgs : row[j]? = some args)
    (atTarget : prepared.code.blocks[target]? = some tb)
    (atExecution : prepared.code.blocks[execution]? = some vb) (arity : args.size = tb.params.size)
    {a0 : AState} (stateSize : a0.size = stateSizeAt prepared.code prepared.edges) :
    Runs c vb 0 (spillArgMovesAt (spillHomesAt prepared.code prepared.edges) args tb.params) a0
      (SpillCopyPost prepared args tb a0) := by
  obtain ⟨p,raw',_,_,arguments,params⟩ := stock_prepare_copy_metadata run scope ssa
  have same := Except.ok.inj (raw.symm.trans raw')
  subst p
  have argShape := arguments b j row args atRow atArgs
  have targetShape := params target tb atTarget
  have classes : ∀ (i : Nat) (ar p : Reg),args[i]? = some ar → tb.params[i]? = some p →
      ∃ v w cl,ar = .vreg v cl ∧ p = .vreg w cl := by
    intro i ar p arAt pAt
    obtain ⟨v,rfl⟩ := argShape ar (Array.mem_toList_iff.mpr (Array.mem_of_getElem? arAt))
    obtain ⟨w,rfl⟩ := targetShape.1 p (Array.mem_toList_iff.mpr (Array.mem_of_getElem? pAt))
    exact ⟨v,w,.int,rfl,rfl⟩
  have slots : c.rf.spillSlots = (spillHomesAt prepared.code prepared.edges).size + maxArgsAt prepared.edges := by
    rw [allocated]; exact (spillAllocAt_storage _ _).1
  obtain ⟨nonempty,labels⟩ := stock_prepare_domain run scope
  obtain ⟨_,ss,ps,cfg⟩ := PerEdgePrep.prepareAt_cfg raw nonempty labels
  obtain ⟨T,last,_⟩ := cfg_last cfg atExecution
  have beforeTerminator : 0 ≠ vb.insts.size := by have := (back_get last).1; omega
  exact spillArgMovesAt_runs slots atRow atArgs atTarget arity classes targetShape.2 beforeTerminator stateSize

end Backend.Stock.Proof

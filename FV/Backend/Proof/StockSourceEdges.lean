module

public import FV.Backend.Proof.StockSourceDefined
public import FV.Backend.Proof.LowerCert

@[expose] public section

/-! Source definedness across actual successor entry. Parameters are defined
by successful source argument binding; inherited available values are carried
from the predecessor using the original must-availability fixed point. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Successful source successor entry preserves all available source values.
Only original SSA, actual edge/target lookup and successful source execution
are used; no new accepted-program check is introduced. -/
theorem source_defined_enterBlock {f : Clif.Function} (ssa : (valueDefs f).Nodup) (ctx : Ctx)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b)
    {fr fr' : Clif.Frame} (func : fr.func = f) {bc : Clif.BlockCall}
    (edge : bc.block ∈ succIds b.term) {tl : Nat} (index : blockIdx? f bc.block = some tl)
    (defined : SourceDefinedAt f ctx bi b.body.length fr)
    (entered : Clif.enterBlock fr bc = .ok fr') : SourceDefinedAt f ctx tl 0 fr' := by
  obtain ⟨target,args,regs,found,read,types,set,rfl⟩ := enterBlock_spec entered
  rw [func] at found
  have targetBlock := blockIdx_block index found
  have nodup := (List.nodup_append.mp (block_nodup ssa targetBlock)).1
  intro x available
  obtain ⟨present,_⟩ := (mem_av targetBlock).mp available
  rcases present with parameter | incoming | ⟨j,stm,earlier,_,_⟩
  · obtain ⟨_,value,_,_,lookup⟩ := setMany_mem set nodup x parameter
    exact ⟨value,lookup⟩
  · have fixed := inFix_fixOk (f := f) (ctx := ctx) (gn := id)
    have notParameter : x ∉ target.params.map (·.1) := by
      have absent := (fixed.cand tl x incoming).2.2.2.2.1
      rwa [parsOf_of targetBlock] at absent
    have successor : tl ∈ succIdx f bi := by
      simp only [succIdx,block]
      exact List.mem_filterMap.mpr ⟨bc.block,edge,index⟩
    have previous : x ∈ availOf f (availIn f ctx) bi b.body.length := by
      refine (mem_av block).mpr ⟨?_,?_⟩
      · rcases fixed.out tl x incoming bi successor with parameter | result | inherited
        · exact .inl (by rwa [parsOf_of block] at parameter)
        · obtain ⟨original,j,stm,originalBlock,statement,result⟩ := mem_defsOf.mp result
          cases Option.some.inj (originalBlock.symm.trans block)
          exact .inr (.inr ⟨j,stm,lt_of_getElem? statement,statement,result⟩)
        · exact .inr (.inl inherited)
      · rintro ⟨j,stm,later,statement,_⟩
        have bound := lt_of_getElem? statement
        omega
    obtain ⟨value,lookup⟩ := defined x previous
    refine ⟨value,?_⟩
    change regs x = some value
    rw [setMany_other set notParameter]
    exact lookup
  · omega

private theorem block_index_of_found {f : Clif.Function} {id : Clif.BlockId} {b : Clif.Block}
    (found : f.block? id = some b) : ∃ tl,blockIdx? f id = some tl := by
  cases index : blockIdx? f id with
  | some tl => exact ⟨tl,rfl⟩
  | none =>
    have absent : f.block? id = none := by
      simp only [Clif.Function.block?,List.find?_eq_none,Bool.not_eq_true]
      exact List.findIdx?_eq_none_iff.mp index
    rw [absent] at found
    cases found

/-- An actual successful original branch step derives its selected successor
index and entry position, preserves source memory/callers, and establishes
source definedness there. Jump, conditional and table branches share the proof. -/
theorem source_defined_branch_step {f : Clif.Function} (ssa : (valueDefs f).Nodup) (ctx : Ctx)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b)
    {env : Clif.Env} {cp : Clif.Program} {s next : Clif.State} (func : s.frame.func = f)
    (defined : SourceDefinedAt f ctx bi b.body.length s.frame) (branch : dests b.term ≠ [])
    (step : Clif.stepTerm env cp s b.term = .next next) :
    ∃ tl target, f.blocks[tl]? = some target ∧ next.frame.func = f ∧
      next.frame.body = target.body ∧ next.frame.term = target.term ∧
      SourceDefinedAt f ctx tl 0 next.frame ∧ next.mem = s.mem ∧ next.callers = s.callers := by
  obtain ⟨j,bc,fr,selected,dest,entered,nextEq⟩ := stepTerm_branch branch step
  obtain ⟨target,args,regs,found,read,types,set,frameEq⟩ := enterBlock_spec entered
  rw [func] at found
  obtain ⟨tl,index⟩ := block_index_of_found found
  have successor := edge_succ (mem_edgeIds_of_dests (List.mem_of_getElem? dest))
  have holds := source_defined_enterBlock ssa ctx block func successor index defined entered
  refine ⟨tl,target,blockIdx_block index found,?_,?_,?_,?_,?_,?_⟩
  · rw [nextEq,frameEq]; exact func
  · rw [nextEq,frameEq]
  · rw [nextEq,frameEq]
  · simpa only [nextEq] using holds
  · rw [nextEq]
  · rw [nextEq]
end Backend.Stock.Proof

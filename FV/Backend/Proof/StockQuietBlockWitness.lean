import FV.Backend.Proof.StockQuietBlockSourceRecords

namespace Backend.Stock.Proof.QuietBlockWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.lower Stock.runTerm

/-- Quiet positions in two original blocks, with a real colored division
before the demanded bmask and original successor arguments. -/
def function : Clif.Function := {
  name := "stock_quiet_original_blocks"
  sig := {params := [{ty := .i64},{ty := .i64}],returns := [{ty := .i64}]}
  blocks := [
    {id := 0,params := [(1,.i64),(6,.i64)],
      body := [⟨[100],.iconst .i64 0⟩,⟨[],.nop⟩],term := .jump ⟨10,[1,6]⟩},
    {id := 10,params := [(2,.i64),(3,.i64)],
      body := [⟨[4],.div .udiv .i64 2 3⟩,⟨[5],.bmask .i64 4⟩],term := .ret [5]}] }

private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)

private def observed (result : Except String Result) : Bool :=
  match result with
  | .error _ => false
  | .ok output => output.blockScans.any fun event =>
      event.block == 1 && event.output.records.any fun record => record.inst == 4

private theorem checked : observed (Stock.lower function) = true := by native_decide

/-- A genuine emitted/omitted scan in the second original block inhabits
the generalized metadata, whole-driver unsunkness and source-record contracts. -/
theorem actual_block_record_witness : ∃ output event record,
    Stock.lower function = .ok output ∧ LowerScope function ∧
    event ∈ output.blockScans.toList ∧ event.block = 1 ∧
    record ∈ event.output.records ∧ record.inst = 4 ∧
    output.initial.entryColor[4]! = 0 ∧ output.final.sunk[4]! = false ∧
    PureBody.SourceRecord function event.ctx event.block record := by
  have check := checked
  cases run : Stock.lower function with
  | error message => simp only [run,observed] at check; cases check
  | ok output =>
    simp only [run,observed] at check
    have any : output.blockScans.toList.any (fun event =>
        event.block == 1 && event.output.records.any (fun record => record.inst == 4)) = true := by
      simpa only [Array.any_toList] using check
    obtain ⟨event,events,found⟩ := List.any_eq_true.mp any
    simp only [Bool.and_eq_true,beq_iff_eq] at found
    obtain ⟨record,retained,index⟩ := List.any_eq_true.mp found.2
    have atIndex : record.inst = 4 := beq_iff_eq.mp index
    let b := function.blocks[1]!
    have block : function.blocks[event.block]? = some b := by rw [found.1]; rfl
    have statement : b.body[1]? = some ⟨[5],.bmask .i64 4⟩ := rfl
    have current : record.inst = blockStart function event.block+1 := by
      rw [atIndex,found.1]; rfl
    obtain ⟨original,term,body,split⟩ := stock_lower_body_scan_split run scope events
    have same : original = b := Option.some.inj (split.block.symm.trans block)
    subst original
    have ordinary : record.inst ≠ term.inst := by
      rw [atIndex,split.termInst,split.termIndex,found.1]
      decide
    have member : record ∈ body.records := by
      rw [split.records] at retained
      rcases List.mem_cons.mp retained with same | member
      · exact False.elim (ordinary (congrArg ScanRecord.inst same))
      · exact member
    have quiet : colored (Clif.Inst.bmask .i64 4) = false := rfl
    have unsunk := QuietSourceColors.stock_lower_quiet_block_unsunk run block statement quiet
    have position : blockStart function event.block+1 = 4 := current.symm.trans atIndex
    refine ⟨output,event,record,rfl,scope,events,found.1,retained,atIndex,?_,?_,?_⟩
    · simpa only [position] using unsunk.1
    · simpa only [position] using unsunk.2.1
    · exact QuietSourceColors.actual_quiet_source_record_at_block run scope events split member
        statement current quiet (by rfl)

end Backend.Stock.Proof.QuietBlockWitness

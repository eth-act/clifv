import FV.Backend.Proof.StockPureDriverUnsunk
import FV.Backend.Proof.StockCoverageRecords
import FV.Backend.Proof.StockBodyScanOrigin

/-! Ordinary pure source records derive their real scan decisions from the
complete driver. No decision/family certificate is added to the input domain. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

private theorem scans_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records, exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

/-- A successful ordinary unsunk scan always retains a concrete decision. -/
theorem stock_ordinary_unsunk_decision {ctx : Ctx} {block i ti : Nat} {branch : Bool}
    {input : State} {output : Scan} (unsunk : input.sunk[i]! = false) (ordinary : i ≠ ti)
    (run : scanInstruction ctx block i ti branch input = .ok output) :
    ∃ step, output.step = some step ∧
      (step.decision = .omitted ∨ step.decision = .opportunistic ∨ step.decision = .emitted) := by
  have emit (h : (emitInstruction ctx i (scanState input i) >>= fun e =>
      pure (e.scan block i (scanState input i))) = .ok output) :
      ∃ step, output.step = some step ∧
        (step.decision = .omitted ∨ step.decision = .opportunistic ∨ step.decision = .emitted) := by
    cases call : emitInstruction ctx i (scanState input i) with
    | error e => simp only [call,bind,Except.bind] at h; cases h
    | ok e =>
      simp only [call,bind,Except.bind,pure,Except.pure] at h
      cases h
      exact ⟨_,rfl,Or.inr (Or.inr rfl)⟩
  unfold scanInstruction at run
  have notTerm : (i == ti) = false := by simp [ordinary]
  simp only [unsunk,Bool.false_eq_true,ite_false,notTerm,Bool.false_and] at run
  split at run
  · cases run
    exact ⟨_,rfl,Or.inl rfl⟩
  · split at run
    · cases call : commitOpportunistic ctx block i (scanState input i) with
      | error e => simp only [call,bind,Except.bind] at run; cases run
      | ok result =>
        simp only [call,bind,Except.bind] at run
        cases result with
        | none => exact emit run
        | some next =>
          cases run
          exact ⟨_,rfl,Or.inr (Or.inl rfl)⟩
    · exact emit run

/-- Actual pure single-block source bodies derive emitted/omitted decisions.
Sunk paths are excluded by source metadata and the complete driver; remembered
binding is excluded by the unchanged original source scope. -/
theorem stock_lower_pure_body_decisions {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (quiet : ∀ stm ∈ b.body, colored stm.inst = false)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ term body, SourceBodySplit f event b term body ∧
      ∀ record ∈ body.records, ∃ step, record.output.step = some step ∧
        (step.decision = .omitted ∨ step.decision = .emitted) := by
  obtain ⟨source,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have bound := (List.getElem?_eq_some_iff.mp split.block).1
  rw [blocks] at bound
  have bi : event.block = 0 := by simpa using bound
  have same := split.block
  rw [bi,blocks] at same
  have same' : source = b := by simpa using same.symm
  subst source
  refine ⟨term,body,split,?_⟩
  intro record member
  obtain ⟨j,stm,statement,current⟩ := split.positions record member
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have current' : record.inst = j := by simpa [bi,blockStart] using current
  have ordinary : record.inst ≠ event.termInst := by
    rw [current',split.termIndex,bi]
    simp only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add]
    omega
  have preserved := (stock_lower_pure_single_block_unsunk run blocks quiet inside).2.2 event events
  have safe : record.input.sunk[record.inst]! = false := by
    rw [current']
    exact (preserved.2 record (split.retained record member)).1
  have actual := scans_execute split.scanned record member
  obtain ⟨step,recorded,decision⟩ := stock_ordinary_unsunk_decision safe ordinary actual
  refine ⟨step,recorded,?_⟩
  rcases decision with omitted | remembered | emitted
  · exact Or.inl omitted
  · exact False.elim ((Coverage.lower_record_noOpportunistic scope run events
      (split.retained record member) recorded) remembered)
  · exact Or.inr emitted
end Backend.Stock.Proof

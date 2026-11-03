import FV.Backend.Proof.StockAcquireReadEffectFrontier

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The exact source execution constructs captures only at actual marked source records. -/
inductive SourceReadCaptures (ctx : Ctx) (env : Clif.Env) (program : Clif.Program) :
    List ScanRecord → (Clif.Frame × Clif.Mem) → (Clif.Frame × Clif.Mem) →
      List (SunkReadSnapshot ctx env program) → Prop where
  | nil (state : Clif.Frame × Clif.Mem) : SourceReadCaptures ctx env program [] state state []
  | skipped {record : ScanRecord} {records : List ScanRecord} {before middle after : Clif.Frame × Clif.Mem}
      {captures : List (SunkReadSnapshot ctx env program)}
      (unmarked : record.input.sunk[record.inst]! = false)
      (source : SourceInstResult env program ctx record.inst before middle)
      (tail : SourceReadCaptures ctx env program records middle after captures) :
      SourceReadCaptures ctx env program (record::records) before after captures
  | captured {record : ScanRecord} {records : List ScanRecord} {before middle after : Clif.Frame × Clif.Mem}
      {captures : List (SunkReadSnapshot ctx env program)}
      (marked : record.input.sunk[record.inst]! = true)
      (source : SourceInstResult env program ctx record.inst before middle)
      (read : SourceReadFrame ctx record.inst)
      (tail : SourceReadCaptures ctx env program records middle after captures) :
      SourceReadCaptures ctx env program (record::records) before after
        (⟨record,before,middle,marked,source,read⟩::captures)

/-- Captures retain their exact original successful source steps, including every uncaptured effect. -/
theorem SourceReadCaptures.source_steps {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    {records : List ScanRecord} {before after : Clif.Frame × Clif.Mem}
    {captures : List (SunkReadSnapshot ctx env program)} (trace : SourceReadCaptures ctx env program records before after captures) :
    SourceSteps (SourceInstResult env program ctx) (records.map (·.inst)) before after := by
  induction trace with
  | nil state => exact .nil state
  | skipped unmarked source tail ih => exact .cons source ih
  | captured marked source read tail ih => exact .cons source ih

/-- The capture order equals the marked subsequence of the actual forward source records. -/
theorem SourceReadCaptures.marked_slots {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    {records : List ScanRecord} {before after : Clif.Frame × Clif.Mem}
    {captures : List (SunkReadSnapshot ctx env program)} (trace : SourceReadCaptures ctx env program records before after captures) :
    captures.map (fun captured => captured.record.inst) =
      (records.filter (fun record => record.input.sunk[record.inst]!)).map (·.inst) := by
  induction trace with
  | nil state => rfl
  | skipped unmarked source tail ih => simp only [List.filter_cons,unmarked,Bool.false_eq_true,ite_false,ih]
  | captured marked source read tail ih => simp only [List.filter_cons,marked,ite_true,List.map_cons,ih]

/-- Every captured record belongs to the actual executed source list. -/
theorem SourceReadCaptures.record_membership {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    {records : List ScanRecord} {before after : Clif.Frame × Clif.Mem}
    {captures : List (SunkReadSnapshot ctx env program)} (trace : SourceReadCaptures ctx env program records before after captures) :
    ∀ captured ∈ captures,captured.record ∈ records := by
  induction trace with
  | nil state => intro captured member;cases member
  | skipped unmarked source tail ih =>
    intro captured member
    exact List.mem_cons_of_mem _ (ih captured member)
  | captured marked source read tail ih =>
    intro captured member
    rcases List.mem_cons.mp member with same | later
    · subst captured
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih captured later)

/-- Actual lowering and source execution derive the complete capture history internally.
The list can end before a later source fault. No empty-mark assumption or external capture certificate is used. -/
theorem stock_lower_source_read_captures {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {records : List ScanRecord} (retained : ∀ record ∈ records,record ∈ event.output.records)
    {env : Clif.Env} {program : Clif.Program} {before after : Clif.Frame × Clif.Mem}
    (executed : SourceSteps (SourceInstResult env program event.ctx) (records.map (·.inst)) before after) :
    ∃ captures,SourceReadCaptures event.ctx env program records before after captures ∧
      ∀ captured ∈ captures,captured.record ∈ event.output.records := by
  induction records generalizing before with
  | nil =>
    cases executed
    exact ⟨[],.nil _,by simp⟩
  | cons record records ih =>
    cases executed with
    | cons source tail =>
      obtain ⟨captures,trace,members⟩ := ih (fun actual member => retained actual (List.mem_cons_of_mem _ member)) tail
      cases marked : record.input.sunk[record.inst]! with
      | false => exact ⟨captures,.skipped marked source trace,members⟩
      | true =>
        have actual := retained record (List.mem_cons_self ..)
        have read := stock_lower_record_marked_source_read run scope events actual record.inst marked
        refine ⟨⟨record,_,_,marked,source,read⟩::captures,.captured marked source read trace,?_⟩
        intro captured member
        rcases List.mem_cons.mp member with same | later
        · subst captured
          exact actual
        · exact members captured later

end Backend.Stock.Proof.Acquire810

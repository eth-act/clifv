import FV.Backend.Proof.StockArithmeticBodyRefines

namespace Backend.Stock.Proof.Inherited
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Values carried into a block are never redefined by its source statements.
This follows from original entry availability, including the inherited-value
fixed point, and does not depend on the current compiler demand. -/
theorem source_entry_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {record : ScanRecord} {j : Nat} {stm : Clif.Stmt}
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f event.block+j)
    {env : Clif.Env} {cp : Clif.Program} {fr fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (step : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm'))
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0) :
    ∀ x,needed x → fr'.regs x = fr.regs x := by
  obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split statement current
  obtain ⟨info',inst,vals,regs,rest,found,original,remaining,evaluated,written,updated⟩ := step
  cases Option.some.inj (found.symm.trans source)
  intro x member
  have absent : x ∉ info.results := by
    rw [results]
    intro defined
    exact ((mem_av split.block).mp (available x member)).2 ⟨j,stm,Nat.zero_le _,statement,defined⟩
  dsimp only at updated
  rw [updated]
  exact setMany_other written absent

/-- Existing available-value noninterference carries arbitrary entry values
through a real source/machine record. Fresh-write bounds are an internal code
composition interface, to be discharged by the actual emitted-rule proof. -/
theorem record_fresh_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {record : ScanRecord}
    (records : record ∈ event.output.records) {j : Nat} {stm : Clif.Stmt}
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f event.block+j)
    {env : Clif.Env} {cp : Clif.Program} {fr fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (step : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm'))
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {W : Type} {isem : ISem CV W} {ρ ρ' : Nat → CV} {w w' : W} {ms : List MInst}
    (defs : ∀ m ∈ ms,∀ key ∈ vdefs m,
      record.input.base.nextVreg ≤ key ∧ key < record.output.state.base.nextVreg)
    (executed : seqRun isem ms ρ w = some (.fall ρ' w'))
    (held : ValuesHeld needed event.ctx fr (fun k => ρ (aliasNum result.final.alias k))) :
    ValuesHeld needed event.ctx fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  have sourceFrame := source_entry_carry run events split statement current step available
  have maps := (stock_lower_record_context run scope events).2.1
  intro x member value read
  rw [sourceFrame x member] at read
  obtain ⟨key,mapped,old⟩ := held x member value read
  have preserved := stock_lower_available_fresh_frame run scope dominated events records
    split.block statement current (availOf_mono (Nat.zero_le j) (available x member))
    (by rw [← maps]; exact mapped) defs executed
  refine ⟨key,mapped,?_⟩
  change VHolds value (ρ' (aliasNum result.final.alias key))
  rw [preserved]
  exact old

/-- Original source entry values are preserved across any finite sequence of
actual body positions. Position membership is structural, independent of source
values, compiler demands and emitted machine code. -/
theorem source_steps_entry_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {env : Clif.Env} {cp : Clif.Program} {indices : List Nat} {s t : SourcePoint}
    (positions : ∀ i ∈ indices,∃ j stm,b.body[j]? = some stm ∧ i = blockStart f event.block+j)
    (steps : SourceSteps (IndexedSourceInst env cp f event.ctx event.block) indices s t) :
    ∀ x,needed x → t.2.1.regs x = s.2.1.regs x := by
  induction steps with
  | nil s => intro x member; rfl
  | @cons i indices s mid t first tail ih =>
    obtain ⟨j,stm,statement,current⟩ := positions i (List.mem_cons_self ..)
    have head := source_entry_carry run events split (record := ⟨i,default,default⟩)
      statement current first.2.2 available
    have rest := ih (fun ii inside => positions ii (List.mem_cons_of_mem _ inside))
    intro x member
    exact (rest x member).trans (head x member)

end Backend.Stock.Proof.Inherited

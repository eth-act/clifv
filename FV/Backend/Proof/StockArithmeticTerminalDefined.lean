module

public import FV.Backend.Proof.StockArithmeticSourceExecution
public import FV.Backend.Proof.StockSourceDefined

@[expose] public section

namespace Backend.Stock.Proof.ArithmeticBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem steps_cons {S : Type} {exec : Nat → S → S → Prop}
    {i : Nat} {indices : List Nat} {s t : S} (steps : SourceSteps exec (i::indices) s t) :
    ∃ middle, exec i s middle ∧ SourceSteps exec indices middle t := by
  cases steps with
  | cons head tail => exact ⟨_,head,tail⟩

/-- Original source availability stays defined through the exact source-body
sequence, using the original SSA/dominance hypotheses and actual context. -/
theorem arithmetic_steps_defined {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {env : Clif.Env} {cp : Clif.Program} {n j : Nat} {s t : SourcePoint}
    (bound : j+n ≤ b.body.length) (atStart : s.1 = j)
    (steps : SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
      (List.range' (blockStart f event.block+j) n) s t)
    (defined : SourceDefinedAt f result.ctx event.block s.1 s.2.1) :
    SourceDefinedAt f result.ctx event.block t.1 t.2.1 := by
  induction n generalizing j s with
  | zero =>
    simp only [List.range'_zero] at steps
    cases steps
    exact defined
  | succ n ih =>
    obtain ⟨middle,head,tail⟩ := steps_cons (by simpa only [List.range'_succ] using steps)
    have middlePos : middle.1 = j+1 := by
      rw [head.2.1,atStart]
    have inside : j < b.body.length := by omega
    have statement : b.body[j]? = some b.body[j] := List.getElem?_eq_getElem inside
    have before : SourceDefinedAt f result.ctx event.block j s.2.1 := by
      simpa only [atStart] using defined
    have after := stock_lower_source_defined_step run scope dominated events block statement rfl before head.2.2
    apply ih (j := j+1) (s := middle) (by omega) middlePos
    · simpa only [Nat.add_assoc] using tail
    · simpa only [middlePos] using after

/-- A successful actual reference run preserves source definedness all the way
to the original terminator, rather than assuming a terminal definition certificate. -/
theorem actual_arithmetic_terminal_defined {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    (family : ∀ stm ∈ b.body, ∃ subtract : Bool, ∃ ty x y,
      stm.inst = .binary (if subtract then .isub else .iadd) ty x y)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {s : Clif.State}
    (remaining : s.frame.body = b.body)
    (defined : SourceDefinedAt f result.ctx event.block 0 s.frame)
    {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel s = .returned vals mem) :
    ∃ t left, left+b.body.length = fuel ∧
      Clif.runLoop env cp left t = .returned vals mem ∧ t.frame.body = [] ∧
      SourceDefinedAt f result.ctx event.block b.body.length t.frame := by
  have remaining' : s.frame.body = b.body.drop 0 := by simpa using remaining
  obtain ⟨t,left,total,ends,empty,steps⟩ := actual_arithmetic_source_execution
    run events split family (j := 0) (by omega) remaining' returned
  refine ⟨t,left,by simpa using total,ends,empty,?_⟩
  apply arithmetic_steps_defined run scope dominated events split.block
    (env := env) (cp := cp) (s := (0,s.frame,s.mem)) (t := (b.body.length,t.frame,t.mem)) (j := 0) (n := b.body.length) (by omega) rfl ?_ defined
  simpa only [Nat.add_zero,Nat.sub_zero] using steps

end Backend.Stock.Proof.ArithmeticBody

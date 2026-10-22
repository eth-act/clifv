import FV.Concurrency.SegShape
import FV.Backend.Proof.DriverCheckSound
import FV.Backend.Proof.RegallocCSem
import FV.Concurrency.IselClif

/-!
# The multi-threaded scope of the lowering, checked (T2h, #311, layer 2e)

Layer 2's refinement (CLIF thread → VCode thread) needs facts about each statement's code that
semantics does not give (`SegShape`'s argument) or that the thread run needs before it knows the
CLIF outcome. They are checked on the driver's lowering, by translation validation:

* `stmtOkB inst ms`: the statement is in the multi-threaded scope (`threadInstB`: a pure
  instruction (`pureInst`), `fence`, or a little-endian `load`/`atomic_*`, a `store`/
  `atomic_store`), its code has the segment shape (`SegShape.segShape`), and every instruction of
  the code is a control form or a covered straight-line form (`FormOk`), not a call and not a
  `rets`;
* `termOkB t ms`: the terminator is a branch, a return or a trap (no `try_call`, no tail call)
  and its code has no instruction with a memory kind;
* **`threadCheck f`**: both, on the driver's lowering of `f` (as `lowerCheck` computes it);
  `obligations_of_threadCheck`: with `lowerCheck`, M7's lowering obligations for that lowering
  and the check on it.
-/

namespace Concurrency.IselCheck

open Backend Backend.Proof Backend.Proof.Driver Code SegShape

/-- `rets`. -/
def isRetsB : MInst → Bool
  | .rets _ => true
  | _ => false

/-- A call (`call`, `tryCall`). -/
def isCallB : MInst → Bool
  | .call _ | .tryCall _ _ => true
  | _ => false

/-- The statements of the multi-threaded scope: pure instructions, `fence`, and the memory
statements of `ClifThread.CStep` (loads and atomics little-endian). -/
def threadInstB : Clif.Inst → Bool
  | .load _ _ fl _ _ | .atomicLoad _ fl _ | .atomicRmw _ _ fl _ _ | .atomicCas _ fl _ _ _ =>
    !IselClif.bigOf fl
  | .store .. | .atomicStore .. | .fence => true
  | i => pureInst i

/-- One instruction of a statement's code: a control form or a covered form, not a call, not
`rets`. -/
def instOkB (i : MInst) : Bool := (i.isCtl || FormOk default i) && !isCallB i && !isRetsB i

/-- **A statement and its code** (module doc). -/
def stmtOkB (inst : Clif.Inst) (ms : List MInst) : Bool :=
  threadInstB inst && segShape inst ms && ms.all instOkB

/-- **A terminator and its code** (module doc). -/
def termOkB (t : Clif.Terminator) (ms : List MInst) : Bool :=
  !t.isTry && (match t with | .returnCall .. => false | _ => true) &&
    ms.all fun i => (akinds i).isEmpty

/-- The check on the driver's lowering `bl`. -/
def threadCheckBl (f : Clif.Function) (bl : List BLow) : Bool :=
  (f.blocks.zip bl).all fun (B, L) =>
    (B.body.zip L.sl).all (fun (stm, sl) => stmtOkB stm.inst sl.st'.emitted.toList) &&
      termOkB B.term L.tst'.emitted.toList

/-- **The per-function check**, on the driver's lowering of `f`. -/
def threadCheck (f : Clif.Function) : Bool :=
  match buildCtx f with
  | .error _ => false
  | .ok (ctx, _, st0) =>
    match lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => false
    | some bl => threadCheckBl f bl

/-- **M7's lowering obligations with the multi-threaded check** on the same lowering. -/
theorem obligations_of_threadCheck {f : Clif.Function} {vc : VCode} (h : lowerCheck f vc = true)
    (ht : threadCheck f = true) :
    ∃ ctx st0 R gn bl A, LowerShape f vc ctx st0 R gn bl ∧ Cert f ctx st0 gn bl A ∧
      (∀ B ∈ f.blocks, BrIdxTyped ctx B.term) ∧ threadCheckBl f bl = true := by
  unfold lowerCheck at h
  unfold threadCheck at ht
  split at h
  · cases h
  · rename_i ctx ranges st0 hb
    rw [hb] at ht
    simp only at ht
    split at h
    · cases h
    · rename_i bl hl
      rw [hl] at ht
      simp only [Bool.and_eq_true] at h
      have hS := lowerShape_of_ok (gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))) hb hl
        (fun n hn => gnAt_temp hn) h.1.1.1.1
      exact ⟨ctx, st0, _, _, bl, _, hS, cert_of_ok hS.len h.1.1.1.2, brIdx_of_ok h.1.1.2, ht⟩

/-- The check on one statement. -/
theorem stmtOk_of {f : Clif.Function} {bl : List BLow} (h : threadCheckBl f bl = true)
    {bi j : Nat} {B : Clif.Block} {stm : Clif.Stmt} (hB : f.blocks[bi]? = some B)
    (hstm : B.body[j]? = some stm) {L : BLow} (hL : bl[bi]? = some L) {sl : SLow}
    (hsl : L.sl[j]? = some sl) : stmtOkB stm.inst sl.st'.emitted.toList = true := by
  have h1 := all_zip_getElem h hB hL
  simp only [Bool.and_eq_true] at h1
  exact all_zip_getElem h1.1 hstm hsl

/-- The check on one terminator. -/
theorem termOk_of {f : Clif.Function} {bl : List BLow} (h : threadCheckBl f bl = true)
    {bi : Nat} {B : Clif.Block} (hB : f.blocks[bi]? = some B) {L : BLow}
    (hL : bl[bi]? = some L) : termOkB B.term L.tst'.emitted.toList = true := by
  have h1 := all_zip_getElem h hB hL
  simp only [Bool.and_eq_true] at h1
  exact h1.2

end Concurrency.IselCheck

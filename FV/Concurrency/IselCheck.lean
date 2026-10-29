module

public import FV.Concurrency.SegShape
public import FV.Backend.Proof.DriverCheckSound
public import FV.Backend.Proof.RegallocCSem
public import FV.Concurrency.IselClif

@[expose] public section

/-!
# The multi-threaded scope of the lowering, checked (T2h, #311, layer 2e)

Layer 2's refinement (CLIF thread → VCode thread) needs facts about each statement's code that
semantics does not give (`SegShape`'s argument) or that the thread run needs before it knows the
CLIF outcome. They are checked on the driver's lowering, by translation validation:

* `stmtOkB inst ms`: the statement is in the multi-threaded scope (`threadInstB`: a pure
  instruction (`pureInst`), `fence`, or a little-endian `load`/`atomic_*`, a `store`/
  `atomic_store`), its code has the segment shape (`SegShape.segShape`), every instruction of
  the code is a control form or a covered straight-line form (`FormOk`), not a call and not a
  `rets`, an `atomic_rmw`'s memory instruction is an `atomic_rmw` loop, and an `atomic_cas`'s
  loop (on integer vregs) compares with the expected value's vreg (`casOkB`);
* `termOkB t ms`: the terminator is a branch, a return or a trap (no `try_call`, no tail call)
  and its code has no instruction with a memory kind;
* **`threadCheck f`**: both, on the driver's lowering of `f` (as `lowerCheck` computes it);
  `obligations_of_threadCheck`: with `lowerCheck`, M7's lowering obligations for that lowering
  and the check on it;
* calls (#473): `callOkB stm sl`: a `call` statement whose code is exactly one direct `call`
  (a `bl`: register arguments only, no stack-argument stores, no GOT load) and whose results
  need no extra moves; **`threadCheckBlC`**/`threadCheckC`: `threadCheckBl`/`threadCheck`
  admitting such calls (`threadCheckBlC_of`, `obligations_of_threadCheckC`, `stmtOk_ofC`,
  `callOk_ofC`, `termOk_ofC`).
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

/-- An integer vreg. -/
def intV : Reg → Bool
  | .vreg _ .int => true
  | _ => false

theorem intV_eq {r : Reg} (h : intV r = true) : ∃ n, r = .vreg n .int := by
  cases r with
  | vreg n c => cases c <;> simp [intV] at h ⊢
  | _ => simp [intV] at h

/-- The atomic updates' memory instruction: an `atomic_rmw`'s is an `atomic_rmw` loop on integer
vregs (an `atomic_cas` loop has the same kinds but may skip its write), an `atomic_cas`'s is an
`atomic_cas` loop on integer vregs comparing with its expected value's own vreg (the loop's
`expect` operand): the comparison of the code is the comparison of the CLIF statement. -/
def casOkB (inst : Clif.Inst) (ms : List MInst) : Bool :=
  match inst with
  | .atomicCas _ _ _ ex _ => (memInsts ms).all fun i => match i with
    | .atomicCasLoop _ _ (.vreg _ .int) (.vreg e .int) (.vreg _ .int) (.vreg _ .int)
        (.vreg _ .int) => e == ex
    | _ => false
  | .atomicRmw .. => (memInsts ms).all fun i => match i with
    | .atomicRmwLoop _ _ _ a x d r1 r2 => intV a && intV x && intV d && intV r1 && intV r2
    | _ => false
  | _ => true

/-- **A statement and its code** (module doc). -/
def stmtOkB (inst : Clif.Inst) (ms : List MInst) : Bool :=
  threadInstB inst && segShape inst ms && ms.all instOkB && casOkB inst ms

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

/-! ## Calls (#473) -/

/-- **A call statement and its code** (module doc): a `call` whose code is one direct `call`,
its results in the call's output vregs. -/
def callOkB (stm : Clif.Stmt) (sl : SLow) : Bool :=
  (match stm.inst with | .call .. => true | _ => false) &&
    (match sl.st'.emitted.toList with
      | [.call ⟨.sym _, _, _⟩] => true
      | _ => false) &&
    (extraOf stm.results sl.rss).isEmpty

/-- **The check admitting calls**, on the driver's lowering `bl`. -/
def threadCheckBlC (f : Clif.Function) (bl : List BLow) : Bool :=
  (f.blocks.zip bl).all fun (B, L) =>
    (B.body.zip L.sl).all (fun (stm, sl) => stmtOkB stm.inst sl.st'.emitted.toList || callOkB stm sl) &&
      termOkB B.term L.tst'.emitted.toList

/-- **The per-function check admitting calls**, on the driver's lowering of `f`. -/
def threadCheckC (f : Clif.Function) : Bool :=
  match buildCtx f with
  | .error _ => false
  | .ok (ctx, _, st0) =>
    match lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => false
    | some bl => threadCheckBlC f bl

theorem threadCheckBlC_of {f : Clif.Function} {bl : List BLow} (h : threadCheckBl f bl = true) :
    threadCheckBlC f bl = true := by
  unfold threadCheckBl at h
  unfold threadCheckBlC
  rw [List.all_eq_true] at h ⊢
  intro x hx
  have h1 := h x hx
  simp only [Bool.and_eq_true, List.all_eq_true] at h1 ⊢
  exact ⟨fun y hy => by simp [h1.1 y hy], h1.2⟩

/-- **M7's lowering obligations with the check admitting calls** on the same lowering. -/
theorem obligations_of_threadCheckC {f : Clif.Function} {vc : VCode} (h : lowerCheck f vc = true)
    (ht : threadCheckC f = true) :
    ∃ ctx st0 R gn bl A, LowerShape f vc ctx st0 R gn bl ∧ Cert f ctx st0 gn bl A ∧
      (∀ B ∈ f.blocks, BrIdxTyped ctx B.term) ∧ threadCheckBlC f bl = true := by
  unfold lowerCheck at h
  unfold threadCheckC at ht
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

theorem stmtOkC_of {f : Clif.Function} {bl : List BLow} (h : threadCheckBlC f bl = true)
    {bi j : Nat} {B : Clif.Block} {stm : Clif.Stmt} (hB : f.blocks[bi]? = some B)
    (hstm : B.body[j]? = some stm) {L : BLow} (hL : bl[bi]? = some L) {sl : SLow}
    (hsl : L.sl[j]? = some sl) :
    (stmtOkB stm.inst sl.st'.emitted.toList || callOkB stm sl) = true := by
  have h1 := all_zip_getElem h hB hL
  simp only [Bool.and_eq_true] at h1
  exact all_zip_getElem h1.1 hstm hsl

/-- The check admitting calls on a statement other than a call. -/
theorem stmtOk_ofC {f : Clif.Function} {bl : List BLow} (h : threadCheckBlC f bl = true)
    {bi j : Nat} {B : Clif.Block} {stm : Clif.Stmt} (hB : f.blocks[bi]? = some B)
    (hstm : B.body[j]? = some stm) {L : BLow} (hL : bl[bi]? = some L) {sl : SLow}
    (hsl : L.sl[j]? = some sl) (hnc : ∀ fn args, stm.inst ≠ .call fn args) :
    stmtOkB stm.inst sl.st'.emitted.toList = true := by
  have h1 := stmtOkC_of h hB hstm hL hsl
  have hc : callOkB stm sl = false := by
    unfold callOkB
    cases hi : stm.inst <;> simp
    exact absurd hi (hnc _ _)
  rw [hc, Bool.or_false] at h1
  exact h1

/-- The check admitting calls on a call. -/
theorem callOk_ofC {f : Clif.Function} {bl : List BLow} (h : threadCheckBlC f bl = true)
    {bi j : Nat} {B : Clif.Block} {stm : Clif.Stmt} (hB : f.blocks[bi]? = some B)
    (hstm : B.body[j]? = some stm) {L : BLow} (hL : bl[bi]? = some L) {sl : SLow}
    (hsl : L.sl[j]? = some sl) {fn : Clif.FnRef} {args : List Clif.ValueId}
    (hc : stm.inst = .call fn args) : callOkB stm sl = true := by
  have h1 := stmtOkC_of h hB hstm hL hsl
  have hs : stmtOkB stm.inst sl.st'.emitted.toList = false := by
    simp [stmtOkB, threadInstB, hc, pureInst]
  rw [hs, Bool.false_or] at h1
  exact h1

/-- The check admitting calls on a terminator. -/
theorem termOk_ofC {f : Clif.Function} {bl : List BLow} (h : threadCheckBlC f bl = true)
    {bi : Nat} {B : Clif.Block} (hB : f.blocks[bi]? = some B) {L : BLow}
    (hL : bl[bi]? = some L) : termOkB B.term L.tst'.emitted.toList = true := by
  have h1 := all_zip_getElem h hB hL
  simp only [Bool.and_eq_true] at h1
  exact h1.2

end Concurrency.IselCheck

import FV.Backend.Regalloc
import FV.Backend.Proof.RelaxReady

/-!
# Emission readiness of regalloc2's allocation (V6b)

regalloc2 is an untrusted oracle: `checkAlloc` validates its allocation, but an accepted
allocation can still give code that does not lay out — e.g. any number of redundant moves (a
callee-save store repeated) passes the checker, so the function can exceed the 128 MiB reach of
`b`. The backend therefore keeps regalloc2's lowered function only if its emitted code passes
`FnAsm.layoutReadyB` (`emitReady`), and otherwise lowers the spill allocation, whose emission is
proven ready for in-scope input (`E2E.backend_correct_final_total_emit`).

* `lowerAllocReady vcp ra`: `lowerAlloc vcp ra` if that is emittable, else the spill allocation.
* `allocateRegalloc2`: the backend's regalloc2 driver, lowering with `lowerAllocReady`.
* `readyAnswer vcp ra`: the answer `lowerAlloc` is effectively given (`ra`, or none);
  `lowerAllocReady_eq`: `lowerAllocReady vcp ra = lowerAlloc vcp (readyAnswer vcp ra)`, so every
  theorem about `lowerAlloc` applies.
-/

namespace Backend

/-- The emitted code of `af` passes `layoutReadyB` (the function index only names labels in
the assembly text, so index 0 decides it for every index: `E2E.emitPre_index`). -/
def emitReady (af : AFunc) : Bool :=
  match emitFunc 0 af with
  | .ok fa => fa.layoutReadyB
  | .error _ => false

/-- `lowerAlloc`, falling back to the spill allocation when the lowered function is not
`emitReady`. -/
def lowerAllocReady (vcp : VCode) (ra : Except String RFunc) : Except String AFunc :=
  match lowerAlloc vcp ra with
  | .ok af => if emitReady af then .ok af else lowerRFunc vcp (spillAlloc vcp)
  | .error e => .error e

/-- The allocator answer `lowerAllocReady` lowers: `ra` if `lowerAlloc`'s function of it is
`emitReady`, else none (so the spill allocation). -/
def readyAnswer (vcp : VCode) (ra : Except String RFunc) : Except String RFunc :=
  match lowerAlloc vcp ra with
  | .ok af => if emitReady af then ra else .error "allocation not emittable (emitReady)"
  | .error e => .error e

/-- Allocate a batch of functions with regalloc2 (one `lean-regalloc` run); every result is
checked by `checkAlloc`, and a rejected, unlowerable or missing allocation (regalloc2 failed, or
is absent) is replaced by the spill allocation (`lowerAlloc`), and so is one whose emitted code
is not `emitReady` (`lowerAllocReady`). -/
def allocateRegalloc2 (bin : String) (env : MachineEnv) (vcs : Array VCode) : IO (Array (Except String AFunc)) := do
  let prepared := vcs.map prepareChecked
  let ok := prepared.filterMap (·.toOption)
  let rs : Array (Except String RFunc) ← do
    try
      match ← runLeanRegalloc bin env ok with
      | .error e => pure (ok.map fun _ => .error e)
      | .ok rs => pure (rs.map (·.bind RAResult.oracle))
    catch e => pure (ok.map fun _ => .error (toString e))
  let mut out : Array (Except String AFunc) := #[]
  let mut j := 0
  for p in prepared do
    match p with
    | .error e => out := out.push (.error e)
    | .ok vcp =>
      out := out.push (lowerAllocReady vcp (rs[j]?.getD (.error "lean-regalloc: missing result")))
      j := j + 1
  pure out

/-- `lowerAlloc` fails only if the spill allocation does not lower. -/
theorem lowerAlloc_error {vcp : VCode} {ra : Except String RFunc} {e : String}
    (h : lowerAlloc vcp ra = .error e) : lowerRFunc vcp (spillAlloc vcp) = .error e := by
  unfold lowerAlloc at h
  cases ra with
  | error _ => exact h
  | ok rf =>
    simp only at h
    split at h
    · split at h
      · cases h
      · exact h
    · exact h

theorem lowerAllocReady_eq (vcp : VCode) (ra : Except String RFunc) :
    lowerAllocReady vcp ra = lowerAlloc vcp (readyAnswer vcp ra) := by
  unfold lowerAllocReady readyAnswer
  cases h : lowerAlloc vcp ra with
  | ok af =>
    simp only
    split
    · exact h.symm
    · rfl
  | error e =>
    simp only [lowerAlloc]
    exact (lowerAlloc_error h).symm

end Backend

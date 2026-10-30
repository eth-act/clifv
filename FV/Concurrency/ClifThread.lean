import FV.Concurrency.Program
import FV.Clif.Run

/-!
# Multi-threaded CLIF (T2e, #303)

* **`MTStep env p`, the multi-threaded `Clif.run`**: threads (`TState`: running `Clif.State`, or
  returned values) share the byte memory; a step of thread `i` is `Clif.step` on its state with
  the shared bytes, and the bytes it leaves are the new shared bytes. Allocation metadata
  (`allocs`, `next`, symbols) stays per thread: threads share the memory valid at their start
  (the program image and what the spawner allocated), and their stack slots are private.
* **`CStep env p`, the event semantics of one CLIF thread** (for executions and the memory model):
  a step of `Clif.step` labelled with the memory events of its statement (`evShape`: a `load` its
  `naR` read, a `store` its `naW` write, `atomic_load`/`atomic_store` an `scR`/`scW` access,
  `atomic_rmw`/a successful `atomic_cas` an `scR` read and an `scW` write, `fence` a `fence`
  event, every other statement none; sizes the access sizes), which are its **footprint**: on
  every byte memory holding the read events' bytes the step writes exactly the write events and
  reaches the same state (up to the bytes, `strip`). With the sizes fixed, the footprint pins the
  addresses: a step's events are exactly its accesses. Statements without events must neither
  read nor write the shared bytes (an extern call that touches memory has no step: such threads
  are outside the multi-threaded semantics). `tls_value` gives every thread the image's instance.
* `mrun_mt`: runs of the interleaving machine of `CStep` (`Prog.MRun`) are runs of `MTStep`.

Plan: `docs/plans/atomics.md` (T2e).
-/

namespace Concurrency.ClifThread

open Prog

/-- CLIF's byte memory. -/
abbrev Bytes := Nat → Option (BitVec 8)

/-- The value of an access: its bytes. -/
abbrev BVal := List (Option (BitVec 8))

/-- The `n` bytes at `l`. -/
def getB (B : Bytes) (l n : Nat) : BVal := (List.range n).map fun k => B (l + k)

/-- `B` with the `n` bytes at `l` set to `v`. -/
def putB (B : Bytes) (l n : Nat) (v : BVal) : Bytes :=
  fun a => if l ≤ a ∧ a < l + n then v.getD (a - l) none else B a

/-- The byte memory as a `Prog.MemI`. -/
def bytesI : MemI Bytes BVal where
  get := getB
  put := putB
  ok n v := v.length = n
  get_put_same M l n v hv := by
    apply List.ext_getElem
    · simp [getB, hv]
    · intro k h1 h2
      simp only [getB, List.getElem_map, List.getElem_range, putB]
      have hin : l ≤ l + k ∧ l + k < l + n := ⟨Nat.le_add_right _ _, by simp [getB] at h1; omega⟩
      simp only [hin, and_self, ite_true]
      simp [List.getD_eq_getElem?_getD, show l + k - l = k by omega, h2]
  get_put_disj M l n v l' n' h := by
    simp only [getB, putB]
    apply List.map_congr_left
    intro k hk
    have := List.mem_range.mp hk
    have hout : ¬ (l ≤ l' + k ∧ l' + k < l + n) := by omega
    simp only [hout, ite_false]

/-- A CLIF thread: running, or returned with values. -/
inductive TState where
  | run (s : Clif.State)
  | ret (vals : List Clif.Val)

/-- The CLIF state `s` with the byte memory `B`. -/
def withBytes (s : Clif.State) (B : Bytes) : Clif.State :=
  { s with mem := { s.mem with bytes := B } }

/-- A thread state without its bytes. -/
def strip : TState → TState
  | .run s => .run (withBytes s fun _ => none)
  | .ret v => .ret v

/-- The thread state and bytes after a step (`none`: trapped or stuck). -/
def res : Clif.StepResult → Option (TState × Bytes)
  | .next s => some (.run s, s.mem.bytes)
  | .done vals mem => some (.ret vals, mem.bytes)
  | _ => none

/-- The events the statement about to run may have, as lists of (kind, size): a load its read,
a store its write, `atomic_load`/`atomic_store` their access, `atomic_rmw` its read and write,
`atomic_cas` its read (comparison failed) or its read and write, `fence` its `fence` event, every
other statement (and terminator) none. -/
def evShape (s : Clif.State) : List (List (SKind × Nat)) :=
  match s.frame.body with
  | st :: _ => match st.inst with
    | .load op ty .. => [[(.naR, op.size ty)]]
    | .store op ty .. => [[(.naW, op.size ty)]]
    | .atomicLoad ty .. => [[(.scR, ty.bytes)]]
    | .atomicStore ty .. => [[(.scW, ty.bytes)]]
    | .atomicRmw _ ty .. => [[(.scR, ty.bytes), (.scW, ty.bytes)]]
    | .atomicCas ty .. => [[(.scR, ty.bytes)], [(.scR, ty.bytes), (.scW, ty.bytes)]]
    | .fence => [[(.fence, 0)]]
    | _ => [[]]
  | [] => [[]]

/-- The events have the statement's shape, their kinds' directions and values of their sizes. -/
def KindsOk (s : Clif.State) (evs : List (Ev SKind BVal)) : Prop :=
  evs.map (fun e => (e.k, e.n)) ∈ evShape s ∧ ∀ e ∈ evs, e.dir = e.k.dir ∧ e.val.length = e.n

/-- **One step of a CLIF thread with its events**: the events are the step's footprint. -/
def CStep (env : Clif.Env) (p : Clif.Program) : TSem TState SKind BVal := fun t evs t' =>
  match t with
  | .ret _ => False
  | .run s => KindsOk s evs ∧ (∃ B, Agrees bytesI B evs) ∧
      ∀ B, Agrees bytesI B evs → ∃ t'', res (Clif.step env p (withBytes s B)) =
        some (t'', applyEvs bytesI B evs) ∧ strip t'' = strip t'

/-- `ts` and `ts'` agree up to the threads' bytes. -/
def StripEq (ts ts' : Nat → TState) : Prop := ∀ i, strip (ts i) = strip (ts' i)

/-- **The multi-threaded `Clif.run`**: a step of one thread on the shared bytes. -/
inductive MTStep (env : Clif.Env) (p : Clif.Program) :
    (Nat → TState) × Bytes → (Nat → TState) × Bytes → Prop
  | mk {ts : Nat → TState} {B B' : Bytes} {i : Nat} {s : Clif.State} {t' : TState} :
      ts i = .run s → res (Clif.step env p (withBytes s B)) = some (t', B') →
      MTStep env p (ts, B) (upd ts i t', B')

/-- Runs of the multi-threaded `Clif.run`. -/
inductive MTRun (env : Clif.Env) (p : Clif.Program) :
    (Nat → TState) × Bytes → (Nat → TState) × Bytes → Prop
  | refl {c} : MTRun env p c c
  | tail {c c' c''} : MTRun env p c c' → MTStep env p c' c'' → MTRun env p c c''

theorem withBytes_withBytes (s : Clif.State) (B B' : Bytes) :
    withBytes (withBytes s B) B' = withBytes s B' := rfl

theorem withBytes_strip {s s' : Clif.State} (h : strip (.run s) = strip (.run s')) (B : Bytes) :
    withBytes s B = withBytes s' B := by
  simp only [strip, TState.run.injEq] at h
  rw [← withBytes_withBytes s (fun _ => none), h, withBytes_withBytes]

theorem stripEq_upd {ts ts' : Nat → TState} (h : StripEq ts ts') (i : Nat) {t t' : TState}
    (ht : strip t = strip t') : StripEq (upd ts i t) (upd ts' i t') := by
  intro j; simp only [upd]; split
  · exact ht
  · exact h j

/-- **Runs of the interleaving machine of the CLIF event semantics are runs of the
multi-threaded `Clif.run`** (the same shared bytes, the threads up to their local bytes). -/
theorem mrun_mt {env : Clif.Env} {p : Clif.Program} {c c' : (Nat → TState) × Bytes}
    (h : MRun bytesI (CStep env p) c c') :
    ∃ ts, MTRun env p c (ts, c'.2) ∧ StripEq ts c'.1 := by
  induction h with
  | refl => exact ⟨_, .refl, fun _ => rfl⟩
  | tail _ hs ih =>
    obtain ⟨ts, hrun, heq⟩ := ih
    cases hs with
    | @mk ts1 B i es s' hT hag =>
      simp only at hrun heq ⊢
      rcases hti : ts1 i with s | v
      · rw [hti] at hT
        obtain ⟨-, -, hfp⟩ := hT
        obtain ⟨t'', hres, hst⟩ := hfp B hag
        have hsi := heq i
        rw [hti] at hsi
        rcases hts : ts i with s2 | v2
        · rw [hts] at hsi
          have e := withBytes_strip hsi B
          refine ⟨upd ts i t'', .tail hrun (.mk hts ?_), stripEq_upd heq i hst⟩
          rw [e]; exact hres
        · rw [hts] at hsi; cases hsi
      · rw [hti] at hT; exact hT.elim

end Concurrency.ClifThread

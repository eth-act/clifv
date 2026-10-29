module

public import FV.E2E.LinkPlace

@[expose] public section

/-!
# The valid memory across a callee's CLIF run (#473, step (3))

`CallArity.resume_allA` resumes a caller after its callee returned and asks (`hval`) that every
range valid in the memory the callee returns (its slots freed, `Mem.leave`) was valid in the
caller's memory at the call. The callee's run is a contiguous piece of the thread's CLIF run,
from the caller's call (the caller at depth `n`: `n` suspended frames) to the return back to
depth `n`; the callee's own calls push and pop frames above. Here, along the lines of
`Clif.AllocInv` (`E2E/LinkPlace.lean`, which tracks every frame):

* `slotBasesAbove n s`: the slot bases of the frames of `s` above depth `n`;
* `AllocInvD cm n s`: every allocation of `s` lies within `cm`'s valid ranges or is a slot of a
  frame above depth `n`;
* `allocInvD_self`: at depth `n` itself, any state with `cm` its own memory;
* **`allocInvD_step`**: every step of a `LinkFree` program (calls push a frame with its slots,
  returns free the returning frame's slots, the externs keep allocations) that stays at depth
  `n` or above keeps it;
* **`allocInvD_run`**: the same along `Clif.step` runs;
* **`valid_of_allocInvD`**: back at depth `n`, every valid range is valid in `cm` — the
  premise `hval` of `resume_allA` with `cm` the caller's memory at the call.

Witness: `allocInvD_ret_witness` (a frame with one slot above depth 0 returning).
-/

namespace Concurrency.CallValid

open Clif

/-- The slot bases of a list of frames. -/
def basesOf (l : List Frame) : List Nat := l.flatMap fun fr => fr.slots.map (·.2)

/-- **The slot bases of the frames of `s` above depth `n`** (the running frame and the
suspended ones but the bottom `n`). -/
def slotBasesAbove (n : Nat) (s : State) : List Nat :=
  basesOf ((s.frame :: s.callers.map (·.1)).take (s.callers.length + 1 - (n + 1)))

/-- **The allocations of a state of a callee's run from the caller's memory `cm` at depth
`n`**: within `cm`'s valid ranges, or slots of frames above depth `n`. -/
def AllocInvD (cm : Mem) (n : Nat) (s : State) : Prop :=
  ∀ x ∈ s.mem.allocs, (∀ a k, x.contains a k = true → cm.valid a k = true) ∨
    x.base ∈ slotBasesAbove n s

theorem basesOf_take_succ (fr : Frame) (l : List Frame) (c : Nat) :
    basesOf ((fr :: l).take (c + 1)) = fr.slots.map (·.2) ++ basesOf (l.take c) := by
  simp [basesOf, List.take_succ_cons, List.flatMap_cons]

theorem basesOf_take_congr {fr fr' : Frame} (h : fr'.slots = fr.slots) (l : List Frame) (c : Nat) :
    basesOf ((fr' :: l).take c) = basesOf ((fr :: l).take c) := by
  cases c with
  | zero => rfl
  | succ c => rw [basesOf_take_succ, basesOf_take_succ, h]

/-- At depth `n` itself, a state's allocations are valid in its own memory. -/
theorem allocInvD_self (s : State) (n : Nat) : AllocInvD s.mem n s := fun x hx =>
  .inl fun a k hc => List.any_eq_true.mpr ⟨x, hx, hc⟩

/-- **A step at depth `n` or above keeps `AllocInvD`** (module doc). -/
theorem allocInvD_step {P p : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (hk : EnvKeepsAllocs env) {cm : Mem} {n : Nat} {s s1 : State} (hI : LInv P s)
    (hp : AllocInvD cm n s) (h : step env p s = .next s1) (hn : n ≤ s.callers.length)
    (hn1 : n ≤ s1.callers.length) : AllocInvD cm n s1 := by
  rcases step_next_cases hP hI h with ⟨hc, hsl, ⟨-, hal⟩ | ⟨nm, g, vals, rv, hg, hr⟩⟩ |
      ⟨c, hc, hcs, g, vals, he⟩ | ⟨c, hc, hsl, hm⟩
  · have e : slotBasesAbove n s1 = slotBasesAbove n s := by
      simp only [slotBasesAbove, hc]
      exact basesOf_take_congr hsl _ _
    intro x hx
    rw [hal] at hx
    rw [e]
    exact hp x hx
  · have e : slotBasesAbove n s1 = slotBasesAbove n s := by
      simp only [slotBasesAbove, hc]
      exact basesOf_take_congr hsl _ _
    intro x hx
    rw [e]
    exact hp x (hk nm g hg vals s.mem rv s1.mem hr x hx)
  · obtain ⟨_, _, _, _, _, _, hal, -⟩ := Opt.enterFunc_ok he
    have e : slotBasesAbove n s1 =
        s1.frame.slots.map (·.2) ++ slotBasesAbove n s := by
      simp only [slotBasesAbove, hc, List.map_cons, List.length_cons]
      rw [show s.callers.length + 1 + 1 - (n + 1) = (s.callers.length + 1 - (n + 1)) + 1 by omega,
        basesOf_take_succ, basesOf_take_congr hcs]
    intro x hx
    have := enterSlots_allocs g s.mem x
    rw [hal] at this
    rw [e, List.mem_append]
    rcases this hx with h1 | h1
    · rcases hp x h1 with h2 | h2
      · exact .inl h2
      · exact .inr (.inr h2)
    · exact .inr (.inl h1)
  · have e : slotBasesAbove n s =
        s.frame.slots.map (·.2) ++ slotBasesAbove n s1 := by
      simp only [slotBasesAbove, hc, List.map_cons, List.length_cons]
      rw [show s1.callers.length + 1 + 1 - (n + 1) = (s1.callers.length + 1 - (n + 1)) + 1 by omega,
        basesOf_take_succ, basesOf_take_congr hsl]
    intro x hx
    rw [hm, Mem.leave_allocs] at hx
    simp only [Mem.free, List.mem_filter, Bool.not_eq_true'] at hx
    obtain ⟨hx, hnb⟩ := hx
    rcases hp x hx with h1 | h1
    · exact .inl h1
    · rw [e, List.mem_append] at h1
      rcases h1 with h1 | h1
      · exact absurd h1 (by simpa using hnb)
      · exact .inr h1

/-- **`AllocInvD` along a run of `Clif.step`** staying at depth `n` or above (the frames
reached in between keep `LInv`). -/
theorem allocInvD_run {P p : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (hk : EnvKeepsAllocs env) (hpP : ∀ g ∈ p.funcs, g ∈ P.funcs) {cm : Mem} {n : Nat} :
    ∀ (sts : List State) (s : State), LInv P s → AllocInvD cm n s → n ≤ s.callers.length →
      (∀ i (h : i < sts.length), step env p ((s :: sts)[i]'(by simp; omega)) = .next sts[i] ∧
        n ≤ sts[i].callers.length) →
      ∀ s' ∈ sts, AllocInvD cm n s'
  | [], _, _, _, _, _ => fun _ h => absurd h List.not_mem_nil
  | s1 :: sts, s, hI, hp, hn, hst => by
    obtain ⟨h0, hn1⟩ := hst 0 (by simp)
    simp only [List.getElem_cons_zero] at h0 hn1
    have hp1 := allocInvD_step hP hk hI hp h0 hn hn1
    have hI1 := (step_next_linv hP hI h0 hpP).1
    intro s' hs'
    rcases List.mem_cons.mp hs' with rfl | hs'
    · exact hp1
    · exact allocInvD_run hP hk hpP sts s1 hI1 hp1 hn1 (fun i hi => by
        have := hst (i + 1) (by simp; omega)
        simpa using this) s' hs'

/-- **Back at depth `n`, the valid ranges are `cm`'s** (`resume_allA`'s `hval`). -/
theorem valid_of_allocInvD {cm : Mem} {n : Nat} {s : State} (hp : AllocInvD cm n s)
    (hd : s.callers.length = n) : ∀ a k, s.mem.valid a k = true → cm.valid a k = true := by
  intro a k hv
  obtain ⟨x, hx, hc⟩ := List.any_eq_true.mp hv
  rcases hp x hx with h1 | h1
  · exact h1 a k hc
  · simp [slotBasesAbove, hd, basesOf] at h1

end Concurrency.CallValid

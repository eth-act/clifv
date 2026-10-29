module

public import FV.E2E.LinkArmPlaceB

@[expose] public section

/-! # The slot-byte counter at an activation's `n`-th call (SEM1, `docs/plans/uninit.md` §5.5)

The CLIF-side invariant of the count correspondence: an activation of `h` entered from a memory
placed with the slot-byte oracle `ini` (counter `j0 = ini.next`) has, after its first `n` calls
(call `k` advancing the counter by `E k`, the callee run's count, `crun_nextAdv`), the counter
`j0 + slotted? + Σ_{k<n} E k` (`counter_at`). The advance of a step is unique (`NextAdv.unique`),
so `E k` is determined by the memories. -/

namespace Clif

/-- `Σ_{k<n} E k`. -/
def sumTo (E : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo E n + E n

/-- The advance between two memories is unique when the first has a slot-byte oracle. -/
theorem NextAdv.unique {m m' : Mem} {e e' : Nat} (h : NextAdv m m' e) (h' : NextAdv m m' e')
    {pl : Place} {ini : SlotInit} (hp : m.place = some pl) (hi : pl.init = some ini) : e = e' := by
  have h1 := h pl ini hp hi
  rw [h' pl ini hp hi] at h1
  simp only [Option.some.injEq, Place.mk.injEq, SlotInit.adv, SlotInit.mk.injEq] at h1
  omega

/-- **A chain of advances adds up**: memories `m 0, …, m n`, step `k` advancing by `E k`. -/
theorem nextAdv_chain (m : Nat → Mem) (E : Nat → Nat) :
    ∀ n, (∀ k < n, NextAdv (m k) (m (k + 1)) (E k)) → NextAdv (m 0) (m n) (sumTo E n)
  | 0, _ => NextAdv.of_place rfl
  | n + 1, h =>
    (nextAdv_chain m E n fun k hk => h k (Nat.lt_succ_of_lt hk)).trans (h n (Nat.lt_succ_self n))

end Clif

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)

/-- Placed activations with slots count `1`. -/
def slotted (h : Clif.Function) : Nat := if h.slots.isEmpty then 0 else 1

/-- **The counter at the activation's `n`-th call**: `h` entered from `cm` (`PlaceAtB cm c ini`)
at `cs`, and memories `m 0 = cs.mem, …, m n` along its run, step `k` advancing by `E k`: the
memory `m n` is placed at `h`'s `sp` with the counter `ini.next + slotted h + Σ_{k<n} E k`. -/
theorem counter_at {h : Clif.Function} {n : String} (hpf : L.P.func? n = some h)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State}
    (hinit : Clif.initState L.P n vals cm = .ok cs) {c : BitVec 64} {ini : Clif.SlotInit}
    (hpB : L.PlaceAtB cm c ini) (m : Nat → Clif.Mem) (E : Nat → Nat) (hm0 : m 0 = cs.mem)
    (N : Nat) (hE : ∀ k < N, Clif.NextAdv (m k) (m (k + 1)) (E k)) :
    L.PlaceAtB (m N) (c - BitVec.ofNat 64 (frameDrop (L.A h).af))
      (ini.adv (slotted h + Clif.sumTo E N)) := by
  obtain ⟨-, -, -, -, hpl⟩ := L.initState_memB hpf hinit hpB
  have hch := Clif.nextAdv_chain m E N hE
  rw [hm0] at hch
  have h1 : L.PlaceAtB cs.mem (c - BitVec.ofNat 64 (frameDrop (L.A h).af)) (ini.adv (slotted h)) := by
    unfold slotted
    by_cases hs : h.slots.isEmpty
    · simp only [hs, ↓reduceIte] at hpl ⊢; exact hpl
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hpl ⊢; exact hpl
  have := h1.adv hch
  rwa [Clif.SlotInit.adv_adv] at this

end LinkSys

end E2E

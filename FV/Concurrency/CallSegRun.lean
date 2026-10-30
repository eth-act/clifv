import FV.Concurrency.CallSegOkG
import FV.Concurrency.CallEntryRel

/-!
# The allocations of an activation's CLIF run (#473, the frame-padding gap)

A callee's start-dirty set has to cover its frame padding (the slot area outside its placed
slots) and the parts of its caller's private set outside its own: no CLIF read of the callee's
segments may start there. A CLIF event is at valid memory (`CallSegGeo.cstep_reads_valid`); here
the valid memory of every state of an activation's own CLIF run (from a state `S` whose memory is
`m0`, the activation's frame on top, its oracle stack pointer `spB` on top of the slot-placement
oracle) is bounded:

* `PlaceOk p fr M`: the oracle's frames of the program's functions drop at most `M` bytes and
  hold their slots;
* **`SegInv`**: the state's frames (`LInv`), the oracle's stack pointers of the frames above the
  activation (each at most `M` bytes per level below `spB`, `SpsOk`), and every allocation either
  within `m0`'s valid ranges or in the `K` bytes below `spB` (the activation's dead stack);
* **`segInv_step`**: a `Clif.step` keeps `SegInv` when the next state's depth stays within the
  budget (`depth * M ≤ K ≤ spB`): a callee's slots are placed below its caller's stack pointer,
  without wrapping;
* **`segInv_crun`**: along a `CRun` of the activation from `S` (below callers `ext`, its lifted
  states reachable, and every reachable state's call depth below `Dcap`), every memory event lies in
  `m0`'s valid ranges or in the dead stack.
-/

namespace Concurrency.CallSegRun

open Clif ClifThread ClifCStepTerm ClifLift CallSegOkG Prog

/-- **The oracle's frames of the program** (module doc). -/
def PlaceOk (p : Program) (fr : String → Option (Nat × (SlotId → Nat))) (M : Nat) : Prop :=
  ∀ g ∈ p.funcs, ∃ d off, fr g.name = some (d, off) ∧ d ≤ M ∧
    ∀ q ∈ g.slots, off q.1 + q.2.size ≤ d

/-- The oracle's stack pointers above the activation, innermost first: the `i`-th at most
`(l.length - i) * M` bytes below `spB`, and not above it. -/
def SpsOk (spB : BitVec 64) (M : Nat) (l : List (BitVec 64)) : Prop :=
  ∀ i (h : i < l.length), spB.toNat ≤ l[i].toNat + (l.length - i) * M ∧ l[i].toNat ≤ spB.toNat

/-- **The run invariant of an activation** (module doc). -/
structure SegInv (p : Program) (fr : String → Option (Nat × (SlotId → Nat))) (M : Nat)
    (spB : BitVec 64) (sps0 : List (BitVec 64)) (K : Nat) (m0 : Mem) (S : State) : Prop where
  linv : LInv p S
  place : ∃ l, S.mem.place = some ⟨l ++ spB :: sps0, fr, none⟩ ∧
    l.length = S.callers.length ∧ SpsOk spB M l
  allocs : ∀ x ∈ S.mem.allocs, (∀ a k, x.contains a k = true → m0.valid a k = true) ∨
    (spB.toNat ≤ x.base + K ∧ x.base + x.size ≤ spB.toNat)

variable {p : Program} {fr : String → Option (Nat × (SlotId → Nat))} {M : Nat} {spB : BitVec 64}
  {sps0 : List (BitVec 64)} {K : Nat} {m0 : Mem}

/-- At the start of a segment (depth `0`, memory `m0`). -/
theorem segInv_start {S : State} (hI : LInv p S) (hc : S.callers = [])
    (hpl : S.mem.place = some ⟨spB :: sps0, fr, none⟩) :
    SegInv p fr M spB sps0 K S.mem S :=
  ⟨hI, ⟨[], hpl, by rw [hc]; rfl, fun i h => absurd h (Nat.not_lt_zero _)⟩,
    fun x hx => .inl fun a k hc => List.any_eq_true.mpr ⟨x, hx, hc⟩⟩

/-- `SegInv` does not depend on the bytes. -/
theorem segInv_withBytes {S : State} {B : Bytes} :
    SegInv p fr M spB sps0 K m0 (withBytes S B) ↔ SegInv p fr M spB sps0 K m0 S :=
  ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-- **A step keeps `SegInv`** (module doc). -/
theorem segInv_step (hP : ∀ g ∈ p.funcs, LinkFree g) {env : Env} (hk : EnvKeepsAllocs env)
    (hkp : EnvKeepsPlace env) (hpo : PlaceOk p fr M) (hKs : K ≤ spB.toNat) {S S1 : State}
    (hI : SegInv p fr M spB sps0 K m0 S) (h : step env p S = .next S1)
    (hd : S1.callers.length * M ≤ K) : SegInv p fr M spB sps0 K m0 S1 := by
  have hI1 := (step_next_linv hP hI.linv h).1
  obtain ⟨l, hpl, hlen, hsps⟩ := hI.place
  rcases step_next_cases hP hI.linv h with ⟨hc, -, ⟨hp1, hal⟩ | ⟨n, g, vals, rv, hg, hr⟩⟩ |
      ⟨c, hc, -, g, vals, he⟩ | ⟨c, hc, -, hm⟩
  · exact ⟨hI1, ⟨l, by rw [hp1, hpl], by rw [hc, hlen], hsps⟩,
      fun x hx => hI.allocs x (hal ▸ hx)⟩
  · exact ⟨hI1, ⟨l, by rw [hkp n g hg vals S.mem rv S1.mem hr, hpl], by rw [hc, hlen], hsps⟩,
      fun x hx => hI.allocs x (hk n g hg vals S.mem rv S1.mem hr x hx)⟩
  · -- a call: the callee's slots placed below the caller's stack pointer
    obtain ⟨b, regs, -, -, -, -, hal, hfr⟩ := Opt.enterFunc_ok he
    have hg : g ∈ p.funcs := by
      have := hI1.1.1
      rw [hfr] at this
      exact this
    obtain ⟨d, off, hgd, hdM, hfit⟩ := hpo g hg
    rw [hc] at hd
    simp only [List.length_cons] at hd
    -- the innermost stack pointer
    obtain ⟨top, rest, htop, htb, hle⟩ : ∃ top rest, l ++ spB :: sps0 = top :: rest ∧
        spB.toNat ≤ top.toNat + l.length * M ∧ top.toNat ≤ spB.toNat := by
      cases l with
      | nil => exact ⟨spB, sps0, rfl, by omega, Nat.le_refl _⟩
      | cons y l' =>
        obtain ⟨h1, h2⟩ := hsps 0 (by simp)
        exact ⟨y, l' ++ spB :: sps0, rfl, by simpa using h1, h2⟩
    rw [htop] at hpl
    obtain ⟨-, -, hal', -, hpl'⟩ := CallEntryRel.enterSlots_at (f := g) hpl hgd
    rw [hal] at hal' hpl'
    have hlenM : (l.length + 1) * M ≤ K := by rw [hlen]; exact hd
    have hdtop : d ≤ top.toNat := by
      have : l.length * M + M ≤ K := by rw [Nat.succ_mul] at hlenM; exact hlenM
      omega
    have hsub : (top - BitVec.ofNat 64 d).toNat = top.toNat - d := by
      have hd64 : d < 2 ^ 64 := by have := top.isLt; omega
      rw [BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd64]; exact hdtop),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd64]
    refine ⟨hI1, ⟨(top - BitVec.ofNat 64 d) :: l, ?_, ?_, ?_⟩, fun x hx => ?_⟩
    · rw [hpl', ← htop]; rfl
    · simp [hc, hlen]
    · intro i hi
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero, List.length_cons, Nat.sub_zero, hsub]
        constructor
        · rw [Nat.add_mul, Nat.one_mul] at *; omega
        · omega
      | succ i =>
        simp only [List.getElem_cons_succ, List.length_cons]
        have := hsps i (by simp at hi; omega)
        rwa [show l.length + 1 - (i + 1) = l.length - i by omega]
    · rcases hal' x hx with hx' | ⟨q, hq, rfl⟩
      · exact hI.allocs x hx'
      · right
        have := hfit q hq
        simp only [hsub]
        constructor
        · rw [Nat.add_mul, Nat.one_mul] at hlenM; omega
        · omega
  · -- a return: the callee's slots freed, the oracle popped
    rw [hc] at hlen
    obtain ⟨y, l', rfl⟩ : ∃ y l', l = y :: l' := by
      cases l with
      | nil => simp at hlen
      | cons y l' => exact ⟨y, l', rfl⟩
    refine ⟨hI1, ⟨l', ?_, by simpa using hlen, fun i hi => ?_⟩, fun x hx => ?_⟩
    · rw [hm]
      simp only [Mem.leave, Mem.free, hpl, List.cons_append, List.tail_cons]
    · have := hsps (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ, List.length_cons] at this
      rwa [show l'.length + 1 - (i + 1) = l'.length - i by omega] at this
    · rw [hm, Mem.leave_allocs] at hx
      simp only [Mem.free, List.mem_filter] at hx
      exact hI.allocs x hx.1

/-- A `CStep` between running states is a `Clif.step` on some bytes, up to the target's bytes. -/
theorem cstep_next {env : Env} {S S1 : State} {evs : List (Ev SKind BVal)}
    (h : CStep env p (.run S) evs (.run S1)) :
    ∃ B S1', step env p (withBytes S B) = .next S1' ∧ withBytes S1' (fun _ => none) =
      withBytes S1 (fun _ => none) := by
  obtain ⟨-, ⟨B, hB⟩, hf⟩ := h
  obtain ⟨t'', h1, h2⟩ := hf B hB
  cases hs : step env p (withBytes S B) with
  | next S1' =>
    rw [hs] at h1
    simp only [res, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, -⟩ := h1
    simp only [strip, TState.run.injEq] at h2
    exact ⟨B, S1', hs, h2⟩
  | done v m =>
    rw [hs] at h1
    simp only [res, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, -⟩ := h1
    simp [strip] at h2
  | trapped c => rw [hs] at h1; cases h1
  | stuck m => rw [hs] at h1; cases h1

/-- `SegInv` is a property of a state up to its bytes. -/
theorem segInv_congr {S S' : State}
    (h : withBytes S (fun _ => none) = withBytes S' (fun _ => none)) :
    SegInv p fr M spB sps0 K m0 S → SegInv p fr M spB sps0 K m0 S' := by
  intro hI
  have e1 : S.frame = S'.frame := congrArg (·.frame) h
  have e2 : S.callers = S'.callers := congrArg (·.callers) h
  have e3 : S.mem.allocs = S'.mem.allocs := congrArg (·.mem.allocs) h
  have e4 : S.mem.place = S'.mem.place := congrArg (·.mem.place) h
  obtain ⟨hl, ⟨l, hp, hlen, hs⟩, ha⟩ := hI
  refine ⟨⟨e1 ▸ hl.1, fun c hc => hl.2 c (e2 ▸ hc)⟩, ⟨l, e4 ▸ hp, e2 ▸ hlen, hs⟩,
    fun x hx => ha x (e3 ▸ hx)⟩

/-- **The memory events of an activation's run** (module doc): in `m0`'s valid ranges or in the
`K` bytes below `spB`. -/
theorem segInv_crun (hP : ∀ g ∈ p.funcs, LinkFree g) {env : Env} (hk : EnvKeepsAllocs env)
    (hkp : EnvKeepsPlace env) (hpo : PlaceOk p fr M) (hKs : K ≤ spB.toNat) {c0 : TState}
    {Dcap : Nat} (hdep : ∀ S, RReach env p c0 (.run S) → S.callers.length < Dcap)
    {ext : List (Frame × List ValueId)} (hbud : (Dcap - ext.length) * M ≤ K) :
    ∀ {S : State} {trS : List (List (Ev SKind BVal))} {t : TState},
      CRun env p (.run S) trS t → RReach env p c0 (.run (pushC ext S)) →
      SegInv p fr M spB sps0 K m0 S →
      ∀ evs ∈ trS, ∀ x ∈ evs, x.dir ≠ .F →
        m0.valid x.loc x.n = true ∨ (spB.toNat ≤ x.loc + K ∧ x.loc + x.n ≤ spB.toNat)
  | _, _, _, .nil, _, _ => fun _ h => absurd h List.not_mem_nil
  | S, _, _, .cons (t' := t1) hs r, hR, hI => by
    intro evs hevs x hx hd
    rcases List.mem_cons.mp hevs with rfl | hevs
    · have hv := CallSegGeo.cstep_reads_valid hs x hx hd
      simp only [Mem.valid, List.any_eq_true] at hv
      obtain ⟨y, hy, hcy⟩ := hv
      rcases hI.allocs y hy with h1 | ⟨h1, h2⟩
      · exact .inl (h1 _ _ hcy)
      · right
        simp only [Alloc.contains, Bool.and_eq_true, decide_eq_true_eq] at hcy
        omega
    · cases t1 with
      | ret v => cases r with
        | nil => cases hevs
        | cons h' _ => exact absurd h' (by intro h; exact h)
      | run S1 =>
        have hR1 : RReach env p c0 (.run (pushC ext S1)) := hR.step (cstep_pushC hs)
        obtain ⟨B, S1', hst, he⟩ := cstep_next hs
        have hd1 : S1.callers.length * M ≤ K := by
          have := hdep _ hR1
          simp only [pushC, List.length_append] at this
          have h2 : S1.callers.length ≤ Dcap - ext.length - 1 := by omega
          calc S1.callers.length * M ≤ (Dcap - ext.length - 1) * M := Nat.mul_le_mul_right _ h2
            _ ≤ (Dcap - ext.length) * M := Nat.mul_le_mul_right _ (by omega)
            _ ≤ K := hbud
        have hd1' : S1'.callers.length * M ≤ K := by
          have : S1'.callers = S1.callers := congrArg (·.callers) he
          rw [this]; exact hd1
        have hI1 : SegInv p fr M spB sps0 K m0 S1 :=
          segInv_congr he (segInv_step hP hk hkp hpo hKs (segInv_withBytes.mpr hI) hst hd1')
        exact segInv_crun hP hk hkp hpo hKs hdep hbud r hR1 hI1 evs hevs x hx hd

end Concurrency.CallSegRun

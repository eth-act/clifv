module

public import FV.E2E.LinkArm
public import FV.E2E.LinkPlaceB

@[expose] public section

/-! # The linked system's slot-placement oracle with the slot-byte oracle (SEM1)

`LinkSys.PlaceAt` pins `init = none`. With the slot-byte oracle on (`docs/plans/uninit.md` §5.5:
the byte table is the machine memory at each placed activation with slots, in the order the
whole run enters them), a memory is placed at `c` with the oracle `ini` (`PlaceAtB`). The callee
runs of a linked system (`crun M`, `CrunOk`) advance its counter, by the number of placed
activations with slots they enter (`crun_adv`, `crun_nextAdv`), when the base externs keep the
oracle (`Ok.baseKeepsPlace`, needed only with slots). -/

namespace Clif

/-- **A returning whole-program run of an entry advances the counter** (`R` the runs of `P`
under `base`, e.g. a linked system's `crun M`): from the entry of `n` on `vals` in `cm`, a
returning `R` gives back `cm`'s oracle with the counter advanced by some `e`. -/
theorem runsOf_nextAdv {P : Program} {base : Env} {R : State → Outcome} (hR : RunsOf base P R)
    (hP : ∀ g ∈ P.funcs, LinkFree g) (hk : EnvAdv base) {n : String} {vals : List Val}
    {cm : Mem} {cs : State} {rvals : List Val} {cm' : Mem} (hi : initState P n vals cm = .ok cs)
    (hr : R cs = .returned rvals cm') : ∃ e, NextAdv cm cm' e := by
  obtain ⟨g, hg⟩ : ∃ g, P.func? n = some g := by
    cases h : P.func? n with
    | some g => exact ⟨g, rfl⟩
    | none => simp [initState, h] at hi
  refine linkEnvR_adv hR hP hk n _ (linkEnvR_some (base := base) (R := R) hg) vals cm rvals cm' ?_
  simp only [hi]
  exact hr

/-- The bytes after `fillSlots`: a filled slot byte is the table's, any other is the former. -/
theorem fillSlots_bytes (sp : BitVec 64) (off : SlotId → Nat) (b : Nat → BitVec 8) :
    ∀ (slots : List (SlotId × StackSlot)) (m : Mem) (a : Nat) (x : BitVec 8),
    (fillSlots slots sp off b m).bytes a = some x →
      (∃ p ∈ slots, sp.toNat + off p.1 ≤ a ∧ a < sp.toNat + off p.1 + p.2.size ∧ x = b a) ∨
      m.bytes a = some x
  | [], m, a, x, h => .inr h
  | q :: qs, m, a, x, h => by
    simp only [fillSlots, List.foldl_cons] at h
    rcases fillSlots_bytes sp off b qs _ a x h with ⟨p, hp, hr⟩ | h'
    · exact .inl ⟨p, List.mem_cons_of_mem _ hp, hr⟩
    · simp only [Mem.fillAt] at h'
      split at h'
      · rename_i hin
        exact .inl ⟨q, List.mem_cons_self .., hin.1, hin.2, (Option.some.inj h').symm⟩
      · exact .inr h'

theorem fillSlots_fields (slots : List (SlotId × StackSlot)) (sp : BitVec 64) (off : SlotId → Nat)
    (b : Nat → BitVec 8) (m : Mem) :
    (fillSlots slots sp off b m).allocs = m.allocs ∧ (fillSlots slots sp off b m).symbols = m.symbols ∧
      (fillSlots slots sp off b m).place = m.place := by
  obtain ⟨bytes, h⟩ := fillSlots_eq slots sp off b m
  rw [h]
  exact ⟨rfl, rfl, rfl⟩

end Clif

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)

/-- The CLIF memory's oracle has the running activation's stack pointer `c`, the program's frames
and the slot-byte oracle `ini`. -/
def PlaceAtB (cm : Clif.Mem) (c : BitVec 64) (ini : Clif.SlotInit) : Prop :=
  ∃ sps, cm.place = some ⟨c :: sps, L.frames, some ini⟩

/-- `PlaceAtB` is `PlaceAt` with the slot-byte oracle in place of `none`. -/
theorem placeAtB_iff (cm : Clif.Mem) (c : BitVec 64) (ini : Clif.SlotInit) :
    L.PlaceAtB cm c ini ↔ ∃ sps, cm.place = some ⟨c :: sps, L.frames, some ini⟩ := Iff.rfl

/-- The advanced oracle is placed at the same stack pointer. -/
theorem PlaceAtB.adv {L : LinkSys} {cm cm' : Clif.Mem} {c : BitVec 64} {ini : Clif.SlotInit}
    {e : Nat} (h : L.PlaceAtB cm c ini) (ha : Clif.NextAdv cm cm' e) :
    L.PlaceAtB cm' c (ini.adv e) := by
  obtain ⟨sps, hp⟩ := h
  exact ⟨sps, ha _ ini hp rfl⟩

/-- **The callee runs' linked environment advances the slot-byte counter** when the base
externs keep the oracle. -/
theorem crun_advK [L.CrunOk] (hfree : ∀ g ∈ L.P.funcs, Clif.LinkFree g)
    (hk : Clif.EnvKeepsPlace L.base) (M : Nat) :
    Clif.EnvAdv (Clif.linkEnvR L.P L.base (L.crun M)) :=
  Clif.linkEnvR_adv (CrunOk.runs M) hfree (Clif.envAdv_of_keepsPlace hk)

/-- `crun_advK` for a linked system that is `Ok` and has a program callee with slots. -/
theorem crun_adv (hL : L.Ok) [L.CrunOk] (hN : L.NeedSlots) (M : Nat) :
    Clif.EnvAdv (Clif.linkEnvR L.P L.base (L.crun M)) :=
  L.crun_advK hL.free (hL.baseKeepsPlace hN) M

/-- **A returning callee run advances the counter**: from the entry of `n` on `vals` in `cm`,
a returning `crun M` gives back `cm`'s oracle with the counter advanced by some `e`. -/
theorem crun_nextAdv [L.CrunOk] (hfree : ∀ g ∈ L.P.funcs, Clif.LinkFree g)
    (hk : Clif.EnvKeepsPlace L.base) {M : Nat} {n : String}
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem} (hi : Clif.initState L.P n vals cm = .ok cs)
    (hr : L.crun M cs = .returned rvals cm') : ∃ e, Clif.NextAdv cm cm' e :=
  Clif.runsOf_nextAdv (CrunOk.runs M) hfree (Clif.envAdv_of_keepsPlace hk) hi hr

/-- **The entry of a program function under the slot-byte oracle** (`initState_mem` with
`PlaceAtB` for `PlaceAt`): the same slots, symbols and allocations; an initialised byte of the
entry memory is either the caller memory's outside the new slots, or in a new slot and the byte
table's entry `ini.next + 1` (the activation is the `ini.next + 1`-th placed one with slots);
the entry memory is placed at the callee's `sp` with the counter advanced by `1` (by `0`
without slots). -/
theorem initState_memB {h : Clif.Function} {n : String} (hpf : L.P.func? n = some h)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State}
    (hinit : Clif.initState L.P n vals cm = .ok cs) {c : BitVec 64} {ini : Clif.SlotInit}
    (hpB : L.PlaceAtB cm c ini) :
    cs.frame.slots = h.slots.map (fun p => (p.1,
      (c - BitVec.ofNat 64 (frameDrop (L.A h).af)).toNat +
        ((L.A h).af.slotBase + ((slotLayout h.slots).1.lookup p.1).getD 0))) ∧
    cs.mem.symbols = cm.symbols ∧
    (∀ x ∈ cs.mem.allocs, x ∈ cm.allocs ∨ ∃ p ∈ h.slots,
      x = ⟨(c - BitVec.ofNat 64 (frameDrop (L.A h).af)).toNat +
        ((L.A h).af.slotBase + ((slotLayout h.slots).1.lookup p.1).getD 0), p.2.size, false⟩) ∧
    (∀ a b, cs.mem.bytes a = some b →
      (cm.bytes a = some b ∧ ∀ p ∈ h.slots,
        ¬ ((c - BitVec.ofNat 64 (frameDrop (L.A h).af)).toNat +
            ((L.A h).af.slotBase + ((slotLayout h.slots).1.lookup p.1).getD 0) ≤ a ∧
          a < (c - BitVec.ofNat 64 (frameDrop (L.A h).af)).toNat +
            ((L.A h).af.slotBase + ((slotLayout h.slots).1.lookup p.1).getD 0) + p.2.size)) ∨
      (∃ p ∈ h.slots,
        (c - BitVec.ofNat 64 (frameDrop (L.A h).af)).toNat +
            ((L.A h).af.slotBase + ((slotLayout h.slots).1.lookup p.1).getD 0) ≤ a ∧
          a < (c - BitVec.ofNat 64 (frameDrop (L.A h).af)).toNat +
            ((L.A h).af.slotBase + ((slotLayout h.slots).1.lookup p.1).getD 0) + p.2.size ∧
        b = ini.bytes (ini.next + 1) a)) ∧
    L.PlaceAtB cs.mem (c - BitVec.ofNat 64 (frameDrop (L.A h).af))
      (if h.slots.isEmpty then ini else ini.adv 1) := by
  obtain ⟨hh, rfl⟩ := Clif.Program.func?_some hpf
  simp only [Clif.initState, hpf, Clif.Res.ofOption_some, Clif.Res.ok_bind] at hinit
  cases he : Clif.enterFunc h vals cm with
  | trap => rw [he] at hinit; cases hinit
  | stuck => rw [he] at hinit; cases hinit
  | ok r =>
    obtain ⟨fr, mem'⟩ := r
    rw [he] at hinit
    simp only [Clif.Res.ok_bind, Clif.Res.pure_eq, Clif.Res.ok.injEq] at hinit
    subst hinit
    obtain ⟨_, _, _, _, _, _, hal, -⟩ := Opt.enterFunc_ok he
    simp only
    obtain ⟨sps, hcp⟩ := hpB
    let sp := c - BitVec.ofNat 64 (frameDrop (L.A h).af)
    let off : Clif.SlotId → Nat :=
      fun id => (L.A h).af.slotBase + ((slotLayout h.slots).1.lookup id).getD 0
    let acc : List (Clif.SlotId × Nat) × Clif.Mem :=
      ([], { cm with place := some ⟨sp :: c :: sps, L.frames, some ini⟩ })
    have hfr : L.frames h.name = some (frameDrop (L.A h).af, off) := by simp [frames, hpf, off]
    have e : Clif.enterSlots h cm =
        Clif.initSlots h.slots sp off (some ini) (h.slots.foldl (Clif.placeStep sp off) acc) := by
      simp only [Clif.enterSlots, hcp, hfr, List.headD]
      rfl
    obtain ⟨h1, h2, h3, h4⟩ := Clif.placeSlots_spec sp off h.slots acc
    have h5 : (h.slots.foldl (Clif.placeStep sp off) acc).2.place = acc.2.place :=
      (Clif.placeSlots_facts sp off h.slots acc).1
    rw [e] at hal
    by_cases hs : h.slots.isEmpty
    · simp only [Clif.initSlots, hs, ↓reduceIte] at hal
      have hs1 := congrArg Prod.fst hal
      have hs2 := congrArg Prod.snd hal
      simp only at hs1 hs2
      rw [hs1] at h1
      rw [hs2] at h2 h3 h4 h5
      refine ⟨h1.trans (List.nil_append _), h2, h3, fun a b hb => .inl (h4 a b hb),
        ⟨c :: sps, ?_⟩⟩
      rw [h5]
      simp only [hs, ↓reduceIte]
      rfl
    · simp only [Clif.initSlots, hs, ↓reduceIte, Bool.false_eq_true, Prod.mk.injEq] at hal
      obtain ⟨hs1, hs2⟩ := hal
      rw [hs1] at h1
      obtain ⟨fa, fs, fp⟩ := Clif.fillSlots_fields h.slots sp off (ini.bytes ini.succ.next)
        { (h.slots.foldl (Clif.placeStep sp off) acc).2 with
          place := (h.slots.foldl (Clif.placeStep sp off) acc).2.place.map (Clif.Place.advance ini) }
      rw [hs2] at fa fs fp
      refine ⟨h1.trans (List.nil_append _), fs.trans h2, fun x hx => h3 x (fa ▸ hx),
        fun a b hb => ?_, ⟨c :: sps, ?_⟩⟩
      · rw [← hs2] at hb
        rcases Clif.fillSlots_bytes sp off _ h.slots _ a b hb with ⟨p, hp, hlo, hhi, rfl⟩ | hb'
        · exact .inr ⟨p, hp, hlo, hhi, rfl⟩
        · exact .inl (h4 a b hb')
      · rw [fp, h5]
        simp only [acc, Option.map_some, hs, Bool.false_eq_true, ↓reduceIte, Clif.Place.advance,
          Clif.SlotInit.succ_eq_adv]
        rfl

end LinkSys

end E2E

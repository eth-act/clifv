import FV.E2E.LinkArmProgCallPRB

/-!
# The popped entry of an activation (SEM1 #537, #694)

`ThmPRBRL` states the counter advance from `cs.mem.leave`, the entry memory with the activation's
stack pointer popped. For an entry `cs` of `h` from a caller memory `cm` placed at `c` with the
oracle `ini`, that is `cm`'s oracle with the counter advanced by `h`'s own placed activation
(`calleeIni`):

* `initState_place`: the exact oracle of the entry (`initState_memB`'s `PlaceAtB` with the
  caller's stack pointers named);
* **`initState_leave_nextAdv`**: `NextAdv cm cs.mem.leave (if h.slots.isEmpty then 0 else 1)`;
* `NextAdv.cancel`: advances from a common memory subtract, so the caller-level advance of a
  returning callee run (`runsOf_nextAdv`) gives the one from the popped entry.
-/

namespace Clif

theorem NextAdv.cancel {m m₁ m₂ : Mem} {e₁ e₂ : Nat} (h₁ : NextAdv m m₁ e₁)
    (h₂ : NextAdv m m₂ e₂) {pl : Place} {ini : SlotInit} (hp : m.place = some pl)
    (hi : pl.init = some ini) (hle : e₁ ≤ e₂) : NextAdv m₁ m₂ (e₂ - e₁) := by
  intro pl' ini' hp' hi'
  rw [h₁ pl ini hp hi] at hp'
  cases hp'
  simp only [Option.some.injEq] at hi'
  subst hi'
  rw [h₂ pl ini hp hi, SlotInit.adv_adv, Nat.add_sub_cancel' hle]

end Clif

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)

/-- **The oracle of an entry**: `h`'s body `sp` pushed on the caller's stack pointers, the
counter advanced by `h`'s own placed activation (`calleeIni`). -/
theorem initState_place {h : Clif.Function} {n : String} (hpf : L.P.func? n = some h)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State}
    (hinit : Clif.initState L.P n vals cm = .ok cs) {c : BitVec 64} {sps : List (BitVec 64)}
    {ini : Clif.SlotInit} (hcp : cm.place = some ⟨c :: sps, L.frames, some ini⟩) :
    cs.mem.place = some ⟨(c - BitVec.ofNat 64 (frameDrop (L.A h).af)) :: c :: sps, L.frames,
      some (calleeIni h ini)⟩ := by
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
    have h5 : (h.slots.foldl (Clif.placeStep sp off) acc).2.place = acc.2.place :=
      (Clif.placeSlots_facts sp off h.slots acc).1
    rw [e] at hal
    by_cases hs : h.slots.isEmpty
    · simp only [Clif.initSlots, hs, ↓reduceIte] at hal
      have hs2 := congrArg Prod.snd hal
      simp only at hs2
      rw [hs2] at h5
      rw [h5]
      simp only [calleeIni, hs, ↓reduceIte]
      rfl
    · simp only [Clif.initSlots, hs, ↓reduceIte, Bool.false_eq_true, Prod.mk.injEq] at hal
      obtain ⟨-, hs2⟩ := hal
      obtain ⟨-, -, fp⟩ := Clif.fillSlots_fields h.slots sp off (ini.bytes ini.succ.next)
        { (h.slots.foldl (Clif.placeStep sp off) acc).2 with
          place := (h.slots.foldl (Clif.placeStep sp off) acc).2.place.map (Clif.Place.advance ini) }
      rw [hs2] at fp
      rw [fp, h5]
      simp only [acc, Option.map_some, calleeIni, hs, Bool.false_eq_true, ↓reduceIte,
        Clif.Place.advance, Clif.SlotInit.succ_eq_adv]
      rfl

/-- **The popped entry is the caller's memory with `h`'s own activation counted** (#694). -/
theorem initState_leave_nextAdv {h : Clif.Function} {n : String} (hpf : L.P.func? n = some h)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State}
    (hinit : Clif.initState L.P n vals cm = .ok cs) {c : BitVec 64} {ini : Clif.SlotInit}
    (hpB : L.PlaceAtB cm c ini) :
    Clif.NextAdv cm cs.mem.leave (if h.slots.isEmpty then 0 else 1) := by
  obtain ⟨sps, hcp⟩ := hpB
  intro pl ini' hp hi
  rw [hcp] at hp
  cases hp
  cases hi
  have hpl := L.initState_place hpf hinit hcp
  simp only [Clif.Mem.leave, hpl, List.tail_cons, calleeIni]
  split <;> rfl

end LinkSys

end E2E

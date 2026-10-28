import FV.E2E.LinkArm
import FV.E2E.LinkPlaceB

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

end Clif

namespace E2E

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

end LinkSys

end E2E

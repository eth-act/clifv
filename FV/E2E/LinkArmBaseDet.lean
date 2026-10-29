module

public import FV.E2E.LinkArm

@[expose] public section

/-!
# Determinism of the base hooks on the dead stack (SEM1 step 2o, `docs/plans/uninit.md` §5.7)

Prophecy determinism (two runs of one activation have the same prophecy) needs the base hooks
`L.Hb.call`/`L.Hb.tls` (externs outside `P`, TLS) to leave the two runs' machine states equal
wherever they were equal: `CalleeOk`/`baseNI` constrain only the world (unmasked registers,
memory outside `F`), not the scratch registers and the bytes the extern leaves below `sp`.

* `StEqOut Z s t`: same registers and program, same memory outside `Z` (`refl`, `symm`, `trans`,
  `mono`);
* `HookDet Hb BD`: from two states equal outside a set `Z` of dead stack bytes (strictly below
  the state's `sp`: AAPCS64 has no red zone, so no callee reads them before writing them), a base
  call (`BD d`) or a TLS hook gives states equal outside `Z`;
* `OkD`: `Ok` plus `HookDet L.Hb L.BaseDest` under `NeedNI` (as `baseNI`); `OkD.ok`,
  `Ok.okD_of_not_needNI` (without non-interference it is `Ok`), `hookDet_id`.
-/

namespace E2E

open Backend Backend.Proof

/-- **Equal but for the memory in `Z`**: same registers, program, and memory outside `Z`. -/
def StEqOut (Z : BitVec 64 → Prop) (s t : Arm.ArmState) : Prop :=
  (∀ f, Arm.r f s = Arm.r f t) ∧ s.program = t.program ∧ ∀ a, ¬ Z a → s.mem a = t.mem a

theorem StEqOut.refl (Z : BitVec 64 → Prop) (s : Arm.ArmState) : StEqOut Z s s :=
  ⟨fun _ => rfl, rfl, fun _ _ => rfl⟩

theorem StEqOut.symm {Z : BitVec 64 → Prop} {s t : Arm.ArmState} (h : StEqOut Z s t) :
    StEqOut Z t s :=
  ⟨fun f => (h.1 f).symm, h.2.1.symm, fun a ha => (h.2.2 a ha).symm⟩

theorem StEqOut.trans {Z : BitVec 64 → Prop} {s t u : Arm.ArmState} (h : StEqOut Z s t)
    (h' : StEqOut Z t u) : StEqOut Z s u :=
  ⟨fun f => (h.1 f).trans (h'.1 f), h.2.1.trans h'.2.1,
    fun a ha => (h.2.2 a ha).trans (h'.2.2 a ha)⟩

theorem StEqOut.mono {Z Z' : BitVec 64 → Prop} {s t : Arm.ArmState} (h : StEqOut Z s t)
    (hZ : ∀ a, Z a → Z' a) : StEqOut Z' s t :=
  ⟨h.1, h.2.1, fun a ha => h.2.2 a fun h' => ha (hZ a h')⟩

/-- **The base hooks are deterministic on the dead stack**: from two states equal but for bytes
`Z` strictly below `sp`, a call of a destination `BD d` and a TLS hook give states equal but for
`Z`. -/
def HookDet (Hb : ArmHooks) (BD : Option String → Prop) : Prop :=
  (∀ d, BD d → ∀ (Z : BitVec 64 → Prop) (s t : Arm.ArmState), StEqOut Z s t →
      (∀ a, Z a → a.toNat < (spv s).toNat) → StEqOut Z (Hb.call d s) (Hb.call d t)) ∧
    (∀ n r (Z : BitVec 64 → Prop) (s t : Arm.ArmState), StEqOut Z s t →
      (∀ a, Z a → a.toNat < (spv s).toNat) → StEqOut Z (Hb.tls n r s) (Hb.tls n r t))

/-- The hooks that change nothing are deterministic. -/
theorem hookDet_id (BD : Option String → Prop) :
    HookDet ⟨fun _ s => s, fun _ _ s => s⟩ BD :=
  ⟨fun _ _ _ _ _ h _ => h, fun _ _ _ _ _ h _ => h⟩

namespace LinkSys

variable (L : LinkSys)

/-- **The premises of the linked program with deterministic base hooks**: `Ok`, and (needed only
with non-interference, as `baseNI`) `HookDet` of the base hooks at the base destinations. -/
structure OkD : Prop extends L.Ok where
  baseDet : L.NeedNI → HookDet L.Hb L.BaseDest

theorem OkD.ok {L : LinkSys} (h : L.OkD) : L.Ok := h.toOk

/-- **Without non-interference, `OkD` is `Ok`.** -/
theorem Ok.okD_of_not_needNI {L : LinkSys} (hL : L.Ok) (hN : ¬ L.NeedNI) : L.OkD :=
  { hL with baseDet := fun h => absurd h hN }

/-- `OkD` from `Ok` and deterministic base hooks. -/
theorem Ok.okD {L : LinkSys} (hL : L.Ok) (hD : HookDet L.Hb L.BaseDest) : L.OkD :=
  { hL with baseDet := fun _ => hD }

end LinkSys

end E2E

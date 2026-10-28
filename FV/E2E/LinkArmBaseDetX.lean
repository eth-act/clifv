import FV.E2E.LinkArmBaseDet
import FV.E2E.LinkArmStepX30

/-!
# Base hooks that do not observe return addresses (SEM1, `docs/plans/uninit.md` §5.9, step 3n)

In the lock-step of prophecy determinism the two runs of one activation differ in `x30` until
its first call, and in the saved-LR bytes of its frame record for the whole activation (the
canonical entry returns to `raStar`, the actual one to its call site). A base extern (outside the
program) is called from such states. `HookDet` (step 2o) assumes all registers equal and
differences only strictly below `sp`, so it does not apply. Decided (conservative, a trusted
premise beside `OkD.baseDet`, needed only with non-interference):

* `fpChain s n`: the frame-record chain (AAPCS64 §6.2.3: `x29` points at a record whose first
  word is the caller's `x29`);
* `LRByte s a`: `a` is one of the 8 saved-LR bytes of a record of the chain;
* `HookDetX Hb BD`: from two states equal but for `x30` and bytes `Z` that are below `sp` or
  saved-LR bytes, a base call (`BD d`) and a TLS hook give states equal but for `x30` and `Z`:
  the extern does not observe return addresses (an unwinder that takes a backtrace does; such an
  extern is outside this premise);
* `OkDX`: `OkD` plus `HookDetX L.Hb L.BaseDest` under `NeedNI`; `OkDX.okD`,
  `Ok.okDX_of_not_needNI`, `Ok.okDX`, `hookDetX_id`.
-/

namespace E2E

open Backend Backend.Proof

/-- **The frame-record chain** of `s`: `x29`, then the first word of each record. -/
def fpChain (s : Arm.ArmState) : Nat → BitVec 64
  | 0 => Arm.r (.GPR 29#5) s
  | n + 1 => Arm.read_mem_bytes 8 (fpChain s n) s

/-- **A saved-LR byte** of a frame record of `s`'s chain. -/
def LRByte (s : Arm.ArmState) (a : BitVec 64) : Prop :=
  ∃ n k, k < 8 ∧ a = fpChain s n + 8#64 + BitVec.ofNat 64 k

/-- **The base hooks do not observe return addresses**: from two states equal but for `x30` and
bytes `Z` below `sp` or saved-LR bytes (of the second state's chain), a call of a destination
`BD d` and a TLS hook give states equal but for `x30` and `Z`. -/
def HookDetX (Hb : ArmHooks) (BD : Option String → Prop) : Prop :=
  (∀ d, BD d → ∀ (Z : BitVec 64 → Prop) (s t : Arm.ArmState), StEqOutX Z s t →
      (∀ a, Z a → a.toNat < (spv t).toNat ∨ LRByte t a) →
      StEqOutX Z (Hb.call d s) (Hb.call d t)) ∧
    (∀ n r (Z : BitVec 64 → Prop) (s t : Arm.ArmState), StEqOutX Z s t →
      (∀ a, Z a → a.toNat < (spv t).toNat ∨ LRByte t a) →
      StEqOutX Z (Hb.tls n r s) (Hb.tls n r t))

/-- The hooks that change nothing do not observe return addresses. -/
theorem hookDetX_id (BD : Option String → Prop) :
    HookDetX ⟨fun _ s => s, fun _ _ s => s⟩ BD :=
  ⟨fun _ _ _ _ _ h _ => h, fun _ _ _ _ _ h _ => h⟩

namespace LinkSys

variable (L : LinkSys)

/-- **The premises of the linked program with base hooks that are deterministic and do not
observe return addresses**: `OkD`, and (under `NeedNI`, as `baseNI`/`baseDet`) `HookDetX`. -/
structure OkDX : Prop extends L.OkD where
  baseDetX : L.NeedNI → HookDetX L.Hb L.BaseDest

theorem OkDX.okD {L : LinkSys} (h : L.OkDX) : L.OkD := h.toOkD

/-- **Without non-interference, `OkDX` is `Ok`.** -/
theorem Ok.okDX_of_not_needNI {L : LinkSys} (hL : L.Ok) (hN : ¬ L.NeedNI) : L.OkDX :=
  { hL.okD_of_not_needNI hN with baseDetX := fun h => absurd h hN }

/-- `OkDX` from `Ok` and the two hook premises. -/
theorem Ok.okDX {L : LinkSys} (hL : L.Ok) (hD : HookDet L.Hb L.BaseDest)
    (hX : HookDetX L.Hb L.BaseDest) : L.OkDX :=
  { hL.okD hD with baseDetX := fun _ => hX }

end LinkSys

end E2E

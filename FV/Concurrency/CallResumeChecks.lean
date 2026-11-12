import FV.Arm.MinTheory
import FV.Backend.Proof.IselExtern
import FV.Backend.Proof.SpillLocal

/-!
# `resume_all`'s static premises as checks on the lowered code (#473, step (3))

`CallResumeAll.resume_all` takes static premises about the caller's prepared VCode `RA.vc`:

* `hvdef`: every `call` defines virtual registers only;
* the register part of `habi`: the `j`-th def of every `call` is the real register of the
  callee's `j`-th `rets` pair.

Both are Bool checks over the lowered code, each **sound and complete**:

* `callDefsVirtB vc` ↔ `CallDefsVirt vc` (`callDefsVirtB_iff`);
* `callDefsRetB vc rs` ↔ `CallDefsRet vc rs` (`callDefsRetB_iff`), and `CallDefsRet vc
  (usB.map (·.2))` gives the register part of `habi` (`habi_regs`).

The third premise, `info.defs.length = ext.sig.returns.length` with `ext` the CLIF extern the
call statement names, stays a premise: it ties the VCode call to the CLIF statement (the call's
destination symbol to `ext.name`), which the check on the VCode alone cannot see.
-/

namespace Concurrency.CallResumeChecks

open Backend

/-- A register is virtual. -/
def isVReg : Reg → Bool
  | .vreg _ _ => true
  | _ => false

theorem isVReg_iff (r : Reg) : isVReg r = true ↔ ∃ (n : Nat) (c : RegClass), r = .vreg n c := by
  cases r <;> simp [isVReg]

/-- Every call instruction of `vc` satisfies `P`. -/
def CallsAll (vc : VCode) (P : CallInfo → Prop) : Prop :=
  ∀ (b : Nat) (vb : VBlock) (k : Nat) (info : CallInfo),
    vc.blocks[b]? = some vb → vb.insts[k]? = some (.call info) → P info

/-- The check: every call instruction of `vc` passes `c`. -/
def callsAllB (vc : VCode) (c : CallInfo → Bool) : Bool :=
  vc.blocks.all fun vb => vb.insts.all fun i => match i with
    | .call info => c info
    | _ => true

theorem callsAllB_iff (vc : VCode) (c : CallInfo → Bool) :
    callsAllB vc c = true ↔ CallsAll vc fun info => c info = true := by
  unfold callsAllB CallsAll
  simp only [Array.all_eq_true]
  constructor
  · intro h b vb k info hb hk
    obtain ⟨hb1, rfl⟩ := Array.getElem?_eq_some_iff.mp hb
    obtain ⟨hk1, e⟩ := Array.getElem?_eq_some_iff.mp hk
    have h2 := h b hb1 k hk1
    rw [e] at h2
    exact h2
  · intro h b hb k hk
    split
    · rename_i info e
      exact h b _ k info (Array.getElem?_eq_getElem hb) (by rw [Array.getElem?_eq_getElem hk, e])
    · rfl

/-! ## Virtual defs (`hvdef`) -/

/-- **Every call defines virtual registers only** (`resume_all`'s `hvdef`). -/
def CallDefsVirt (vc : VCode) : Prop :=
  CallsAll vc fun info => ∀ d ∈ info.defs, ∃ (n : Nat) (c : RegClass), d.2 = .vreg n c

/-- The check of `CallDefsVirt`. -/
def callDefsVirtB (vc : VCode) : Bool := callsAllB vc fun info => info.defs.all (isVReg ·.2)

/-- **The check is sound and complete.** -/
theorem callDefsVirtB_iff (vc : VCode) : callDefsVirtB vc = true ↔ CallDefsVirt vc := by
  unfold callDefsVirtB CallDefsVirt
  rw [callsAllB_iff]
  simp only [List.all_eq_true, isVReg_iff]

/-! ## Def registers (`habi`, register part) -/

/-- **The `j`-th def of every call is the `j`-th of the registers `rs`.** -/
def CallDefsRet (vc : VCode) (rs : List Reg) : Prop :=
  CallsAll vc fun info => info.defs.map (·.1) <+: rs

/-- The check of `CallDefsRet`. -/
def callDefsRetB (vc : VCode) (rs : List Reg) : Bool :=
  callsAllB vc fun info => (info.defs.map (·.1)).isPrefixOf rs

/-- **The check is sound and complete.** -/
theorem callDefsRetB_iff (vc : VCode) (rs : List Reg) :
    callDefsRetB vc rs = true ↔ CallDefsRet vc rs := by
  unfold callDefsRetB CallDefsRet
  rw [callsAllB_iff]
  simp only [List.isPrefixOf_iff_prefix]

/-- **The register part of `resume_all`'s `habi`** from `CallDefsRet` for the callee's `rets`
registers. -/
theorem habi_regs {vc : VCode} {usB : List (Reg × Reg)} (h : CallDefsRet vc (usB.map (·.2)))
    {b : Nat} {vb : VBlock} {k : Nat} {info : CallInfo} (hb : vc.blocks[b]? = some vb)
    (hk : vb.insts[k]? = some (.call info)) :
    ∀ (j : Nat) (d : Reg × Reg), info.defs[j]? = some d → ∃ v, usB[j]? = some (v, d.1) := by
  intro j d hd
  obtain ⟨t, ht⟩ := h b vb k info hb hk
  have h1 : (info.defs.map (·.1))[j]? = some d.1 := by simp [hd]
  have h2 : (usB.map (·.2))[j]? = some d.1 := by
    rw [← ht, List.getElem?_append_left (by
      have := (List.getElem?_eq_some_iff.mp h1).1; exact this)]
    exact h1
  rw [List.getElem?_map] at h2
  cases hu : usB[j]? with
  | none => rw [hu] at h2; cases h2
  | some u =>
    rw [hu] at h2
    have e : u.2 = d.1 := Option.some.inj h2
    exact ⟨u.1, by rw [← e]⟩

end Concurrency.CallResumeChecks

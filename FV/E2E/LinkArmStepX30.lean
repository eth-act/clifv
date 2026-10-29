module

public import FV.E2E.LinkArmStepDet
public import FV.E2E.ArmGprFoot

@[expose] public section

/-!
# One machine step from two states equal but for `x30` (SEM1, `docs/plans/uninit.md` §5.8 (1))

The two runs of prophecy determinism enter the activation with different `x30` (the canonical
entry returns to `raStar`, the actual one to its call site), so the lock-step relation is
`StEqOut` up to `x30`:

* `StEqOutX Z s t`: every register but `x30` equal, same program, same memory outside `Z`;
* `stEqOut_setGpr30`: `s` with `t`'s `x30` is `StEqOut Z`-related to `t`;
* `stEqOutX_exec_inst`: an instruction that names no `x30` (`ArmInst.gprs`,
  `GprFoot.gprFree_exec_inst`) and whose reads avoid `Z` keeps `StEqOutX Z`;
* `stEqOutX_stepi`, `stEqOutX_w`, **`stEqOutX_armStepX`**: `Arm.stepi`, a register write, and a
  step of `ArmStepX` at an unhooked line whose instruction names no `x30`;
* `stEqOutX_armStepX_call`: at a hooked line, hooks that keep `StEqOutX Z` do.

The lines that name `x30` (`bl`/`blr`: hooked; `ret`; the frame-record pair) are the remaining
step lemmas of the lock-step (`docs/plans/uninit.md` §5.8, step 3j).
-/

namespace E2E

open Arm Backend Backend.Proof Concurrency.ArmFoot Concurrency.ArmThread Concurrency.ArmInstFoot
  Concurrency.VCodeThread GprFoot

/-- **Equal but for `x30` and the memory in `Z`.** -/
def StEqOutX (Z : BitVec 64 → Prop) (s t : ArmState) : Prop :=
  (∀ f, f ≠ .GPR 30#5 → r f s = r f t) ∧ s.program = t.program ∧ ∀ a, ¬ Z a → s.mem a = t.mem a

theorem StEqOut.toX {Z : BitVec 64 → Prop} {s t : ArmState} (h : StEqOut Z s t) :
    StEqOutX Z s t :=
  ⟨fun f _ => h.1 f, h.2.1, h.2.2⟩

theorem StEqOutX.refl (Z : BitVec 64 → Prop) (s : ArmState) : StEqOutX Z s s :=
  ⟨fun _ _ => rfl, rfl, fun _ _ => rfl⟩

theorem StEqOutX.symm {Z : BitVec 64 → Prop} {s t : ArmState} (h : StEqOutX Z s t) :
    StEqOutX Z t s :=
  ⟨fun f hf => (h.1 f hf).symm, h.2.1.symm, fun a ha => (h.2.2 a ha).symm⟩

theorem StEqOutX.trans {Z : BitVec 64 → Prop} {s t u : ArmState} (h : StEqOutX Z s t)
    (h' : StEqOutX Z t u) : StEqOutX Z s u :=
  ⟨fun f hf => (h.1 f hf).trans (h'.1 f hf), h.2.1.trans h'.2.1,
    fun a ha => (h.2.2 a ha).trans (h'.2.2 a ha)⟩

theorem StEqOutX.mono {Z Z' : BitVec 64 → Prop} {s t : ArmState} (h : StEqOutX Z s t)
    (hZ : ∀ a, Z a → Z' a) : StEqOutX Z' s t :=
  ⟨h.1, h.2.1, fun a ha => h.2.2 a fun h' => ha (hZ a h')⟩

/-- Setting `x30` keeps `StEqOutX`. -/
theorem stEqOutX_setGpr30 {Z : BitVec 64 → Prop} (v : BitVec 64) (s : ArmState) :
    StEqOutX Z (setGpr 30#5 v s) s :=
  ⟨fun _ hf => r_setGpr hf _ _, setGpr_program _ _ _, fun _ _ => by rw [setGpr_mem]⟩

/-- **`s` with `t`'s `x30` is `StEqOut`-related to `t`.** -/
theorem stEqOut_setGpr30 {Z : BitVec 64 → Prop} {s t : ArmState} (h : StEqOutX Z s t) :
    StEqOut Z (setGpr 30#5 (r (.GPR 30#5) t) s) t := by
  refine ⟨fun f => ?_, by rw [setGpr_program]; exact h.2.1, fun a ha => by
    rw [setGpr_mem]; exact h.2.2 a ha⟩
  by_cases hf : f = .GPR 30#5
  · subst hf; exact r_of_w_same
  · rw [r_setGpr hf]; exact h.1 f hf

/-- **An instruction that names no `x30` and reads nothing in `Z`** keeps `StEqOutX Z` (the
reads are those of `t`'s step). -/
theorem stEqOutX_exec_inst {Z : BitVec 64 → Prop} {s t : ArmState} (ai : ArmInst)
    (h30 : ∀ x ∈ ai.gprs, ¬ x = 30#5) (h : StEqOutX Z s t) (hZ : ReadsAvoid Z (instEvs ai t)) :
    StEqOutX Z (exec_inst ai s) (exec_inst ai t) := by
  have hfree := gprFree_exec_inst ai (by decide) h30 (r (.GPR 30#5) t) s
  have h1 := (stEqOut_exec_inst ai (stEqOut_setGpr30 h).symm hZ).symm
  rw [hfree] at h1
  exact (stEqOutX_setGpr30 _ _).symm.trans h1.toX

/-- The decoded instruction at `t`'s pc names no `x30`. -/
def DecX30Free (t : ArmState) : Prop :=
  ∀ w ai, fetch_inst (read_pc t) t = some w → decode_raw_inst w = some ai → ∀ x ∈ ai.gprs, ¬ x = 30#5

theorem stEqOutX_write_err {Z : BitVec 64 → Prop} {s t : ArmState} (h : StEqOutX Z s t)
    (e : StateError) : StEqOutX Z (write_err e s) (write_err e t) := by
  refine ⟨fun f hf => ?_, ?_, fun x hx => ?_⟩
  · simp only [write_err]
    by_cases hfe : f = .ERR
    · subst hfe; rw [r_of_w_same, r_of_w_same]
    · rw [r_of_w_different hfe, r_of_w_different hfe]; exact h.1 f hf
  · simp only [write_err]; rw [Arm.w_program, Arm.w_program]; exact h.2.1
  · simp only [write_err]
    rw [Arm.mem_w_of_mem_eq rfl, Arm.mem_w_of_mem_eq rfl]; exact h.2.2 x hx

/-- **`Arm.stepi` from two states equal but for `x30` and memory in `Z`**, at an instruction
that names no `x30` and reads nothing in `Z`. -/
theorem stEqOutX_stepi {Z : BitVec 64 → Prop} {s t : ArmState} (h : StEqOutX Z s t)
    (hZ : ReadsAvoid Z (stepiEvs t)) (h30 : DecX30Free t) : StEqOutX Z (stepi s) (stepi t) := by
  have herr : read_err s = read_err t := h.1 .ERR (by simp)
  have hpc : read_pc s = read_pc t := h.1 .PC (by simp)
  have hf : ∀ a, fetch_inst a s = fetch_inst a t := fun a => by
    simp only [fetch_inst, h.2.1]
  simp only [stepi, herr, hpc, hf]
  unfold stepiEvs at hZ
  cases he : read_err t with
  | None =>
    rw [he] at hZ
    simp only
    cases hfe : fetch_inst (read_pc t) t with
    | none => exact stEqOutX_write_err h _
    | some i =>
      rw [hfe] at hZ
      simp only
      cases hd : decode_raw_inst i with
      | none => exact stEqOutX_write_err h _
      | some ai =>
        simp only [hd] at hZ
        exact stEqOutX_exec_inst ai (h30 i ai hfe hd) h hZ
  | _ => exact h

theorem stEqOutX_w {Z : BitVec 64 → Prop} {s t : ArmState} (h : StEqOutX Z s t)
    (g : StateField) (v : state_value g) : StEqOutX Z (Arm.w g v s) (Arm.w g v t) := by
  refine ⟨fun f hf => ?_, ?_, fun x hx => ?_⟩
  · by_cases hfg : f = g
    · subst hfg; rw [r_of_w_same, r_of_w_same]
    · rw [r_of_w_different hfg, r_of_w_different hfg]; exact h.1 f hf
  · rw [Arm.w_program, Arm.w_program]; exact h.2.1
  · rw [Arm.mem_w_of_mem_eq rfl, Arm.mem_w_of_mem_eq rfl]; exact h.2.2 x hx

/-- **A step of `ArmStepX` at an unhooked line from two states equal but for `x30` and memory in
`Z`**, when the line's instruction names no `x30` and reads nothing in `Z`. -/
theorem stEqOutX_armStepX {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {Z : BitVec 64 → Prop}
    {s t : ArmState} (h : StEqOutX Z s t)
    (hn : ¬ HookedInsn (insnAt fa (progBase t) (r .PC t)))
    (hZ : ReadsAvoid Z (stepiEvs t)) (h30 : DecX30Free t) :
    StEqOutX Z (ArmStepX X H fa s) (ArmStepX X H fa t) := by
  have hpb : progBase s = progBase t := by simp only [progBase, h.2.1]
  have hpc : r .PC s = r .PC t := h.1 .PC (by simp)
  simp only [ArmStepX, hpb, hpc]
  split
  all_goals first
    | (exfalso; apply hn; rename_i hh; rw [hh]; exact trivial)
    | exact stEqOutX_w (stEqOutX_w h _ _) _ _
    | exact stEqOutX_w h _ _
    | exact stEqOutX_stepi h hZ h30

/-- **A step of `ArmStepX` keeps `StEqOutX Z` when the hooks do** (and the instruction names no
`x30` and does not read `Z`). -/
theorem stEqOutX_armStepX_call {X : ExtSem} {H : ArmHooks} {fa : FnAsm} {Z : BitVec 64 → Prop}
    {s t : ArmState} (h : StEqOutX Z s t)
    (hc : ∀ d, StEqOutX Z (H.call d s) (H.call d t))
    (ht : ∀ n r, StEqOutX Z (H.tls n r s) (H.tls n r t)) (hZ : ReadsAvoid Z (stepiEvs t))
    (h30 : DecX30Free t) :
    StEqOutX Z (ArmStepX X H fa s) (ArmStepX X H fa t) := by
  have hpb : progBase s = progBase t := by simp only [progBase, h.2.1]
  have hpc : r .PC s = r .PC t := h.1 .PC (by simp)
  simp only [ArmStepX, hpb, hpc]
  split
  all_goals first
    | exact hc _
    | exact ht _ _
    | exact stEqOutX_w (stEqOutX_w h _ _) _ _
    | exact stEqOutX_w h _ _
    | exact stEqOutX_stepi h hZ h30

end E2E

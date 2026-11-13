import FV.E2E.RegLevelGoodX
import FV.E2E.LeafKeepDefs
import FV.E2E.ArmGprFoot

/-!
# `x29` and `x30` through the body of a frameless leaf (#1028, slice 2)

With a frame, the epilogue reloads `x29` and `x30` from the frame record before `ret`
(`ret_machine`), so the register-level proof needs nothing about them in the body but the frame
pointer the prologue set (`StRel.fp`). A frameless leaf (`preserve_frame_pointers=false`,
`Backend.frameless`) returns with the `x29` and `x30` it was entered with: every step of its body
must keep them. Cranelift never allocates `x29`/`x30`; among the lines the backend emits, only the
calls (`bl`, `blr`, the TLS descriptor call: hooked lines), the frame-record pair
(`stp fp, lr` / `ldp fp, lr`), the prologue's `mov fp, sp` and the accesses to the incoming
arguments through `fp` name them, and a leaf has none of these.

* `Insn.gprKeep k env x`: the machine's step at line `x` keeps `x_k`: `ret` (it reads `x30` and
  writes only the pc); a hooked line that is no call and whose destination (`adrp`, the GOT's
  `adrp`) is not `x_k`; an unhooked line whose instruction names no `x_k` (`ArmInst.gprs`,
  `GprFoot.gprFree_exec_inst`).
* `FnAsm.gprKeep k fa lm`: every instruction line of `fa` is `gprKeep k` at its encoder
  environment (decidable, on the compiled code). `FnAsm.leafKeep`: for `x29` and `x30` (it fails
  on any call or frame-record line).
* **`RL.step_gprKeep`**: a machine step at a checked line keeps `x_k`.
* **`RL.iterN_gprKeep`**, **`RL.iterN_leafKeep`**: on a function that passes the check, every run
  whose states are those of the activation (`RL.GoodX`, which every state of the register-level
  runs satisfies) keeps `x_k` (`x29` and `x30`).
-/

namespace E2E

open Backend Backend.Proof GprFoot

/-- `leafKeep` at the function's own label offsets (`false` if they do not resolve): the check
`lean-backend` runs on a frameless leaf's compiled code. -/
def _root_.Backend.FnAsm.leafChk (fa : FnAsm) : Bool :=
  match labelOffsets fa.lines with
  | .ok lm => fa.leafKeep lm
  | .error _ => false

theorem leafKeep_of_leafChk {fa : FnAsm} (h : fa.leafChk = true) {lm : Std.HashMap Lbl Nat}
    (hm : labelOffsets fa.lines = .ok lm) : fa.leafKeep lm = true := by
  simpa [FnAsm.leafChk, hm] using h

/-- `x_k` after a write of another field. -/
theorem gpr_w {k : BitVec 5} {f : Arm.StateField} (hf : f ≠ .GPR k) (v : Arm.state_value f)
    (s : Arm.ArmState) : Arm.r (.GPR k) (Arm.w f v s) = Arm.r (.GPR k) s :=
  Arm.r_of_w_different (Ne.symm hf)

/-- An instruction that names no `x_k` (`k ≠ 31`) keeps it. -/
theorem gpr_exec_inst {k : BitVec 5} (hk : ¬ 31#5 = k) {a : Arm.ArmInst}
    (h : ∀ x ∈ a.gprs, ¬ x = k) (s : Arm.ArmState) :
    Arm.r (.GPR k) (Arm.exec_inst a s) = Arm.r (.GPR k) s := by
  have hfree := gprFree_exec_inst a hk h (Arm.r (.GPR k) s) s
  have hs : setGpr k (Arm.r (.GPR k) s) s = s := Arm.w_irrelevant
  rw [hs] at hfree
  rw [hfree]
  exact Arm.r_of_w_same

/-- The Arm instruction of the backend's `ret` (`br x30`'s return form; `E2E.retI`). -/
def retInsn : Arm.ArmInst :=
  .BR (.Uncond_branch_reg { opc := 2, op2 := 31, op3 := 0, Rn := 30, op4 := 0 })

/-- `ret` keeps every general-purpose register (it reads `x30` and writes only the pc). -/
theorem gpr_exec_ret (k : BitVec 5) (s : Arm.ArmState) :
    Arm.r (.GPR k) (Arm.exec_inst retInsn s) = Arm.r (.GPR k) s := by
  simp (config := { decide := true }) only [retInsn, Arm.exec_inst, Arm.BR.exec_uncond_branch_reg,
    ↓reduceIte]
  simp only [Arm.write_pc]
  exact gpr_w (by simp) _ _

/-- **A machine step at a line that passes `gprKeep k` keeps `x_k`** (`k ≠ 31`). -/
theorem RL.step_gprKeep {R : RL} (hR : R.Wf) {k : BitVec 5} (hk31 : ¬ 31#5 = k)
    {u : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC u = R.pcOf j)
    (hprog : u.program = R.fb.program R.base) (herr : Arm.r .ERR u = .None)
    (hk : x.gprKeep k (R.envOf j) = true) : Arm.r (.GPR k) (R.step u) = Arm.r (.GPR k) u := by
  cases hh : x.hooked
  · obtain ⟨a, ha, hstep⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj hh hprog
      hpc herr
    show Arm.r (.GPR k) (ArmStepX R.X R.H R.fa u) = Arm.r (.GPR k) u
    rw [hstep]
    simp only [Insn.gprKeep, hh, Bool.false_eq_true, ↓reduceIte] at hk
    split at hk
    · have e : a = retInsn := by
        have := ha
        simp only [show Insn.ret.toArmInst _ = .ok retInsn from rfl, Except.ok.injEq] at this
        exact this.symm
      subst e
      exact gpr_exec_ret k u
    · change Insn.toArmInst (R.envOf j) _ = _ at ha
      rw [ha] at hk
      exact gpr_exec_inst hk31 (fun y hy hyk => by
        have := List.all_eq_true.mp hk y hy
        simp [hyk] at this) u
  · obtain ⟨_, w, hw, hk4⟩ := FnAsm.layout_word hR.layout hR.lm hj rfl
    have hne : R.fb.words.toList ≠ [] := by
      intro h
      have : R.fb.words.size = 0 := by simpa using congrArg List.length h
      simp [this] at hk4
    have hb : progBase u = R.base := progBase_eq (by rw [hprog]; rfl) hne
    have hsum := layout_sum hR.layout
    have hfit := hR.fit
    have hins : insnAt R.fa (progBase u) (Arm.r .PC u) = some x := by
      rw [hb, hpc]; exact insnAt_line (by omega) hj
    simp only [Insn.gprKeep, hh, ↓reduceIte] at hk
    unfold RL.step ArmStepX
    simp only [hins]
    cases x <;> simp only [Insn.hooked, Insn.hookedGprKeep, Bool.false_eq_true] at hh hk ⊢
    all_goals first
      | (rw [gpr_w (by simp), gpr_w (fun e => by simp at hk; exact hk (Arm.StateField.GPR.inj e))])
      | exact gpr_w (by simp) _ _

/-- **Every run of the activation's states keeps `x_k`** on a function that passes the check
(`k ≠ 31`). -/
theorem RL.iterN_gprKeep {R : RL} (hR : R.Wf) {k : BitVec 5} (hk31 : ¬ 31#5 = k)
    (hk : R.fa.gprKeep k R.lm = true) :
    ∀ {n : Nat} {s : Arm.ArmState}, (∀ i < n, R.GoodX (iterN R.step i s)) →
      Arm.r (.GPR k) (iterN R.step n s) = Arm.r (.GPR k) s
  | 0, _, _ => rfl
  | n + 1, s, hg => by
    have h0 := hg 0 (Nat.succ_pos n)
    obtain ⟨x, ⟨j, t, hj, hpc⟩, -⟩ := h0.line
    have hs : Arm.r (.GPR k) (R.step s) = Arm.r (.GPR k) s :=
      RL.step_gprKeep hR hk31 hj hpc h0.prog h0.err (gprKeep_line hk hj)
    show Arm.r (.GPR k) (iterN R.step n (R.step s)) = Arm.r (.GPR k) s
    rw [RL.iterN_gprKeep hR hk31 hk (n := n) (s := R.step s) fun i hi => hg (i + 1) (by omega), hs]

/-- **A frameless leaf's run keeps `x29` and `x30`** (`FnAsm.leafKeep`). -/
theorem RL.iterN_leafKeep {R : RL} (hR : R.Wf) (hk : R.fa.leafKeep R.lm = true)
    {n : Nat} {s : Arm.ArmState} (hg : ∀ i < n, R.GoodX (iterN R.step i s)) :
    xreg 29 (iterN R.step n s) = xreg 29 s ∧ xreg 30 (iterN R.step n s) = xreg 30 s := by
  simp only [FnAsm.leafKeep, Bool.and_eq_true] at hk
  exact ⟨RL.iterN_gprKeep hR (by decide) hk.1 hg, RL.iterN_gprKeep hR (by decide) hk.2 hg⟩

/-- **The x29/x30 premise of `ret_machine`** from the activation's run: on a frameless leaf
(`RL.Wf.leaf`), a run of `GoodX` states keeps x29 and x30. -/
theorem RL.leafRegs {R : RL} (hR : R.Wf) {n : Nat} {s : Arm.ArmState}
    (hg : ∀ i < n, R.GoodX (iterN R.step i s)) :
    R.af.frame = false →
      xreg 29 (iterN R.step n s) = xreg 29 s ∧ xreg 30 (iterN R.step n s) = xreg 30 s :=
  fun hf => RL.iterN_leafKeep hR (hR.leaf hf) hg

/-- `RL.leafRegs` for a run in three parts (the prologue, the body, the last step's segment). -/
theorem RL.leafRegs3 {R : RL} (hR : R.Wf) {a b c : Nat} {s : Arm.ArmState}
    (h0 : ∀ i < a, R.GoodX (iterN R.step i s))
    (h1 : ∀ i < b, R.GoodX (iterN R.step i (iterN R.step a s)))
    (h2 : ∀ i < c, R.GoodX (iterN R.step i (iterN R.step b (iterN R.step a s)))) :
    R.af.frame = false →
      xreg 29 (iterN R.step c (iterN R.step b (iterN R.step a s))) = xreg 29 s ∧
      xreg 30 (iterN R.step c (iterN R.step b (iterN R.step a s))) = xreg 30 s := by
  intro hf
  have h := RL.leafRegs hR (trace_add h0 (trace_add h1 h2)) hf
  rw [iterN_add, iterN_add] at h
  exact h

end E2E

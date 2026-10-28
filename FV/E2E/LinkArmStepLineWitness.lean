import FV.E2E.LinkArmStepLine

/-!
# Non-vacuity of the per-line lock-step steps (`LinkArmStepLine.lean`)

`faW`: `stp fp, lr, [sp, #-16]!; add x0, x1, x2; ldp fp, lr, [sp], #16; ret`, laid out
(`faW_layout`) and passing the `x30` check (`faW_x30Free`). `tAt j`: the state holding its program
at line `j`. `stp_line`, `add_line`, `ldp_line`, `ret_line`: from `tAt j` and the same state
with another `x30`, one step of the machine at each line keeps the lock-step relation
(`ret_line`: agreement on `x0`).
-/

namespace E2E.StepLineWitness

open Arm Backend Backend.Proof

def faW : FnAsm :=
  { name := "w", k := 0, size := 16, traps := []
    lines := #[.ins (.stp .fp .lr (.spPreIndexed (-16))) none,
      .ins (.aluRRR .add true (.x 0) (.x 1) (.x 2)) none,
      .ins (.ldp .fp .lr (.spPostIndexed 16)) none, .ins .ret none] }

def fbW : FnBin := match faW.layout with
  | .ok b => b
  | .error _ => default

def lmW : Std.HashMap Lbl Nat := match labelOffsets faW.lines with
  | .ok m => m
  | .error _ => {}

theorem faW_layout : faW.layout = .ok fbW := by
  have h : faW.layout.toBool = true := by native_decide
  unfold fbW; revert h; cases faW.layout <;> simp [Except.toBool]

theorem faW_lm : labelOffsets faW.lines = .ok lmW := by
  have h : (labelOffsets faW.lines).toBool = true := by native_decide
  unfold lmW; revert h; cases labelOffsets faW.lines <;> simp [Except.toBool]

theorem fbW_fit : 4 * fbW.words.size ≤ 2 ^ 64 := by native_decide
theorem faW_x30Free : faW.x30Free lmW = true := by native_decide

def baseW : BitVec 64 := 0x10000

/-- The state at line `j` (offset `4 j`) of `faW`, loaded at `baseW`. -/
def tAt (j : Nat) : ArmState :=
  Arm.w .PC (baseW + BitVec.ofNat 64 (4 * j))
    (Arm.w .ERR .None { ArmState.default with program := fbW.program baseW })

theorem onLine (j : Nat) (x : Insn) (hj : faW.lines.toList[j]? = some (.ins x none))
    (ho : lineOffset faW.lines.toList j = 4 * j) : OnLine faW fbW lmW baseW (tAt j) x :=
  ⟨faW_layout, faW_lm, fbW_fit, by simp [tAt, Arm.w_program],
    by rw [tAt, Arm.r_of_w_different (by simp), Arm.r_of_w_same],
    ⟨j, none, hj, by rw [ho, tAt, Arm.r_of_w_same]⟩⟩

variable (X : ExtSem) (H : ArmHooks) (v : BitVec 64)

/-- The hooks that change nothing. -/
def Hid : ArmHooks := ⟨fun _ s => s, fun _ _ s => s⟩

theorem stp_line :
    StEqOutX (fun a => False ∨ HiBytes (stpAddr 0x7e (tAt 0)) 8 16 a)
      (ArmStepX X H faW (GprFoot.setGpr 30#5 v (tAt 0))) (ArmStepX X H faW (tAt 0)) :=
  stEqOutX_line_stpFR (onLine 0 _ rfl (by decide)) (stEqOutX_setGpr30 v _)

theorem add_line :
    StEqOutX (fun _ => False)
      (ArmStepX X Hid faW (GprFoot.setGpr 30#5 v (tAt 1))) (ArmStepX X Hid faW (tAt 1)) :=
  stEqOutX_line_free (onLine 1 _ rfl (by decide)) faW_x30Free (by decide)
    (stEqOutX_setGpr30 v _) (fun _ _ _ _ _ h => h) (fun _ _ _ => stEqOutX_setGpr30 v _)

/-- The combined step at the prologue line (`stEqOutX_line`). -/
theorem stp_line_any :
    StEqOutX (zNext (fun _ => False) (.stp .fp .lr (.spPreIndexed (-16))) (tAt 0))
      (ArmStepX X Hid faW (GprFoot.setGpr 30#5 v (tAt 0))) (ArmStepX X Hid faW (tAt 0)) :=
  stEqOutX_line (onLine 0 _ rfl (by decide)) faW_x30Free (by decide) (by decide)
    (stEqOutX_setGpr30 v _) (fun _ _ _ _ _ _ h => h) (fun _ _ _ h => h)
    (fun _ _ => stEqOutX_setGpr30 v _) (fun _ _ _ => stEqOutX_setGpr30 v _)

theorem ldp_line :
    StEqOutX (fun _ => False)
      (ArmStepX X H faW (GprFoot.setGpr 30#5 v (tAt 2))) (ArmStepX X H faW (tAt 2)) :=
  stEqOutX_line_ldpFR (onLine 2 _ rfl (by decide)) (stEqOutX_setGpr30 v _) fun _ _ h => h

theorem ret_line :
    r (.GPR 0#5) (ArmStepX X H faW (GprFoot.setGpr 30#5 v (tAt 3))) =
      r (.GPR 0#5) (ArmStepX X H faW (tAt 3)) :=
  (retAgree_line_ret (Z := fun _ => False) (onLine 3 _ rfl (by decide))
    (stEqOutX_setGpr30 v _)).1 _ (by simp) (by simp)

/-- The run induction on the identity machine. -/
theorem lockstep_id (n : Nat) (s : ArmState) :
    ∀ i ≤ n, StEqOutX (fun _ => False) (runX id i (GprFoot.setGpr 30#5 v s)) (runX id i s) :=
  lockstep_runX (stEqOutX_setGpr30 v s) fun _ _ h => h

end E2E.StepLineWitness

/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license; see third_party/NOTICE-lnsym.md.
-/
module

public import FV.Arm.Exec

@[expose] public section

/-! # The thread pointer `TPIDR_EL0` (FV addition)

`StateField.TPIDR` is the EL0 thread pointer. `MRS Xt, TPIDR_EL0` reads it (`exec_mrs_tpidr`);
no instruction of the model writes it (`r_TPIDR_exec_inst`, `r_TPIDR_stepi`): the loader / OS
sets it, outside the model.

Proof of the invariance: the instruction semantics only reach the state through `r`/`w` and
`read_mem_bytes`/`write_mem_bytes` (as for `E2E.ExecFrame.exec_simR`). `tp_norm` unfolds the
semantics into these; `tp_walk` walks the state term: a write `w fld` with `fld ≠ TPIDR` and a
memory write keep `r .TPIDR`, and a case split (`if`, `dite`, `match`) is walked branch-wise.
-/

namespace Arm

namespace Tpidr

theorem w_ne {fld : StateField} (hf : StateField.TPIDR ≠ fld) {v : state_value fld}
    {t : ArmState} {x : BitVec 64} (h : r .TPIDR t = x) : r .TPIDR (w fld v t) = x := by
  rw [r_of_w_different hf]; exact h

theorem wmb {n : Nat} {a : BitVec 64} {v : BitVec (n * 8)} {t : ArmState} {x : BitVec 64}
    (h : r .TPIDR t = x) : r .TPIDR (write_mem_bytes n a v t) = x := by
  rw [r_of_write_mem_bytes]; exact h

theorem ite' {c : Prop} [Decidable c] {a b : ArmState} {x : BitVec 64}
    (h1 : c → r .TPIDR a = x) (h2 : ¬ c → r .TPIDR b = x) :
    r .TPIDR (if c then a else b) = x := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h1 hc
  · simp only [hc, ↓reduceIte]; exact h2 hc

theorem dite' {c : Prop} [Decidable c] {a : c → ArmState} {b : ¬ c → ArmState} {x : BitVec 64}
    (h1 : ∀ hc, r .TPIDR (a hc) = x) (h2 : ∀ hc, r .TPIDR (b hc) = x) :
    r .TPIDR (dite c a b) = x := by
  by_cases hc : c
  · simp only [hc, ↓reduceDIte]; exact h1 hc
  · simp only [hc, ↓reduceDIte]; exact h2 hc

/-- Unfold the semantics into `r`/`w`/`read_mem_bytes`/`write_mem_bytes`. -/
syntax "tp_norm" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| tp_norm $[$loc]?) => `(tactic| simp only [exec_inst, state_simp_rules,
      ne_eq, reduceCtorEq, not_false_eq_true,
      r_of_w_different, r_of_write_mem_bytes, CheckSPAlignment, Bool.false_eq_true, true_and,
      and_true, false_and, and_false, not_true_eq_false, ↓reduceIte, ↓reduceDIte,
      Bool.not_eq_true, Bool.not_eq_false, Bool.not_false, Bool.not_true, true_implies] $[$loc]?)

/-- Walk the state term of `r .TPIDR (F s) = r .TPIDR s` (after `tp_norm`). -/
macro "tp_walk" : tactic => `(tactic| repeat (first
  | rfl
  | (refine w_ne (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) ?_)
  | apply wmb
  | (apply ite' <;> intro _)
  | (apply dite' <;> intro _)
  | (split <;> (try tp_norm))))

end Tpidr

open Tpidr in
/-- No instruction of the model writes the thread pointer. -/
theorem r_TPIDR_exec_inst (a : ArmInst) (s : ArmState) :
    r .TPIDR (exec_inst a s) = r .TPIDR s := by
  cases a with
  | DPI i => cases i <;> (tp_norm; tp_walk)
  | BR i => cases i <;> (tp_norm; tp_walk)
  | DPR i => cases i <;> (tp_norm; tp_walk)
  | DPSFP i => cases i <;> (tp_norm; tp_walk)
  | LDST i => cases i <;> (tp_norm; tp_walk)
  | RES i => cases i <;> (tp_norm; tp_walk)

/-- A step of the machine keeps the thread pointer. -/
theorem r_TPIDR_stepi (s : ArmState) : r .TPIDR (stepi s) = r .TPIDR s := by
  simp only [stepi]
  split
  · split
    · simp only [write_err, r_of_w_different (show StateField.TPIDR ≠ .ERR by decide)]
    · split
      · simp only [write_err, r_of_w_different (show StateField.TPIDR ≠ .ERR by decide)]
      · exact r_TPIDR_exec_inst _ s
  · rfl

/-- `MRS Xt, TPIDR_EL0` (Cranelift's `0xd53bd040 | Rt`) writes the thread pointer to `Xt`
(`Rt = 31` is XZR: no write) and steps the PC. -/
theorem exec_mrs_tpidr (Rt : BitVec 5) (s : ArmState) :
    exec_inst (.BR (.Mrs
      {o0 := 1, op1 := 0b011#3, CRn := 0b1101#4, CRm := 0, op2 := 0b010#3, Rt := Rt})) s =
      w .PC (r .PC s + 4) (write_gpr_zr 64 Rt (r .TPIDR s) s) := by
  have hpc : r .PC (write_gpr_zr 64 Rt (r .TPIDR s) s) = r .PC s := by
    simp only [write_gpr_zr, write_gpr]
    split
    · exact r_of_w_different (by simp)
    · rfl
  simp only [exec_inst, BR.exec_mrs, Mrs_cls.isTpidrEl0, write_pc, read_pc, hpc]
  rfl

end Arm

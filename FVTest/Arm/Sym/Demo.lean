/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.

Symbolic-simulation demos for the `FV.Arm` model with the ported LNSym `sym_n` tactic (see
`docs/contracts/arm.md`, "Tactic API"). Both programs are straight-line code ending in `ret`,
the shape the M3 translation validator checks.
-/
import FV.Arm.Exec
import FV.Arm.Tactics.Sym
import FV.Arm.Tactics.StepThms

namespace Arm.SymDemo

open _root_.BitVec Arm.BitVec

/-! ## `add x0, x0, x1; ret` -/

def add_ret : Program :=
  def_program
  [(0x1000#64, 0x8b010000#32),   -- add x0, x0, x1
   (0x1004#64, 0xd65f03c0#32)]   -- ret

#genStepEqTheorems add_ret

theorem add_ret_sym (s0 sf : ArmState)
    (h_s0_pc : read_pc s0 = 0x1000#64)
    (h_s0_program : s0.program = add_ret)
    (h_s0_err : read_err s0 = StateError.None)
    (_h_s0_sp_aligned : CheckSPAlignment s0)
    (h_run : sf = run 2 s0) :
    read_gpr 64 0#5 sf = read_gpr 64 0#5 s0 + read_gpr 64 1#5 s0 ∧
    read_pc sf = read_gpr 64 30#5 s0 ∧
    read_err sf = StateError.None := by
  simp_all only [state_simp_rules, -h_run]
  -- `sym_n` steps both instructions and discharges the (now trivial) goal itself.
  sym_n 2

/-! ## Five instructions with a load

```
ldr x2, [x0]
add x2, x2, x1
lsl x3, x2, #3
sub x0, x3, x2
ret
```
computes `x0 := 7 * (mem64[x0] + x1)` and returns. -/

def load_scale : Program :=
  def_program
  [(0x2000#64, 0xf9400002#32),   -- ldr x2, [x0]
   (0x2004#64, 0x8b010042#32),   -- add x2, x2, x1
   (0x2008#64, 0xd37df043#32),   -- lsl x3, x2, #3  (ubfm x3, x2, #61, #60)
   (0x200c#64, 0xcb020060#32),   -- sub x0, x3, x2
   (0x2010#64, 0xd65f03c0#32)]   -- ret

#genStepEqTheorems load_scale

theorem load_scale_sym (s0 sf : ArmState)
    (h_s0_pc : read_pc s0 = 0x2000#64)
    (h_s0_program : s0.program = load_scale)
    (h_s0_err : read_err s0 = StateError.None)
    (_h_s0_sp_aligned : CheckSPAlignment s0)
    (h_run : sf = run 5 s0) :
    read_gpr 64 0#5 sf =
      7#64 * (read_mem_bytes 8 (read_gpr 64 0#5 s0) s0 + read_gpr 64 1#5 s0) ∧
    read_pc sf = read_gpr 64 30#5 s0 ∧
    read_err sf = StateError.None := by
  simp_all only [state_simp_rules, -h_run]
  sym_n 5
  -- `sym_n` leaves one bit-vector identity over the loaded word and `x1`:
  -- `((m + x1) ror 61 &&& ~7) - ~~~(~~~(m + x1)) = 7 * (m + x1)`.
  bv_decide

#print axioms add_ret_sym
#print axioms load_scale_sym

end Arm.SymDemo

/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license as described in third_party/lnsym-upstream/LICENSE.
-/
-- (FV addition, not in LNSym) ADDV (Advanced SIMD across lanes, `U = 0`, `opcode = 11011`).
--
-- Transcribed from the Arm ARM (DDI 0487) "ADDV" ASL:
--
--   if size:Q == '100' then UNDEFINED;   // 4S only with Q = 1
--   if size == '11' then UNDEFINED;
--   constant integer esize = 8 << UInt(size);
--   constant integer datasize = 64 << UInt(Q);
--   constant integer elements = datasize DIV esize;
--
--   bits(datasize) operand = V[n, datasize];
--   V[d, esize] = Reduce(ReduceOp_ADD, operand, esize);
--
-- `Reduce(ReduceOp_ADD, x, esize)` is the (wrapping) sum of the `esize`-bit elements of `x`;
-- the pairwise tree order of the ASL does not matter for modular addition. `V[d, esize] = x`
-- zeroes bits 127:esize (`write_sfp`). Cross-checked against VeriISLE `MInst.VecLanes`
-- (`Addv`) in cranelift/codegen/src/isa/aarch64/spec/vec_lanes.isle.

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm

namespace DPSFP

open _root_.BitVec Arm.BitVec

/-- Wrapping sum of elements `e .. elements-1` of `x`, added to `acc`. -/
def addv_aux (e : Nat) (elements : Nat) (esize : Nat) (x : BitVec n) (acc : BitVec esize) :
    BitVec esize :=
  if elements ≤ e then
    acc
  else
    addv_aux (e + 1) elements esize x (acc + elem_get x e esize)
  termination_by (elements - e)

@[state_simp_rules]
def exec_addv (inst : Advanced_simd_across_lanes_cls) (s : ArmState) : ArmState :=
  if (inst.size = 0b10#2 ∧ inst.Q = 0#1) ∨ inst.size = 0b11#2 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let esize := 8 <<< inst.size.toNat
    let datasize := if inst.Q = 1#1 then 128 else 64
    let operand := read_sfp datasize inst.Rn s
    let result := addv_aux 0 (datasize / esize) esize operand (BitVec.zero esize)
    let s := write_sfp esize inst.Rd result s
    let s := write_pc ((read_pc s) + 4#64) s
    s

@[state_simp_rules]
def exec_advanced_simd_across_lanes
  (inst : Advanced_simd_across_lanes_cls) (s : ArmState) : ArmState :=
  match inst.U, inst.opcode with
  | 0#1, 0b11011#5 => exec_addv inst s -- ADDV
  | _, _ => write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s

end DPSFP

end Arm

/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- AND, ORR, EOR, ANDS (immediate): 32- and 64-bit versions
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1, module prefix FV.Arm, wrapped in
-- namespace Arm; `Rn = 31` is XZR for every opcode (see `exec_logical_imm`).

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm


namespace DPI

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def decode_op (opc : BitVec 2) : LogicalImmType :=
  match opc with
  | 00#2 => LogicalImmType.AND
  | 01#2 => LogicalImmType.ORR
  | 10#2 => LogicalImmType.EOR
  | 11#2 => LogicalImmType.ANDS

def update_logical_imm_pstate (bv : BitVec n) : PState :=
  let N : BitVec 1 := BitVec.lsb bv (n-1)
  let Z := zero_flag_spec bv
  let C := 0#1
  let V := 0#1
  (make_pstate N Z C V)

@[state_simp_rules]
def exec_logical_imm_op (op : LogicalImmType) (op1 : BitVec n) (op2 : BitVec n)
  : (BitVec n × Option PState) :=
  match op with
  | LogicalImmType.AND => (op1 &&& op2, none)
  | LogicalImmType.ORR => (op1 ||| op2, none)
  | LogicalImmType.EOR => (op1 ^^^ op2, none)
  | LogicalImmType.ANDS =>
    let result := op1 &&& op2
    (op1 &&& op2, some (update_logical_imm_pstate result))

/--
Instruction semantics for `Logical_imm_cls` instructions
`AND, ORR, EOR, ANDS (immediate): 32- and 64-bit versions`.

Note that `ORR` and `ANDS` have aliases, as follows:

```
MOV <Wd|WSP>, #<imm> / MOV <Xd|SP>, #<imm>
```
is equivalent to
`ORR <Wd|WSP>, WZR, #<imm> / ORR <Xd|SP>, XZR, #<imm>`
and
`TST <Wn>, #<imm> / TST <Xn>, #<imm>`
is equivalent to
`ANDS WZR, <Wn>, #<imm> / ANDS XZR, <Xn>, #<imm>`

Sources:
https://developer.arm.com/documentation/ddi0602/2023-03/Base-Instructions/ANDS--immediate---Bitwise-AND--immediate---setting-flags-?lang=en
https://developer.arm.com/documentation/ddi0602/2023-03/Base-Instructions/TST--immediate---Test-bits--immediate---an-alias-of-ANDS--immediate--?lang=en
https://developer.arm.com/documentation/ddi0602/2023-03/Base-Instructions/ORR--immediate---Bitwise-OR--immediate--?lang=en
https://developer.arm.com/documentation/ddi0602/2023-03/Base-Instructions/MOV--bitmask-immediate---Move--bitmask-immediate---an-alias-of-ORR--immediate--?lang=en
https://developer.arm.com/documentation/ddi0602/2023-03/Base-Instructions/EOR--immediate---Bitwise-Exclusive-OR--immediate--?lang=en
https://developer.arm.com/documentation/ddi0602/2023-03/Base-Instructions/AND--immediate---Bitwise-AND--immediate--?lang=en
-/
@[state_simp_rules]
def exec_logical_imm (inst : Logical_imm_cls) (s : ArmState) : ArmState :=
  if inst.sf = 0#1 ∧ inst.N ≠ 0#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := 32 <<< inst.sf.toNat
    let imm := decode_bit_masks inst.N inst.imms inst.immr true datasize
    match imm with
    | none => write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
    | some (imm, _) =>
      let op := decode_op inst.opc
      -- (FV fix) The Arm ARM (DDI 0487) ASL reads `bits(datasize) operand1 = X[n, datasize];`
      -- for all four opcodes, so `Rn = 31` is always XZR. (Upstream read SP for `Rn = 31`
      -- unless the instruction was ORR with `MoveWidePreferred` false; `MoveWidePreferred`
      -- only selects the preferred disassembly and has no semantic effect.)
      let operand1 := read_gpr_zr datasize inst.Rn s
      let (result, maybe_pstate) := exec_logical_imm_op op operand1 imm
      -- State Updates
      let s'            := write_pc ((read_pc s) + 4#64) s
      let s'            := match maybe_pstate with
                           | none => s'
                           | some pstate => write_pstate pstate s'
      let s'            := match op with
                           | .ANDS =>
                              -- TST (immediate) is an alias of ANDS when
                              -- Rd == '11111'.
                              write_gpr_zr datasize inst.Rd result s'
                           | _ => write_gpr datasize inst.Rd result s'
      s'

----------------------------------------------------------------------

end DPI

end Arm

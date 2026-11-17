/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.

Witnesses for the Advanced SIMD (scalar) shift by immediate classes (USHR, SLI): the four words
Cranelift emits for scalar `fcopysign` (`fcopy_sign`, isa/aarch64/inst.isle; filetests
isa/aarch64/floating-point.clif `%f31`/`%f32`; `MInst.FpuRRI`/`FpuRRIMod`, inst/emit.rs) decode
to the new classes, and the model executes them as the ASL does, on concrete registers: the
two-instruction sequences compute `copysign`.
-/
import FV.Arm.Exec

namespace Arm.ShiftImmWitness

open Arm

/-- `ushr d4, d1, #63` (`0x7F410424`: `immh:immb = 128 - 63`). -/
def ushrD : ArmInst := .DPSFP (.Advanced_simd_scalar_shift_by_immediate
  { U := 1#1, immh := 0b1000#4, immb := 0b001#3, opcode := 0b00000#5, Rn := 1#5, Rd := 4#5 })

/-- `sli d0, d4, #63` (`0x7F7F5480`: `immh:immb = 64 + 63`). -/
def sliD : ArmInst := .DPSFP (.Advanced_simd_scalar_shift_by_immediate
  { U := 1#1, immh := 0b1111#4, immb := 0b111#3, opcode := 0b01010#5, Rn := 4#5, Rd := 0#5 })

/-- `ushr v4.2s, v1.2s, #31` (`0x2F210424`: `immh:immb = 64 - 31`). -/
def ushr2S : ArmInst := .DPSFP (.Advanced_simd_shift_by_immediate
  { Q := 0#1, U := 1#1, immh := 0b0100#4, immb := 0b001#3, opcode := 0b00000#5, Rn := 1#5,
    Rd := 4#5 })

/-- `sli v0.2s, v4.2s, #31` (`0x2F3F5480`: `immh:immb = 32 + 31`). -/
def sli2S : ArmInst := .DPSFP (.Advanced_simd_shift_by_immediate
  { Q := 0#1, U := 1#1, immh := 0b0111#4, immb := 0b111#3, opcode := 0b01010#5, Rn := 4#5,
    Rd := 0#5 })

example : decode_raw_inst 0x7F410424#32 = some ushrD := rfl
example : decode_raw_inst 0x7F7F5480#32 = some sliD := rfl
example : decode_raw_inst 0x2F210424#32 = some ushr2S := rfl
example : decode_raw_inst 0x2F3F5480#32 = some sli2S := rfl

/-- `immh = 0000` stays an Advanced SIMD modified immediate (`movi v4.2s, #0`). -/
example : decode_raw_inst 0x0F000404#32 = some (.DPSFP (.Advanced_simd_modified_immediate
    { Q := 0#1, op := 0#1, a := 0#1, b := 0#1, c := 0#1, cmode := 0#4, o2 := 0#1, d := 0#1,
      e := 0#1, f := 0#1, g := 0#1, h := 0#1, Rd := 4#5 })) := rfl

/-! ### f64: `v0 = 1.0`, `v1 = -2.0` (upper halves and `v4` garbage) -/

def sD : ArmState :=
  w (.SFP 0#5) 0xAAAAAAAAAAAAAAAA3FF0000000000000#128 <|
  w (.SFP 1#5) 0x5555555555555555C000000000000000#128 <|
  w (.SFP 4#5) 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF#128 ArmState.default

-- `ushr d4, d1, #63`: the sign bit of `v1` in bit 0, the rest of the 128-bit register zeroed
example : r (.SFP 4#5) (exec_inst ushrD sD) = 1#128 := by decide +kernel
-- `sli d0, d4, #63`: `v0 = copysign(1.0, -2.0) = -1.0`, upper half zeroed
example : r (.SFP 0#5) (exec_inst sliD (exec_inst ushrD sD)) = 0xBFF0000000000000#128 := by
  decide +kernel
example : r .PC (exec_inst sliD (exec_inst ushrD sD)) = 8#64 := by decide +kernel
example : r .ERR (exec_inst sliD (exec_inst ushrD sD)) = .None := by decide +kernel

/-! ### f32 (`.2s`): lane 0 `v0 = 1.0`, `v1 = -2.0`; lane 1 `v0 = 0x12345678`, `v1 = 0x80000001` -/

def sS : ArmState :=
  w (.SFP 0#5) 0xAAAAAAAAAAAAAAAA123456783F800000#128 <|
  w (.SFP 1#5) 0x555555555555555580000001C0000000#128 <|
  w (.SFP 4#5) 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF#128 ArmState.default

-- `ushr v4.2s, v1.2s, #31`: each lane's sign bit in its bit 0
example : r (.SFP 4#5) (exec_inst ushr2S sS) = 0x0000000100000001#128 := by decide +kernel
-- `sli v0.2s, v4.2s, #31`: each lane's sign replaced, `copysign(1.0, -2.0) = -1.0` in lane 0
example : r (.SFP 0#5) (exec_inst sli2S (exec_inst ushr2S sS)) = 0x92345678BF800000#128 := by
  decide +kernel
example : r .PC (exec_inst sli2S (exec_inst ushr2S sS)) = 8#64 := by decide +kernel
example : r .ERR (exec_inst sli2S (exec_inst ushr2S sS)) = .None := by decide +kernel

/-! ### Reserved and unmodelled encodings -/

/-- The error's constructor: `0` none, `1` illegal, `2` unimplemented, `3` other. -/
def errKind : StateError → Nat
  | .None => 0
  | .Illegal _ => 1
  | .Unimplemented _ => 2
  | _ => 3

-- `ushr v4.1d, …` (`immh<3>:Q = 10`) is reserved
example : errKind (r .ERR (exec_inst (.DPSFP (.Advanced_simd_shift_by_immediate
    { Q := 0#1, U := 1#1, immh := 0b1000#4, immb := 0b001#3, opcode := 0b00000#5, Rn := 1#5,
      Rd := 4#5 })) sS)) = 1 := by decide +kernel
-- scalar `ushr` with `immh<3> = 0` is UNDEFINED
example : errKind (r .ERR (exec_inst (.DPSFP (.Advanced_simd_scalar_shift_by_immediate
    { U := 1#1, immh := 0b0100#4, immb := 0b001#3, opcode := 0b00000#5, Rn := 1#5,
      Rd := 4#5 })) sS)) = 1 := by decide +kernel
-- `sshr` (`U = 0`) is not modelled
example : errKind (r .ERR (exec_inst (.DPSFP (.Advanced_simd_shift_by_immediate
    { Q := 0#1, U := 0#1, immh := 0b0100#4, immb := 0b001#3, opcode := 0b00000#5, Rn := 1#5,
      Rd := 4#5 })) sS)) = 2 := by decide +kernel

end Arm.ShiftImmWitness

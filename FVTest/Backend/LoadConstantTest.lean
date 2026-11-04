import FV.Backend.Asm
import FV.Backend.Encode

/-!
# `loadConst64` against Cranelift's `Inst::load_constant`

Gate 1 of AG-2j (#554). Each case gives the value, the instructions Cranelift's
`Inst::load_constant` (`isa/aarch64/inst/mod.rs`) emits for it (computed by hand from the Rust,
case by case, as assembly text) and the machine words `llvm-mc -triple=aarch64 -show-encoding`
assembles that text to. The `#guard`s check that `loadConst64 (x16) value` prints that text
(`Insn.asm`) and encodes to those words (`Insn.encode`).

`%huge_slots` (`runtests/stack.clif`): the stock word `f0437db2` (`0xb27d43f0`) is
`mov x16, #0xffff8` (`orr x16, xzr, #0xffff8`, `llvm-mc --disassemble`): the slot offset
1048568 in `mem_finalize`, a bitmask immediate (case 3).
-/

namespace Backend.LoadConstantTest

open Backend

/-- No labels; the instruction at offset 0. -/
def env0 : Env := ⟨0, fun _ => none⟩

/-- The instructions of a line list (labels and words dropped). -/
def insns (ls : List Line) : List Insn :=
  ls.filterMap fun | .ins i _ => some i | _ => none

/-- `loadConst64 x16 v` as assembly text. -/
def asmOf (v : Nat) : List String := (insns (loadConst64 (.x 16) v)).map (·.asm 0)

/-- `loadConst64 x16 v` as machine words. -/
def wordsOf (v : Nat) : List (Option (BitVec 32)) :=
  (insns (loadConst64 (.x 16) v)).map fun i => (i.encode env0).toOption

/-- One test case: value, expected `load_constant` text, `llvm-mc` words of that text. -/
structure Case where
  value : Nat
  asm : List String
  words : List (BitVec 32)

def cases : List Case := [
  -- case 1: `MoveWideConst::maybe_from_u64(0)` is `movz #0`
  ⟨0, ["movz x16, #0x0, lsl #0"], [0xd2800010]⟩,
  ⟨0x10000, ["movz x16, #0x1, lsl #16"], [0xd2a00030]⟩,
  ⟨0x5550, ["movz x16, #0x5550, lsl #0"], [0xd28aaa10]⟩,
  ⟨0x1_0000_0000, ["movz x16, #0x1, lsl #32"], [0xd2c00030]⟩,
  -- case 2: `!value` has one nonzero halfword
  ⟨0xffff_ffff_ffff_0000, ["movn x16, #0xffff, lsl #0"], [0x929ffff0]⟩,
  ⟨0xffff_ffff_ffff_fff0, ["movn x16, #0xf, lsl #0"], [0x928001f0]⟩,
  ⟨0xffff_1234_ffff_ffff, ["movn x16, #0xedcb, lsl #32"], [0x92ddb970]⟩,
  -- case 3: bitmask immediate
  ⟨0x5555_5555_5555_5555, ["orr x16, xzr, #0x5555555555555555"], [0xb200f3f0]⟩,
  -- `%huge_slots`: stock `f0437db2`
  ⟨0xffff8, ["orr x16, xzr, #0xffff8"], [0xb27d43f0]⟩,
  -- case 4, 32-bit (`value >> 32 == 0`): `movz w`/`movk w` (the frame-size loads)
  ⟨0x12345, ["movz w16, #0x2345, lsl #0", "movk w16, #0x1, lsl #16"],
    [0x528468b0, 0x72a00030]⟩,
  ⟨0x12340, ["movz w16, #0x2340, lsl #0", "movk w16, #0x1, lsl #16"],
    [0x52846810, 0x72a00030]⟩,
  -- case 4, 32-bit, first inverted: `negated = 0xedcb` has a zero halfword, `value` none
  ⟨0xffff_1234, ["movn w16, #0xedcb, lsl #0"], [0x129db970]⟩,
  -- case 4, 64-bit, zero halfwords skipped
  ⟨0x1_0000_1234, ["movz x16, #0x1234, lsl #0", "movk x16, #0x1, lsl #32"],
    [0xd2824690, 0xf2c00030]⟩,
  ⟨0x1234_5678_9abc_def0,
    ["movz x16, #0xdef0, lsl #0", "movk x16, #0x9abc, lsl #16", "movk x16, #0x5678, lsl #32",
     "movk x16, #0x1234, lsl #48"],
    [0xd29bde10, 0xf2b35790, 0xf2cacf10, 0xf2e24690]⟩,
  -- case 4, 64-bit, first inverted, `0xffff` halfwords skipped
  ⟨0xffff_ffff_1234_5678, ["movn x16, #0xa987, lsl #0", "movk x16, #0x1234, lsl #16"],
    [0x929530f0, 0xf2a24690]⟩]

#guard cases.all fun c => asmOf c.value == c.asm
#guard cases.all fun c => wordsOf c.value == c.words.map some

-- `value` is taken mod 2^64
#guard asmOf (2 ^ 64 + 0x12345) == asmOf 0x12345

-- the frame-size load of the 6 functions: 32-bit forms below 2^32, 64-bit at and above
#guard asmOf 0x2_0010 == ["movz w16, #0x10, lsl #0", "movk w16, #0x2, lsl #16"]
#guard asmOf 0x1_0002_0010 ==
  ["movz x16, #0x10, lsl #0", "movk x16, #0x2, lsl #16", "movk x16, #0x1, lsl #32"]

end Backend.LoadConstantTest

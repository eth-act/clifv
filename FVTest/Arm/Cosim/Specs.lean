/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.

Co-simulation test generators: one `Spec` per instruction form, each producing random valid
encodings and random initial states (see `Harness.lean`). The forms are the instructions
Cranelift 0.136.1 emits at `opt_level=none` for the `clif-subset-v1` emitter subset (see
`docs/contracts/arm.md`), each with all of its encoding-field variations.
-/
import FVTest.Arm.Cosim.Harness

namespace Arm.Cosim

structure Spec where
  /-- Instruction form, as reported (e.g. `"adds (imm)"`). -/
  name : String
  /-- Batch: all specs with the same `batch` are run in one program. -/
  batch : String
  /-- Generator for test number `i` of its batch. -/
  gen : Nat → GenM TestCase

/-- Assemble fields `(value, width)`, most significant first, into an instruction word. -/
def enc (fs : List (Nat × Nat)) : UInt32 :=
  (fs.foldl (fun acc (v, n) => (acc <<< n) ||| (v % 2 ^ n)) 0).toUInt32

def reg : GenM Nat := below 32

/-- A SIMD&FP register other than v31 (the harness's scratch register). -/
def vreg : GenM Nat := below 31

/-- Two's-complement `n`-bit encoding of `j`. -/
def twos (n : Nat) (j : Int) : Nat := (j % (2 ^ n : Int)).toNat

/-- Signed interpretation of an `n`-bit field. -/
def sext (n v : Nat) : Int := if v ≥ 2 ^ (n - 1) then (v : Int) - 2 ^ n else v

/-! ## Data processing (immediate) -/

def addSubImm (op S : Nat) (name : String) : Spec := ⟨name, "dpi", fun _ => do
  let inst := enc [(← bits 1, 1), (op, 1), (S, 1), (0b100010, 6), (← bits 1, 1), (← bits 12, 12),
    (← reg, 5), (← reg, 5)]
  randomCase name inst⟩

/-- ASL `DecodeBitMasks` validity for a logical immediate. -/
def validBitmask (sf N imms : Nat) : Bool :=
  if sf == 0 && N == 1 then false else
  let x := (N <<< 6) ||| (63 - imms % 64)
  if x == 0 then false else
  let len := Nat.log2 x
  if len < 1 then false else
  let levels := 2 ^ len - 1
  (imms &&& levels) != levels

partial def logicalImm (opc : Nat) (name : String) : Spec := ⟨name, "dpi", fun _ => do
  let rec go : GenM UInt32 := do
    let sf ← bits 1
    let N ← if sf == 1 then bits 1 else pure 0
    let immr ← bits 6
    let imms ← bits 6
    if validBitmask sf N imms then
      return enc [(sf, 1), (opc, 2), (0b100100, 6), (N, 1), (immr, 6), (imms, 6), (← reg, 5), (← reg, 5)]
    else go
  randomCase name (← go)⟩

def moveWide (opc : Nat) (name : String) : Spec := ⟨name, "dpi", fun _ => do
  let sf ← bits 1
  let hw ← if sf == 1 then bits 2 else bits 1
  randomCase name (enc [(sf, 1), (opc, 2), (0b100101, 6), (hw, 2), (← bits 16, 16), (← reg, 5)])⟩

def bitfield (opc : Nat) (name : String) : Spec := ⟨name, "dpi", fun _ => do
  let sf ← bits 1
  let w := if sf == 1 then 6 else 5
  randomCase name (enc [(sf, 1), (opc, 2), (0b100110, 6), (sf, 1), (← bits w, 6), (← bits w, 6),
    (← reg, 5), (← reg, 5)])⟩

def extract : Spec := ⟨"extr", "dpi", fun _ => do
  let sf ← bits 1
  let w := if sf == 1 then 6 else 5
  randomCase "extr" (enc [(sf, 1), (0, 2), (0b100111, 6), (sf, 1), (0, 1), (← reg, 5), (← bits w, 6),
    (← reg, 5), (← reg, 5)])⟩

def pcRel (op : Nat) (name : String) : Spec := ⟨name, "dpi", fun _ => do
  randomCase name (enc [(op, 1), (← bits 2, 2), (0b10000, 5), (← bits 19, 19), (← reg, 5)])⟩

/-! ## Data processing (register) -/

def addSubShifted (op S : Nat) (name : String) : Spec := ⟨name, "dpr", fun _ => do
  let sf ← bits 1
  randomCase name (enc [(sf, 1), (op, 1), (S, 1), (0b01011, 5), (← below 3, 2), (0, 1), (← reg, 5),
    (← bits (if sf == 1 then 6 else 5), 6), (← reg, 5), (← reg, 5)])⟩

def addSubExt (op S : Nat) (name : String) : Spec := ⟨name, "dpr", fun _ => do
  randomCase name (enc [(← bits 1, 1), (op, 1), (S, 1), (0b01011, 5), (0, 2), (1, 1), (← reg, 5),
    (← bits 3, 3), (← below 5, 3), (← reg, 5), (← reg, 5)])⟩

def logicalShifted (opc N : Nat) (name : String) : Spec := ⟨name, "dpr", fun _ => do
  let sf ← bits 1
  randomCase name (enc [(sf, 1), (opc, 2), (0b01010, 5), (← bits 2, 2), (N, 1), (← reg, 5),
    (← bits (if sf == 1 then 6 else 5), 6), (← reg, 5), (← reg, 5)])⟩

def dp2 (opcode : Nat) (name : String) : Spec := ⟨name, "dpr", fun _ => do
  randomCase name (enc [(← bits 1, 1), (0, 1), (0, 1), (0b11010110, 8), (← reg, 5), (opcode, 6),
    (← reg, 5), (← reg, 5)])⟩

def dp3 (sf? : Option Nat) (op31 o0 : Nat) (raOnes : Bool) (name : String) : Spec :=
  ⟨name, "dpr", fun _ => do
    let sf ← match sf? with | some v => pure v | none => bits 1
    let ra ← if raOnes then pure 31 else reg
    randomCase name (enc [(sf, 1), (0, 2), (0b11011, 5), (op31, 3), (← reg, 5), (o0, 1), (ra, 5),
      (← reg, 5), (← reg, 5)])⟩

def dp1 (sf? : Option Nat) (opcode : Nat) (name : String) : Spec := ⟨name, "dpr", fun _ => do
  let sf ← match sf? with | some v => pure v | none => bits 1
  randomCase name (enc [(sf, 1), (1, 1), (0, 1), (0b11010110, 8), (0, 5), (opcode, 6), (← reg, 5),
    (← reg, 5)])⟩

def condSel (op op2 : Nat) (name : String) : Spec := ⟨name, "dpr", fun _ => do
  randomCase name (enc [(← bits 1, 1), (op, 1), (0, 1), (0b11010100, 8), (← reg, 5), (← bits 4, 4),
    (op2, 2), (← reg, 5), (← reg, 5)])⟩

def condCmp (op imm : Nat) (name : String) : Spec := ⟨name, "dpr", fun _ => do
  randomCase name (enc [(← bits 1, 1), (op, 1), (1, 1), (0b11010010, 8), (← bits 5, 5), (← bits 4, 4),
    (imm, 1), (0, 1), (← reg, 5), (0, 1), (← bits 4, 4)])⟩

def addSubCarry (op S : Nat) (name : String) : Spec := ⟨name, "dpr", fun _ => do
  randomCase name (enc [(← bits 1, 1), (op, 1), (S, 1), (0b11010000, 8), (← reg, 5), (0, 6),
    (← reg, 5), (← reg, 5)])⟩

/-! ## Branches, hints, udf -/

/-- A random landing-pad index `j ∈ [-padK, padK] \ {0}`. -/
def padIdx : GenM Int := do
  let j : Int := (← below (2 * padK)) - padK
  return if j ≥ 0 then j + 1 else j

def branchCase (name : String) (inst : UInt32) : GenM TestCase := do
  return { (← randomCase name inst) with kind := .branch }

def bcond : Spec := ⟨"b.cond", "br", fun _ => do
  branchCase "b.cond" (enc [(0b01010100, 8), (twos 19 (← padIdx), 19), (0, 1), (← bits 4, 4)])⟩

def cbranch (op : Nat) (name : String) : Spec := ⟨name, "br", fun _ => do
  let rt ← reg
  let tc ← branchCase name (enc [(← bits 1, 1), (0b011010, 6), (op, 1), (twos 19 (← padIdx), 19), (rt, 5)])
  -- Make the tested register zero (in the tested width) about a third of the time.
  match ← below 3 with
  | 0 => return tc.setReg rt "0"
  | 1 => return tc.setReg rt "0xffffffff00000000"
  | _ => return tc⟩

def tbranch (op : Nat) (name : String) : Spec := ⟨name, "br", fun _ => do
  branchCase name (enc [(← bits 1, 1), (0b011011, 6), (op, 1), (← bits 5, 5), (twos 14 (← padIdx), 14),
    (← reg, 5)])⟩

def uncondImm (op : Nat) (name : String) : Spec := ⟨name, "br", fun _ => do
  branchCase name (enc [(op, 1), (0b00101, 5), (twos 26 (← padIdx), 26)])⟩

/-- `br`/`blr`/`ret`: the target register holds a landing-pad address. -/
def uncondReg (opc : Nat) (name : String) (rn? : Option Nat := none) : Spec := ⟨name, "br", fun i => do
  let rn ← match rn? with | some r => pure r | none => below 31
  let tc ← branchCase name (enc [(0b1101011, 7), (opc, 4), (0b11111, 5), (0, 6), (rn, 5), (0, 5)])
  return tc.setReg rn (padLabel i (← padIdx))⟩

def hint (w : UInt32) (name : String) : Spec := ⟨name, "misc", fun _ => randomCase name w⟩

def udf : Spec := ⟨"udf", "misc", fun _ => do
  return { (← randomCase "udf" (enc [(0, 16), (← bits 16, 16)])) with kind := .udf }⟩

/-! ## Loads and stores (GPR) -/

/-- `(size, opc, access bytes, mnemonic)` for single-register GPR loads/stores. -/
def ldstVariants : List (Nat × Nat × Nat × String) :=
  [(0, 0, 1, "strb"), (0, 1, 1, "ldrb"), (0, 2, 1, "ldrsb (x)"), (0, 3, 1, "ldrsb (w)"),
   (1, 0, 2, "strh"), (1, 1, 2, "ldrh"), (1, 2, 2, "ldrsh (x)"), (1, 3, 2, "ldrsh (w)"),
   (2, 0, 4, "str (w)"), (2, 1, 4, "ldr (w)"), (2, 2, 4, "ldrsw"),
   (3, 0, 8, "str (x)"), (3, 1, 8, "ldr (x)")]

/-- `(size, opc, access bytes, mnemonic)` for single-register SIMD&FP loads/stores
(C7.2 LDR/STR (immediate / register, SIMD&FP), LDUR/STUR (SIMD&FP)). -/
def ldstSimdVariants : List (Nat × Nat × Nat × String) :=
  [(0, 0, 1, "str (b)"), (0, 1, 1, "ldr (b)"), (1, 0, 2, "str (h)"), (1, 1, 2, "ldr (h)"),
   (2, 0, 4, "str (s)"), (2, 1, 4, "ldr (s)"), (3, 0, 8, "str (d)"), (3, 1, 8, "ldr (d)"),
   (0, 2, 16, "str (q)"), (0, 3, 16, "ldr (q)")]

inductive Mode where
  | uimm | unscaled | pre | post | regoff
deriving BEq

def Mode.suffix : Mode → String
  | .uimm => "[xn, #uimm]" | .unscaled => "[xn, #simm] (unscaled)" | .pre => "[xn, #simm]!"
  | .post => "[xn], #simm" | .regoff => "[xn, xm, ext]"

/-- ASL `ExtendReg(m, option, shift)` on a concrete 64-bit value. -/
def extendVal (v : Nat) (option shift : Nat) : Nat :=
  let x := match option with
    | 0b010 => v % 2 ^ 32
    | 0b110 => let w := v % 2 ^ 32; if w ≥ 2 ^ 31 then w + (2 ^ 64 - 2 ^ 32) else w
    | _ => v % 2 ^ 64
  (x <<< shift) % 2 ^ 64

/-- Signed interpretation of a 64-bit value. -/
def signed64 (v : Nat) : Int := sext 64 (v % 2 ^ 64)

/-- Choose the buffer offset `e` of the access (so `[e, e + bytes)` ⊆ the 64-byte buffer); when
the base is SP it must also make `SP = buf + e - off` 16-byte aligned. -/
def chooseE (bytes : Nat) (off : Int) (spBase : Bool) : GenM Nat := do
  if spBase then
    let r := (off % 16).toNat
    let kmax := (64 - bytes - r) / 16
    return r + 16 * (← below (kmax + 1))
  else below (64 - bytes + 1)

/-- A single-register load/store; `V = 1`: SIMD&FP (`Rt` a v register, never v31). -/
def ldst (V size opc bytes : Nat) (mnem : String) (mode : Mode) : Spec :=
  ⟨s!"{mnem} {mode.suffix}", s!"ldst-{mode.suffix}", fun i => do
    let name := s!"{mnem} {mode.suffix}"
    let scale := Nat.log2 bytes
    let rn ← reg
    let wback := mode == .pre || mode == .post
    let mut rt0 ← if V == 1 then vreg else reg
    for _ in [0:100] do
      if V == 0 && wback && rt0 == rn && rn != 31 then rt0 ← reg
    let rt := if V == 0 && wback && rt0 == rn && rn != 31 then (rn + 1) % 31 else rt0
    let hdr := [(size, 2), (0b111, 3), (V, 1)]
    let (inst, off, setRm) ← match mode with
      | .uimm =>
        let imm ← bits 12
        pure (enc (hdr ++ [(0b01, 2), (opc, 2), (imm, 12), (rn, 5), (rt, 5)]),
          ((imm * bytes : Nat) : Int), (none : Option (Nat × Nat)))
      | .unscaled | .pre | .post =>
        let imm ← bits 9
        let tag := match mode with | .unscaled => 0b00 | .pre => 0b11 | _ => 0b01
        pure (enc (hdr ++ [(0b00, 2), (opc, 2), (0, 1), (imm, 9), (tag, 2), (rn, 5), (rt, 5)]),
          (if mode == .post then 0 else sext 9 imm), none)
      | .regoff =>
        let option ← pick #[0b010, 0b011, 0b110, 0b111]
        let S ← bits 1
        let mut rm0 ← reg
        for _ in [0:100] do
          if rm0 == rn then rm0 ← reg
        let rm := if rm0 == rn then (rn + 1) % 32 else rm0
        -- Keep the offset register value small half of the time, so offsets are realistic.
        let v ← if ← coin then pure (← randVal).toNat else pure ((← bits 12) : Nat)
        let v := if rm == 31 then 0 else v
        pure (enc (hdr ++ [(0b00, 2), (opc, 2), (1, 1), (rm, 5), (option, 3), (S, 1), (0b10, 2),
          (rn, 5), (rt, 5)]), signed64 (extendVal v option (if S == 1 then scale else 0)),
          if rm == 31 then none else some (rm, v))
    let e ← chooseE bytes off (rn == 31)
    let mut tc ← if V == 1 then randomFpCase name (bytes == 8) inst else randomCase name inst
    if let some (rm, v) := setRm then tc := tc.setReg rm (hex v)
    let delta := signed64 (((e : Int) - off) % (2 ^ 64 : Int)).toNat
    return tc.setReg rn (bufPlus i delta)⟩

/-- Load/store pair: `(opc, L, mnemonic)`; `mode` is 0b001 post, 0b011 pre, 0b010 offset;
`V = 1`: SIMD&FP (`opc` 00 S, 01 D, 10 Q). -/
def ldstPair (V opc L : Nat) (mnem : String) (mode : Nat) : Spec :=
  let suffix := match mode with
    | 0b001 => "[xn], #simm" | 0b011 => "[xn, #simm]!" | _ => "[xn, #simm]"
  ⟨s!"{mnem} {suffix}", "ldst-pair", fun i => do
    let name := s!"{mnem} {suffix}"
    let scale := if V == 1 then 2 + opc else if opc == 0b10 then 3 else 2
    let bytes := 2 * 2 ^ scale
    let wback := mode != 0b010
    let treg : GenM Nat := if V == 1 then vreg else reg
    let rn ← reg
    let mut rt ← treg
    let mut rt2 ← treg
    for _ in [0:1000] do
      if (L == 1 && rt == rt2) || (V == 0 && wback && rn != 31 && (rt == rn || rt2 == rn)) then
        rt ← treg
        rt2 ← treg
    let imm ← bits 7
    let off : Int := if mode == 0b001 then 0 else sext 7 imm * 2 ^ scale
    let inst := enc [(opc, 2), (0b101, 3), (V, 1), (mode, 3), (L, 1), (imm, 7), (rt2, 5), (rn, 5), (rt, 5)]
    let e ← chooseE bytes off (rn == 31)
    let tc ← if V == 1 then randomFpCase name (scale == 3) inst else randomCase name inst
    let delta := signed64 (((e : Int) - off) % (2 ^ 64 : Int)).toNat
    return tc.setReg rn (bufPlus i delta)⟩

/-- LDR (literal) `(opc, V)`: the target is in one of the test's literal pools
(`TestCase.pool`: 64 bytes at `pc - 64` and at `pc + 8`), at any word offset there. -/
def ldrLiteral (opc V bytes : Nat) (mnem : String) : Spec := ⟨mnem, "ldst-literal", fun _ => do
  let k ← below ((64 - bytes) / 4 + 1)
  let off : Int := if ← coin then -64 + 4 * k else 8 + 4 * k
  let rt ← if V == 1 then vreg else reg
  let inst := enc [(opc, 2), (0b011, 3), (V, 1), (0b00, 2), (twos 19 (off / 4), 19), (rt, 5)]
  let tc ← if V == 1 then randomFpCase mnem (bytes == 8) inst else randomCase mnem inst
  return { tc with pool := true }⟩

/-- `ldar`/`stlr`/`ldaxr` (`(o2, L)`; C4.1 "Load/store exclusive"/"Load-acquire/store-release",
Rs = Rt2 = 11111, o0 = 1): no offset, and the address `bytes`-aligned, which these require.
`stlxr` is not co-simulated: single-instruction cases cannot hold qemu's exclusive monitor
(qemu fails a lone `stlxr`), while the model's exclusive store always succeeds. -/
def ldstExcl (o2 L : Nat) (mnem : String) : Spec := ⟨mnem, "ldst-excl", fun i => do
  let size ← bits 2
  let bytes := 2 ^ size
  let rn ← reg
  let rt ← reg
  let inst := enc [(size, 2), (0b001000, 6), (o2, 1), (L, 1), (0, 1), (31, 5), (1, 1), (31, 5),
    (rn, 5), (rt, 5)]
  let e ← chooseE bytes 0 (rn == 31)
  let tc ← randomCase mnem inst
  return tc.setReg rn (bufPlus i (e - e % bytes : Nat))⟩

/-! ## SIMD&FP (popcnt sequence) -/

def fmovGen (sf ftype opcode : Nat) (name : String) (toV : Bool) : Spec := ⟨name, "simd", fun _ => do
  let rn ← if toV then reg else vreg
  let rd ← if toV then vreg else reg
  randomCase name (enc [(sf, 1), (0, 1), (0, 1), (0b11110, 5), (ftype, 2), (1, 1), (0, 2), (opcode, 3),
    (0, 6), (rn, 5), (rd, 5)])⟩

def cnt : Spec := ⟨"cnt", "simd", fun _ => do
  randomCase "cnt" (enc [(0, 1), (← bits 1, 1), (0, 1), (0b01110, 5), (0, 2), (0b10000, 5), (0b00101, 5),
    (0b10, 2), (← vreg, 5), (← vreg, 5)])⟩

/-- `addv` (U = 0, opcode 11011) / `uaddlv` (U = 1, opcode 00011). -/
def acrossLanes (U opcode : Nat) (name : String) : Spec := ⟨name, "simd", fun _ => do
  let (size, Q) ← pick #[(0, 0), (0, 1), (1, 0), (1, 1), (2, 1)]
  randomCase name (enc [(0, 1), (Q, 1), (U, 1), (0b01110, 5), (size, 2), (0b11000, 5), (opcode, 5),
    (0b10, 2), (← vreg, 5), (← vreg, 5)])⟩

def addp : Spec := ⟨"addp (vector)", "simd", fun _ => do
  let (size, Q) ← pick #[(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 1)]
  randomCase "addp (vector)" (enc [(0, 1), (Q, 1), (0, 1), (0b01110, 5), (size, 2), (1, 1), (← vreg, 5),
    (0b10111, 5), (1, 1), (← vreg, 5), (← vreg, 5)])⟩

def umov : Spec := ⟨"umov", "simd", fun _ => do
  let (imm5, Q) ← pick #[(1, 0), (2, 0), (4, 0), (8, 1)]
  let idx ← match imm5 with
    | 1 => bits 4 | 2 => bits 3 | 4 => bits 2 | _ => bits 1
  let imm5 := imm5 ||| (idx <<< (Nat.log2 imm5 + 1))
  randomCase "umov" (enc [(0, 1), (Q, 1), (0, 1), (0b01110000, 8), (imm5, 5), (0, 1), (0b0111, 4),
    (1, 1), (← vreg, 5), (← reg, 5)])⟩

/-! ## Scalar floating point and SIMD&FP data movement (FV additions) -/

/-- `name (s)` / `name (d)` for `ftype` 00 / 01. -/
def fpName (name : String) (ftype : Nat) : String :=
  s!"{name} ({if ftype == 1 then "d" else "s"})"

/-- Floating-point data-processing (1 source) with `opcode` (FMOV/FABS/FNEG …). -/
def fp1 (opcode : Nat) (name : String) (ftype : Nat) : Spec :=
  let name := fpName name ftype
  ⟨name, "fp", fun _ => do
    randomFpCase name (ftype == 1) (enc [(0, 1), (0, 1), (0, 1), (0b11110, 5), (ftype, 2), (1, 1),
      (opcode, 6), (0b10000, 5), (← vreg, 5), (← vreg, 5)])⟩

/-- FMOV (scalar, immediate): every `imm8`. -/
def fmovImm (ftype : Nat) : Spec :=
  let name := fpName "fmov (imm)" ftype
  ⟨name, "fp", fun _ => do
    randomFpCase name (ftype == 1) (enc [(0, 1), (0, 1), (0, 1), (0b11110, 5), (ftype, 2), (1, 1),
      (← bits 8, 8), (0b100, 3), (0, 5), (← vreg, 5)])⟩

/-- FCSEL: every condition, random NZCV. -/
def fcsel (ftype : Nat) : Spec :=
  let name := fpName "fcsel" ftype
  ⟨name, "fp", fun _ => do
    randomFpCase name (ftype == 1) (enc [(0, 1), (0, 1), (0, 1), (0b11110, 5), (ftype, 2), (1, 1),
      (← vreg, 5), (← bits 4, 4), (0b11, 2), (← vreg, 5), (← vreg, 5)])⟩

/-- Advanced SIMD modified immediate: every allocated `(Q, op, cmode, o2)` (C4.1 table:
`o2 = 1` only with `op:cmode = 0:1111`; `op:cmode = 1:1111` only with `Q = 1`), every `imm8`. -/
partial def modImm : Spec := ⟨"movi/mvni/orr/bic/fmov (vector, imm)", "simd-imm", fun _ => do
  let rec go : GenM (Nat × Nat × Nat × Nat) := do
    let Q ← bits 1
    let op ← bits 1
    let cmode ← bits 4
    let o2 ← bits 1
    if (cmode == 15 && op == 1 && Q == 0) || (o2 == 1 && !(cmode == 15 && op == 0)) then go
    else return (Q, op, cmode, o2)
  let (Q, op, cmode, o2) ← go
  let imm8 ← bits 8
  randomCase "movi/mvni/orr/bic/fmov (vector, imm)" (enc [(0, 1), (Q, 1), (op, 1),
    (0b0111100000, 10), (imm8 >>> 5, 3), (cmode, 4), (o2, 1), (1, 1), (imm8 % 32, 5), (← vreg, 5)])⟩

/-- `movi vd.2s, #0` (Cranelift's zero `f32const`/`f64const`). -/
def moviZero : Spec := ⟨"movi (2s, #0)", "simd-imm", fun _ => do
  randomFpCase "movi (2s, #0)" (← coin) (enc [(0, 1), (0, 1), (0, 1), (0b0111100000, 10), (0, 3),
    (0, 4), (0, 1), (1, 1), (0, 5), (← vreg, 5)])⟩

/-- ORR (vector, register), 8B/16B; half of the cases are `mov vd.<T>, vn.<T>` (`Rm = Rn`,
Cranelift's `FpuMove128` register move). -/
def orrVector : Spec := ⟨"orr (vector)", "simd", fun _ => do
  let rn ← vreg
  let rm ← if ← coin then pure rn else vreg
  randomFpCase "orr (vector)" (← coin) (enc [(0, 1), (← bits 1, 1), (0, 1), (0b01110, 5), (0b10, 2),
    (1, 1), (rm, 5), (0b00011, 5), (1, 1), (rn, 5), (← vreg, 5)])⟩

/-! ## Scalar floating-point arithmetic, compare and conversion (FV additions, FPCR = 0) -/

/-- The float (`dbl`: binary64, else binary32) in the low bits of `v{r}`. -/
def TestCase.fp (tc : TestCase) (r : Nat) (dbl : Bool) : Nat :=
  (tc.simd[r]!.1.toNat) % 2 ^ (if dbl then 64 else 32)

/-- Set the float in the low bits of `v{r}` (the other bits unchanged). -/
def TestCase.setFp (tc : TestCase) (r : Nat) (dbl : Bool) (v : Nat) : TestCase :=
  let (lo, hi) := tc.simd[r]!
  let lo := if dbl then v.toUInt64 else (lo &&& 0xFFFFFFFF00000000) ||| v.toUInt64
  { tc with simd := tc.simd.set! r (lo, hi) }

/-- Operand pairs `(v{rn}, v{rm})` that stress rounding: with probability 1/5 each, `v{rm}` is
half an ulp of `v{rn}` (the sum is a tie), `v{rn} = 3 · 2^j` and `v{rm} = 1 + k · ulp` with `k`
odd (the product is a tie), `v{rm} = ±v{rn}` (exact cancellation, equal operands), or
`v{rm}` is a short power-of-two multiple of `v{rn}`'s ulp; otherwise both stay random. -/
def fpPair (tc : TestCase) (dbl : Bool) (rn rm : Nat) : GenM TestCase := do
  let (E, F) := if dbl then (11, 52) else (8, 23)
  let bias := 2 ^ (E - 1) - 1
  let a := tc.fp rn dbl
  let ea := a / 2 ^ F % 2 ^ E
  if rn == rm then return tc
  match ← below 5 with
  | 0 =>
    if ea ≥ F + 2 && ea < 2 ^ E - 1 then
      return tc.setFp rm dbl (fpBits E F (← bits 1) (ea - F - 1) 0)
    else return tc
  | 1 =>
    let j ← below 9
    let tc := tc.setFp rn dbl (fpBits E F (← bits 1) (bias + 1 + j - 4) (2 ^ (F - 1)))
    return tc.setFp rm dbl (fpBits E F (← bits 1) bias (2 * (← below 8) + 1))
  | 2 => return tc.setFp rm dbl ((a + (← bits 1) * 2 ^ (E + F)) % 2 ^ (1 + E + F))
  | 3 =>
    if ea ≥ F + 2 && ea < 2 ^ E - 1 then
      return tc.setFp rm dbl (fpBits E F (← bits 1) (ea - F + (← below 3) - 1) (← bits 2))
    else return tc
  | _ => return tc

/-- Floating-point data-processing (2 source) with `opcode` (FMUL/FDIV/FADD/FSUB/FMAX/FMIN/
FNMUL). -/
def fp2 (opcode : Nat) (name : String) (ftype : Nat) : Spec :=
  let name := fpName name ftype
  ⟨name, "fp-arith", fun _ => do
    let rn ← vreg
    let rm ← vreg
    let tc ← randomFpCase name (ftype == 1) (enc [(0, 1), (0, 1), (0, 1), (0b11110, 5), (ftype, 2),
      (1, 1), (rm, 5), (opcode, 4), (0b10, 2), (rn, 5), (← vreg, 5)])
    fpPair tc (ftype == 1) rn rm⟩

/-- Floating-point data-processing (3 source) `(o1, o0)`: FMADD/FMSUB/FNMADD/FNMSUB. A fifth of
the cases set `v{ra} = -round(v{rn} · v{rm})` (the fused result is the product's rounding
error). -/
def fp3 (o1 o0 : Nat) (name : String) (ftype : Nat) : Spec :=
  let name := fpName name ftype
  ⟨name, "fp-arith", fun _ => do
    let dbl := ftype == 1
    let rn ← vreg
    let rm ← vreg
    let ra ← vreg
    let tc ← randomFpCase name dbl (enc [(0, 1), (0, 1), (0, 1), (0b11111, 5), (ftype, 2), (o1, 1),
      (rm, 5), (o0, 1), (ra, 5), (rn, 5), (← vreg, 5)])
    let tc ← fpPair tc dbl rn rm
    if ra == rn || ra == rm || (← below 5) != 0 then return tc
    let p : Nat :=
      if dbl then (IEEE.neg .b64 (IEEE.mul .b64 .rne (BitVec.ofNat 64 (tc.fp rn true))
        (BitVec.ofNat 64 (tc.fp rm true)))).toNat
      else (IEEE.neg .b32 (IEEE.mul .b32 .rne (BitVec.ofNat 32 (tc.fp rn false))
        (BitVec.ofNat 32 (tc.fp rm false)))).toNat
    return tc.setFp ra dbl p⟩

/-- FCMP/FCMPE (register, `#0.0`): `opcode2` 00000/01000/10000/11000 (`Rm = 0` for `#0.0`);
operand pairs as `fpPair`, and a fifth of the register cases compare `±0`. -/
def fcmp (opcode2 : Nat) (name : String) (ftype : Nat) : Spec :=
  let name := fpName name ftype
  ⟨name, "fp-arith", fun _ => do
    let dbl := ftype == 1
    let rn ← vreg
    let rm ← if opcode2 % 16 == 8 then pure 0 else vreg
    let tc ← randomFpCase name dbl (enc [(0, 1), (0, 1), (0, 1), (0b11110, 5), (ftype, 2), (1, 1),
      (rm, 5), (0, 2), (0b1000, 4), (rn, 5), (opcode2, 5)])
    let tc ← fpPair tc dbl rn rm
    if (← below 5) == 0 then
      return tc.setFp rn dbl ((← bits 1) * 2 ^ (if dbl then 63 else 31))
    else return tc⟩

/-- FP → integer conversion (`rmode`, `opcode`; Conversion between floating-point and integer):
`sf` random, Rd a GPR (31 = ZR). -/
def fcvtToInt (rmode opcode : Nat) (name : String) (ftype : Nat) : Spec :=
  let name := fpName name ftype
  ⟨name, "fp-cvt", fun _ => do
    randomFpCase name (ftype == 1) (enc [(← bits 1, 1), (0, 1), (0, 1), (0b11110, 5), (ftype, 2),
      (1, 1), (rmode, 2), (opcode, 3), (0, 6), (← vreg, 5), (← reg, 5)])⟩

/-- SCVTF/UCVTF (integer → FP): `sf` random, Rn a GPR (31 = ZR) with edge-biased values. -/
def cvtToFp (opcode : Nat) (name : String) (ftype : Nat) : Spec :=
  let name := fpName name ftype
  ⟨name, "fp-cvt", fun _ => do
    randomFpCase name (ftype == 1) (enc [(← bits 1, 1), (0, 1), (0, 1), (0b11110, 5), (ftype, 2),
      (1, 1), (0, 2), (opcode, 3), (0, 6), (← reg, 5), (← vreg, 5)])⟩

/-! ## All specs -/

def allSpecs : List Spec :=
  [ addSubImm 0 0 "add (imm)", addSubImm 0 1 "adds (imm)", addSubImm 1 0 "sub (imm)",
    addSubImm 1 1 "subs (imm)",
    logicalImm 0 "and (imm)", logicalImm 1 "orr (imm)", logicalImm 2 "eor (imm)",
    logicalImm 3 "ands (imm)",
    moveWide 0 "movn", moveWide 2 "movz", moveWide 3 "movk",
    bitfield 0 "sbfm", bitfield 1 "bfm", bitfield 2 "ubfm",
    extract, pcRel 0 "adr", pcRel 1 "adrp",
    addSubShifted 0 0 "add (shifted)", addSubShifted 0 1 "adds (shifted)",
    addSubShifted 1 0 "sub (shifted)", addSubShifted 1 1 "subs (shifted)",
    addSubExt 0 0 "add (extended)", addSubExt 0 1 "adds (extended)",
    addSubExt 1 0 "sub (extended)", addSubExt 1 1 "subs (extended)",
    logicalShifted 0 0 "and (shifted)", logicalShifted 0 1 "bic", logicalShifted 1 0 "orr (shifted)",
    logicalShifted 1 1 "orn", logicalShifted 2 0 "eor (shifted)", logicalShifted 2 1 "eon",
    logicalShifted 3 0 "ands (shifted)", logicalShifted 3 1 "bics",
    dp2 0b000010 "udiv", dp2 0b000011 "sdiv", dp2 0b001000 "lslv", dp2 0b001001 "lsrv",
    dp2 0b001010 "asrv", dp2 0b001011 "rorv",
    dp3 none 0b000 0 false "madd", dp3 none 0b000 1 false "msub",
    dp3 (some 1) 0b010 0 true "smulh", dp3 (some 1) 0b110 0 true "umulh",
    dp1 none 0b000000 "rbit", dp1 none 0b000100 "clz", dp1 none 0b000101 "cls",
    dp1 none 0b000001 "rev16", dp1 (some 0) 0b000010 "rev (32)", dp1 (some 1) 0b000010 "rev32",
    dp1 (some 1) 0b000011 "rev (64)",
    condSel 0 0 "csel", condSel 0 1 "csinc", condSel 1 0 "csinv", condSel 1 1 "csneg",
    condCmp 1 1 "ccmp (imm)", condCmp 0 1 "ccmn (imm)", condCmp 1 0 "ccmp (reg)",
    condCmp 0 0 "ccmn (reg)",
    addSubCarry 0 0 "adc", addSubCarry 0 1 "adcs", addSubCarry 1 0 "sbc", addSubCarry 1 1 "sbcs",
    bcond, cbranch 0 "cbz", cbranch 1 "cbnz", tbranch 0 "tbz", tbranch 1 "tbnz",
    uncondImm 0 "b", uncondImm 1 "bl", uncondReg 0 "br", uncondReg 1 "blr",
    uncondReg 2 "ret" (some 30), uncondReg 2 "ret xn",
    hint 0xd503201f "nop", hint 0xd503229f "csdb", hint 0xd5033bbf "dmb ish", udf,
    ldstExcl 1 1 "ldar", ldstExcl 1 0 "stlr", ldstExcl 0 1 "ldaxr",
    fmovGen 0 0 0b111 "fmov (s, w)" true, fmovGen 1 1 0b111 "fmov (d, x)" true,
    fmovGen 0 0 0b110 "fmov (w, s)" false, fmovGen 1 1 0b110 "fmov (x, d)" false,
    cnt, acrossLanes 0 0b11011 "addv", acrossLanes 1 0b00011 "uaddlv", addp, umov ] ++
  ([0, 1].flatMap fun ft =>
    [fp1 0b000000 "fmov (reg)" ft, fp1 0b000001 "fabs" ft, fp1 0b000010 "fneg" ft, fmovImm ft,
     fcsel ft]) ++
  [modImm, moviZero, orrVector] ++
  ([Mode.uimm, .unscaled, .pre, .post, .regoff].flatMap fun m =>
    ldstVariants.map fun (size, opc, bytes, mnem) => ldst 0 size opc bytes mnem m) ++
  ([0b010, 0b011, 0b001].flatMap fun mode =>
    [ldstPair 0 0b10 0 "stp (x)" mode, ldstPair 0 0b10 1 "ldp (x)" mode, ldstPair 0 0b00 0 "stp (w)" mode,
     ldstPair 0 0b00 1 "ldp (w)" mode, ldstPair 0 0b01 1 "ldpsw" mode]) ++
  ([Mode.uimm, .unscaled, .pre, .post, .regoff].flatMap fun m =>
    ldstSimdVariants.map fun (size, opc, bytes, mnem) => ldst 1 size opc bytes mnem m) ++
  ([0b010, 0b011, 0b001].flatMap fun mode =>
    [0, 1, 2].flatMap fun opc =>
      let t := match opc with | 0 => "s" | 1 => "d" | _ => "q"
      [ldstPair 1 opc 0 s!"stp ({t})" mode, ldstPair 1 opc 1 s!"ldp ({t})" mode]) ++
  [ldrLiteral 0 0 4 "ldr (literal, w)", ldrLiteral 1 0 8 "ldr (literal, x)",
   ldrLiteral 2 0 4 "ldrsw (literal)", ldrLiteral 0 1 4 "ldr (literal, s)",
   ldrLiteral 1 1 8 "ldr (literal, d)", ldrLiteral 2 1 16 "ldr (literal, q)"] ++
  ([0, 1].flatMap fun ft =>
    [fp1 0b000011 "fsqrt" ft, fp1 (if ft == 0 then 0b000101 else 0b000100) "fcvt" ft,
     fp1 0b001000 "frintn" ft, fp1 0b001001 "frintp" ft, fp1 0b001010 "frintm" ft,
     fp1 0b001011 "frintz" ft, fp1 0b001100 "frinta" ft, fp1 0b001110 "frintx" ft,
     fp1 0b001111 "frinti" ft,
     fp2 0b0000 "fmul" ft, fp2 0b0001 "fdiv" ft, fp2 0b0010 "fadd" ft, fp2 0b0011 "fsub" ft,
     fp2 0b0100 "fmax" ft, fp2 0b0101 "fmin" ft, fp2 0b1000 "fnmul" ft,
     fp3 0 0 "fmadd" ft, fp3 0 1 "fmsub" ft, fp3 1 0 "fnmadd" ft, fp3 1 1 "fnmsub" ft,
     fcmp 0b00000 "fcmp (reg)" ft, fcmp 0b01000 "fcmp (#0.0)" ft, fcmp 0b10000 "fcmpe (reg)" ft,
     fcmp 0b11000 "fcmpe (#0.0)" ft,
     fcvtToInt 0b00 0b000 "fcvtns" ft, fcvtToInt 0b00 0b001 "fcvtnu" ft,
     fcvtToInt 0b01 0b000 "fcvtps" ft, fcvtToInt 0b01 0b001 "fcvtpu" ft,
     fcvtToInt 0b10 0b000 "fcvtms" ft, fcvtToInt 0b10 0b001 "fcvtmu" ft,
     fcvtToInt 0b11 0b000 "fcvtzs" ft, fcvtToInt 0b11 0b001 "fcvtzu" ft,
     fcvtToInt 0b00 0b100 "fcvtas" ft, fcvtToInt 0b00 0b101 "fcvtau" ft,
     cvtToFp 0b010 "scvtf" ft, cvtToFp 0b011 "ucvtf" ft])

end Arm.Cosim

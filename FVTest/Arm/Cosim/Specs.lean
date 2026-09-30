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

def ldst (size opc bytes : Nat) (mnem : String) (mode : Mode) : Spec :=
  ⟨s!"{mnem} {mode.suffix}", s!"ldst-{mode.suffix}", fun i => do
    let name := s!"{mnem} {mode.suffix}"
    let rn ← reg
    let wback := mode == .pre || mode == .post
    let mut rt0 ← reg
    for _ in [0:100] do
      if wback && rt0 == rn && rn != 31 then rt0 ← reg
    let rt := if wback && rt0 == rn && rn != 31 then (rn + 1) % 31 else rt0
    let hdr := [(size, 2), (0b111, 3), (0, 1)]
    let (inst, off, setRm) ← match mode with
      | .uimm =>
        let imm ← bits 12
        pure (enc (hdr ++ [(0b01, 2), (opc, 2), (imm, 12), (rn, 5), (rt, 5)]),
          ((imm <<< size : Nat) : Int), (none : Option (Nat × Nat)))
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
          (rn, 5), (rt, 5)]), signed64 (extendVal v option (if S == 1 then size else 0)),
          if rm == 31 then none else some (rm, v))
    let e ← chooseE bytes off (rn == 31)
    let mut tc ← randomCase name inst
    if let some (rm, v) := setRm then tc := tc.setReg rm (hex v)
    let delta := signed64 (((e : Int) - off) % (2 ^ 64 : Int)).toNat
    return tc.setReg rn (bufPlus i delta)⟩

/-- Load/store pair: `(opc, L, mnemonic)`; `mode` is 0b001 post, 0b011 pre, 0b010 offset. -/
def ldstPair (opc L : Nat) (mnem : String) (mode : Nat) : Spec :=
  let suffix := match mode with
    | 0b001 => "[xn], #simm" | 0b011 => "[xn, #simm]!" | _ => "[xn, #simm]"
  ⟨s!"{mnem} {suffix}", "ldst-pair", fun i => do
    let name := s!"{mnem} {suffix}"
    let scale := if opc == 0b10 then 3 else 2
    let bytes := 2 * 2 ^ scale
    let wback := mode != 0b010
    let rn ← reg
    let mut rt ← reg
    let mut rt2 ← reg
    for _ in [0:1000] do
      if (L == 1 && rt == rt2) || (wback && rn != 31 && (rt == rn || rt2 == rn)) then
        rt ← reg
        rt2 ← reg
    let imm ← bits 7
    let off : Int := if mode == 0b001 then 0 else sext 7 imm * 2 ^ scale
    let inst := enc [(opc, 2), (0b101, 3), (0, 1), (mode, 3), (L, 1), (imm, 7), (rt2, 5), (rn, 5), (rt, 5)]
    let e ← chooseE bytes off (rn == 31)
    let tc ← randomCase name inst
    let delta := signed64 (((e : Int) - off) % (2 ^ 64 : Int)).toNat
    return tc.setReg rn (bufPlus i delta)⟩

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

def vreg : GenM Nat := below 31

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
  ([Mode.uimm, .unscaled, .pre, .post, .regoff].flatMap fun m =>
    ldstVariants.map fun (size, opc, bytes, mnem) => ldst size opc bytes mnem m) ++
  ([0b010, 0b011, 0b001].flatMap fun mode =>
    [ldstPair 0b10 0 "stp (x)" mode, ldstPair 0b10 1 "ldp (x)" mode, ldstPair 0b00 0 "stp (w)" mode,
     ldstPair 0b00 1 "ldp (w)" mode, ldstPair 0b01 1 "ldpsw" mode])

end Arm.Cosim

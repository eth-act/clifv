/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.

Encoder-driven co-simulation (T4, #40): random `Backend.Insn` values of every constructor and
operand variant that the encoder accepts, encoded by `Backend.Insn.encode` (the words the
backend emits), each run against qemu by the harness of `Harness.lean`.

`Specs.lean` builds its words by hand from the Arm ARM encoding diagrams; the forms here come
from the encoder itself, so every word shape the backend can emit is co-simulated, including
the operand constraints the encoder adds (register 31 as SP or ZR, `cset`'s inverted condition,
the relocated immediates). Relocated fields (`R_AARCH64_*`: `bl`'s `imm26`, `adrp`'s page
offset, the `:lo12:` immediates) are zero in the encoder's word; here they get the values a
linker would write (a landing pad, a random page offset, a buffer offset).

Not co-simulated (`excluded`): `mrs xt, tpidr_el0` (the model has no system registers and stops
with `Unimplemented`; it is only in `tls_value`'s TLSDESC sequence, outside every theorem), and
`umaddl`/`smaddl`, which the model does not implement (#271; Cranelift emits them only for
`umul_overflow`/`smul_overflow`, outside subset E).

`coverage` compares the encoder forms with the hand-written specs: a form counts as covered by
a spec when every sampled word of the form lies in the spec's sampled cube (the bits that are
constant across the spec's samples have the same values in the form's words).
-/
import FVTest.Arm.Cosim.Specs
import FV.Backend.Encode

namespace Arm.Cosim.Enc

open Arm.Cosim
open Backend (Insn Reg AMode Lbl ALUOp ALUOp3 ShiftOp ExtendOp BitOp Cond ScalarSize
  VectorSize LoadOp StoreOp MoveWideOp BfmOp VecLanesOp FPUOp1 FPUOp2 FPUOp3 FpuRoundMode
  FpuToIntOp IntToFpuOp)

/-- The last component of a constructor's `repr` (`Backend.ALUOp.add` ↦ `add`). -/
def short {α} [Repr α] (a : α) : String :=
  ((toString (repr a)).splitOn ".").getLast!.trimAscii.toString

/-- The encoder's position for every form: labels are resolved relative to it. -/
def basePc : Nat := 4096

/-- An environment where every label is `rel` bytes from the instruction. -/
def envRel (rel : Int) : Backend.Env :=
  { pc := basePc, lbl := fun _ => some ((basePc : Int) + rel).toNat }

def encodeRel (rel : Int) (i : Insn) : Option UInt32 :=
  match i.encode (envRel rel) with
  | .ok w => some w.toNat.toUInt32
  | .error _ => none

def encode0 (i : Insn) : Option UInt32 := encodeRel 0 i

/-- Retry a generator until it succeeds (a generator returns `none` for operand combinations
the encoder rejects or the test cannot set up). -/
def retry {α} [Inhabited α] (what : String) (g : GenM (Option α)) : GenM α := do
  for _ in [0:10000] do
    if let some a ← g then return a
  return panic! s!"encoder cosim: no valid instance of {what}"

/-! ## Operand generators (index, register) -/

def gX : GenM (Nat × Reg) := do let n ← below 31; return (n, .x n)
def gZR : GenM (Nat × Reg) := do
  let n ← below 32; return (n, if n == 31 then .xzr else .x n)
def gSP : GenM (Nat × Reg) := do
  let n ← below 32; return (n, if n == 31 then .sp else .x n)
def gV : GenM (Nat × Reg) := do let n ← below 31; return (n, .v n)
def gCond : GenM Cond := pick #[.eq, .ne, .hs, .lo, .mi, .pl, .vs, .vc, .hi, .ls, .ge, .lt, .gt,
  .le, .al, .nv]
def gNZCV : GenM Backend.NZCV := do
  return { n := ← coin, z := ← coin, c := ← coin, v := ← coin }

def sizeBits (w : Bool) : String := if w then "64" else "32"

/-- Replace bits `[lo, lo + n)` of `w` by `v`. -/
def setField (w : UInt32) (lo n v : Nat) : UInt32 :=
  let m : Nat := (2 ^ n - 1) <<< lo
  ((w.toNat &&& ((2 ^ 32 - 1) - m)) ||| ((v % 2 ^ n) <<< lo)).toUInt32

/-- A form: the report key and a spec running it. -/
def form (key batch : String) (g : Nat → GenM TestCase) : Spec := ⟨key, batch, g⟩

/-- A register-only form: `mk` returns the instruction and the float precision of the initial
SIMD&FP registers (`some dbl`: IEEE values, see `randomFpCase`), or `none` if invalid. -/
def simple (key batch : String) (mk : GenM (Option (Insn × Option Bool))) : Spec :=
  form key batch fun _ => do
    let (w, fp) ← retry key do
      let some (i, fp) ← mk | return none
      return (encode0 i).map (·, fp)
    match fp with
    | some dbl => randomFpCase key dbl w
    | none => randomCase key w

/-- Like `simple`, then stress the rounding of a binary FP operation on `v{rn}`, `v{rm}`
(`fpPair`). -/
def fpBinary (key : String) (dbl : Bool) (mk : Nat → Nat → Reg → Reg → GenM (Option Insn)) :
    Spec :=
  form key "enc-fp" fun _ => do
    let (w, rn, rm) ← retry key do
      let (rn, rnR) ← gV
      let (rm, rmR) ← gV
      let some i ← mk rn rm rnR rmR | return none
      return (encode0 i).map (·, rn, rm)
    fpPair (← randomFpCase key dbl w) dbl rn rm

/-! ## Integer data processing -/

def aluRRROps : List ALUOp :=
  [.add, .sub, .orr, .orrNot, .and, .andS, .andNot, .eor, .eorNot, .addS, .subS, .sMulH, .uMulH,
   .sDiv, .uDiv, .extr, .lsr, .asr, .lsl, .adc, .adcS, .sbc, .sbcS]

def dpForms : List Spec :=
  ([true, false].flatMap fun w =>
    ((aluRRROps.filter fun op => w || !(op == .sMulH || op == .uMulH)).map fun op =>
      simple s!"aluRRR {short op} {sizeBits w}" "enc-dp" do
        return some (.aluRRR op w (← gZR).2 (← gZR).2 (← gZR).2, none)) ++
    -- (`uMAddL`/`sMAddL`: `excluded`)
    ([ALUOp3.mAdd, .mSub].map fun op =>
      simple s!"aluRRRR {short op} {sizeBits w}" "enc-dp" do
        return some (.aluRRRR op w (← gZR).2 (← gZR).2 (← gZR).2 (← gZR).2, none)) ++
    ([ALUOp.add, .sub, .addS, .subS].map fun op =>
      simple s!"aluImm12 {short op} {sizeBits w}" "enc-dp" do
        let imm : Backend.Imm12 := { bits := ← bits 12, shift12 := ← coin }
        return some (.aluImm12 op w (← gSP).2 (← gSP).2 imm, none)) ++
    ([ALUOp.and, .orr, .eor, .andS].map fun op =>
      simple s!"logicImm {short op} {sizeBits w}" "enc-dp" do
        -- a bitmask immediate: a rotated run of `c` ones in an `e`-bit element, replicated
        let size := if w then 64 else 32
        let e ← pick (#[2, 4, 8, 16, 32, 64].filter (· ≤ size))
        let c := 1 + (← below (e - 1))
        let elem := Backend.rorN e (2 ^ c - 1) (← below e)
        let v := (List.range (size / e)).foldl (fun acc k => acc + elem * 2 ^ (e * k)) 0
        return some (.logicImm op w (← gSP).2 (← gZR).2 v, none)) ++
    ([ShiftOp.lsl, .lsr, .asr, .ror].map fun op =>
      simple s!"shiftImm {short op} {sizeBits w}" "enc-dp" do
        return some (.shiftImm op w (← gZR).2 (← gZR).2 (← below (if w then 64 else 32)), none)) ++
    ([ALUOp.add, .sub, .addS, .subS, .and, .andNot, .orr, .orrNot, .eor, .eorNot, .andS].map
      fun op => simple s!"aluRRRShift {short op} {sizeBits w}" "enc-dp" do
        let sh : Backend.ShiftOpAndAmt :=
          { op := ← pick #[.lsl, .lsr, .asr, .ror], amt := ← below (if w then 64 else 32) }
        return some (.aluRRRShift op w (← gZR).2 (← gZR).2 (← gZR).2 sh, none)) ++
    [simple s!"extr {sizeBits w}" "enc-dp" do
      return some (.extr w (← gZR).2 (← gZR).2 (← gZR).2 (← below (if w then 64 else 32)), none)] ++
    ([ALUOp.add, .sub, .addS, .subS].map fun op =>
      simple s!"aluRRRExtend {short op} {sizeBits w}" "enc-dp" do
        let e ← pick #[ExtendOp.uxtb, .uxth, .uxtw, .uxtx, .sxtb, .sxth, .sxtw, .sxtx]
        return some (.aluRRRExtend op w (← gSP).2 (← gSP).2 (← gZR).2 e, none)) ++
    ([BitOp.rbit, .clz, .cls, .rev16, .rev32, .rev64].map fun op =>
      simple s!"bitRR {short op} {sizeBits w}" "enc-dp" do
        return some (.bitRR op w (← gZR).2 (← gZR).2, none)) ++
    -- `mov` is ORR (register) unless an operand is SP, then ADD (immediate) #0
    [simple s!"mov (reg) {sizeBits w}" "enc-dp" do
      return some (.mov w (← gZR).2 (← gZR).2, none),
     simple s!"mov (sp) {sizeBits w}" "enc-dp" do
      let (rd, rm) ← if ← coin then pure (Reg.sp, (← gX).2) else pure ((← gX).2, Reg.sp)
      return some (.mov w rd rm, none)] ++
    ([MoveWideOp.movZ, .movN].map fun op =>
      simple s!"movWide {short op} {sizeBits w}" "enc-dp" do
        let imm : Backend.MoveWideConst := { bits := ← bits 16, shift := ← below (if w then 4 else 2) }
        return some (.movWide op w (← gZR).2 imm, none)) ++
    [simple s!"movk {sizeBits w}" "enc-dp" do
      let imm : Backend.MoveWideConst := { bits := ← bits 16, shift := ← below (if w then 4 else 2) }
      return some (.movk w (← gZR).2 imm, none)] ++
    ([BfmOp.sBfm, .uBfm].map fun op =>
      simple s!"bfm {short op} {sizeBits w}" "enc-dp" do
        let n := if w then 64 else 32
        return some (.bfm op w (← gZR).2 (← gZR).2 (← below n) (← below n), none)) ++
    [simple s!"ccmp {sizeBits w}" "enc-dp" do
      return some (.ccmp w (← gZR).2 (← gZR).2 (← gNZCV) (← gCond), none),
     simple s!"ccmpImm {sizeBits w}" "enc-dp" do
      return some (.ccmpImm w (← gZR).2 (← below 32) (← gNZCV) (← gCond), none)]) ++
  [simple "cset" "enc-dp" do return some (.cset (← gZR).2 (← gCond), none),
   simple "csetm" "enc-dp" do return some (.csetm (← gZR).2 (← gCond), none),
   simple "csel" "enc-dp" do return some (.csel (← gZR).2 (← gZR).2 (← gZR).2 (← gCond), none)]

/-! ## Branches, PC-relative and relocated forms, misc -/

/-- A landing-pad offset in bytes. -/
def padRel : GenM Int := do return 4 * (← padIdx)

def labelBranch (key : String) (mk : GenM Insn) : Spec :=
  form key "enc-br" fun _ => do
    let (w, _) ← retry key do
      let rel ← padRel
      let i ← mk
      return (encodeRel rel i).map (·, rel)
    branchCase key w

/-- `br`/`blr`-like forms: the target register holds a landing-pad address. -/
def regBranch (key : String) (mk : Reg → Insn) (rn? : Option Nat := none) : Spec :=
  form key "enc-br" fun i => do
    let rn ← match rn? with | some r => pure r | none => below 31
    let w ← retry key (pure (encode0 (mk (.x rn))))
    let tc ← branchCase key w
    return tc.setReg rn (padLabel i (← padIdx))

def brForms : List Spec :=
  [labelBranch "b" do return .b (.block 0),
   labelBranch "bcond" do return .bcond (← gCond) (.block 0)] ++
  ([false, true].flatMap fun nz => [true, false].map fun w =>
    form s!"cbz {if nz then "nz" else "z"} {sizeBits w}" "enc-br" fun _ => do
      let key := s!"cbz {if nz then "nz" else "z"} {sizeBits w}"
      let (rt, rtR) ← gZR
      let w' ← retry key do return encodeRel (← padRel) (.cbz nz w rtR (.block 0))
      let tc ← branchCase key w'
      -- make the tested register zero (in the tested width) a third of the time
      match ← below 3 with
      | 0 => return if rt < 31 then tc.setReg rt "0" else tc
      | 1 => return if rt < 31 then tc.setReg rt "0xffffffff00000000" else tc
      | _ => return tc) ++
  ([false, true].map fun nz =>
    labelBranch s!"tbz {if nz then "nz" else "z"}" do
      return .tbz nz (← gZR).2 (← below 64) (.block 0)) ++
  [form "bl (CALL26)" "enc-br" fun _ => do
     -- the encoder leaves imm26 zero for R_AARCH64_CALL26; a linker writes the offset
     let w ← retry "bl" (pure (encode0 (.bl "f")))
     branchCase "bl (CALL26)" (setField w 0 26 (twos 26 (← padIdx))),
   regBranch "blr" .blr, regBranch "br" .br, regBranch "ret" (fun _ => .ret) (some 30),
   regBranch "blr (TLSDESC_CALL)" (fun r => .blrTlsDesc r "t"),
   form "udf" "enc-misc" fun _ => do
     let w ← retry "udf" do return encode0 (.udf (← bits 16))
     return { (← randomCase "udf" w) with kind := .udf },
   simple "dmb ish" "enc-misc" (return some (.dmbish, none)),
   form "adr" "enc-misc" fun _ => do
     let w ← retry "adr" do
       return encodeRel ((← below 2049 : Nat) - (1024 : Int)) (.adr (← gZR).2 (.block 0))
     randomCase "adr" w] ++
  -- ADRP: R_AARCH64_ADR_PREL_PG_HI21 / ADR_GOT_PAGE / TLSDESC_ADR_PAGE21 fill immhi:immlo
  ([("adrp (ADR_PREL_PG_HI21)", fun r => Insn.adrp r "s" 0),
    ("adrp (ADR_GOT_PAGE)", fun r => Insn.adrpGot r "s"),
    ("adrp (TLSDESC_ADR_PAGE21)", fun r => Insn.adrpTlsDesc r "s")].map fun (key, mk) =>
    form key "enc-misc" fun _ => do
      let w ← retry key do return encode0 (mk (← gZR).2)
      let imm ← bits 21
      randomCase key (setField (setField w 29 2 imm) 5 19 (imm >>> 2))) ++
  -- ADD :lo12: (ADD_ABS_LO12_NC / TLSDESC_ADD_LO12): any imm12
  ([("add (ADD_ABS_LO12_NC)", fun rd rn => Insn.addLo12 rd rn "s" 0),
    ("add (TLSDESC_ADD_LO12)", fun rd rn => Insn.addTlsDescLo12 rd rn "s")].map fun (key, mk) =>
    form key "enc-misc" fun _ => do
      let w ← retry key do return encode0 (mk (← gSP).2 (← gSP).2)
      randomCase key (setField w 10 12 (← bits 12))) ++
  -- LDR :got_lo12: / :tlsdesc_lo12: (LD64_GOT_LO12_NC / TLSDESC_LD64_LO12): imm12 = offset / 8,
  -- the base set so that the address is in the buffer
  ([("ldr (LD64_GOT_LO12_NC)", fun rt rn => Insn.ldrGotLo12 rt rn "s"),
    ("ldr (TLSDESC_LD64_LO12)", fun rt rn => Insn.ldrTlsDescLo12 rt rn "s")].map fun (key, mk) =>
    form key "enc-misc" fun i => do
      let (rn, rnR) ← gSP
      let w ← retry key do return encode0 (mk (← gZR).2 rnR)
      let k ← if ← coin then below 8 else bits 12
      let off : Int := 8 * k
      let e ← chooseE 8 off (rn == 31)
      let tc ← randomCase key (setField w 10 12 k)
      return tc.setReg rn (bufPlus i ((e : Int) - off)))

/-! ## Loads and stores -/

inductive MKind where
  | uoff | unscaled | pre | post | regReg | regScaled | regScaledExt | regExt
deriving BEq, Repr, Inhabited

def MKind.all : List MKind := [.uoff, .unscaled, .pre, .post, .regReg, .regScaled, .regScaledExt, .regExt]

/-- A random final addressing mode of kind `k` for a `bytes`-byte access: the mode, the base
register index (31 = SP), the offset from the base to the accessed address, and the offset
register with its value. `none` when the base and offset registers coincide. -/
def genAMode (k : MKind) (bytes : Nat) : GenM (Option (AMode × Nat × Int × Option (Nat × Nat))) := do
  let simm9 : GenM Int := do return sext 9 (← bits 9)
  match k with
  | .uoff =>
    let (rn, rnR) ← gSP
    let q ← if ← coin then below 16 else bits 12
    return some (.unsignedOffset rnR (q * bytes), rn, (q * bytes : Nat), none)
  | .unscaled =>
    let (rn, rnR) ← gSP
    let s ← simm9
    return some (.unscaled rnR s, rn, s, none)
  | .pre => let s ← simm9; return some (.spPreIndexed s, 31, s, none)
  | .post => let s ← simm9; return some (.spPostIndexed s, 31, 0, none)
  | _ =>
    let (rn, rnR) ← gSP
    let (rm, rmR) ← gZR
    if rm == rn && rn != 31 then return none
    let e ← pick #[ExtendOp.uxtw, .uxtx, .sxtw, .sxtx]
    let v ← if rm == 31 then pure 0 else if ← coin then pure (← randVal).toNat else bits 12
    let sh := Nat.log2 bytes
    let (am, option, shift) : AMode × Nat × Nat := match k with
      | .regReg => (.regReg rnR rmR, 3, 0)
      | .regScaled => (.regScaled rnR rmR, 3, sh)
      | .regScaledExt => (.regScaledExtended rnR rmR e, (Backend.ExtendOp.bits e).toNat, sh)
      | _ => (.regExtended rnR rmR e, (Backend.ExtendOp.bits e).toNat, 0)
    return some (am, rn, signed64 (extendVal v option shift), if rm == 31 then none else some (rm, v))

/-- A single-register load/store form: `mk am` builds the instruction (the data register is
chosen by `mk`); `fp` as in `simple`. -/
def ldstForm (key : String) (k : MKind) (bytes : Nat) (fp : Option Bool)
    (mk : AMode → GenM Insn) : Spec :=
  form s!"{key} {short k}" s!"enc-ldst-{short k}" fun i => do
    let key := s!"{key} {short k}"
    let (w, rn, off, rmv) ← retry key do
      let some (am, rn, off, rmv) ← genAMode k bytes | return none
      return (encode0 (← mk am)).map (·, rn, off, rmv)
    let mut tc ← match fp with
      | some dbl => randomFpCase key dbl w
      | none => randomCase key w
    if let some (rm, v) := rmv then tc := tc.setReg rm (Arm.Cosim.hex v)
    let e ← chooseE bytes off (rn == 31)
    return tc.setReg rn (bufPlus i ((e : Int) - off))

def loadOps : List (LoadOp × Nat) :=
  [(.uload8, 1), (.sload8, 1), (.uload16, 2), (.sload16, 2), (.uload32, 4), (.sload32, 4),
   (.uload64, 8), (.fpuLoad128, 16)]

def storeOps : List (StoreOp × Nat) :=
  [(.store8, 1), (.store16, 2), (.store32, 4), (.store64, 8), (.fpuStore128, 16)]

def ldstForms : List Spec :=
  MKind.all.flatMap fun k =>
    (loadOps.map fun (op, bytes) =>
      ldstForm s!"load {short op}" k bytes (if op == .fpuLoad128 then some true else none) fun am => do
        let rt ← if op == .fpuLoad128 then (·.2) <$> gV else (·.2) <$> gZR
        return .load op rt am) ++
    (storeOps.map fun (op, bytes) =>
      ldstForm s!"store {short op}" k bytes (if op == .fpuStore128 then some true else none) fun am => do
        let rt ← if op == .fpuStore128 then (·.2) <$> gV else (·.2) <$> gZR
        return .store op rt am) ++
    ([(ScalarSize.size32, 4), (.size64, 8)].flatMap fun (s, bytes) =>
      [ldstForm s!"fpuLoad {short s}" k bytes (some (bytes == 8)) fun am => do
         return .fpuLoad s (← gV).2 am,
       ldstForm s!"fpuStore {short s}" k bytes (some (bytes == 8)) fun am => do
         return .fpuStore s (← gV).2 am])

/-- `ldp`/`stp` (SP pre/post-indexed, the encoder's only pair modes): `scale` bytes per
register, `mk rt rt2 am`; loads need distinct registers. -/
def pairForm (key : String) (scale : Nat) (load : Bool) (fp : Option Bool) (pre : Bool)
    (mk : Nat → AMode → GenM (Option Insn)) : Spec :=
  let key := s!"{key} {if pre then "pre" else "post"}"
  form key "enc-ldst-pair" fun i => do
    let (w, off) ← retry key do
      let s : Int := sext 7 (← bits 7) * scale
      let am : AMode := if pre then .spPreIndexed s else .spPostIndexed s
      let some ins ← mk (if load then 1 else 0) am | return none
      return (encode0 ins).map (·, if pre then s else 0)
    let tc ← match fp with
      | some dbl => randomFpCase key dbl w
      | none => randomCase key w
    let e ← chooseE (2 * scale) off true
    return tc.setReg 31 (bufPlus i ((e : Int) - off))

def pairForms : List Spec :=
  [true, false].flatMap fun pre =>
    [pairForm "ldp" 8 true none pre fun _ am => do
       let (a, ra) ← gZR
       let (b, rb) ← gZR
       return if a == b then none else some (.ldp ra rb am),
     pairForm "stp" 8 false none pre fun _ am => do return some (.stp (← gZR).2 (← gZR).2 am)] ++
    ([(ScalarSize.size32, 4), (.size64, 8), (.size128, 16)].flatMap fun (s, scale) =>
      [pairForm s!"fpuLoadP {short s}" scale true (some (scale == 8)) pre fun _ am => do
         let (a, ra) ← gV
         let (b, rb) ← gV
         return if a == b then none else some (.fpuLoadP s ra rb am),
       pairForm s!"fpuStoreP {short s}" scale false (some (scale == 8)) pre fun _ am => do
         return some (.fpuStoreP s (← gV).2 (← gV).2 am)])

/-- `ldr (literal)` (SIMD&FP): the target is a word of one of the test's literal pools. -/
def litForms : List Spec :=
  [(ScalarSize.size32, 4), (.size64, 8), (.size128, 16)].map fun (s, bytes) =>
    let key := s!"fpuLoadLit {short s}"
    form key "enc-ldst-literal" fun _ => do
      let w ← retry key do
        let k ← below ((64 - bytes) / 4 + 1)
        let rel : Int := if ← coin then -64 + 4 * k else 8 + 4 * k
        return encodeRel rel (.fpuLoadLit s (← gV).2 (.block 0))
      return { (← randomFpCase key (bytes == 8) w) with pool := true }

/-- `ldar`/`stlr`/`ldaxr`, and `stlxr` preceded by an `ldaxr` of the same address (a lone
`stlxr` fails in qemu, whose exclusive monitor is then clear; the model's always succeeds).
Addresses are aligned to the access size. -/
def exclForms : List Spec :=
  [8, 16, 32, 64].flatMap fun b =>
    let bytes := b / 8
    let one (key : String) (mk : Reg → Reg → Insn) : Spec :=
      form key "enc-ldst-excl" fun i => do
        let (rn, rnR) ← gSP
        let w ← retry key do return encode0 (mk (← gZR).2 rnR)
        let e ← chooseE bytes 0 (rn == 31)
        return (← randomCase key w).setReg rn (bufPlus i (e - e % bytes : Nat))
    [one s!"ldar {b}" (Insn.ldar b), one s!"stlr {b}" (Insn.stlr b), one s!"ldaxr {b}" (Insn.ldaxr b),
     form s!"stlxr {b} (after ldaxr)" "enc-ldst-excl" fun i => do
       let key := s!"stlxr {b} (after ldaxr)"
       let (rn, rnR) ← gSP
       let (w, pre) ← retry key do
         let (rs, rsR) ← gZR
         let (rt, rtR) ← gZR
         let (r0, r0R) ← gZR
         -- CONSTRAINED UNPREDICTABLE: Rs = Rt, Rs = Rn (Rn ≠ SP); the `ldaxr` must keep Rn
         if rs == rt || (rs == rn && rn != 31) || (r0 == rn && rn != 31) then return none
         return do
           let w ← encode0 (.stlxr b rsR rtR rnR)
           let p ← encode0 (.ldaxr b r0R rnR)
           pure (w, p)
       let e ← chooseE bytes 0 (rn == 31)
       let tc := (← randomCase key w).setReg rn (bufPlus i (e - e % bytes : Nat))
       return { tc with pre := #[pre] }]

/-! ## SIMD&FP -/

def fpSizes : List (ScalarSize × Bool) := [(.size32, false), (.size64, true)]

def fpForms : List Spec :=
  ([ScalarSize.size16, .size32, .size64].map fun s =>
    simple s!"fmovToFp {short s}" "enc-simd" do
      return some (.fmovToFp s (← gV).2 (← gZR).2, none)) ++
  ([(ScalarSize.size8, 16), (.size16, 8), (.size32, 4), (.size64, 2)].map fun (s, n) =>
    simple s!"umov {short s}" "enc-simd" do
      return some (.umov s (← gZR).2 (← gV).2 (← below n), none)) ++
  ([VectorSize.size8x8, .size8x16].map fun s =>
    simple s!"cnt {short s}" "enc-simd" do return some (.cnt s (← gV).2 (← gV).2, none)) ++
  ([VecLanesOp.addv, .uaddlv].flatMap fun op =>
    [VectorSize.size8x8, .size8x16, .size16x4, .size16x8, .size32x4].map fun s =>
      simple s!"vecLanes {short op} {short s}" "enc-simd" do
        return some (.vecLanes op s (← gV).2 (← gV).2, none)) ++
  ([VectorSize.size8x8, .size8x16, .size16x4, .size16x8, .size32x2, .size32x4, .size64x2].map
    fun s => simple s!"addp {short s}" "enc-simd" do
      return some (.addp s (← gV).2 (← gV).2 (← gV).2, none)) ++
  ([VectorSize.size8x8, .size8x16, .size16x4, .size16x8, .size32x2, .size32x4].map fun s =>
    simple s!"movi {short s}" "enc-simd" do
      return some (.movi s (← gV).2 (← bits 8), some (← coin))) ++
  [simple "fpuMove128" "enc-simd" do return some (.fpuMove128 (← gV).2 (← gV).2, some (← coin))] ++
  (fpSizes.flatMap fun (s, dbl) =>
    [simple s!"fpuMove {short s}" "enc-fp" do return some (.fpuMove s (← gV).2 (← gV).2, some dbl),
     simple s!"fpuMoveFPImm {short s}" "enc-fp" do
       return some (.fpuMoveFPImm s (← gV).2 (← bits 8), some dbl),
     simple s!"fpuCSel {short s}" "enc-fp" do
       return some (.fpuCSel s (← gV).2 (← gV).2 (← gV).2 (← gCond), some dbl),
     fpBinary s!"fpuCmp {short s}" dbl fun _ _ rn rm => return some (.fpuCmp s rn rm)] ++
    ([FPUOp1.abs, .neg, .sqrt].map fun op =>
      simple s!"fpuRR {short op} {short s}" "enc-fp" do
        return some (.fpuRR op s (← gV).2 (← gV).2, some dbl)) ++
    ([FPUOp2.add, .sub, .mul, .div, .max, .min].map fun op =>
      fpBinary s!"fpuRRR {short op} {short s}" dbl fun _ _ rn rm => do
        return some (.fpuRRR op s (← gV).2 rn rm)) ++
    ([FPUOp3.mAdd, .mSub, .nMAdd, .nMSub].map fun op =>
      fpBinary s!"fpuRRRR {short op} {short s}" dbl fun _ _ rn rm => do
        return some (.fpuRRRR op s (← gV).2 rn rm (← gV).2))) ++
  [simple "fpuRR cvt32To64 size32" "enc-fp" do
     return some (.fpuRR .cvt32To64 .size32 (← gV).2 (← gV).2, some false),
   simple "fpuRR cvt64To32 size64" "enc-fp" do
     return some (.fpuRR .cvt64To32 .size64 (← gV).2 (← gV).2, some true)] ++
  ([FpuRoundMode.minus32, .minus64, .plus32, .plus64, .zero32, .zero64, .nearest32,
    .nearest64].map fun op =>
    simple s!"fpuRound {short op}" "enc-fp" do
      return some (.fpuRound op (← gV).2 (← gV).2, some ((short op).endsWith "64"))) ++
  ([FpuToIntOp.f32ToU32, .f32ToI32, .f32ToU64, .f32ToI64, .f64ToU32, .f64ToI32, .f64ToU64,
    .f64ToI64].map fun op =>
    simple s!"fpuToInt {short op}" "enc-fp" do
      return some (.fpuToInt op (← gZR).2 (← gV).2, some ((short op).startsWith "f64"))) ++
  ([IntToFpuOp.u32ToF32, .i32ToF32, .u32ToF64, .i32ToF64, .u64ToF32, .i64ToF32, .u64ToF64,
    .i64ToF64].map fun op =>
    simple s!"intToFpu {short op}" "enc-fp" do
      return some (.intToFpu op (← gV).2 (← gZR).2, some ((short op).endsWith "64")))

/-- Every encoder form. -/
def encoderSpecs : List Spec :=
  dpForms ++ brForms ++ ldstForms ++ pairForms ++ litForms ++ exclForms ++ fpForms

/-- `Insn` forms deliberately not co-simulated, with the reason. -/
def excluded : List (String × String) :=
  [("mrsTpidrEl0", "the model has no system registers (Unimplemented by design; only in tls_value's TLSDESC sequence, outside every theorem)"),
   ("aluRRRR uMAddL/sMAddL", "the model does not implement UMADDL/SMADDL (Unimplemented; co-simulation: 400/400 vectors stop there; #271); Cranelift emits them only for umul_overflow/smul_overflow, outside subset E")]

/-! ## Coverage of the encoder forms by the hand-written specs -/

/-- The bits that are constant over `ws` (mask) and their values. -/
def cube (ws : Array UInt32) : UInt32 × UInt32 :=
  match ws[0]? with
  | none => (0, 0)
  | some w0 =>
    let diff := ws.foldl (fun d w => d ||| (w ^^^ w0)) 0
    (~~~diff, w0 &&& ~~~diff)

def sampleWords (sp : Spec) (n : Nat) (rng : Rng) : Array UInt32 × Rng := Id.run do
  let mut g := rng
  let mut ws := #[]
  for k in [0:n] do
    let (tc, g') := (sp.gen k).run g
    g := g'
    ws := ws.push tc.inst
  return (ws, g)

/-- For each encoder form: the hand-written specs whose sampled cube contains all of the
form's sampled words (empty: the form was not co-simulated by `Specs.lean`). -/
def coverage (nForm nSpec : Nat) (seed : UInt64) : Array (String × List String) := Id.run do
  let mut g : Rng := ⟨seed ||| 1⟩
  let mut cubes : Array (String × UInt32 × UInt32) := #[]
  for sp in allSpecs do
    let (ws, g') := sampleWords sp nSpec g
    g := g'
    let (m, v) := cube ws
    cubes := cubes.push (sp.name, m, v)
  let mut out := #[]
  for f in encoderSpecs do
    let (ws, g') := sampleWords f nForm g
    g := g'
    let hits := cubes.toList.filterMap fun (nm, m, v) =>
      if ws.all (fun w => w &&& m == v) then some nm else none
    out := out.push (f.name, hits)
  return out

end Arm.Cosim.Enc

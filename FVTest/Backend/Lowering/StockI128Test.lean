import FV.Backend.Lowering.StockI128

/-! Probes for the native `i128` stock lowering `Backend.Stock.lower128` (no proof).

* The `#guard`s below check that `lower128` lowers the 16 foundation shapes, 13 `i128` shift
  and rotate shapes (`shifts`), 15 `i128` comparison shapes (`compares`), 14 `select`,
  `select_spectre_guard`, `bmask` and `bitselect` shapes (`selects`), 10 arithmetic shapes
  (`ariths`), 16 bit-operation shapes (`bitops`), 4 minimum and maximum shapes (`minmaxes`),
  4 overflow shapes (`overflows`) and 18 load and store shapes (`mems`), that the instructions
  it selects have the shape of stock Cranelift's (the expected VCode of the filetests, with
  registers abstracted, and without regalloc moves and the frame), and they pin its exact
  pre-allocation VCode.
* Further `#guard`s check that `lower128` gives the result of `Stock.lower` on functions without
  `i128` values, and that it rejects `i128` instructions outside the foundation.
* `main` does the two checks over Cranelift's filetests (the build does not run it):
  `lake env lean --run FVTest/Backend/Lowering/StockI128Test.lean [--print] [PATH...]`,
  with the default path `third_party/wasmtime/cranelift/filetests/filetests/isa/aarch64`
  (`--print`: also the exact VCode and the rejection reasons). With `--shapes`, it prints the
  shapes and the results of the checks above instead. A `select_spectre_guard` function of a
  `use_csdb` filetest is not compared: `lower128` lowers without `use_csdb`, and the
  stock-configured driver rejects such a function (`StockConfig.usesCsdb`).
-/

namespace Backend.Stock.I128Test

open Backend Backend.Stock

/-! ## Rendering -/

def reg : Reg → String
  | .vreg n _ => s!"%{n}"
  | .x n => s!"x{n}"
  | .v n => s!"v{n}"
  | .xzr => "xzr"
  | .sp => "sp"

/-- The last component of a constructor's name (`Backend.Cond.eq` → `eq`). -/
def lastName {α : Type} [Repr α] (a : α) : String :=
  ((repr a).pretty.splitOn ".").getLast?.getD ""

def aluName : ALUOp → String
  | .orr => "orr" | .and => "and" | .eor => "eor" | .add => "add" | .sub => "sub"
  | .addS => "adds" | .subS => "subs" | .andS => "ands"
  | .asr => "asr" | .lsr => "lsr" | .lsl => "lsl" | .orrNot => "orn" | .extr => "extr"
  | .sbcS => "sbcs" | .andNot => "bic" | .adc => "adc" | .adcS => "adcs" | .sbc => "sbc"
  | .uMulH => "umulh"
  | .sMulH => "smulh" | .eorNot => "eon"
  | op => s!"?{lastName op}"

/-- A `BitRR` mnemonic as Cranelift's VCode printing gives it (`BitOp::op_str`). -/
def bitName : BitOp → String
  | .rbit => "rbit" | .clz => "clz" | .cls => "cls" | .rev16 => "rev16" | .rev32 => "rev32"
  | .rev64 => "rev64"

def alu3Name : ALUOp3 → String
  | .mAdd => "madd" | .mSub => "msub"
  | op => s!"?{lastName op}"

/-- An `NZCV` immediate as Cranelift prints it: `#nzcv`, a set flag in upper case. -/
def nzcv (f : NZCV) : String :=
  let c (ch : Char) (b : Bool) : Char := if b then ch.toUpper else ch
  s!"#{c 'n' f.n}{c 'z' f.z}{c 'c' f.c}{c 'v' f.v}"

/-- A `PairAMode::SignedOffset` as Cranelift prints it (`[xn]`, `[xn, #off]`). -/
def pairAMode (rn : Reg) (off : Int) : String :=
  if off == 0 then s!"[{reg rn}]" else s!"[{reg rn}, #{off}]"

/-- A vector arrangement as Cranelift prints it (`16b`, `2d`). -/
def arr : VectorSize → String
  | .size8x8 => "8b" | .size8x16 => "16b" | .size16x4 => "4h" | .size16x8 => "8h"
  | .size32x2 => "2s" | .size32x4 => "4s" | .size64x2 => "2d"

/-- The lane letter of a vector arrangement (`b` of `16b`, `d` of `2d`). -/
def lane : VectorSize → String
  | .size8x8 | .size8x16 => "b" | .size16x4 | .size16x8 => "h"
  | .size32x2 | .size32x4 => "s" | .size64x2 => "d"

/-- The lane letter of a scalar size (`b` for 8 bits). -/
def scalarLane : ScalarSize → String
  | .size8 => "b" | .size16 => "h" | .size32 => "s" | .size64 => "d" | .size128 => "q"

def amode : AMode → String
  | .fpOffset off => s!"[fp, #{off}]"
  | .spOffset off => s!"[sp, #{off}]"
  | m => s!"?{(repr m).pretty}"

/-- One instruction in the syntax of Cranelift's VCode printing (`isa/aarch64/inst/mod.rs`),
for the instructions of the foundation, the shifts and rotates, the comparisons, the
selects, the arithmetic, the bit operations (with the vector instructions of `popcnt`), the
minimum and maximum and the overflow operations; `?` and the representation for every other
one. `args` and `rets` show their
(vreg, physical register) pairs. -/
def inst : MInst → String
  | .args ps => " ".intercalate ("args" :: ps.map fun (a, p) => s!"{reg a}={reg p}")
  | .rets ps => " ".intercalate ("rets" :: ps.map fun (a, p) => s!"{reg a}={reg p}")
  | .load _ rd m _ => s!"ldr {reg rd}, {amode m}"
  | .extend rd rn signed fromBits _ =>
    if !signed && fromBits == 32 then s!"mov {reg rd}, {reg rn}"
    else
      let w := match fromBits with | 8 => "b" | 16 => "h" | _ => "w"
      s!"{if signed then "sxt" else "uxt"}{w} {reg rd}, {reg rn}"
  | .movWide op rd imm _ =>
    let name := match op with | .movZ => "movz" | .movN => "movn"
    if imm.shift == 0 then s!"{name} {reg rd}, #{imm.bits}"
    else s!"{name} {reg rd}, #{imm.bits}, LSL #{imm.shift * 16}"
  | .aluRRR op _ rd rn rm => s!"{aluName op} {reg rd}, {reg rn}, {reg rm}"
  | .aluRRRR op _ rd rn rm ra => s!"{alu3Name op} {reg rd}, {reg rn}, {reg rm}, {reg ra}"
  | .aluRRImm12 op _ rd rn imm => s!"{aluName op} {reg rd}, {reg rn}, #{imm.value}"
  | .aluRRImmShift op _ rd rn imm => s!"{aluName op} {reg rd}, {reg rn}, #{imm}"
  | .aluRRImmLogic op _ rd rn imm => s!"{aluName op} {reg rd}, {reg rn}, #{imm.value}"
  | .aluRRRExtend op _ rd rn rm e => s!"{aluName op} {reg rd}, {reg rn}, {reg rm}, {lastName e}"
  | .bitRR op _ rd rn => s!"{bitName op} {reg rd}, {reg rn}"
  | .csel rd rn rm c => s!"csel {reg rd}, {reg rn}, {reg rm}, {lastName c}"
  | .cset rd c => s!"cset {reg rd}, {lastName c}"
  | .csetm rd c => s!"csetm {reg rd}, {lastName c}"
  | .ccmp _ rn rm f c => s!"ccmp {reg rn}, {reg rm}, {nzcv f}, {lastName c}"
  | .condBr t e (.notZero r _) => s!"cbnz {reg r}, label{t} ; b label{e}"
  | .condBr t e (.zero r _) => s!"cbz {reg r}, label{t} ; b label{e}"
  | .condBr t e (.cond c) => s!"b.{lastName c} label{t} ; b label{e}"
  | .jump l => s!"b label{l}"
  | .mov _ rd rm => s!"mov {reg rd}, {reg rm}"
  | .loadP64 rt rt2 rn off _ => s!"ldp {reg rt}, {reg rt2}, {pairAMode rn off}"
  | .storeP64 rt rt2 rn off _ => s!"stp {reg rt}, {reg rt2}, {pairAMode rn off}"
  | .loadAddr rd (.slotOffset off) =>
    if off == 0 then s!"mov {reg rd}, sp" else s!"add {reg rd}, sp, #{off}"
  | .movToFpu rd rn _ => s!"fmov {reg rd}, {reg rn}"
  | .movToVec rd ri rn idx s =>
    s!"mov {reg rd}.{lane s}[{idx}], {reg ri}.{lane s}[{idx}], {reg rn}"
  | .vecMisc .cnt rd rn s => s!"cnt {reg rd}.{arr s}, {reg rn}.{arr s}"
  | .vecLanes .addv rd rn s => s!"addv {reg rd}, {reg rn}.{arr s}"
  | .movFromVec rd rn idx s =>
    let op := if s == .size8 || s == .size16 then "umov" else "mov"
    s!"{op} {reg rd}, {reg rn}.{scalarLane s}[{idx}]"
  | i => s!"?{(repr i).pretty}"

/-- The registers of an instruction, with those of the `args`/`rets` pseudo-instructions (which
`MInst.defs` and `MInst.uses` leave out). -/
def instRegs : MInst → List Reg
  | .args ps | .rets ps => ps.map (·.1)
  | i => i.defs ++ i.uses

/-- The vregs of a VCode in increasing order. -/
def vregs (vc : VCode) : List Nat :=
  let rs := vc.blocks.toList.flatMap fun b =>
    b.params.toList ++ b.branchArgs.toList ++ b.insts.toList.flatMap instRegs
  let ns := rs.filterMap fun | .vreg n _ => some n | _ => none
  (ns.toArray.qsort (· < ·)).toList.eraseDups

/-- Rename vreg `n` to its rank among the vregs of the VCode. -/
def renumber (vc : VCode) : Reg → Reg :=
  let ns := vregs vc
  fun | .vreg n c => .vreg ((ns.idxOf? n).getD n) c | r => r

/-- The exact pre-allocation VCode, vregs renumbered by rank: one line per block (label,
parameters, the arguments of each successor), then one line per instruction. -/
def exact (r : Result) : List String :=
  let vc := r.code
  let rn := renumber vc
  let regs (rs : Array Reg) : String := s!"[{", ".intercalate (rs.toList.map (reg ∘ rn))}]"
  vc.blocks.toList.flatMap fun b =>
    let succ := (r.edgeArgs[b.label]?).getD #[]
    let head := s!"block{b.label}"
      ++ (if b.params.isEmpty then "" else s!"({", ".intercalate (b.params.toList.map (reg ∘ rn))})")
      ++ (if succ.all (·.isEmpty) then "" else s!" -> {" ".intercalate (succ.toList.map regs)}")
      ++ ":"
    head :: b.insts.toList.map fun i => inst (i.mapRegs rn)

/-- `s` without leading and trailing white space. -/
def trim (s : String) : String :=
  String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- Does `s` contain `sub`? -/
def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- Is `t` a register name: a general register, a vreg (`%n`), or a SIMD&FP register (`v4`, and
the scalar views `b16`, `h`, `s`, `d4`, `q`)? -/
def isRegTok (t : String) : Bool :=
  t == "fp" || t == "sp" || t == "xzr" || t == "wzr" ||
    (t.length > 1 && ["x", "w", "%", "v", "b", "h", "s", "d", "q"].any (t.startsWith ·) &&
      (t.toList.drop 1).all Char.isDigit)

/-- `line` with every register name replaced by `r`. -/
def abstractLine (line : String) : String := Id.run do
  let mut out := ""
  let mut tok := ""
  for c in line.toList do
    if c.isAlphanum || c == '%' || c == '#' || c == '_' || c == '-' then tok := tok.push c
    else
      out := (out ++ (if isRegTok tok then "r" else tok)).push c
      tok := ""
  return out ++ (if isRegTok tok then "r" else tok)

/-- Is `line` a 64-bit register move (`mov xA, xB`), which the register allocator inserts? -/
def isMove64 (line : String) : Bool :=
  match (line.splitOn " ").filter (· != "") with
  | ["mov", a, b] => a.startsWith "x" && a.endsWith "," && b.startsWith "x"
  | _ => false

/-- `line` with the extend operators in lower case (Cranelift's VCode printing writes `SXTW`,
the disassembly of the CI snapshot `sxtw`; the renderer writes lower case). -/
def lowerExtend (line : String) : String :=
  ["UXTB", "UXTH", "UXTW", "UXTX", "SXTB", "SXTH", "SXTW", "SXTX"].foldl
    (fun l e => l.replace e e.toLower) line

/-- Is `line` the frame allocation of the prologue or the epilogue (`sub sp, sp, …`,
`add sp, sp, …`, and the `movz`/`movk` of `w16` that load a large frame size)? -/
def isFrameAlloc (line : String) : Bool :=
  line.startsWith "sub sp, sp," || line.startsWith "add sp, sp," ||
    line.startsWith "movz w16," || line.startsWith "movk w16,"

/-- The instruction shape of stock's expected VCode (after allocation): no frame setup, no
`ret`, no 64-bit register moves; registers abstracted. -/
def stockShape (lines : List String) : List String :=
  ((lines.map trim).filter fun l =>
    !l.isEmpty && l != "ret" && l != "mov fp, sp" && !hasSub l "fp, lr" && !isMove64 l &&
      !isFrameAlloc l)
    |>.map (abstractLine ∘ lowerExtend)

/-- The instruction shape of a Lean VCode: block labels and instructions, without the `args`
and `rets` pseudo-instructions and register copies; registers abstracted. -/
def leanShape (vc : VCode) : List String :=
  vc.blocks.toList.flatMap fun b =>
    s!"block{b.label}:" :: (b.insts.toList.filter (fun
      | .args _ | .rets _ | .mov .. => false
      | _ => true)).map (abstractLine ∘ inst)

/-! ## Comparison with `Stock.lower` -/

def sameBlock (a b : VBlock) : Bool :=
  a.label == b.label && a.insts == b.insts && a.params == b.params && a.branchArgs == b.branchArgs

def sameCode (a b : VCode) : Bool :=
  a.name == b.name && a.blocks.size == b.blocks.size &&
    (a.blocks.zip b.blocks).all (fun (x, y) => sameBlock x y) && a.classes == b.classes &&
    a.slotBytes == b.slotBytes && a.outgoing == b.outgoing && a.rulesFired == b.rulesFired

/-- The two lowerings agree on everything except the `Ctx` values (of which the value types,
definitions and registers are compared). -/
def sameResult (a b : Result) : Bool :=
  sameCode a.code b.code && a.edgeArgs == b.edgeArgs && a.schedule == b.schedule &&
    a.initial == b.initial && a.final == b.final &&
    a.order.nodes == b.order.nodes && a.order.successors == b.order.successors &&
    a.ctx.valReg == b.ctx.valReg && a.ctx.valTy == b.ctx.valTy && a.ctx.valDef == b.ctx.valDef &&
    a.scans.size == b.scans.size &&
    (a.scans.zip b.scans).all (fun (x, y) => x.block == y.block && x.inst == y.inst &&
      x.termInst == y.termInst && x.isBranch == y.isBranch && x.input == y.input &&
      x.output == y.output) &&
    a.blockScans.size == b.blockScans.size &&
    (a.blockScans.zip b.blockScans).all (fun (x, y) => x.block == y.block &&
      x.termInst == y.termInst && x.isBranch == y.isBranch && x.indices == y.indices &&
      x.input == y.input && x.output == y.output)

/-- `lower128 f` and `Stock.lower f` agree: the same result, or the same error. -/
def agrees (f : Clif.Function) : Bool :=
  match lower128 f, Stock.lower f with
  | .ok a, .ok b => sameResult a b
  | .error a, .error b => a == b
  | _, _ => false

/-- Does `f` have an `i128` parameter, return or value? -/
def has128 (f : Clif.Function) : Bool :=
  let sigOf (r : Nat) : Option Clif.Signature := (f.extern? r).map (·.sig)
  f.sig.params.any (·.ty == .i128) || f.sig.returns.any (·.ty == .i128) ||
    f.blocks.any fun b => b.params.any (·.2 == .i128) ||
      b.body.any fun s => match s.inst.resultTypes sigOf (f.sigDecls.lookup ·) with
        | some tys => tys.contains .i128
        | none => false

def parse (src : String) : List (String × Except String Clif.Function) :=
  (Clif.parseFile src).funcs.map fun p => (p.name, p.func.mapError (·.toString))

def function? (src : String) : Option Clif.Function :=
  match parse src with
  | [(_, .ok f)] => some f
  | _ => none

/-! ## The 16 foundation shapes -/

structure Shape where
  name : String
  clif : String
  /-- Where `stock` comes from: a filetest, or the stock ISLE rule where no filetest has the
  shape. -/
  source : String
  /-- Stock Cranelift's VCode (after register allocation). -/
  stock : List String
  /-- `lower128`'s exact pre-allocation VCode (`exact`). -/
  pinned : List String

def shapes : List Shape := [
  { name := "f11", source := "isa/aarch64/call.clif"
    clif := "function %f11(i128, i64) -> i64 {
block0(v0: i128, v1: i64):
    v2, v3 = isplit v0
    return v3
}"
    stock := ["block0:", "mov x0, x1", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "rets %1=x0"] },
  { name := "f12", source := "isa/aarch64/call.clif"
    clif := "function %f12(i64, i128) -> i64 {
block0(v0: i64, v1: i128):
    v2, v3 = isplit v1
    return v2
}"
    stock := ["block0:", "mov x0, x2", "ret"]
    pinned := ["block0:", "args %0=x2 %1=x3", "rets %0=x0"] },
  { name := "f14", source := "isa/aarch64/call.clif"
    clif := "function %f14(i128, i128, i128, i64, i128) -> i128 {
block0(v0: i128, v1: i128, v2: i128, v3: i64, v4: i128):
    return v4
}"
    stock := ["stp fp, lr, [sp, #-16]!", "mov fp, sp", "block0:", "ldr x0, [sp, #16]",
      "ldr x1, [sp, #24]", "ldp fp, lr, [sp], #16", "ret"]
    pinned := ["block0:", "ldr %0, [fp, #16]", "ldr %1, [fp, #24]", "rets %0=x0 %1=x1"] },
  { name := "i128_uextend_i64", source := "isa/aarch64/extend-op.clif"
    clif := "function %i128_uextend_i64(i64) -> i128 {
block0(v0: i64):
    v1 = uextend.i128 v0
    return v1
}"
    stock := ["block0:", "movz x1, #0", "ret"]
    pinned := ["block0:", "args %0=x0", "movz %1, #0", "rets %0=x0 %1=x1"] },
  { name := "i128_sextend_i64", source := "isa/aarch64/extend-op.clif"
    clif := "function %i128_sextend_i64(i64) -> i128 {
block0(v0: i64):
    v1 = sextend.i128 v0
    return v1
}"
    stock := ["block0:", "asr x1, x0, #63", "ret"]
    pinned := ["block0:", "args %0=x0", "asr %1, %0, #63", "rets %0=x0 %1=x1"] },
  { name := "i128_uextend_i32", source := "isa/aarch64/extend-op.clif"
    clif := "function %i128_uextend_i32(i32) -> i128 {
block0(v0: i32):
    v1 = uextend.i128 v0
    return v1
}"
    stock := ["block0:", "mov w0, w0", "movz x1, #0", "ret"]
    pinned := ["block0:", "args %0=x0", "mov %1, %0", "movz %2, #0", "rets %1=x0 %2=x1"] },
  { name := "i128_sextend_i32", source := "isa/aarch64/extend-op.clif"
    clif := "function %i128_sextend_i32(i32) -> i128 {
block0(v0: i32):
    v1 = sextend.i128 v0
    return v1
}"
    stock := ["block0:", "sxtw x0, w0", "asr x1, x0, #63", "ret"]
    pinned := ["block0:", "args %0=x0", "sxtw %1, %0", "asr %2, %1, #63", "rets %1=x0 %2=x1"] },
  { name := "i128_uextend_i16", source := "isa/aarch64/extend-op.clif"
    clif := "function %i128_uextend_i16(i16) -> i128 {
block0(v0: i16):
    v1 = uextend.i128 v0
    return v1
}"
    stock := ["block0:", "uxth w0, w0", "movz x1, #0", "ret"]
    pinned := ["block0:", "args %0=x0", "uxth %1, %0", "movz %2, #0", "rets %1=x0 %2=x1"] },
  { name := "i128_sextend_i16", source := "isa/aarch64/extend-op.clif"
    clif := "function %i128_sextend_i16(i16) -> i128 {
block0(v0: i16):
    v1 = sextend.i128 v0
    return v1
}"
    stock := ["block0:", "sxth x0, w0", "asr x1, x0, #63", "ret"]
    pinned := ["block0:", "args %0=x0", "sxth %1, %0", "asr %2, %1, #63", "rets %1=x0 %2=x1"] },
  { name := "i128_uextend_i8", source := "isa/aarch64/extend-op.clif"
    clif := "function %i128_uextend_i8(i8) -> i128 {
block0(v0: i8):
    v1 = uextend.i128 v0
    return v1
}"
    stock := ["block0:", "uxtb w0, w0", "movz x1, #0", "ret"]
    pinned := ["block0:", "args %0=x0", "uxtb %1, %0", "movz %2, #0", "rets %1=x0 %2=x1"] },
  { name := "i128_sextend_i8", source := "isa/aarch64/extend-op.clif"
    clif := "function %i128_sextend_i8(i8) -> i128 {
block0(v0: i8):
    v1 = sextend.i128 v0
    return v1
}"
    stock := ["block0:", "sxtb x0, w0", "asr x1, x0, #63", "ret"]
    pinned := ["block0:", "args %0=x0", "sxtb %1, %0", "asr %2, %1, #63", "rets %1=x0 %2=x1"] },
  { name := "ireduce_128_64", source := "isa/aarch64/reduce.clif"
    clif := "function %ireduce_128_64(i128) -> i64 {
block0(v0: i128):
  v1 = ireduce.i64 v0
  return v1
}"
    stock := ["block0:", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "rets %0=x0"] },
  { name := "i128_brif_false", source := "isa/aarch64/condbr.clif"
    clif := "function %i128_brif_false(i128){
block0(v0: i128):
    brif v0, block1, block1

block1:
    nop
    return
}"
    stock := ["block0:", "orr x3, x0, x1", "cbnz x3, label1 ; b label2", "block1:", "b label3",
      "block2:", "b label3", "block3:", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "orr %2, %0, %1", "cbnz %2, label1 ; b label2",
      "block1:", "b label3", "block2:", "b label3", "block3:", "rets"] },
  { name := "iconcat", source := "rule iconcat_i128 (isa/aarch64/lower.isle): no instruction"
    clif := "function %iconcat(i64, i64) -> i128 {
block0(v0: i64, v1: i64):
    v2 = iconcat v0, v1
    return v2
}"
    stock := ["block0:", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "rets %0=x0 %1=x1"] },
  { name := "bitcast_i128", source := "bitcast to the same type (isa/aarch64/lower.isle): no instruction"
    clif := "function %bitcast_i128(i128) -> i128 {
block0(v0: i128):
    v1 = bitcast.i128 v0
    return v1
}"
    stock := ["block0:", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "rets %0=x0 %1=x1"] },
  { name := "block_param_i128", source := "block parameters (machinst/lower.rs add_block_params)"
    clif := "function %block_param_i128(i128) -> i128 {
block0(v0: i128):
    jump block1(v0)

block1(v1: i128):
    return v1
}"
    stock := ["block0:", "b label1", "block1:", "ret"]
    pinned := ["block0 -> [%0, %1]:", "args %0=x0 %1=x1", "b label1", "block1(%2, %3):",
      "rets %2=x0 %3=x1"] }]

/-- Further `i128` shapes of the foundation, without a stock filetest: an `i64` parameter in
`x7` after a stack pair, an `i128` return in an even-aligned pair after an `i64` return,
`i128` branch arguments of a `brif` on an `i64`, and on its split critical edges (stock lays out the `else` block first, as in
`isa/aarch64/condbr.clif` `%f`: `b.eq label2 ; b label1`). -/
def extras : List Shape := [
  { name := "x7_after_pair", source := "abi.rs compute_arg_locs"
    clif := "function %x7_after_pair(i128, i128, i128, i64, i128, i64) -> i64 {
block0(v0: i128, v1: i128, v2: i128, v3: i64, v4: i128, v5: i64):
    return v5
}"
    stock := ["block0:", "mov x0, x7", "ret"]
    pinned := ["block0:", "args %0=x7", "rets %0=x0"] },
  { name := "ret_pair_aligned", source := "abi.rs compute_arg_locs"
    clif := "function %ret_pair_aligned(i64, i64) -> i64, i128 {
block0(v0: i64, v1: i64):
    v2 = iconcat v0, v1
    return v0, v2
}"
    stock := ["block0:", "mov x2, x0", "mov x3, x1", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "rets %0=x0 %0=x2 %1=x3"] },
  { name := "brif_i128_args", source := "machinst/lower.rs collect_block_call"
    clif := "function %brif_i128_args(i128, i64) -> i128 {
block0(v0: i128, v1: i64):
    brif v1, block1(v0), block2

block1(v2: i128):
    return v2

block2:
    v3 = uextend.i128 v1
    return v3
}"
    stock := ["block0:", "cbnz x2, label2 ; b label1", "block1:", "mov x0, x2", "movz x1, #0", "ret",
      "block2:", "ret"]
    pinned := ["block0 -> [%0, %1] []:", "args %0=x0 %1=x1 %2=x2", "cbnz %2, label2 ; b label1",
      "block1:", "movz %5, #0", "rets %2=x0 %5=x1", "block2(%3, %4):", "rets %3=x0 %4=x1"] },
  { name := "brif_i128_edges", source := "machinst/blockorder.rs critical edges"
    clif := "function %brif_i128_edges(i128, i64) -> i128 {
block0(v0: i128, v1: i64):
    v2 = uextend.i128 v1
    brif v1, block1(v0), block1(v2)

block1(v3: i128):
    return v3
}"
    stock := ["block0:", "movz x3, #0", "cbnz x2, label1 ; b label2", "block1:", "b label3",
      "block2:", "mov x0, x2", "mov x1, x3", "b label3", "block3:", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2", "movz %5, #0", "cbnz %2, label1 ; b label2",
      "block1 -> [%0, %1]:", "b label3", "block2 -> [%2, %5]:", "b label3", "block3(%3, %4):",
      "rets %3=x0 %4=x1"] }]

/-- `i128` shifts and rotates (`lower.isle` `lower_shl128`, `lower_ushr128`, `lower_sshr128`,
the `rotl`/`rotr` `$I128` rules), and narrow shifts and rotates by an `i128` amount, which use
the amount's low register. The narrow shapes have no filetest with expected VCode: `stock` is
the stock code of the CI comparison snapshot (`runtests/i128-shifts.clif`,
`runtests/i128-rotate.clif`) in the syntax of the VCode printing (`neg` is `sub` from `wzr`,
`ror` is `extr`). -/
def shifts : List Shape := [
  { name := "ishl_i128_i8", source := "isa/aarch64/bitops.clif"
    clif := "function %ishl_i128_i8(i128, i8) -> i128 {
block0(v0: i128, v1: i8):
    v2 = ishl.i128 v0, v1
    return v2
}"
    stock := ["block0:", "lsl x4, x0, x2", "lsl x6, x1, x2", "orn w8, wzr, w2", "lsr x10, x0, #1",
      "lsr x12, x10, x8", "orr x14, x6, x12", "ands xzr, x2, #64", "csel x0, xzr, x4, ne",
      "csel x1, x4, x14, ne", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2", "lsl %3, %0, %2", "lsl %4, %1, %2",
      "orn %5, xzr, %2", "lsr %6, %0, #1", "lsr %7, %6, %5", "orr %8, %4, %7",
      "ands xzr, %2, #64", "csel %9, xzr, %3, ne", "csel %10, %3, %8, ne", "rets %9=x0 %10=x1"] },
  { name := "ishl_i128_i128", source := "isa/aarch64/bitops.clif"
    clif := "function %ishl_i128_i128(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v2 = ishl.i128 v0, v1
    return v2
}"
    stock := ["block0:", "lsl x5, x0, x2", "lsl x7, x1, x2", "orn w9, wzr, w2", "lsr x11, x0, #1",
      "lsr x13, x11, x9", "orr x15, x7, x13", "ands xzr, x2, #64", "csel x0, xzr, x5, ne",
      "csel x1, x5, x15, ne", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "lsl %4, %0, %2", "lsl %5, %1, %2",
      "orn %6, xzr, %2", "lsr %7, %0, #1", "lsr %8, %7, %6", "orr %9, %5, %8",
      "ands xzr, %2, #64", "csel %10, xzr, %4, ne", "csel %11, %4, %9, ne", "rets %10=x0 %11=x1"] },
  { name := "ushr_i128_i8", source := "isa/aarch64/bitops.clif"
    clif := "function %ushr_i128_i8(i128, i8) -> i128 {
block0(v0: i128, v1: i8):
    v2 = ushr.i128 v0, v1
    return v2
}"
    stock := ["block0:", "lsr x4, x0, x2", "lsr x6, x1, x2", "orn w8, wzr, w2", "lsl x10, x1, #1",
      "lsl x12, x10, x8", "orr x14, x4, x12", "ands xzr, x2, #64", "csel x0, x6, x14, ne",
      "csel x1, xzr, x6, ne", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2", "lsr %3, %0, %2", "lsr %4, %1, %2",
      "orn %5, xzr, %2", "lsl %6, %1, #1", "lsl %7, %6, %5", "orr %8, %3, %7",
      "ands xzr, %2, #64", "csel %9, %4, %8, ne", "csel %10, xzr, %4, ne", "rets %9=x0 %10=x1"] },
  { name := "ushr_i128_i128", source := "isa/aarch64/bitops.clif"
    clif := "function %ushr_i128_i128(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v2 = ushr.i128 v0, v1
    return v2
}"
    stock := ["block0:", "lsr x5, x0, x2", "lsr x7, x1, x2", "orn w9, wzr, w2", "lsl x11, x1, #1",
      "lsl x13, x11, x9", "orr x15, x5, x13", "ands xzr, x2, #64", "csel x0, x7, x15, ne",
      "csel x1, xzr, x7, ne", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "lsr %4, %0, %2", "lsr %5, %1, %2",
      "orn %6, xzr, %2", "lsl %7, %1, #1", "lsl %8, %7, %6", "orr %9, %4, %8",
      "ands xzr, %2, #64", "csel %10, %5, %9, ne", "csel %11, xzr, %5, ne", "rets %10=x0 %11=x1"] },
  { name := "sshr_i128_i8", source := "isa/aarch64/bitops.clif"
    clif := "function %sshr_i128_i8(i128, i8) -> i128 {
block0(v0: i128, v1: i8):
    v2 = sshr.i128 v0, v1
    return v2
}"
    stock := ["block0:", "lsr x4, x0, x2", "asr x6, x1, x2", "orn w8, wzr, w2", "lsl x10, x1, #1",
      "lsl x12, x10, x8", "asr x14, x1, #63", "orr x0, x4, x12", "ands xzr, x2, #64",
      "csel x0, x6, x0, ne", "csel x1, x14, x6, ne", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2", "lsr %3, %0, %2", "asr %4, %1, %2",
      "orn %5, xzr, %2", "lsl %6, %1, #1", "lsl %7, %6, %5", "asr %8, %1, #63", "orr %9, %3, %7",
      "ands xzr, %2, #64", "csel %10, %4, %9, ne", "csel %11, %8, %4, ne", "rets %10=x0 %11=x1"] },
  { name := "sshr_i128_i128", source := "isa/aarch64/bitops.clif"
    clif := "function %sshr_i128_i128(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v2 = sshr.i128 v0, v1
    return v2
}"
    stock := ["block0:", "lsr x5, x0, x2", "asr x7, x1, x2", "orn w9, wzr, w2", "lsl x11, x1, #1",
      "lsl x13, x11, x9", "asr x15, x1, #63", "orr x0, x5, x13", "ands xzr, x2, #64",
      "csel x0, x7, x0, ne", "csel x1, x15, x7, ne", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "lsr %4, %0, %2", "asr %5, %1, %2",
      "orn %6, xzr, %2", "lsl %7, %1, #1", "lsl %8, %7, %6", "asr %9, %1, #63", "orr %10, %4, %8",
      "ands xzr, %2, #64", "csel %11, %5, %10, ne", "csel %12, %9, %5, ne", "rets %11=x0 %12=x1"] },
  { name := "i128_rotr", source := "isa/aarch64/shift-rotate.clif"
    clif := "function %i128_rotr(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
  v2 = rotr.i128 v0, v1
  return v2
}"
    stock := ["block0:", "movz x5, #128", "sub x7, x5, x2", "lsr x9, x0, x2", "lsr x11, x1, x2",
      "orn w13, wzr, w2", "lsl x15, x1, #1", "lsl x3, x15, x13", "orr x3, x9, x3",
      "ands xzr, x2, #64", "csel x2, x11, x3, ne", "csel x3, xzr, x11, ne", "lsl x4, x0, x7",
      "lsl x1, x1, x7", "orn w5, wzr, w7", "lsr x0, x0, #1", "lsr x0, x0, x5", "orr x1, x1, x0",
      "ands xzr, x7, #64", "csel x0, xzr, x4, ne", "csel x1, x4, x1, ne", "orr x1, x3, x1",
      "orr x0, x2, x0", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "movz %4, #128", "sub %5, %4, %2",
      "lsr %6, %0, %2", "lsr %7, %1, %2", "orn %8, xzr, %2", "lsl %9, %1, #1", "lsl %10, %9, %8",
      "orr %11, %6, %10", "ands xzr, %2, #64", "csel %12, %7, %11, ne", "csel %13, xzr, %7, ne",
      "lsl %14, %0, %5", "lsl %15, %1, %5", "orn %16, xzr, %5", "lsr %17, %0, #1",
      "lsr %18, %17, %16", "orr %19, %15, %18", "ands xzr, %5, #64", "csel %20, xzr, %14, ne",
      "csel %21, %14, %19, ne", "orr %22, %13, %21", "orr %23, %12, %20", "rets %23=x0 %22=x1"] },
  { name := "i128_rotl", source := "isa/aarch64/shift-rotate.clif"
    clif := "function %i128_rotl(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
  v2 = rotl.i128 v0, v1
  return v2
}"
    stock := ["block0:", "movz x5, #128", "sub x7, x5, x2", "lsl x9, x0, x2", "lsl x11, x1, x2",
      "orn w13, wzr, w2", "lsr x15, x0, #1", "lsr x3, x15, x13", "orr x4, x11, x3",
      "ands xzr, x2, #64", "csel x3, xzr, x9, ne", "csel x2, x9, x4, ne", "lsr x4, x0, x7",
      "lsr x0, x1, x7", "orn w5, wzr, w7", "lsl x1, x1, #1", "lsl x1, x1, x5", "orr x1, x4, x1",
      "ands xzr, x7, #64", "csel x4, x0, x1, ne", "csel x1, xzr, x0, ne", "orr x0, x3, x4",
      "orr x1, x2, x1", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "movz %4, #128", "sub %5, %4, %2",
      "lsl %6, %0, %2", "lsl %7, %1, %2", "orn %8, xzr, %2", "lsr %9, %0, #1", "lsr %10, %9, %8",
      "orr %11, %7, %10", "ands xzr, %2, #64", "csel %12, xzr, %6, ne", "csel %13, %6, %11, ne",
      "lsr %14, %0, %5", "lsr %15, %1, %5", "orn %16, xzr, %5", "lsl %17, %1, #1",
      "lsl %18, %17, %16", "orr %19, %14, %18", "ands xzr, %5, #64", "csel %20, %15, %19, ne",
      "csel %21, xzr, %15, ne", "orr %22, %12, %20", "orr %23, %13, %21", "rets %22=x0 %23=x1"] },
  { name := "ishl_i64_i128", source := "runtests/i128-shifts.clif (CI snapshot stock code)"
    clif := "function %ishl_i64_i128(i64, i128) -> i64 {
block0(v0: i64, v1: i128):
    v2 = ishl v0, v1
    return v2
}"
    stock := ["block0:", "lsl x0, x0, x2", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x2 %2=x3", "lsl %3, %0, %1", "rets %3=x0"] },
  { name := "ushr_i8_i128", source := "runtests/i128-shifts.clif (CI snapshot stock code)"
    clif := "function %ushr_i8_i128(i8, i128) -> i8 {
block0(v0: i8, v1: i128):
    v2 = ushr v0, v1
    return v2
}"
    stock := ["block0:", "uxtb w4, w0", "and w6, w2, #7", "lsr w0, w4, w6", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x2 %2=x3", "uxtb %3, %0", "and %4, %1, #7",
      "lsr %5, %3, %4", "rets %5=x0"] },
  { name := "sshr_i32_i128", source := "runtests/i128-shifts.clif (CI snapshot stock code)"
    clif := "function %sshr_i32_i128(i32, i128) -> i32 {
block0(v0: i32, v1: i128):
    v2 = sshr v0, v1
    return v2
}"
    stock := ["block0:", "asr w0, w0, w2", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x2 %2=x3", "asr %3, %0, %1", "rets %3=x0"] },
  { name := "rotl_i32_i128", source := "runtests/i128-rotate.clif (CI snapshot stock code)"
    clif := "function %rotl_i32_i128(i32, i128) -> i32 {
block0(v0: i32, v1: i128):
    v2 = rotl v0, v1
    return v2
}"
    stock := ["block0:", "sub w4, wzr, w2", "extr w0, w0, w4", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x2 %2=x3", "sub %3, xzr, %1", "extr %4, %0, %3",
      "rets %4=x0"] },
  { name := "rotr_i16_i128", source := "runtests/i128-rotate.clif (CI snapshot stock code)"
    clif := "function %rotr_i16_i128(i16, i128) -> i16 {
block0(v0: i16, v1: i128):
    v2 = rotr v0, v1
    return v2
}"
    stock := ["block0:", "uxth w4, w0", "and w6, w2, #15", "sub w8, w6, #16", "sub w10, wzr, w8",
      "lsr w12, w4, w6", "lsl w14, w4, w10", "orr w0, w14, w12", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x2 %2=x3", "uxth %3, %0", "and %4, %1, #15",
      "sub %5, %4, #16", "sub %6, xzr, %5", "lsr %7, %3, %4", "lsl %8, %3, %6", "orr %9, %8, %7",
      "rets %9=x0"] }]

/-- `icmp` of `i128` operands (`inst.isle` `emit_icmp_i128`): `eq`/`ne` compare the low halves
and then the high halves (`cmp` and `ccmp`, `emit_icmp_i128_eq_ne`), the orderings subtract with
borrow (`cmp` and `sbcs`), a greater-than or less-or-equal ordering with the operands swapped.
The flags feed a `cset`, a `b.cond` of a `brif` (through the `uextend`, `is_nonzero_cmp`), or a
`csel` of a `select`. -/
def compares : List Shape := [
  { name := "icmp_eq_i128", source := "isa/aarch64/condbr.clif"
    clif := "function %icmp_eq_i128(i128, i128) -> i8 {
block0(v0: i128, v1: i128):
  v2 = icmp eq v0, v1
  return v2
}"
    stock := ["block0:", "subs xzr, x0, x2", "ccmp x1, x3, #nzcv, eq", "cset x0, eq", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %0, %2",
      "ccmp %1, %3, #nzcv, eq", "cset %4, eq", "rets %4=x0"] },
  { name := "icmp_ne_i128", source := "isa/aarch64/condbr.clif"
    clif := "function %icmp_ne_i128(i128, i128) -> i8 {
block0(v0: i128, v1: i128):
  v2 = icmp ne v0, v1
  return v2
}"
    stock := ["block0:", "subs xzr, x0, x2", "ccmp x1, x3, #nzcv, eq", "cset x0, ne", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %0, %2",
      "ccmp %1, %3, #nzcv, eq", "cset %4, ne", "rets %4=x0"] },
  { name := "icmp_slt_i128", source := "isa/aarch64/condbr.clif"
    clif := "function %icmp_slt_i128(i128, i128) -> i8 {
block0(v0: i128, v1: i128):
  v2 = icmp slt v0, v1
  return v2
}"
    stock := ["block0:", "subs xzr, x0, x2", "sbcs xzr, x1, x3", "cset x0, lt", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %0, %2", "sbcs xzr, %1, %3",
      "cset %4, lt", "rets %4=x0"] },
  { name := "icmp_ult_i128", source := "isa/aarch64/condbr.clif"
    clif := "function %icmp_ult_i128(i128, i128) -> i8 {
block0(v0: i128, v1: i128):
  v2 = icmp ult v0, v1
  return v2
}"
    stock := ["block0:", "subs xzr, x0, x2", "sbcs xzr, x1, x3", "cset x0, lo", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %0, %2", "sbcs xzr, %1, %3",
      "cset %4, lo", "rets %4=x0"] },
  { name := "icmp_sle_i128", source := "isa/aarch64/condbr.clif"
    clif := "function %icmp_sle_i128(i128, i128) -> i8 {
block0(v0: i128, v1: i128):
  v2 = icmp sle v0, v1
  return v2
}"
    stock := ["block0:", "subs xzr, x2, x0", "sbcs xzr, x3, x1", "cset x0, ge", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %2, %0", "sbcs xzr, %3, %1",
      "cset %4, ge", "rets %4=x0"] },
  { name := "icmp_ule_i128", source := "isa/aarch64/condbr.clif"
    clif := "function %icmp_ule_i128(i128, i128) -> i8 {
block0(v0: i128, v1: i128):
  v2 = icmp ule v0, v1
  return v2
}"
    stock := ["block0:", "subs xzr, x2, x0", "sbcs xzr, x3, x1", "cset x0, hs", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %2, %0", "sbcs xzr, %3, %1",
      "cset %4, hs", "rets %4=x0"] },
  { name := "icmp_sgt_i128", source := "isa/aarch64/condbr.clif"
    clif := "function %icmp_sgt_i128(i128, i128) -> i8 {
block0(v0: i128, v1: i128):
  v2 = icmp sgt v0, v1
  return v2
}"
    stock := ["block0:", "subs xzr, x2, x0", "sbcs xzr, x3, x1", "cset x0, lt", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %2, %0", "sbcs xzr, %3, %1",
      "cset %4, lt", "rets %4=x0"] },
  { name := "icmp_ugt_i128", source := "isa/aarch64/condbr.clif"
    clif := "function %icmp_ugt_i128(i128, i128) -> i8 {
block0(v0: i128, v1: i128):
  v2 = icmp ugt v0, v1
  return v2
}"
    stock := ["block0:", "subs xzr, x2, x0", "sbcs xzr, x3, x1", "cset x0, lo", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %2, %0", "sbcs xzr, %3, %1",
      "cset %4, lo", "rets %4=x0"] },
  { name := "icmp_sge_i128", source := "isa/aarch64/condbr.clif"
    clif := "function %icmp_sge_i128(i128, i128) -> i8 {
block0(v0: i128, v1: i128):
  v2 = icmp sge v0, v1
  return v2
}"
    stock := ["block0:", "subs xzr, x0, x2", "sbcs xzr, x1, x3", "cset x0, ge", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %0, %2", "sbcs xzr, %1, %3",
      "cset %4, ge", "rets %4=x0"] },
  { name := "icmp_uge_i128", source := "isa/aarch64/condbr.clif"
    clif := "function %icmp_uge_i128(i128, i128) -> i8 {
block0(v0: i128, v1: i128):
  v2 = icmp uge v0, v1
  return v2
}"
    stock := ["block0:", "subs xzr, x0, x2", "sbcs xzr, x1, x3", "cset x0, hs", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %0, %2", "sbcs xzr, %1, %3",
      "cset %4, hs", "rets %4=x0"] },
  { name := "i128_bricmp_eq", source := "isa/aarch64/condbr.clif"
    clif := "function %i128_bricmp_eq(i128, i128) {
block0(v0: i128, v1: i128):
  v2 = icmp eq v0, v1
  v3 = uextend.i32 v2
  brif v3, block1, block1

block1:
  return
}"
    stock := ["block0:", "subs xzr, x0, x2", "ccmp x1, x3, #nzcv, eq", "b.eq label1 ; b label2",
      "block1:", "b label3", "block2:", "b label3", "block3:", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %0, %2",
      "ccmp %1, %3, #nzcv, eq", "b.eq label1 ; b label2", "block1:", "b label3", "block2:",
      "b label3", "block3:", "rets"] },
  { name := "i128_bricmp_ne", source := "isa/aarch64/condbr.clif"
    clif := "function %i128_bricmp_ne(i128, i128) {
block0(v0: i128, v1: i128):
  v2 = icmp ne v0, v1
  v3 = uextend.i32 v2
  brif v3, block1, block1

block1:
  return
}"
    stock := ["block0:", "subs xzr, x0, x2", "ccmp x1, x3, #nzcv, eq", "b.ne label1 ; b label2",
      "block1:", "b label3", "block2:", "b label3", "block3:", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %0, %2",
      "ccmp %1, %3, #nzcv, eq", "b.ne label1 ; b label2", "block1:", "b label3", "block2:",
      "b label3", "block3:", "rets"] },
  { name := "i128_bricmp_slt", source := "isa/aarch64/condbr.clif"
    clif := "function %i128_bricmp_slt(i128, i128) {
block0(v0: i128, v1: i128):
  v2 = icmp slt v0, v1
  v3 = uextend.i32 v2
  brif v3, block1, block1

block1:
  return
}"
    stock := ["block0:", "subs xzr, x0, x2", "sbcs xzr, x1, x3", "b.lt label1 ; b label2",
      "block1:", "b label3", "block2:", "b label3", "block3:", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %0, %2", "sbcs xzr, %1, %3",
      "b.lt label1 ; b label2", "block1:", "b label3", "block2:", "b label3", "block3:", "rets"] },
  { name := "i128_bricmp_ugt", source := "isa/aarch64/condbr.clif"
    clif := "function %i128_bricmp_ugt(i128, i128) {
block0(v0: i128, v1: i128):
  v2 = icmp ugt v0, v1
  v3 = uextend.i32 v2
  brif v3, block1, block1

block1:
  return
}"
    stock := ["block0:", "subs xzr, x2, x0", "sbcs xzr, x3, x1", "b.lo label1 ; b label2",
      "block1:", "b label3", "block2:", "b label3", "block3:", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %2, %0", "sbcs xzr, %3, %1",
      "b.lo label1 ; b label2", "block1:", "b label3", "block2:", "b label3", "block3:", "rets"] },
  { name := "f", source := "isa/aarch64/condops.clif (`%f(i128, i64, i64)`)"
    clif := "function %f(i128, i64, i64) -> i64 {
block0(v0: i128, v1: i64, v2: i64):
  v3 = iconst.i64 42
  v4 = uextend.i128 v3
  v5 = icmp eq v0, v4
  v6 = select.i64 v5, v1, v2
  return v6
}"
    stock := ["block0:", "movz x7, #42", "movz x8, #0", "subs xzr, x0, x7",
      "ccmp x1, x8, #nzcv, eq", "csel x0, x2, x3, eq", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "movz %6, #42", "movz %5, #0",
      "subs xzr, %0, %6", "ccmp %1, %5, #nzcv, eq", "csel %4, %2, %3, eq", "rets %4=x0"] }]

/-- `select` and `select_spectre_guard` with an `i128` result or condition, `bmask` from or to
`i128`, and `bitselect` at `i128`. One flag-setter (the `icmp`, an `i128` `icmp` through
`emit_icmp_i128`, or `is_nonzero` of the condition: `ands`/`subs` of a narrow value, `orr` of the
halves of an `i128` value), then one `csel` per half (`lower_select_cond` at `$I128`). Without
`use_csdb`, `select_spectre_guard` is `select` (`maybe_csdb_after_select`). `bmask` of an `i128`
value tests the `orr` of the halves, and `bmask` to `i128` gives the `csetm` register as both
halves (`lower_bmask`). `bitselect` is `and`/`bic`/`orr` per half (`bitselect_i128`). The runtest
shapes have no filetest with expected VCode: `stock` is the stock code of the CI comparison
snapshot in the syntax of the VCode printing (`cmp` is `subs` to `xzr`/`wzr`, `mov` of an
immediate is `movz`). -/
def selects : List Shape := [
  { name := "select_icmp_i8_i128", source := "isa/aarch64/condops.clif (`%f(i8, i128, i128)`, select)"
    clif := "function %f(i8, i128, i128) -> i128 {
block0(v0: i8, v1: i128, v2: i128):
  v3 = iconst.i8 42
  v4 = icmp eq v0, v3
  v5 = select v4, v1, v2
  return v5
}"
    stock := ["block0:", "uxtb w6, w0", "subs wzr, w6, #42", "csel x0, x2, x4, eq",
      "csel x1, x3, x5, eq", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x2 %2=x3 %3=x4 %4=x5", "uxtb %5, %0", "subs xzr, %5, #42",
      "csel %6, %1, %3, eq", "csel %7, %2, %4, eq", "rets %6=x0 %7=x1"] },
  { name := "select_icmp_i128_i128", source := "isa/aarch64/condops.clif (`%f(i128, i128, i128)`, select)"
    clif := "function %f(i128, i128, i128) -> i128 {
block0(v0: i128, v1: i128, v2: i128):
  v3 = iconst.i64 42
  v4 = uextend.i128 v3
  v5 = icmp eq v0, v4
  v6 = select.i128 v5, v1, v2
  return v6
}"
    stock := ["block0:", "movz x10, #42", "movz x11, #0", "subs xzr, x0, x10",
      "ccmp x1, x11, #nzcv, eq", "csel x0, x2, x4, eq", "csel x1, x3, x5, eq", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3 %4=x4 %5=x5", "movz %9, #42", "movz %8, #0",
      "subs xzr, %0, %9", "ccmp %1, %8, #nzcv, eq", "csel %6, %2, %4, eq", "csel %7, %3, %5, eq",
      "rets %6=x0 %7=x1"] },
  { name := "i128_select", source := "isa/aarch64/condops.clif"
    clif := "function %i128_select(i8, i128, i128) -> i128 {
block0(v0: i8, v1: i128, v2: i128):
  v3 = select.i128 v0, v1, v2
  return v3
}"
    stock := ["block0:", "ands wzr, w0, #255", "csel x0, x2, x4, ne", "csel x1, x3, x5, ne", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x2 %2=x3 %3=x4 %4=x5", "ands xzr, %0, #255",
      "csel %5, %1, %3, ne", "csel %6, %2, %4, ne", "rets %5=x0 %6=x1"] },
  { name := "guard_icmp_i8_i128",
    source := "isa/aarch64/condops.clif (`%f(i8, i128, i128)`, select_spectre_guard)"
    clif := "function %f(i8, i128, i128) -> i128 {
block0(v0: i8, v1: i128, v2: i128):
  v3 = iconst.i8 42
  v4 = icmp eq v0, v3
  v5 = select_spectre_guard.i128 v4, v1, v2
  return v5
}"
    stock := ["block0:", "uxtb w6, w0", "subs wzr, w6, #42", "csel x0, x2, x4, eq",
      "csel x1, x3, x5, eq", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x2 %2=x3 %3=x4 %4=x5", "uxtb %5, %0", "subs xzr, %5, #42",
      "csel %6, %1, %3, eq", "csel %7, %2, %4, eq", "rets %6=x0 %7=x1"] },
  { name := "guard_icmp_i128_i128",
    source := "isa/aarch64/condops.clif (`%f(i128, i128, i128)`, select_spectre_guard)"
    clif := "function %f(i128, i128, i128) -> i128 {
block0(v0: i128, v1: i128, v2: i128):
  v3 = iconst.i64 42
  v4 = uextend.i128 v3
  v5 = icmp eq v0, v4
  v6 = select_spectre_guard.i128 v5, v1, v2
  return v6
}"
    stock := ["block0:", "movz x10, #42", "movz x11, #0", "subs xzr, x0, x10",
      "ccmp x1, x11, #nzcv, eq", "csel x0, x2, x4, eq", "csel x1, x3, x5, eq", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3 %4=x4 %5=x5", "movz %9, #42", "movz %8, #0",
      "subs xzr, %0, %9", "ccmp %1, %8, #nzcv, eq", "csel %6, %2, %4, eq", "csel %7, %3, %5, eq",
      "rets %6=x0 %7=x1"] },
  { name := "select_spectre_guard_i128_slt",
    source := "runtests/selectif-spectre-guard.clif (CI snapshot stock code)"
    clif := "function %select_spectre_guard_i128_slt(i8, i128, i128) -> i128 {
block0(v0: i8, v1: i128, v2: i128):
  v3 = iconst.i8 42
  v4 = icmp slt v0, v3
  v5 = select_spectre_guard.i128 v4, v1, v2
  return v5
}"
    stock := ["block0:", "movz w9, #42", "sxtb w7, w0", "subs wzr, w7, w9, sxtb",
      "csel x0, x2, x4, lt", "csel x1, x3, x5, lt", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x2 %2=x3 %3=x4 %4=x5", "movz %8, #42", "sxtb %5, %0",
      "subs xzr, %5, %8, sxtb", "csel %6, %1, %3, lt", "csel %7, %2, %4, lt", "rets %6=x0 %7=x1"] },
  { name := "i128_cond_select", source := "runtests/i128-select.clif (CI snapshot stock code)"
    clif := "function %i128_cond_select(i128, i128, i128) -> i128 {
block0(v0: i128, v1: i128, v2: i128):
    v3 = select.i128 v0, v1, v2
    return v3
}"
    stock := ["block0:", "orr x7, x0, x1", "subs xzr, x7, xzr", "csel x0, x2, x4, ne",
      "csel x1, x3, x5, ne", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3 %4=x4 %5=x5", "orr %6, %0, %1",
      "subs xzr, %6, xzr", "csel %7, %2, %4, ne", "csel %8, %3, %5, ne", "rets %7=x0 %8=x1"] },
  { name := "select_i128_cond", source := "runtests/select.clif (CI snapshot stock code)"
    clif := "function %select_i128_cond(i64, i64) -> i32 {
block0(v0: i64, v1: i64):
    v2 = iconcat v0, v1
    v3 = iconst.i32 42
    v4 = iconst.i32 97
    v5 = select v2, v3, v4
    return v5
}"
    stock := ["block0:", "movz w6, #42", "movz w7, #97", "orr x5, x0, x1", "subs xzr, x5, xzr",
      "csel x0, x6, x7, ne", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "movz %5, #42", "movz %4, #97", "orr %2, %0, %1",
      "subs xzr, %2, xzr", "csel %3, %5, %4, ne", "rets %3=x0"] },
  { name := "bmask_i128_i128", source := "isa/aarch64/bmask.clif"
    clif := "function %bmask_i128_i128(i128) -> i128 {
block0(v0: i128):
  v1 = bmask.i128 v0
  return v1
}"
    stock := ["block0:", "orr x3, x0, x1", "subs xzr, x3, #0", "csetm x1, ne", "mov x0, x1", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "orr %2, %0, %1", "subs xzr, %2, #0", "csetm %3, ne",
      "rets %3=x0 %3=x1"] },
  { name := "bmask_i128_i64", source := "isa/aarch64/bmask.clif"
    clif := "function %bmask_i128_i64(i128) -> i64 {
block0(v0: i128):
  v1 = bmask.i64 v0
  return v1
}"
    stock := ["block0:", "orr x3, x0, x1", "subs xzr, x3, #0", "csetm x0, ne", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "orr %2, %0, %1", "subs xzr, %2, #0", "csetm %3, ne",
      "rets %3=x0"] },
  { name := "bmask_i128_i8", source := "isa/aarch64/bmask.clif"
    clif := "function %bmask_i128_i8(i128) -> i8 {
block0(v0: i128):
  v1 = bmask.i8 v0
  return v1
}"
    stock := ["block0:", "orr x3, x0, x1", "subs xzr, x3, #0", "csetm x0, ne", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "orr %2, %0, %1", "subs xzr, %2, #0", "csetm %3, ne",
      "rets %3=x0"] },
  { name := "bmask_i64_i128", source := "isa/aarch64/bmask.clif"
    clif := "function %bmask_i64_i128(i64) -> i128 {
block0(v0: i64):
  v1 = bmask.i128 v0
  return v1
}"
    stock := ["block0:", "subs xzr, x0, #0", "csetm x1, ne", "mov x0, x1", "ret"]
    pinned := ["block0:", "args %0=x0", "subs xzr, %0, #0", "csetm %1, ne", "rets %1=x0 %1=x1"] },
  { name := "bmask_i8_i128", source := "isa/aarch64/bmask.clif"
    clif := "function %bmask_i8_i128(i8) -> i128 {
block0(v0: i8):
  v1 = bmask.i128 v0
  return v1
}"
    stock := ["block0:", "and w2, w0, #255", "subs wzr, w2, #0", "csetm x1, ne", "mov x0, x1", "ret"]
    pinned := ["block0:", "args %0=x0", "and %1, %0, #255", "subs xzr, %1, #0", "csetm %2, ne",
      "rets %2=x0 %2=x1"] },
  { name := "f0", source := "isa/aarch64/bitselect-i128.clif"
    clif := "function %f0(i128, i128, i128) -> i128 {
block0(v0: i128, v1: i128, v2: i128):
    v3 = bitselect v0, v1, v2
    return v3
}"
    stock := ["block0:", "and x7, x2, x0", "and x9, x3, x1", "bic x11, x4, x0", "bic x13, x5, x1",
      "orr x0, x7, x11", "orr x1, x9, x13", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3 %4=x4 %5=x5", "and %6, %2, %0",
      "and %7, %3, %1", "bic %8, %4, %0", "bic %9, %5, %1", "orr %10, %6, %8", "orr %11, %7, %9",
      "rets %10=x0 %11=x1"] }]

/-- `i128` arithmetic. `iadd` is `adds` of the low halves and `adc` of the high halves
(`iadd_i128`), `isub` is `subs` and `sbc` (`sub_i128`), and `ineg` is `sub_i128` from two
`movz #0` (`value_regs_zero`). `imul` is `umulh` and three `madd` (`imul_i128`); of two
`uextend`s or two `sextend`s, it is one `madd` and `umulh` or `smulh`. `iabs` is `asr`, two
`eor`, `subs` and `sbc`, and `bnot` is `orn` of each half. The runtest shapes have no filetest
with expected VCode: `stock` is the stock code of the CI comparison snapshot in the syntax of
the VCode printing (`mov` of an immediate is `movz`/`movn`, `mvn` is `orn` from `xzr`). -/
def ariths : List Shape := [
  { name := "add_i128", source := "isa/aarch64/arithmetic.clif"
    clif := "function %add_i128(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v2 = iadd v0, v1
    return v2
}"
    stock := ["block0:", "adds x0, x0, x2", "adc x1, x1, x3", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "adds %4, %0, %2", "adc %5, %1, %3",
      "rets %4=x0 %5=x1"] },
  { name := "sub_i128", source := "isa/aarch64/arithmetic.clif"
    clif := "function %sub_i128(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v2 = isub v0, v1
    return v2
}"
    stock := ["block0:", "subs x0, x0, x2", "sbc x1, x1, x3", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs %4, %0, %2", "sbc %5, %1, %3",
      "rets %4=x0 %5=x1"] },
  { name := "mul_i128", source := "isa/aarch64/arithmetic.clif"
    clif := "function %mul_i128(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v2 = imul v0, v1
    return v2
}"
    stock := ["block0:", "umulh x5, x0, x2", "madd x7, x0, x3, x5", "madd x1, x1, x2, x7",
      "madd x0, x0, x2, xzr", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "umulh %4, %0, %2",
      "madd %5, %0, %3, %4", "madd %6, %1, %2, %5", "madd %7, %0, %2, xzr", "rets %7=x0 %6=x1"] },
  { name := "f11", source := "isa/aarch64/iabs.clif"
    clif := "function %f11(i128) -> i128 {
block0(v0: i128):
  v1 = iabs v0
  return v1
}"
    stock := ["block0:", "asr x3, x1, #63", "eor x5, x1, x3", "eor x7, x0, x3", "subs x0, x7, x3",
      "sbc x1, x5, x3", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "asr %2, %1, #63", "eor %3, %1, %2",
      "eor %4, %0, %2", "subs %5, %4, %2", "sbc %6, %3, %2", "rets %5=x0 %6=x1"] },
  { name := "mul_uextend_i64", source := "isa/aarch64/i128.clif"
    clif := "function %mul_uextend_i64(i64, i64) -> i128 {
block0(v0: i64, v1: i64):
    v2 = uextend.i128 v0
    v3 = uextend.i128 v1
    v4 = imul v2, v3
    return v4
}"
    stock := ["block0:", "madd x3, x0, x1, xzr", "umulh x1, x0, x1", "mov x0, x3", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "madd %2, %0, %1, xzr", "umulh %3, %0, %1",
      "rets %2=x0 %3=x1"] },
  { name := "mul_sextend_i64", source := "isa/aarch64/i128.clif"
    clif := "function %mul_sextend_i64(i64, i64) -> i128 {
block0(v0: i64, v1: i64):
    v2 = sextend.i128 v0
    v3 = sextend.i128 v1
    v4 = imul v2, v3
    return v4
}"
    stock := ["block0:", "madd x3, x0, x1, xzr", "smulh x1, x0, x1", "mov x0, x3", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "madd %2, %0, %1, xzr", "smulh %3, %0, %1",
      "rets %2=x0 %3=x1"] },
  { name := "ineg_i128", source := "runtests/i128-ineg.clif (CI snapshot stock code)"
    clif := "function %ineg_i128(i128) -> i128 {
block0(v0: i128):
  v1 = ineg.i128 v0
  return v1
}"
    stock := ["block0:", "movz x3, #0", "movz x5, #0", "subs x0, x3, x0", "sbc x1, x5, x1", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "movz %2, #0", "movz %3, #0", "subs %4, %2, %0",
      "sbc %5, %3, %1", "rets %4=x0 %5=x1"] },
  { name := "iadd_imm_neg", source := "runtests/i128-arithmetic.clif (CI snapshot stock code)"
    clif := "function %iadd_imm_neg(i128) -> i128 {
block0(v0: i128):
    v2 = iconst.i64 -1
    v3 = sextend.i128 v2
    v1 = iadd v0, v3
    return v1
}"
    stock := ["block0:", "movn x6, #0", "asr x7, x6, #63", "adds x0, x0, x6", "adc x1, x1, x7",
      "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "movn %5, #0", "asr %4, %5, #63",
      "adds %2, %0, %5", "adc %3, %1, %4", "rets %2=x0 %3=x1"] },
  { name := "add_i128_splats", source := "runtests/i128-arithmetic.clif (CI snapshot stock code)"
    clif := "function %add_i128_splats(i64, i64, i64, i64) -> i128 {
block0(v0: i64, v1: i64, v2: i64, v3: i64):
    v4 = iconcat v0, v1
    v5 = iconcat v2, v3
    v6 = iadd v4, v5
    return v6
}"
    stock := ["block0:", "adds x0, x0, x2", "adc x1, x1, x3", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "adds %4, %0, %2", "adc %5, %1, %3",
      "rets %4=x0 %5=x1"] },
  { name := "fold_iadd_bnot_x_to_allones_i128_rt"
    source := "runtests/i128-arithmetic-extends.clif (CI snapshot stock code)"
    clif := "function %fold_iadd_bnot_x_to_allones_i128_rt(i128) -> i128 {
block0(v0: i128):
    v1 = bnot v0
    v2 = iadd v1, v0
    return v2
}"
    stock := ["block0:", "orn x5, xzr, x0", "orn x7, xzr, x1", "adds x0, x5, x0",
      "adc x1, x7, x1", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "orn %4, xzr, %0", "orn %5, xzr, %1",
      "adds %2, %4, %0", "adc %3, %5, %1", "rets %2=x0 %3=x1"] }]

/-- `i128` bit operations. `band`, `bor`, `bxor` are one `and`, `orr`, `eor` per half
(`i128_alu_bitop`), and one `bic`, `orn`, `eon` per half when an operand is a `bnot` or for a
`bnot` of a `bxor`. `bitrev` is `rbit` of each half with the halves swapped, `clz` is
`lower_clz128` (`clz` of each half, `lsr`, `madd`, `movz #0`), `ctz` is `rbit` of each half and
then `lower_clz128`, `cls` is the `cls`/`eon`/`madd`/`csel` sequence of its `$I128` rule, and
`bswap` is `rev64` of each half with the halves swapped. The runtest shapes have no filetest
with expected VCode: `stock` is the stock code of the CI comparison snapshot in the syntax of
the VCode printing (`rev` is `rev64`, `cmp` is `subs` to `xzr`, `mov` of an immediate is
`movz`). -/
def bitops : List Shape := [
  { name := "band_i128", source := "isa/aarch64/bitops.clif"
    clif := "function %band_i128(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v2 = band v0, v1
    return v2
}"
    stock := ["block0:", "and x0, x0, x2", "and x1, x1, x3", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "and %4, %0, %2", "and %5, %1, %3",
      "rets %4=x0 %5=x1"] },
  { name := "bor_i128", source := "isa/aarch64/bitops.clif"
    clif := "function %bor_i128(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v2 = bor v0, v1
    return v2
}"
    stock := ["block0:", "orr x0, x0, x2", "orr x1, x1, x3", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "orr %4, %0, %2", "orr %5, %1, %3",
      "rets %4=x0 %5=x1"] },
  { name := "bxor_i128", source := "isa/aarch64/bitops.clif"
    clif := "function %bxor_i128(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v2 = bxor v0, v1
    return v2
}"
    stock := ["block0:", "eor x0, x0, x2", "eor x1, x1, x3", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "eor %4, %0, %2", "eor %5, %1, %3",
      "rets %4=x0 %5=x1"] },
  { name := "band_not_i128", source := "isa/aarch64/bitops.clif"
    clif := "function %band_not_i128(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v3 = bnot v1
    v2 = band v0, v3
    return v2
}"
    stock := ["block0:", "bic x0, x0, x2", "bic x1, x1, x3", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "bic %4, %0, %2", "bic %5, %1, %3",
      "rets %4=x0 %5=x1"] },
  { name := "bor_not_i128", source := "isa/aarch64/bitops.clif"
    clif := "function %bor_not_i128(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v3 = bnot v1
    v2 = bor v0, v3
    return v2
}"
    stock := ["block0:", "orn x0, x0, x2", "orn x1, x1, x3", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "orn %4, %0, %2", "orn %5, %1, %3",
      "rets %4=x0 %5=x1"] },
  { name := "bxor_not_i128", source := "isa/aarch64/bitops.clif"
    clif := "function %bxor_not_i128(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v3 = bnot v1
    v2 = bxor v0, v3
    return v2
}"
    stock := ["block0:", "eon x0, x0, x2", "eon x1, x1, x3", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "eon %4, %0, %2", "eon %5, %1, %3",
      "rets %4=x0 %5=x1"] },
  { name := "bnot_of_bxor", source := "isa/aarch64/bitops.clif"
    clif := "function %bnot_of_bxor(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
  v2 = bxor v0, v1
  v3 = bnot v2
  return v3
}"
    stock := ["block0:", "eon x0, x0, x2", "eon x1, x1, x3", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "eon %4, %0, %2", "eon %5, %1, %3",
      "rets %4=x0 %5=x1"] },
  { name := "a", source := "isa/aarch64/bitops.clif"
    clif := "function %a(i128) -> i128 {
block0(v0: i128):
    v1 = bitrev v0
    return v1
}"
    stock := ["block0:", "mov x6, x1", "rbit x1, x0", "rbit x0, x6", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "rbit %2, %0", "rbit %3, %1", "rets %3=x0 %2=x1"] },
  { name := "b", source := "isa/aarch64/bitops.clif"
    clif := "function %b(i128) -> i128 {
block0(v0: i128):
    v1 = clz v0
    return v1
}"
    stock := ["block0:", "clz x3, x1", "clz x5, x0", "lsr x7, x3, #6", "madd x0, x5, x7, x3",
      "movz x1, #0", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "clz %2, %1", "clz %3, %0", "lsr %4, %2, #6",
      "madd %5, %3, %4, %2", "movz %6, #0", "rets %5=x0 %6=x1"] },
  { name := "c", source := "isa/aarch64/bitops.clif"
    clif := "function %c(i128) -> i128 {
block0(v0: i128):
    v1 = cls v0
    return v1
}"
    stock := ["block0:", "cls x3, x0", "cls x5, x1", "eon x7, x1, x0", "lsr x9, x7, #63",
      "madd x11, x3, x9, x9", "subs xzr, x5, #63", "csel x14, x11, xzr, eq", "add x0, x14, x5",
      "movz x1, #0", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "cls %2, %0", "cls %3, %1", "eon %4, %1, %0",
      "lsr %5, %4, #63", "madd %6, %2, %5, %5", "subs xzr, %3, #63", "csel %7, %6, xzr, eq",
      "add %8, %7, %3", "movz %9, #0", "rets %8=x0 %9=x1"] },
  { name := "d", source := "isa/aarch64/bitops.clif"
    clif := "function %d(i128) -> i128 {
block0(v0: i128):
    v1 = ctz v0
    return v1
}"
    stock := ["block0:", "rbit x3, x0", "rbit x5, x1", "clz x7, x3", "clz x9, x5",
      "lsr x11, x7, #6", "madd x0, x9, x11, x7", "movz x1, #0", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "rbit %2, %0", "rbit %3, %1", "clz %4, %2",
      "clz %5, %3", "lsr %6, %4, #6", "madd %7, %5, %6, %4", "movz %8, #0",
      "rets %7=x0 %8=x1"] },
  { name := "bswap_i128", source := "runtests/i128-bswap.clif (CI snapshot stock code)"
    clif := "function %bswap_i128(i128) -> i128 {
block0(v0: i128):
    v1 = bswap v0
    return v1
}"
    stock := ["block0:", "mov x6, x0", "rev64 x0, x1", "rev64 x1, x6", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "rev64 %2, %1", "rev64 %3, %0",
      "rets %2=x0 %3=x1"] },
  { name := "bitwise_bitselect_i128"
    source := "runtests/i128-bitselect.clif (CI snapshot stock code)"
    clif := "function %bitwise_bitselect_i128(i128, i128, i128) -> i128 {
block0(v0: i128, v1: i128, v2: i128):
    v3 = bnot v0
    v4 = band v3, v2
    v5 = band v0, v1
    v6 = bor v5, v4
    return v6
}"
    stock := ["block0:", "bic x11, x4, x0", "bic x13, x5, x1", "and x12, x0, x2",
      "and x14, x1, x3", "orr x0, x12, x11", "orr x1, x14, x13", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3 %4=x4 %5=x5", "bic %10, %4, %0",
      "bic %11, %5, %1", "and %8, %0, %2", "and %9, %1, %3", "orr %6, %8, %10",
      "orr %7, %9, %11", "rets %6=x0 %7=x1"] },
  { name := "reverse_bits_one", source := "runtests/i128-bitrev.clif (CI snapshot stock code)"
    clif := "function %reverse_bits_one() -> i8 {
block0:
    v0 = iconst.i64 0
    v1 = iconst.i64 1
    v2 = iconcat v0, v1
    v3 = bitrev.i128 v2
    v4 = iconst.i64 0x8000_0000_0000_0000
    v5 = iconst.i64 0
    v6 = iconcat v4, v5
    v7 = icmp eq v3, v6
    return v7
}"
    stock := ["block0:", "movz x6, #0", "movz x7, #1", "rbit x5, x6", "rbit x7, x7",
      "movz x6, #32768, LSL #48", "movz x8, #0", "subs xzr, x7, x6", "ccmp x5, x8, #nzcv, eq",
      "cset x0, eq", "ret"]
    pinned := ["block0:", "movz %6, #0", "movz %5, #1", "rbit %3, %6", "rbit %4, %5",
      "movz %2, #32768, LSL #48", "movz %1, #0", "subs xzr, %4, %2", "ccmp %3, %1, #nzcv, eq",
      "cset %0, eq", "rets %0=x0"] },
  -- `popcnt_i128`: the low half into a vector register (`fmov`), the high half into its lane 1
  -- (`MInst.movToVec`), `cnt` and `addv` of the 16 bytes, `umov` of the sum, 0 as the high half
  { name := "d (popcnt)", source := "isa/aarch64/bitops.clif"
    clif := "function %d(i128) -> i128 {
block0(v0: i128):
    v1 = popcnt v0
    return v1
}"
    stock := ["block0:", "fmov d4, x0", "mov v4.d[1], v4.d[1], x1", "cnt v7.16b, v4.16b",
      "addv b16, v7.16b", "umov w0, v16.b[0]", "movz x1, #0", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "fmov %2, %0",
      "mov %3.d[1], %2.d[1], %1", "cnt %4.16b, %3.16b", "addv %5, %4.16b", "umov %6, %5.b[0]",
      "movz %7, #0", "rets %6=x0 %7=x1"] },
  { name := "popcnt_i128", source := "runtests/i128-bitops-count.clif (CI snapshot stock code)"
    clif := "function %popcnt_i128(i128) -> i128 system_v {
block0(v0: i128):
    v1 = popcnt v0
    return v1
}"
    stock := ["block0:", "fmov d4, x0", "mov v4.d[1], v4.d[1], x1", "cnt v7.16b, v4.16b",
      "addv b16, v7.16b", "umov w0, v16.b[0]", "movz x1, #0", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "fmov %2, %0",
      "mov %3.d[1], %2.d[1], %1", "cnt %4.16b, %3.16b", "addv %5, %4.16b", "umov %6, %5.b[0]",
      "movz %7, #0", "rets %6=x0 %7=x1"] }]

/-- `i128` minimum and maximum (rule 2 of `umin`, `umax`, `smin`, `smax`): `lower_select` at
`$I128` of the `emit_icmp` of the operands, that is `subs` of the low halves and `sbcs` of the
high halves (the operands swapped for a maximum), then one `csel` per half. -/
def minmaxes : List Shape := [
  { name := "umin_i128", source := "isa/aarch64/i128.clif"
    clif := "function %umin_i128(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v2 = umin v0, v1
    return v2
}"
    stock := ["block0:", "subs xzr, x0, x2", "sbcs xzr, x1, x3", "csel x0, x0, x2, lo",
      "csel x1, x1, x3, lo", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %0, %2", "sbcs xzr, %1, %3",
      "csel %4, %0, %2, lo", "csel %5, %1, %3, lo", "rets %4=x0 %5=x1"] },
  { name := "umax_i128", source := "isa/aarch64/i128.clif"
    clif := "function %umax_i128(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v2 = umax v0, v1
    return v2
}"
    stock := ["block0:", "subs xzr, x2, x0", "sbcs xzr, x3, x1", "csel x0, x0, x2, lo",
      "csel x1, x1, x3, lo", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %2, %0", "sbcs xzr, %3, %1",
      "csel %4, %0, %2, lo", "csel %5, %1, %3, lo", "rets %4=x0 %5=x1"] },
  { name := "smin_i128", source := "isa/aarch64/i128.clif"
    clif := "function %smin_i128(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v2 = smin v0, v1
    return v2
}"
    stock := ["block0:", "subs xzr, x0, x2", "sbcs xzr, x1, x3", "csel x0, x0, x2, lt",
      "csel x1, x1, x3, lt", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %0, %2", "sbcs xzr, %1, %3",
      "csel %4, %0, %2, lt", "csel %5, %1, %3, lt", "rets %4=x0 %5=x1"] },
  { name := "smax_i128", source := "isa/aarch64/i128.clif"
    clif := "function %smax_i128(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v2 = smax v0, v1
    return v2
}"
    stock := ["block0:", "subs xzr, x2, x0", "sbcs xzr, x3, x1", "csel x0, x0, x2, lt",
      "csel x1, x1, x3, lt", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs xzr, %2, %0", "sbcs xzr, %3, %1",
      "csel %4, %0, %2, lt", "csel %5, %1, %3, lt", "rets %4=x0 %5=x1"] }]

/-- `i128` overflow operations (`overflow_op_128`): `adds` and `adcs`, or `subs` and `sbcs`, of
the halves, then the `cset` of the overflow condition; the `i8` flag is the third return
register. No filetest has expected VCode for them: `stock` is the stock code of the CI
comparison snapshot. -/
def overflows : List Shape := [
  { name := "saddof_i128", source := "runtests/sadd_overflow.clif (CI snapshot stock code)"
    clif := "function %saddof_i128(i128, i128) -> i128, i8 {
block0(v0: i128, v1: i128):
    v2, v3 = sadd_overflow v0, v1
    return v2, v3
}"
    stock := ["block0:", "adds x0, x0, x2", "adcs x1, x1, x3", "cset x2, vs", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "adds %4, %0, %2", "adcs %5, %1, %3",
      "cset %6, vs", "rets %4=x0 %5=x1 %6=x2"] },
  { name := "ssubof_i128", source := "runtests/ssub_overflow.clif (CI snapshot stock code)"
    clif := "function %ssubof_i128(i128, i128) -> i128, i8 {
block0(v0: i128, v1: i128):
    v2, v3 = ssub_overflow v0, v1
    return v2, v3
}"
    stock := ["block0:", "subs x0, x0, x2", "sbcs x1, x1, x3", "cset x2, vs", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs %4, %0, %2", "sbcs %5, %1, %3",
      "cset %6, vs", "rets %4=x0 %5=x1 %6=x2"] },
  { name := "uaddof_i128", source := "runtests/uadd_overflow_128.clif (CI snapshot stock code)"
    clif := "function %uaddof_i128(i128, i128) -> i128, i8 {
block0(v0: i128, v1: i128):
    v2, v3 = uadd_overflow v0, v1
    return v2, v3
}"
    stock := ["block0:", "adds x0, x0, x2", "adcs x1, x1, x3", "cset x2, hs", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "adds %4, %0, %2", "adcs %5, %1, %3",
      "cset %6, hs", "rets %4=x0 %5=x1 %6=x2"] },
  { name := "usubof_i128", source := "runtests/usub_overflow.clif (CI snapshot stock code)"
    clif := "function %usubof_i128(i128, i128) -> i128, i8 {
block0(v0: i128, v1: i128):
    v2, v3 = usub_overflow v0, v1
    return v2, v3
}"
    stock := ["block0:", "subs x0, x0, x2", "sbcs x1, x1, x3", "cset x2, lo", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1 %2=x2 %3=x3", "subs %4, %0, %2", "sbcs %5, %1, %3",
      "cset %6, lo", "rets %4=x0 %5=x1 %6=x2"] }]

/-- `i128` loads and stores (`load_i128`, `store_i128`): one `ldp`/`stp` of the register pair
with a `PairAMode::SignedOffset` (`pair_amode`: the offset when it is a multiple of 8 in
`-512..504`, else `amode_add` of it and offset 0). A `stack_addr` is the `mov`/`add` from `sp` of
`abi_stackslot_addr`. The runtests have no expected VCode: their `stock` is the stock code of the
CI comparison snapshot, in the VCode syntax. -/
def mems : List Shape := [
  { name := "i128", source := "isa/aarch64/amodes.clif"
    clif := "function %i128(i64) -> i128 {
block0(v0: i64):
  v1 = load.i128 v0
  store.i128 v1, v0
  return v1
}"
    stock := ["block0:", "mov x5, x0", "ldp x0, x1, [x5]", "stp x0, x1, [x5]", "ret"]
    pinned := ["block0:", "args %0=x0", "ldp %1, %2, [%0]", "stp %1, %2, [%0]",
      "rets %1=x0 %2=x1"] },
  { name := "i128_imm_offset", source := "isa/aarch64/amodes.clif"
    clif := "function %i128_imm_offset(i64) -> i128 {
block0(v0: i64):
  v1 = load.i128 v0+16
  store.i128 v1, v0+16
  return v1
}"
    stock := ["block0:", "mov x5, x0", "ldp x0, x1, [x5, #16]", "stp x0, x1, [x5, #16]", "ret"]
    pinned := ["block0:", "args %0=x0", "ldp %1, %2, [%0, #16]", "stp %1, %2, [%0, #16]",
      "rets %1=x0 %2=x1"] },
  { name := "i128_imm_offset_large", source := "isa/aarch64/amodes.clif"
    clif := "function %i128_imm_offset_large(i64) -> i128 {
block0(v0: i64):
  v1 = load.i128 v0+504
  store.i128 v1, v0+504
  return v1
}"
    stock := ["block0:", "mov x5, x0", "ldp x0, x1, [x5, #504]", "stp x0, x1, [x5, #504]", "ret"]
    pinned := ["block0:", "args %0=x0", "ldp %1, %2, [%0, #504]", "stp %1, %2, [%0, #504]",
      "rets %1=x0 %2=x1"] },
  { name := "i128_imm_offset_negative_large", source := "isa/aarch64/amodes.clif"
    clif := "function %i128_imm_offset_negative_large(i64) -> i128 {
block0(v0: i64):
  v1 = load.i128 v0-512
  store.i128 v1, v0-512
  return v1
}"
    stock := ["block0:", "mov x5, x0", "ldp x0, x1, [x5, #-512]", "stp x0, x1, [x5, #-512]", "ret"]
    pinned := ["block0:", "args %0=x0", "ldp %1, %2, [%0, #-512]", "stp %1, %2, [%0, #-512]",
      "rets %1=x0 %2=x1"] },
  { name := "i128_add_offset", source := "isa/aarch64/amodes.clif"
    clif := "function %i128_add_offset(i64) -> i128 {
block0(v0: i64):
  v3 = iconst.i64 32
  v1 = iadd v0, v3
  v2 = load.i128 v1
  store.i128 v2, v1
  return v2
}"
    stock := ["block0:", "add x4, x0, #32", "ldp x0, x1, [x4]", "stp x0, x1, [x4]", "ret"]
    pinned := ["block0:", "args %0=x0", "add %3, %0, #32", "ldp %1, %2, [%3]", "stp %1, %2, [%3]",
      "rets %1=x0 %2=x1"] },
  { name := "i128_32bit_sextend_simple", source := "isa/aarch64/amodes.clif"
    clif := "function %i128_32bit_sextend_simple(i32) -> i128 {
block0(v0: i32):
  v1 = sextend.i64 v0
  v2 = load.i128 v1
  store.i128 v2, v1
  return v2
}"
    stock := ["block0:", "sxtw x4, w0", "ldp x0, x1, [x4]", "stp x0, x1, [x4]", "ret"]
    pinned := ["block0:", "args %0=x0", "sxtw %3, %0", "ldp %1, %2, [%3]", "stp %1, %2, [%3]",
      "rets %1=x0 %2=x1"] },
  { name := "i128_32bit_sextend", source := "isa/aarch64/amodes.clif"
    clif := "function %i128_32bit_sextend(i64, i32) -> i128 {
block0(v0: i64, v1: i32):
  v2 = sextend.i64 v1
  v3 = iadd.i64 v0, v2
  v6 = iconst.i64 24
  v4 = iadd v3, v6
  v5 = load.i128 v4
  store.i128 v5, v4
  return v5
}"
    stock := ["block0:", "add x6, x0, x1, SXTW", "add x6, x6, #24", "ldp x0, x1, [x6]",
      "stp x0, x1, [x6]", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "add %5, %0, %1, sxtw", "add %4, %5, #24",
      "ldp %2, %3, [%4]", "stp %2, %3, [%4]", "rets %2=x0 %3=x1"] },
  { name := "i128_stack_load", source := "isa/aarch64/stack.clif"
    clif := "function %i128_stack_load() -> i128 {
ss0 = explicit_slot 16

block0:
  v1 = stack_addr.i64 ss0
  v0 = load.i128 notrap v1
  return v0
}"
    stock := ["stp fp, lr, [sp, #-16]!", "mov fp, sp", "sub sp, sp, #16", "block0:", "mov x2, sp",
      "ldp x0, x1, [x2]", "add sp, sp, #16", "ldp fp, lr, [sp], #16", "ret"]
    pinned := ["block0:", "mov %2, sp", "ldp %0, %1, [%2]", "rets %0=x0 %1=x1"] },
  { name := "i128_stack_load_inst_offset", source := "isa/aarch64/stack.clif"
    clif := "function %i128_stack_load_inst_offset() -> i128 {
ss0 = explicit_slot 16
ss1 = explicit_slot 16

block0:
  v1 = stack_addr.i64 ss1+16
  v0 = load.i128 notrap v1
  return v0
}"
    stock := ["stp fp, lr, [sp, #-16]!", "mov fp, sp", "sub sp, sp, #32", "block0:",
      "add x2, sp, #32", "ldp x0, x1, [x2]", "add sp, sp, #32", "ldp fp, lr, [sp], #16", "ret"]
    pinned := ["block0:", "add %2, sp, #32", "ldp %0, %1, [%2]", "rets %0=x0 %1=x1"] },
  { name := "i128_stack_load_big", source := "isa/aarch64/stack.clif"
    clif := "function %i128_stack_load_big() -> i128 {
ss0 = explicit_slot 100000
ss1 = explicit_slot 8

block0:
  v1 = stack_addr.i64 ss0
  v0 = load.i128 notrap v1
  return v0
}"
    stock := ["stp fp, lr, [sp, #-16]!", "mov fp, sp", "movz w16, #34480",
      "movk w16, w16, #1, LSL #16", "sub sp, sp, x16, UXTX", "block0:", "mov x2, sp",
      "ldp x0, x1, [x2]", "movz w16, #34480", "movk w16, w16, #1, LSL #16", "add sp, sp, x16, UXTX",
      "ldp fp, lr, [sp], #16", "ret"]
    pinned := ["block0:", "mov %2, sp", "ldp %0, %1, [%2]", "rets %0=x0 %1=x1"] },
  { name := "i128_stack_store", source := "isa/aarch64/stack.clif"
    clif := "function %i128_stack_store(i128) {
ss0 = explicit_slot 16

block0(v0: i128):
  v1 = stack_addr.i64 ss0
  store.i128 notrap v0, v1
  return
}"
    stock := ["stp fp, lr, [sp, #-16]!", "mov fp, sp", "sub sp, sp, #16", "block0:", "mov x3, sp",
      "stp x0, x1, [x3]", "add sp, sp, #16", "ldp fp, lr, [sp], #16", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "mov %2, sp", "stp %0, %1, [%2]", "rets"] },
  { name := "i128_stack_store_inst_offset", source := "isa/aarch64/stack.clif"
    clif := "function %i128_stack_store_inst_offset(i128) {
ss0 = explicit_slot 16
ss1 = explicit_slot 16

block0(v0: i128):
  v1 = stack_addr.i64 ss1+16
  store.i128 notrap v0, v1
  return
}"
    stock := ["stp fp, lr, [sp, #-16]!", "mov fp, sp", "sub sp, sp, #32", "block0:",
      "add x3, sp, #32", "stp x0, x1, [x3]", "add sp, sp, #32", "ldp fp, lr, [sp], #16", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "add %2, sp, #32", "stp %0, %1, [%2]", "rets"] },
  { name := "i128_stack_store_big", source := "isa/aarch64/stack.clif"
    clif := "function %i128_stack_store_big(i128) {
ss0 = explicit_slot 100000
ss1 = explicit_slot 8

block0(v0: i128):
  v1 = stack_addr.i64 ss0
  store.i128 notrap v0, v1
  return
}"
    stock := ["stp fp, lr, [sp, #-16]!", "mov fp, sp", "movz w16, #34480",
      "movk w16, w16, #1, LSL #16", "sub sp, sp, x16, UXTX", "block0:", "mov x3, sp",
      "stp x0, x1, [x3]", "movz w16, #34480", "movk w16, w16, #1, LSL #16", "add sp, sp, x16, UXTX",
      "ldp fp, lr, [sp], #16", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "mov %2, sp", "stp %0, %1, [%2]", "rets"] },
  { name := "i128_stack_store_load"
    source := "runtests/i128-load-store.clif (CI snapshot stock code)"
    clif := "function %i128_stack_store_load(i128) -> i8 {
    ss0 = explicit_slot 16

block0(v0: i128):
    v3 = stack_addr.i64 ss0
    store.i128 notrap v0, v3
    v4 = stack_addr.i64 ss0
    v1 = load.i128 notrap v4

    v2 = icmp.i128 eq v0, v1
    return v2
}"
    stock := ["stp fp, lr, [sp, #-16]!", "mov fp, sp", "sub sp, sp, #16", "block0:", "mov x7, sp",
      "stp x0, x1, [x7]", "mov x8, sp", "ldp x7, x8, [x8]", "subs xzr, x0, x7",
      "ccmp x1, x8, #nzcv, eq", "cset x0, eq", "add sp, sp, #16", "ldp fp, lr, [sp], #16", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "mov %6, sp", "stp %0, %1, [%6]", "mov %5, sp",
      "ldp %3, %4, [%5]", "subs xzr, %0, %3", "ccmp %1, %4, #nzcv, eq", "cset %2, eq",
      "rets %2=x0"] },
  { name := "i128_stack_store_load_inst_offset"
    source := "runtests/i128-load-store.clif (CI snapshot stock code)"
    clif := "function %i128_stack_store_load_inst_offset(i128) -> i8 {
    ss0 = explicit_slot 16
    ss1 = explicit_slot 16
    ss2 = explicit_slot 16

block0(v0: i128):
    v3 = stack_addr.i64 ss1+16
    store.i128 notrap v0, v3
    v4 = stack_addr.i64 ss1+16
    v1 = load.i128 notrap v4

    v2 = icmp.i128 eq v0, v1
    return v2
}"
    stock := ["stp fp, lr, [sp, #-16]!", "mov fp, sp", "sub sp, sp, #48", "block0:",
      "add x7, sp, #32", "stp x0, x1, [x7]", "add x8, sp, #32", "ldp x7, x8, [x8]",
      "subs xzr, x0, x7", "ccmp x1, x8, #nzcv, eq", "cset x0, eq", "add sp, sp, #48",
      "ldp fp, lr, [sp], #16", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "add %6, sp, #32", "stp %0, %1, [%6]",
      "add %5, sp, #32", "ldp %3, %4, [%5]", "subs xzr, %0, %3", "ccmp %1, %4, #nzcv, eq",
      "cset %2, eq", "rets %2=x0"] },
  { name := "i128_stack_store_load_big_offset"
    source := "runtests/i128-load-store.clif (CI snapshot stock code)"
    clif := "function %i128_stack_store_load_big_offset(i128) -> i8 {
    ss0 = explicit_slot 100000
    ss1 = explicit_slot 8

block0(v0: i128):
    v3 = stack_addr.i64 ss0
    store.i128 notrap v0, v3
    v4 = stack_addr.i64 ss0
    v1 = load.i128 notrap v4

    v2 = icmp.i128 eq v0, v1
    return v2
}"
    stock := ["stp fp, lr, [sp, #-16]!", "mov fp, sp", "movz w16, #34480",
      "movk w16, w16, #1, LSL #16", "sub sp, sp, x16, UXTX", "block0:", "mov x7, sp",
      "stp x0, x1, [x7]", "mov x8, sp", "ldp x7, x8, [x8]", "subs xzr, x0, x7",
      "ccmp x1, x8, #nzcv, eq", "cset x0, eq", "movz w16, #34480", "movk w16, w16, #1, LSL #16",
      "add sp, sp, x16, UXTX", "ldp fp, lr, [sp], #16", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "mov %6, sp", "stp %0, %1, [%6]", "mov %5, sp",
      "ldp %3, %4, [%5]", "subs xzr, %0, %3", "ccmp %1, %4, #nzcv, eq", "cset %2, eq",
      "rets %2=x0"] },
  { name := "i128_store_load", source := "runtests/i128-load-store.clif (CI snapshot stock code)"
    clif := "function %i128_store_load(i128) -> i8 {
    ss0 = explicit_slot 16

block0(v0: i128):
    v1 = stack_addr.i64 ss0
    store.i128 v0, v1
    v2 = load.i128 v1

    v3 = icmp.i128 eq v0, v2
    return v3
}"
    stock := ["stp fp, lr, [sp, #-16]!", "mov fp, sp", "sub sp, sp, #16", "block0:", "mov x6, sp",
      "stp x0, x1, [x6]", "ldp x6, x7, [x6]", "subs xzr, x0, x6", "ccmp x1, x7, #nzcv, eq",
      "cset x0, eq", "add sp, sp, #16", "ldp fp, lr, [sp], #16", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "mov %5, sp", "stp %0, %1, [%5]", "ldp %3, %4, [%5]",
      "subs xzr, %0, %3", "ccmp %1, %4, #nzcv, eq", "cset %2, eq", "rets %2=x0"] },
  { name := "i128_store_load_offset"
    source := "runtests/i128-load-store.clif (CI snapshot stock code)"
    clif := "function %i128_store_load_offset(i128) -> i8 {
    ss0 = explicit_slot 32

block0(v0: i128):
    v1 = stack_addr.i64 ss0
    store.i128 v0, v1+16
    v2 = load.i128 v1+16

    v3 = icmp.i128 eq v0, v2
    return v3
}"
    stock := ["stp fp, lr, [sp, #-16]!", "mov fp, sp", "sub sp, sp, #32", "block0:", "mov x6, sp",
      "stp x0, x1, [x6, #16]", "ldp x6, x7, [x6, #16]", "subs xzr, x0, x6",
      "ccmp x1, x7, #nzcv, eq", "cset x0, eq", "add sp, sp, #32", "ldp fp, lr, [sp], #16", "ret"]
    pinned := ["block0:", "args %0=x0 %1=x1", "mov %5, sp", "stp %0, %1, [%5, #16]",
      "ldp %3, %4, [%5, #16]", "subs xzr, %0, %3", "ccmp %1, %4, #nzcv, eq", "cset %2, eq",
      "rets %2=x0"] }]

/-- `lower128` lowers the shape, its instruction shape is stock's, and its exact VCode is the
pinned one. -/
def shapeOk (s : Shape) : Bool :=
  match function? s.clif with
  | none => false
  | some f => match lower128 f with
    | .ok r => leanShape r.code == stockShape s.stock && exact r == s.pinned
    | .error _ => false

/-! ## Functions without `i128` values (differential check against `Stock.lower`) -/

/-- `Stock.ComparisonCfg.Fixture.function` (`FV/Backend/Proof/StockComparisonWitness.lean`) and
other `i128`-free functions: a loop with block arguments, a call, memory, stack parameters, an
`sret` signature, `br_table`, `select`, extensions, and an error (an `i64` `isplit`). -/
def i128Free : List String := [
  "function %comparison_leaves(i64, i64) -> i64 {
block0(v0: i64, v1: i64):
    v2 = icmp slt v0, v1
    brif v2, block1, block2
block1:
    return v0
block2:
    trap user3
}",
  "function %sum(i64) -> i64 {
block0(v0: i64):
    v1 = iconst.i64 0
    v6 = iconst.i64 -1
    jump block1(v0, v1)
block1(v2: i64, v3: i64):
    v4 = iadd v3, v2
    v5 = iadd v2, v6
    brif v5, block1(v5, v4), block2
block2:
    return v4
}",
  "function %call(i64, i64) -> i64 {
    fn0 = %g(i64, i64) -> i64
block0(v0: i64, v1: i64):
    v2 = call fn0(v1, v0)
    v3 = iadd v2, v0
    return v3
}",
  "function %mem(i64, i32) -> i32 {
block0(v0: i64, v1: i32):
    store v1, v0+8
    v2 = load.i32 v0+4
    v3 = iadd v2, v1
    return v3
}",
  "function %many(i64, i64, i64, i64, i64, i64, i64, i64, i64, i32) -> i64 {
block0(v0: i64, v1: i64, v2: i64, v3: i64, v4: i64, v5: i64, v6: i64, v7: i64, v8: i64, v9: i32):
    v10 = sextend.i64 v9
    v11 = iadd v8, v10
    return v11
}",
  "function %sret(i64 sret, i64) {
block0(v0: i64, v1: i64):
    store v1, v0
    return
}",
  "function %table(i32) -> i32 {
block0(v0: i32):
    br_table v0, block1, [block2, block3]
block1:
    v1 = iconst.i32 1
    return v1
block2:
    v2 = iconst.i32 2
    return v2
block3:
    return v0
}",
  "function %sel(i64, i64, i8) -> i64 {
block0(v0: i64, v1: i64, v2: i8):
    v3 = uextend.i32 v2
    v4 = select v3, v0, v1
    v5 = ireduce.i16 v4
    v6 = sextend.i64 v5
    return v6
}",
  "function %isplit64(i64) -> i32 {
block0(v0: i64):
    v1, v2 = isplit v0
    return v2
}"]

/-! ## Rejections -/

/-- `i128` instructions outside the foundation (`umul_overflow`, which has no `$I128` rule, a
big-endian load, which `little_or_native_endian` does not match, and others), and the `isplit`
of a widening `imul` (its `lower.isle` rule needs the extern `value_is_unused`, which
`externCtor128` does not model): `lower128` fails on each. -/
def outside : List String := [
  "function %umul_overflow(i128, i128) -> i128, i8 {
block0(v0: i128, v1: i128):
    v2, v3 = umul_overflow v0, v1
    return v2, v3
}",
  "function %umul_high_i64_isplit(i64, i64) -> i64 {
block0(v0: i64, v1: i64):
    v2 = uextend.i128 v0
    v3 = uextend.i128 v1
    v4 = imul v2, v3
    v5, v6 = isplit v4
    return v6
}",
  "function %udiv(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v2 = udiv v0, v1
    return v2
}",
  "function %call(i128) -> i128 {
    fn0 = %g(i128) -> i128
block0(v0: i128):
    v1 = call fn0(v0)
    return v1
}",
  "function %load_big(i64) -> i128 {
block0(v0: i64):
    v1 = load.i128 big v0
    return v1
}"]

def rejected (src : String) : Bool :=
  match function? src with
  | some f => (lower128 f).toOption.isNone
  | none => false

/-! ## Checks -/

#guard shapes.length == 16
#guard shapes.all shapeOk
#guard extras.all shapeOk
#guard shifts.length == 13
#guard shifts.all shapeOk
#guard compares.length == 15
#guard compares.all shapeOk
#guard selects.length == 14
#guard selects.all shapeOk
#guard ariths.length == 10
#guard ariths.all shapeOk
#guard bitops.length == 16
#guard bitops.all shapeOk
#guard minmaxes.length == 4
#guard minmaxes.all shapeOk
#guard overflows.length == 4
#guard overflows.all shapeOk
#guard mems.length == 18
#guard mems.all shapeOk
#guard i128Free.all fun s => (function? s).any fun f => !has128 f && agrees f
#guard outside.all rejected

/-! ## Filetest sweep (`main`) -/

/-- The expected VCode lines of each function of a `precise-output` filetest, by name. -/
def expectedVCode (text : String) : List (String × List String) := Id.run do
  let mut out : Array (String × List String) := #[]
  let mut name : Option String := none
  let mut cur : Option (Array String) := none
  for line in text.splitOn "\n" do
    let t := trim line
    if t.startsWith "; VCode:" then
      cur := some #[]
    else if t.startsWith ";" && !t.startsWith "; Disassembled:" then
      if let some ls := cur then cur := some (ls.push (trim (String.ofList (t.toList.drop 1))))
    else
      if let (some n, some ls) := (name, cur) then
        out := out.push (n, ls.toList)
        name := none
      cur := none
      if t.startsWith "function " then
        let rest := (t.toList.drop 9).dropWhile (· == '%')
        name := some (String.ofList (rest.takeWhile fun c => c != '(' && c != ' '))
  return out.toList

partial def clifFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let es ← p.readDir
    let mut out := #[]
    for e in es.qsort (fun a b => a.fileName < b.fileName) do
      out := out ++ (← clifFiles e.path)
    return out
  else if p.extension == some "clif" then return #[p]
  else return #[]

/-- Print each shape: whether it lowers, its shape against stock's, its exact VCode. -/
def printShapes : IO Unit := do
  for s in shapes ++ extras ++ shifts ++ compares ++ selects ++ ariths ++ bitops ++ minmaxes ++
      overflows ++ mems do
    match function? s.clif with
    | none => IO.println s!"{s.name}: parse error"
    | some f => match lower128 f with
      | .error e => IO.println s!"{s.name}: error {e}"
      | .ok r =>
        let same := leanShape r.code == stockShape s.stock
        IO.println s!"{s.name} ({s.source}): stock shape {same}, pinned {exact r == s.pinned}"
        IO.println s!"  lean:  {leanShape r.code}\n  stock: {stockShape s.stock}"
        for l in exact r do IO.println s!"    {l}"
  for src in i128Free do
    match function? src with
    | none => IO.println "i128-free: parse error"
    | some f =>
      let detail := match lower128 f, Stock.lower f with
        | .ok _, .ok _ => "both lower"
        | .error a, .error b => s!"both fail: {a} / {b}"
        | .ok _, .error b => s!"only lower128 lowers; Stock.lower: {b}"
        | .error a, .ok _ => s!"only Stock.lower lowers; lower128: {a}"
      IO.println s!"i128-free {f.name}: has128 {has128 f}, agrees {agrees f} ({detail})"
  for src in outside do
    match function? src with
    | none => IO.println "outside: parse error"
    | some f => IO.println s!"outside {f.name}: {match lower128 f with
      | .ok _ => "LOWERED" | .error e => s!"rejected: {e}"}"

def main (args : List String) : IO UInt32 := do
  if args.contains "--shapes" then
    printShapes
    return 0
  let print := args.contains "--print"
  let roots := args.filter (· != "--print")
  let roots := if roots.isEmpty then ["third_party/wasmtime/cranelift/filetests/filetests/isa/aarch64"]
    else roots
  let mut free := 0
  let mut freeSame := 0
  let mut wide := 0
  let mut wideLowered := 0
  let mut wideMatch := 0
  let mut wideNoExpect := 0
  let mut wideCsdb := 0
  let mut bad := 0
  for root in roots do
    for path in ← clifFiles root do
      if print then
        IO.println s!"file {path}"
        (← IO.getStdout).flush
      let text ← IO.FS.readFile path
      let expect := if hasSub text "precise-output" && hasSub text "target aarch64" then
        expectedVCode text else []
      let mut seen : List String := []
      for (name, func) in parse text do
        -- the `k`-th function named `name` has the `k`-th expectation of that name (a file
        -- may repeat a name, e.g. `isa/aarch64/condops.clif` `%f`)
        let k := seen.count name
        seen := name :: seen
        let .ok f := func | continue
        if has128 f then
          wide := wide + 1
          let guard := f.blocks.any fun b => b.body.any (·.inst matches .selectSpectreGuard ..)
          if hasSub text "use_csdb" && guard then
            wideCsdb := wideCsdb + 1
            IO.println s!"use_csdb {path} %{name}: not compared (lowered without use_csdb)"
            continue
          match lower128 f with
          | .error e => if print then IO.println s!"reject {path} %{name}: {e}"
          | .ok r =>
            wideLowered := wideLowered + 1
            match ((expect.filter (·.1 == name))[k]?).map (·.2) with
            | none =>
              wideNoExpect := wideNoExpect + 1
              IO.println s!"lowered {path} %{name}: no expected VCode"
            | some lines =>
              if leanShape r.code == stockShape lines then
                wideMatch := wideMatch + 1
                IO.println s!"match {path} %{name}"
              else
                IO.println s!"differ {path} %{name}\n  lean:  {leanShape r.code}\n  stock: {stockShape lines}"
            if print then
              for l in exact r do IO.println s!"    {l}"
        else
          free := free + 1
          if agrees f then freeSame := freeSame + 1
          else
            bad := bad + 1
            IO.println s!"DIFFERENTIAL FAILURE {path} %{name}"
  IO.println s!"i128-free functions: {free}, lower128 = Stock.lower on {freeSame}"
  IO.println s!"i128 functions: {wide}, lowered {wideLowered}, stock shape {wideMatch}, \
    no expected VCode {wideNoExpect}, use_csdb select_spectre_guard {wideCsdb}"
  return if bad == 0 then 0 else 1

end Backend.Stock.I128Test

def main (args : List String) : IO UInt32 := Backend.Stock.I128Test.main args

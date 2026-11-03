import FV.Backend.Lowering.StockI128

/-! Probes for the native `i128` stock lowering `Backend.Stock.lower128` (not wired, no proof).

* The `#guard`s below check that `lower128` lowers the 16 foundation shapes, that the
  instructions it selects have the shape of stock Cranelift's (the expected VCode of the
  filetests, with registers abstracted, and without regalloc moves and the frame), and they pin
  its exact pre-allocation VCode.
* Further `#guard`s check that `lower128` gives the result of `Stock.lower` on functions without
  `i128` values, and that it rejects `i128` instructions outside the foundation.
* `main` does the two checks over Cranelift's filetests (the build does not run it):
  `lake env lean --run FVTest/Backend/Lowering/StockI128Test.lean [--print] [PATH...]`,
  with the default path `third_party/wasmtime/cranelift/filetests/filetests/isa/aarch64`
  (`--print`: also the exact VCode and the rejection reasons). With `--shapes`, it prints the
  shapes and the results of the checks above instead.
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
  | .asr => "asr" | .lsr => "lsr" | .lsl => "lsl"
  | op => s!"?{lastName op}"

def amode : AMode → String
  | .fpOffset off => s!"[fp, #{off}]"
  | .spOffset off => s!"[sp, #{off}]"
  | m => s!"?{(repr m).pretty}"

/-- One instruction in the syntax of Cranelift's VCode printing (`isa/aarch64/inst/mod.rs`),
for the instructions of the foundation; `?` and the representation for every other one. `args`
and `rets` show their (vreg, physical register) pairs. -/
def inst : MInst → String
  | .args ps => " ".intercalate ("args" :: ps.map fun (a, p) => s!"{reg a}={reg p}")
  | .rets ps => " ".intercalate ("rets" :: ps.map fun (a, p) => s!"{reg a}={reg p}")
  | .load _ rd m _ => s!"ldr {reg rd}, {amode m}"
  | .extend rd rn signed fromBits _ =>
    if !signed && fromBits == 32 then s!"mov {reg rd}, {reg rn}"
    else
      let w := match fromBits with | 8 => "b" | 16 => "h" | _ => "w"
      s!"{if signed then "sxt" else "uxt"}{w} {reg rd}, {reg rn}"
  | .movWide .movZ rd imm _ =>
    if imm.shift == 0 then s!"movz {reg rd}, #{imm.bits}"
    else s!"movz {reg rd}, #{imm.bits}, LSL #{imm.shift}"
  | .aluRRR op _ rd rn rm => s!"{aluName op} {reg rd}, {reg rn}, {reg rm}"
  | .aluRRImmShift op _ rd rn imm => s!"{aluName op} {reg rd}, {reg rn}, #{imm}"
  | .cset rd c => s!"cset {reg rd}, {lastName c}"
  | .condBr t e (.notZero r _) => s!"cbnz {reg r}, label{t} ; b label{e}"
  | .condBr t e (.zero r _) => s!"cbz {reg r}, label{t} ; b label{e}"
  | .jump l => s!"b label{l}"
  | .mov _ rd rm => s!"mov {reg rd}, {reg rm}"
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

def isRegTok (t : String) : Bool :=
  t == "fp" || t == "sp" || t == "xzr" || t == "wzr" ||
    (t.length > 1 && (t.startsWith "x" || t.startsWith "w" || t.startsWith "%") &&
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

/-- The instruction shape of stock's expected VCode (after allocation): no frame setup, no
`ret`, no 64-bit register moves; registers abstracted. -/
def stockShape (lines : List String) : List String :=
  ((lines.map trim).filter fun l =>
    !l.isEmpty && l != "ret" && l != "mov fp, sp" && !hasSub l "fp, lr" && !isMove64 l)
    |>.map abstractLine

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

/-- `i128` instructions outside the foundation: `lower128` fails on each. -/
def outside : List String := [
  "function %add(i128, i128) -> i128 {
block0(v0: i128, v1: i128):
    v2 = iadd v0, v1
    return v2
}",
  "function %cmp(i128, i128) -> i8 {
block0(v0: i128, v1: i128):
    v2 = icmp eq v0, v1
    return v2
}",
  "function %sel(i128, i64, i64) -> i64 {
block0(v0: i128, v1: i64, v2: i64):
    v3 = select v0, v1, v2
    return v3
}",
  "function %call(i128) -> i128 {
    fn0 = %g(i128) -> i128
block0(v0: i128):
    v1 = call fn0(v0)
    return v1
}",
  "function %load(i64) -> i128 {
block0(v0: i64):
    v1 = load.i128 v0
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
  for s in shapes ++ extras do
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
  let mut bad := 0
  for root in roots do
    for path in ← clifFiles root do
      if print then
        IO.println s!"file {path}"
        (← IO.getStdout).flush
      let text ← IO.FS.readFile path
      let expect := if hasSub text "precise-output" && hasSub text "target aarch64" then
        expectedVCode text else []
      for (name, func) in parse text do
        let .ok f := func | continue
        if has128 f then
          wide := wide + 1
          match lower128 f with
          | .error e => if print then IO.println s!"reject {path} %{name}: {e}"
          | .ok r =>
            wideLowered := wideLowered + 1
            match expect.lookup name with
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
    no expected VCode {wideNoExpect}"
  return if bad == 0 then 0 else 1

end Backend.Stock.I128Test

def main (args : List String) : IO UInt32 := Backend.Stock.I128Test.main args

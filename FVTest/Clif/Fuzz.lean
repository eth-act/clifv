import FV.Clif.Run
import FV.Clif.Print
import FV.Clif.Parse
import FV.Compile.Subset
import FVTest.Clif.OracleJson

/-!
# `clif-fuzz`: random CLIF differential tests of `Clif.run` (T5, #41)

```
clif-fuzz gen [--seed N] [--per K] [--runs M] [--mix N] [--per-file F] --out-dir DIR
clif-fuzz compare [--interp-dir DIR] [--native-dir DIR] [--report OUT.tsv] [-v] FILE.clif...
clif-fuzz coverage --universe GEN_DIR [--native-list LIST] FILE.clif...
```
`scripts/clif-fuzz.sh` runs the whole pipeline.

`gen` writes runtest files `DIR/fuzzN_XXX.clif` (`F` targets per file, default 150): for every
target (an opcode at a type: every opcode of subset E at `i8`–`i64` — arithmetic, bitwise,
shifts, division, comparisons, select, bmask, extensions, loads/stores, stack addresses,
atomics, fence, calls, `call_indirect`/`func_addr`, `symbol_value`, constants, `br_table`,
`trap`, `brif` — and every float operation at `f32`/`f64`, see `allTargets`), `K` small
functions (default 2) applying it to the parameters (straight-line or through a `brif` diamond
on an integer parameter), plus `N` random mixed functions (default 40) chaining pure operations
of all types and folding the results into an `i64` (floats through `bitcast`, so NaN payloads
are observed); each function gets `M` run lines (default 8) with edge-biased arguments
(integer bounds, IEEE specials, NaNs with payloads, signalling NaNs, subnormals, ties,
conversion bounds; equal operands a third of the time). The expectation of a run line is
`Clif.run`'s result (`== results`); a trapping run is a `; print:` line. The program is printed
and parsed back before it runs, so the expectations are those of the text.

`compare` reruns every run line with `Clif.run` and compares it with the Cranelift interpreter
(`clif-oracle interp` JSON in `DIR/<file>.json`; NaN results agree up to payload, as in
`clif-filetest`) and with the native aarch64 run (`clif-native` JSON; bit-exact, NaN payloads
included, since `Clif.run`'s NaNs are AArch64's). Interpreter-only differences that are not
disagreements: NaN payloads exposed by a float-to-integer `bitcast` when the native run agrees
bit-exactly (`nan-agree`; the interpreter uses the x86 host's NaNs), and the documented
`srem MIN, -1` deviation (`known-deviation`, `docs/contracts/clif.md`). It prints per-key counts
(`instKey`) and every disagreement, and exits 1 on a disagreement or a missing oracle record.

`coverage` lists, per key of the universe (the keys of the generated files), the number of
runtest files with a function that has run lines and contains the key (`interp_files`: every
such file is compared with the interpreter by `scripts/clif-filetests.sh`), and the same
restricted to the files of `--native-list` (`native_files`: the files
`scripts/aarch64-native-filetests.sh` runs natively). Static: a key in a function with run
lines, not necessarily executed.

Not generated: `tls_value` (needs a TLS runtime in the native harness), and the S-only
operations outside E and the float subset (i128, overflow/carry families, `bitselect`,
`iabs`, …).
-/

open Clif

namespace ClifFuzz

/-! ## Keys -/

/-- The coverage key of an instruction: opcode, condition code, controlling type, and for
conversions the operand type (`uextend.i64<i8`, `fcvt_to_sint.i32<f64`). -/
def instKey (tys : ValueId → Option Ty) : Inst → String
  | .iconst ty _ => if ty.isFloat then s!"{ty.name}const" else s!"iconst.{ty.name}"
  | .unary op ty _ => s!"{Print.UnaryOp.name op}.{ty.name}"
  | .binary op ty _ _ => s!"{Print.BinaryOp.name op}.{ty.name}"
  | .div op ty _ _ => s!"{Print.DivOp.name op}.{ty.name}"
  | .overflow op ty _ _ => s!"{Print.OverflowOp.name op}.{ty.name}"
  | .carry op ty _ _ _ => s!"{Print.CarryOp.name op}.{ty.name}"
  | .uaddOverflowTrap ty _ _ _ => s!"uadd_overflow_trap.{ty.name}"
  | .icmp cc ty _ _ => s!"icmp.{cc.name}.{ty.name}"
  | .select ty _ _ _ => s!"select.{ty.name}"
  | .selectSpectreGuard ty _ _ _ => s!"select_spectre_guard.{ty.name}"
  | .bitselect ty _ _ _ => s!"bitselect.{ty.name}"
  | .bmask ty x => s!"bmask.{ty.name}<{src x}"
  | .extend .uextend ty x => s!"uextend.{ty.name}<{src x}"
  | .extend .sextend ty x => s!"sextend.{ty.name}<{src x}"
  | .ireduce ty x => s!"ireduce.{ty.name}<{src x}"
  | .iconcat ty _ _ => s!"iconcat.{ty.name}"
  | .isplit ty _ => s!"isplit.{ty.name}"
  | .load op ty _ _ _ => s!"{Print.LoadOp.name op}.{ty.name}"
  | .store op ty _ _ _ _ => s!"{Print.StoreOp.name op}.{ty.name}"
  | .stackAddr ty _ _ => s!"stack_addr.{ty.name}"
  | .call _ _ => "call"
  | .callIndirect _ _ _ => "call_indirect"
  | .funcAddr ty _ => s!"func_addr.{ty.name}"
  | .atomicRmw op ty _ _ _ => s!"atomic_rmw.{op.name}.{ty.name}"
  | .atomicCas ty _ _ _ _ => s!"atomic_cas.{ty.name}"
  | .atomicLoad ty _ _ => s!"atomic_load.{ty.name}"
  | .atomicStore ty _ _ _ => s!"atomic_store.{ty.name}"
  | .fence => "fence"
  | .bitcast ty _ x => s!"bitcast.{ty.name}<{src x}"
  | .trapz c _ => s!"trapz.{src c}"
  | .trapnz c _ => s!"trapnz.{src c}"
  | .nop => "nop"
  | .symbolValue ty _ => s!"symbol_value.{ty.name}"
  | .tlsValue ty _ => s!"tls_value.{ty.name}"
  | .float (.fcmp cc) ty _ => s!"fcmp.{cc.name}.{ty.name}"
  | .float op ty args =>
    if op.ctrlIsOperand then s!"{op.name}.{ty.name}"
    else s!"{op.name}.{ty.name}<{src (args.headD 0)}"
where
  src (x : ValueId) : String := ((tys x).map Ty.name).getD "?"

def termKey (tys : ValueId → Option Ty) : Terminator → String
  | .jump _ => "jump"
  | .brif c _ _ => s!"brif.{((tys c).map Ty.name).getD "?"}"
  | .brTable .. => "br_table"
  | .ret _ => "return"
  | .returnCall .. => "return_call"
  | .trap _ => "trap"
  | .tryCall .. => "try_call"
  | .tryCallIndirect .. => "try_call_indirect"

/-- The keys of a function (with multiplicity removed), each tagged with whether the
instruction is in subset E (`Compile.instE`/`termE`). -/
def funcKeys (f : Function) : List (String × Bool) :=
  let tyMap := f.valueTypes
  let tys : ValueId → Option Ty := fun x => tyMap.lookup x
  let ks := f.blocks.flatMap fun b =>
    (b.body.map fun s => (instKey tys s.inst, Compile.instE s.inst)) ++
      [(termKey tys b.term, Compile.termE b.term)]
  ks.foldl (fun acc k => if acc.any (·.1 == k.1) then acc else acc ++ [k]) []

/-! ## Generator state -/

structure G where
  gen : StdGen
  next : ValueId := 0
  body : Array Stmt := #[]
  slots : Array (SlotId × StackSlot) := #[]
  externs : Array (FnRef × ExtFunc) := #[]
  sigDecls : Array (Nat × Signature) := #[]
  globals : Array (Nat × GlobalValue) := #[]
  /-- Program-level additions of the function being generated (callees, data objects). -/
  extraFuncs : Array Function := #[]
  data : Array DataObject := #[]

abbrev GM := StateM G

def rand (n : Nat) : GM Nat := do
  if n ≤ 1 then return 0
  let g ← get
  let (k, gen) := randNat g.gen 0 (n - 1)
  set { g with gen }
  return k

def coin : GM Bool := do return (← rand 2) == 1

def pick {α} [Inhabited α] (xs : Array α) : GM α := do return xs[← rand xs.size]!

def fresh : GM ValueId := modifyGet fun g => (g.next, { g with next := g.next + 1 })

def emit (inst : Inst) : GM ValueId := do
  let v ← fresh
  modify fun g => { g with body := g.body.push { results := [v], inst } }
  return v

def emitN (inst : Inst) (n : Nat) : GM (List ValueId) := do
  let mut vs := []
  for _ in [0:n] do vs := vs ++ [← fresh]
  modify fun g => { g with body := g.body.push { results := vs, inst } }
  return vs

def emit0 (inst : Inst) : GM Unit :=
  modify fun g => { g with body := g.body.push { inst } }

def takeBody : GM (List Stmt) := modifyGet fun g => (g.body.toList, { g with body := #[] })

def intTys : Array Ty := #[.i8, .i16, .i32, .i64]
def fTys : Array Ty := #[.f32, .f64]

/-! ## Values -/

def interestingInt (w : Nat) : GM Nat := do
  let k ← rand 24
  let m := 2 ^ w
  let j : Nat ← rand w
  let small : Int := ((← rand 512 : Nat) : Int) - 256
  let mid : Int := ((← rand 65536 : Nat) : Int) - 32768
  let any : Nat ← rand m
  let v : Int := match k with
    | 0 => 0 | 1 => 1 | 2 => -1 | 3 => 2 | 4 => -2
    | 5 => 2 ^ (w - 1) - 1 | 6 => -(2 ^ (w - 1)) | 7 => 2 ^ (w - 1)
    | 8 => j | 9 => 2 ^ j
    | 10 => 2 ^ j - 1 | 11 => -(2 ^ j)
    | 12 | 13 => small
    | 14 | 15 => mid
    | _ => any
  return (v % (m : Int)).toNat

/-- Bits of `s · 2^e · (1 + f / 2^F)` style fields. -/
def fbits (E F s e f : Nat) : Nat := (s <<< (E + F)) ||| ((e % 2 ^ E) <<< F) ||| (f % 2 ^ F)

def fields (ty : Ty) : Nat × Nat := if ty == .f64 then (11, 52) else (8, 23)

/-- Edge-biased float bits of type `ty`. -/
def interestingFloat (ty : Ty) : GM Nat := do
  let (E, F) := fields ty
  let bias := 2 ^ (E - 1) - 1
  let emax := 2 ^ E - 1
  let s ← rand 2
  let k ← rand 30
  match k with
  | 0 => return fbits E F s 0 0                                   -- ±0
  | 1 => return fbits E F s emax 0                                -- ±∞
  | 2 => return fbits E F s emax (2 ^ (F - 1))                    -- default-payload qNaN
  | 3 => return fbits E F s emax (2 ^ (F - 1) + 1 + (← rand (2 ^ (F - 1) - 1)))  -- qNaN payload
  | 4 => return fbits E F s emax (1 + (← rand (2 ^ (F - 1) - 1))) -- sNaN
  | 5 => return fbits E F s 0 (1 + (← rand (2 ^ F - 1)))          -- subnormal
  | 6 => return fbits E F s 0 1                                   -- min subnormal
  | 7 => return fbits E F s 1 0                                   -- min normal
  | 8 => return fbits E F s (emax - 1) (2 ^ F - 1)                -- max finite
  | 9 => return fbits E F s bias 0                                -- ±1
  | 10 =>                                                         -- ties: n + 1/2
    let e := bias + 1 + (← rand 8)
    return fbits E F s e ((← rand (2 ^ (e - bias - 1))) * 2 ^ (F - (e - bias)) + 2 ^ (F - (e - bias) - 1))
  | 11 | 12 =>                                                    -- integer-conversion bounds
    let p ← pick #[7, 8, 15, 16, 31, 32, 63, 64]
    let x := fbits E F s (bias + p) 0
    return match ← rand 3 with | 0 => x | 1 => x + 1 | _ => x - 1
  | 13 | 14 =>                                                    -- small integers
    let e := bias + (← rand 12)
    let sh := F - (e - bias)
    return fbits E F s e (((← rand (2 ^ (e - bias))) <<< sh))
  | 15 => return (← rand (2 ^ (1 + E + F)))                      -- any bits
  | 16 | 17 =>                                                    -- near overflow/underflow
    let e ← if ← coin then pure (emax - 1 - (← rand 3)) else pure (1 + (← rand 3))
    return fbits E F s e (← rand (2 ^ F))
  | _ =>                                                          -- moderate magnitudes
    return fbits E F s (bias - 30 + (← rand 100)) (← rand (2 ^ F))

def randVal (ty : Ty) : GM Val := do
  if ty.isFloat then return ⟨ty, BitVec.ofNat ty.width (← interestingFloat ty)⟩
  return ⟨ty, BitVec.ofNat ty.width (← interestingInt ty.width)⟩

/-- Arguments for `tys`; a third of the time an argument copies an earlier one of the same type
(equal operands: `icmp eq`, `atomic_cas` hits, `x - x`). -/
def genArgs (tys : List Ty) : GM (List Val) := do
  let mut out : Array Val := #[]
  for t in tys do
    let same := out.filter (·.ty == t)
    let r ← rand 3
    match same[← rand same.size]? with
    | some v => if r == 0 then out := out.push v else out := out.push (← randVal t)
    | none => out := out.push (← randVal t)
  return out.toList

def constOf (ty : Ty) : GM ValueId := do
  let v ← randVal ty
  emit (.iconst ty (BitVec.ofNat ty.width v.toNat))

/-! ## Functions -/

def jumpTo (b : BlockId) (args : List ValueId) : Terminator := .jump { block := b, args }

/-- Start a new function: fresh value numbering, no body, slots or declarations. -/
def resetFn : GM Unit :=
  modify fun g => { g with next := 0, body := #[], slots := #[], externs := #[], sigDecls := #[], globals := #[] }

/-- A function `name(params) -> rets` whose body `core` maps the parameters to the results:
straight-line, or (`diamond`) behind a `brif` on an integer parameter (the other arm returns
constants). -/
def mkFunc (name : String) (params : List Ty) (rets : List Ty) (diamond : Bool)
    (core : List ValueId → GM (List ValueId)) : GM Function := do
  resetFn
  -- the diamond's condition: an integer parameter (added if there is none)
  let extra ← pick intTys
  let params := if diamond && !params.any Ty.isInt then params ++ [extra] else params
  let ps ← params.mapM fun t => do return ((← fresh), t)
  let pv := ps.map (·.1)
  let blocks ← if !diamond then do
      let rs ← core pv
      let body ← takeBody
      pure [{ id := 0, params := ps, body, term := .ret rs : Block }]
    else do
      let cs := ps.filter (·.2.isInt)
      let c := (cs[← rand cs.length]!).1
      let rs ← core pv
      let b1 ← takeBody
      let ks ← rets.mapM constOf
      let b2 ← takeBody
      let js ← rets.mapM fun t => do return ((← fresh), t)
      pure [{ id := 0, params := ps, term := .brif c { block := 1 } { block := 2 } : Block },
        { id := 1, body := b1, term := jumpTo 3 rs }, { id := 2, body := b2, term := jumpTo 3 ks },
        { id := 3, params := js, term := .ret (js.map (·.1)) }]
  let g ← get
  return { name, sig := { params := params.map fun t => { ty := t },
                          returns := rets.map fun t => { ty := t } },
           slots := g.slots.toList, externs := g.externs.toList, sigDecls := g.sigDecls.toList,
           globals := g.globals.toList, blocks }

/-! ## Targets -/

/-- A pure operation at fixed types: operand types, result type, instruction. -/
structure PureOp where
  args : List Ty
  ret : Ty
  inst : List ValueId → Inst

instance : Inhabited PureOp := ⟨{ args := [], ret := .i8, inst := fun _ => .nop }⟩

def a0 (xs : List ValueId) : ValueId := xs.headD 0
def a1 (xs : List ValueId) : ValueId := xs.getD 1 0
def a2 (xs : List ValueId) : ValueId := xs.getD 2 0

def unOps : List UnaryOp := [.ineg, .bnot, .clz, .ctz, .popcnt, .bitrev, .bswap]
def binOps : List BinaryOp :=
  [.iadd, .isub, .imul, .umulhi, .smulhi, .band, .bor, .bxor, .smin, .smax, .umin, .umax]
def shiftOps : List BinaryOp := [.ishl, .ushr, .sshr, .rotl, .rotr]
def divOps : List DivOp := [.udiv, .sdiv, .urem, .srem]
def fUnOps : List FOp := [.fneg, .fabs, .sqrt, .ceil, .floor, .trunc, .nearest]
def fBinOps : List FOp := [.fadd, .fsub, .fmul, .fdiv, .fmin, .fmax, .fcopysign]

/-- Every pure operation of subset E (integer) and of the float subset, at every valid type. -/
def pureOps : List PureOp :=
  intTys.toList.flatMap (fun t =>
    (unOps.filter (fun op => !(op == .bswap && t == .i8))).map (fun op =>
      ⟨[t], t, fun xs => .unary op t (a0 xs)⟩) ++
    binOps.map (fun op => ⟨[t, t], t, fun xs => .binary op t (a0 xs) (a1 xs)⟩) ++
    shiftOps.flatMap (fun op => intTys.toList.map fun s =>
      ⟨[t, s], t, fun xs => .binary op t (a0 xs) (a1 xs)⟩) ++
    divOps.map (fun op => ⟨[t, t], t, fun xs => .div op t (a0 xs) (a1 xs)⟩) ++
    IntCC.all.map (fun cc => ⟨[t, t], .i8, fun xs => .icmp cc t (a0 xs) (a1 xs)⟩) ++
    intTys.toList.map (fun c => ⟨[c, t, t], t, fun xs => .select t (a0 xs) (a1 xs) (a2 xs)⟩) ++
    intTys.toList.map (fun s => ⟨[s], t, fun xs => .bmask t (a0 xs)⟩) ++
    (intTys.toList.filter (·.width < t.width)).flatMap (fun s =>
      [⟨[s], t, fun xs => .extend .uextend t (a0 xs)⟩, ⟨[s], t, fun xs => .extend .sextend t (a0 xs)⟩]) ++
    (intTys.toList.filter (·.width > t.width)).map (fun s => ⟨[s], t, fun xs => .ireduce t (a0 xs)⟩)) ++
  fTys.toList.flatMap (fun f =>
    fUnOps.map (fun op => ⟨[f], f, fun xs => .float op f [a0 xs]⟩) ++
    fBinOps.map (fun op => ⟨[f, f], f, fun xs => .float op f [a0 xs, a1 xs]⟩) ++
    [⟨[f, f, f], f, fun xs => .float .fma f [a0 xs, a1 xs, a2 xs]⟩] ++
    FloatCC.all.map (fun cc => ⟨[f, f], .i8, fun xs => .float (.fcmp cc) f [a0 xs, a1 xs]⟩) ++
    intTys.toList.map (fun c => ⟨[c, f, f], f, fun xs => .select f (a0 xs) (a1 xs) (a2 xs)⟩) ++
    [.fcvtToUint, .fcvtToSint, .fcvtToUintSat, .fcvtToSintSat].flatMap (fun op =>
      [Ty.i32, .i64].map fun t => ⟨[f], t, fun xs => .float op t [a0 xs]⟩) ++
    [.fcvtFromUint, .fcvtFromSint].flatMap (fun op =>
      intTys.toList.map fun t => ⟨[t], f, fun xs => .float op f [a0 xs]⟩) ++
    [⟨[if f == .f32 then .i32 else .i64], f, fun xs => .bitcast f {} (a0 xs)⟩,
     ⟨[f], (if f == .f32 then .i32 else .i64), fun xs => .bitcast (if f == .f32 then .i32 else .i64) {} (a0 xs)⟩]) ++
  [⟨[.f32], .f64, fun xs => .float .fpromote .f64 [a0 xs]⟩,
   ⟨[.f64], .f32, fun xs => .float .fdemote .f32 [a0 xs]⟩]

/-- A stack slot of 32 bytes (16-byte aligned) and its address. -/
def slotAddr : GM ValueId := do
  let n := (← get).slots.size
  modify fun g => { g with slots := g.slots.push (n, { size := 32, align := some 16 }) }
  emit (.stackAddr .i64 n 0)

def memFlags (aligned : Bool) : GM MemFlags := do
  match ← rand 3 with
  | 0 => return {}
  | 1 => return { trapCode := none }
  | _ => return { trapCode := none, aligned }

def loadOps (t : Ty) : List (LoadOp × Nat) :=
  [(.load, t.bytes)] ++
  (if t.isInt && t.width > 8 then [(.uload8, 1), (.sload8, 1)] else []) ++
  (if t.isInt && t.width > 16 then [(.uload16, 2), (.sload16, 2)] else []) ++
  (if t.isInt && t.width > 32 then [(.uload32, 4), (.sload32, 4)] else [])

def storeOps (t : Ty) : List (StoreOp × Nat) :=
  [(.store, t.bytes)] ++
  (if t.isInt && t.width > 8 then [(.istore8, 1)] else []) ++
  (if t.isInt && t.width > 16 then [(.istore16, 2)] else []) ++
  (if t.isInt && t.width > 32 then [(.istore32, 4)] else [])

/-- A generator of one program (the target function last): name ↦ program functions, data. -/
abbrev Target := String → GM (List Function × List DataObject)

def single (f : String → GM Function) : Target := fun name => do
  modify fun g => { g with extraFuncs := #[], data := #[] }
  let fn ← f name
  let g ← get
  return (g.extraFuncs.toList ++ [fn], g.data.toList)

def pureTarget (op : PureOp) : Target := single fun name => do
  mkFunc name op.args [op.ret] (← coin) fun xs => do return [← emit (op.inst xs)]

/-- Memory targets: loads (`load`/`uloadN`/`sloadN` at every offset of a 16-byte image
written by two `store.i64`), stores (`store`/`istoreN` into it, read back by two `load.i64`). -/
def memTargets : List Target :=
  (intTys.toList ++ fTys.toList).flatMap fun t =>
    (loadOps t).map (fun (op, bytes) => single fun name => do
      mkFunc name [.i64, .i64] [t] (← coin) fun xs => do
        let p ← slotAddr
        emit0 (.store .store .i64 (← memFlags true) (a0 xs) p 0)
        emit0 (.store .store .i64 (← memFlags true) (a1 xs) p 8)
        let off ← rand (16 - bytes + 1)
        return [← emit (.load op t (← memFlags (off % bytes == 0)) p off)]) ++
    (storeOps t).map (fun (op, bytes) => single fun name => do
      mkFunc name [t, .i64] [.i64] (← coin) fun xs => do
        let p ← slotAddr
        emit0 (.store .store .i64 {} (a1 xs) p 0)
        emit0 (.store .store .i64 {} (a1 xs) p 8)
        let off ← rand (16 - bytes + 1)
        emit0 (.store op t (← memFlags (off % bytes == 0)) (a0 xs) p off)
        if ← coin then emit0 .fence
        let lo ← emit (.load .load .i64 {} p 0)
        let hi ← emit (.load .load .i64 {} p 8)
        let one ← emit (.iconst .i64 1)
        let hi' ← emit (.binary .rotl .i64 hi one)
        return [← emit (.binary .bxor .i64 lo hi')])

/-- Atomics on a stack slot (single-threaded): `atomic_rmw` (every op), `atomic_cas`,
`atomic_load`, `atomic_store`; results: the old value and the memory afterwards. -/
def atomicTargets : List Target :=
  intTys.toList.flatMap fun t =>
    (AtomicRmwOp.all.map fun op => single fun name => do
      mkFunc name [t, t] [t, t] (← coin) fun xs => do
        let p ← slotAddr
        emit0 (.store .store t {} (a0 xs) p 0)
        let old ← emit (.atomicRmw op t {} p (a1 xs))
        return [old, ← emit (.load .load t {} p 0)]) ++
    [single fun name => do mkFunc name [t, t, t] [t, t] (← coin) fun xs => do
       let p ← slotAddr
       emit0 (.store .store t {} (a0 xs) p 0)
       let old ← emit (.atomicCas t {} p (a1 xs) (a2 xs))
       return [old, ← emit (.load .load t {} p 0)],
     single fun name => do mkFunc name [t] [t] (← coin) fun xs => do
       let p ← slotAddr
       emit0 (.store .store t {} (a0 xs) p 0)
       if ← coin then emit0 .fence
       return [← emit (.atomicLoad t {} p)],
     single fun name => do mkFunc name [t, t] [t] (← coin) fun xs => do
       let p ← slotAddr
       emit0 (.store .store t {} (a0 xs) p 0)
       emit0 (.atomicStore t {} (a1 xs) p)
       return [← emit (.load .load t {} p 0)]]

/-- A callee `%name_callee(t, u) -> t` (a random pure binary computation). -/
def callee (name : String) (t u : Ty) : GM Function := do
  let saved ← get
  let f ← mkFunc name [t, u] [t] false fun xs => do
    let r ← if t.isFloat then
        if u == t then emit (.float .fadd t [a0 xs, a1 xs]) else emit (.float .fneg t [a0 xs])
      else if u == t then emit (.binary .bxor t (a0 xs) (a1 xs))
      else emit (.unary .bnot t (a0 xs))
    return [r]
  set { saved with gen := (← get).gen }
  return f

/-- `call`, `call_indirect` through `func_addr.i64`, with integer and float arguments. -/
def callTargets : List Target :=
  (intTys.toList ++ fTys.toList).flatMap fun t =>
    [false, true].map fun indirect => fun name => do
      modify fun g => { g with extraFuncs := #[], data := #[] }
      let u ← pick (intTys ++ fTys)
      let cname := s!"{name}_callee"
      let cf ← callee cname t u
      let sig : Signature := { params := [{ ty := t }, { ty := u }], returns := [{ ty := t }] }
      let fn ← mkFunc name [t, u] [t] (← coin) fun xs => do
        modify fun g => { g with externs := g.externs.push (0, { name := cname, sig }) }
        if indirect then
          modify fun g => { g with sigDecls := g.sigDecls.push (0, sig) }
          let fa ← emit (.funcAddr .i64 0)
          return [← emit (.callIndirect 0 fa [a0 xs, a1 xs])]
        else return [← emit (.call 0 [a0 xs, a1 xs])]
      -- `Clif.run` registers function symbols (for `func_addr`) only in a program with data
      -- objects (`Program.initMem`); without one, `func_addr` is stuck
      let ds : List DataObject :=
        if indirect then [{ name := s!"{name}_d", align := 8, items := List.replicate 8 (.byte 0) }]
        else []
      return ([cf, fn], ds)

/-- `symbol_value.i64` of a writable data object, loaded at a random offset. -/
def symbolTargets : List Target :=
  intTys.toList.map fun t => fun name => do
    let mut items := #[]
    for _ in [0:16] do items := items.push (DataItem.byte (BitVec.ofNat 8 (← rand 256)))
    let d : DataObject := { name := s!"{name}_data", align := 8, writable := true, items := items.toList }
    let fn ← mkFunc name [t] [t] (← coin) fun xs => do
      modify fun g => { g with globals := g.globals.push (0, .symbol d.name 0 false) }
      let p ← emit (.symbolValue .i64 0)
      let off ← rand (16 - t.bytes + 1)
      let v ← emit (.load .load t {} p off)
      if ← coin then emit0 .nop
      return [← emit (.binary .bxor t v (a0 xs))]
    return ([fn], [d])

/-- Constants (`iconst`, `f32const`, `f64const`): no parameters. -/
def constTargets : List Target :=
  (intTys.toList ++ fTys.toList).map fun t => single fun name =>
    mkFunc name [] [t] false fun _ => do return [← constOf t]

/-- `br_table` on an `i32` index, and an explicit `trap` (`user1`) behind a `brif`. -/
def ctlTargets : List Target :=
  [single fun name => do
     resetFn
     let x ← fresh
     let n := 2 + (← rand 4)
     let mut blocks : List Block := []
     for k in [0:n + 1] do
       let c ← fresh
       blocks := blocks ++ [{ id := k + 1, body := [{ results := [c], inst := .iconst .i64 (BitVec.ofNat 64 (100 + k)) }],
                              term := .ret [c] }]
     return { name, sig := { params := [{ ty := .i32 }], returns := [{ ty := .i64 }] },
              blocks := { id := 0, params := [(x, .i32)],
                          term := .brTable x { block := 1 } ((List.range n).map fun k => { block := k + 2 }) } :: blocks },
   single fun name => do
     resetFn
     let t ← pick intTys
     let x ← fresh
     return { name, sig := { params := [{ ty := t }], returns := [{ ty := t }] },
              blocks := [{ id := 0, params := [(x, t)], term := .brif x { block := 1 } { block := 2 } },
                         { id := 1, term := .ret [x] }, { id := 2, term := .trap (.user 1) }] }]

/-- A random mix of pure operations over a pool of values of every type, folded into an `i64`
(floats through `bitcast`, so NaN payloads are observed). -/
def mixTarget : Target := single fun name => do
  let nparams := 1 + (← rand 4)
  let mut ptys : List Ty := []
  for _ in [0:nparams] do ptys := ptys ++ [← pick (intTys ++ fTys)]
  let nops := 3 + (← rand 10)
  let mut chosen : Array PureOp := #[]
  for _ in [0:nops] do chosen := chosen.push (← pick pureOps.toArray)
  -- every operand type the chosen operations need is a parameter type
  for op in chosen do
    for t in op.args do
      if !ptys.contains t then ptys := ptys ++ [t]
  let chosen' := chosen
  mkFunc name ptys [.i64] (← coin) fun xs => do
    let mut pool : Array (ValueId × Ty) := (xs.zip ptys).toArray
    let mut made : Array (ValueId × Ty) := #[]
    for op in chosen' do
      let mut args := []
      for t in op.args do
        let cands := pool.filter (·.2 == t)
        args := args ++ [(← pick cands).1]
      let r ← emit (op.inst args)
      pool := pool.push (r, op.ret)
      made := made.push (r, op.ret)
    let mut acc ← emit (.iconst .i64 0)
    for (v, t) in made do
      let v ← if t == .f32 then emit (.bitcast .i32 {} v) else if t == .f64 then emit (.bitcast .i64 {} v) else pure v
      let w := if t == .f32 then 32 else if t == .f64 then 64 else t.width
      let v ← if w < 64 then emit (.extend .uextend .i64 v) else pure v
      let one ← emit (.iconst .i64 1)
      acc ← emit (.binary .rotl .i64 acc one)
      acc ← emit (.binary .bxor .i64 acc v)
    return [acc]

def allTargets : List Target :=
  pureOps.map pureTarget ++ memTargets ++ atomicTargets ++ callTargets ++ symbolTargets ++
    constTargets ++ ctlTargets

/-! ## Generation -/

def fuel : Nat := 1000000

structure GenStats where
  funcs : Nat := 0
  runs : Nat := 0
  traps : Nat := 0
  stuck : Nat := 0
  bad : Array String := #[]

/-- Generate one target's program, check it round-trips through the printer and parser, and
attach run lines computed by `Clif.run`. -/
def genOne (t : Target) (name : String) (runs : Nat) (st : GenStats) :
    GM (List Function × List DataObject × GenStats) := do
  let (fs, ds) ← t name
  let p0 : Program := { data := ds, funcs := fs }
  let p ← match Clif.parse (Clif.print p0) with
    | .ok p => pure p
    | .error e => return ([], [], { st with bad := st.bad.push s!"%{name}: reparse: {e}" })
  let some main := p.funcs.getLast? | return ([], [], st)
  let mut st := { st with funcs := st.funcs + 1 }
  let mut rcs : Array RunCommand := #[]
  let n := if main.sig.params.isEmpty then 1 else runs
  for _ in [0:n] do
    let args ← genArgs (main.sig.params.map (·.ty))
    match Clif.run {} p main.name args fuel with
    | .returned vs _ => rcs := rcs.push { func := main.name, args, expect := .eq vs }; st := { st with runs := st.runs + 1 }
    | .trapped _ => rcs := rcs.push { func := main.name, args, expect := .print }; st := { st with runs := st.runs + 1, traps := st.traps + 1 }
    | .stuck m => st := { st with stuck := st.stuck + 1, bad := if st.bad.size < 20 then st.bad.push s!"%{name}: stuck: {m}" else st.bad }
    | .outOfFuel => st := { st with stuck := st.stuck + 1 }
  let main' := { main with runs := rcs.toList }
  return (p.funcs.dropLast ++ [main'], p.data, st)

def sanitize (s : String) : String :=
  String.map (fun c => if c.isAlphanum then c else '_') s

end ClifFuzz

/-! ## Comparison -/

namespace ClifFuzz

open ClifFiletest

structure KeyCounts where
  runs : Nat := 0
  iAgree : Nat := 0
  iNan : Nat := 0
  iDis : Nat := 0
  /-- Documented interpreter deviations (`srem MIN, -1`). -/
  iKnown : Nat := 0
  iNone : Nat := 0
  nAgree : Nat := 0
  nDis : Nat := 0
  nNone : Nat := 0
  inE : Bool := false

def hasSrem (f : Function) : Bool :=
  f.blocks.any fun b => b.body.any fun s => match s.inst with
    | .div .srem .. => true
    | _ => false

def bump (m : Std.HashMap String KeyCounts) (k : String) (e : Bool) (f : KeyCounts → KeyCounts) :
    Std.HashMap String KeyCounts :=
  m.insert k (f { (m.getD k {}) with inE := e })

def showO : Outcome → String
  | .returned vs _ => s!"returned {vs.map fun v => (v.ty.name, hexBits v)}"
  | .trapped c => s!"trapped {c.name}"
  | .stuck m => s!"stuck {m}"
  | .outOfFuel => "out of fuel"

def showA : OracleActual → String
  | .returned vs => s!"returned {vs}"
  | .trapped c => s!"trapped {c}"
  | .error e => s!"error {e}"

/-- The oracle records of each function, in order. -/
def byFunc (rs : List OracleRecord) : Std.HashMap String (Array OracleRecord) :=
  rs.foldl (fun m r => m.insert r.attached ((m.getD r.attached #[]).push r)) {}

/-- Does `f` reinterpret float bits as an integer (`bitcast` from a float type)? -/
def foldsFloatBits (f : Function) : Bool :=
  let tyMap := f.valueTypes
  f.blocks.any fun b => b.body.any fun s =>
    match s.inst with
    | .bitcast ty _ x => ty.isInt && ((tyMap.lookup x).map Ty.isFloat).getD false
    | _ => false

/-- Compare the run lines of `paths` with the JSON files `DIR/<file name>.json` of the
interpreter (`interpDir`) and of the native runs (`nativeDir`). -/
def compareMain (paths : List String) (interpDir nativeDir : Option String)
    (report : Option String) (verbose : Bool) : IO UInt32 := do
  let load (dir : Option String) (path : String) :
      IO (Option (Std.HashMap String (Array OracleRecord))) := do
    match dir with
    | none => return none
    | some d =>
      let f := s!"{d}/{(System.FilePath.mk path).fileName.getD path}.json"
      if !(← System.FilePath.pathExists f) then return some {}
      match ← loadOracle f with
      | .ok rs => return some (byFunc rs)
      | .error e => IO.eprintln s!"clif-fuzz: {e}"; return some {}
  let mut counts : Std.HashMap String KeyCounts := {}
  let mut tot : KeyCounts := {}
  let mut shown := 0
  let mut fileErrors := 0
  -- runs without an oracle record (the oracle rejected or crashed on the file): failures
  let mut missing := 0
  for path in paths do
   let p ← match Clif.parse (← IO.FS.readFile path) with
     | .ok p => pure p
     | .error e => IO.eprintln s!"clif-fuzz: {path}: {e}"; fileErrors := fileErrors + 1; continue
   let im ← load interpDir path
   let nm ← load nativeDir path
   for f in p.funcs do
    let keys := funcKeys f
    let nanFold := foldsFloatBits f
    let ir := (im.bind (·.get? f.name)).getD #[]
    let nr := (nm.bind (·.get? f.name)).getD #[]
    for h : i in [0:f.runs.length] do
      let r := f.runs[i]
      let o := Clif.run {} p f.name r.args fuel
      if (im.isSome && ir[i]?.isNone) || (nm.isSome && nr[i]?.isNone) then missing := missing + 1
      let nv : Option (Option Bool) := nm.map fun _ =>
        match nr[i]? with
        | none => none
        | some rec => agree o rec.actual
      -- the interpreter computes NaNs with the host's (x86) rules; when the function exposes
      -- float bits as integers (`bitcast`), a NaN difference shows as an integer difference.
      -- Such a run counts as `nan-agree` when the native run agrees bit-exactly.
      let hostNaN := nanFold && nv == some (some true)
      let iv : Option (Option Bool × Bool) := im.map fun _ =>
        match ir[i]? with
        | none => (none, false)
        | some rec => (agree o rec.actual, agreeUpToNaN o rec.actual || hostNaN)
      -- documented interpreter deviation (docs/contracts/clif.md, "srem MIN, -1"): the
      -- interpreter traps `int_ovf`, CLIF (docs, native backends, `Clif.run`) returns 0
      let knownInterp := hasSrem f && (match o, ir[i]? with
        | .returned .., some { actual := .trapped "int_ovf", .. } => true
        | _, _ => false)
      let upd (c : KeyCounts) : KeyCounts := Id.run do
        let mut c := { c with runs := c.runs + 1 }
        match iv with
        | some (some true, _) => c := { c with iAgree := c.iAgree + 1 }
        | some (some false, true) => c := { c with iNan := c.iNan + 1 }
        | some (some false, false) =>
          if knownInterp then c := { c with iKnown := c.iKnown + 1 }
          else c := { c with iDis := c.iDis + 1 }
        | some (none, _) => c := { c with iNone := c.iNone + 1 }
        | none => pure ()
        match nv with
        | some (some true) => c := { c with nAgree := c.nAgree + 1 }
        | some (some false) => c := { c with nDis := c.nDis + 1 }
        | some none => c := { c with nNone := c.nNone + 1 }
        | none => pure ()
        return c
      for (k, e) in keys do counts := bump counts k e upd
      tot := upd tot
      let bad := (match iv with | some (some false, false) => !knownInterp | _ => false) ||
        (match nv with | some (some false) => true | _ => false)
      if bad || verbose then
        if shown < 200 || verbose then
          shown := shown + 1
          IO.println s!"{if bad then "DISAGREE" else "run"} %{f.name}({r.args.map fun v => (v.ty.name, hexBits v)}): Clif.run {showO o}; interp {(ir[i]?.map (showA ·.actual)).getD "-"}; native {(nr[i]?.map (showA ·.actual)).getD "-"}"
  let rows := counts.toList.toArray.qsort (fun a b => a.1 < b.1)
  let mut lines : Array String := #["key\tE\truns\tinterp_agree\tinterp_nan_agree\tinterp_known_deviation\tinterp_disagree\tinterp_noncomparable\tnative_agree\tnative_disagree\tnative_noncomparable"]
  for (k, c) in rows do
    lines := lines.push s!"{k}\t{if c.inE then "E" else "-"}\t{c.runs}\t{c.iAgree}\t{c.iNan}\t{c.iKnown}\t{c.iDis}\t{c.iNone}\t{c.nAgree}\t{c.nDis}\t{c.nNone}"
  if let some out := report then IO.FS.writeFile out ("\n".intercalate lines.toList ++ "\n")
  let noNative := rows.filter fun (_, c) => nativeDir.isSome && c.nAgree == 0
  let noInterp := rows.filter fun (_, c) => interpDir.isSome && c.iAgree + c.iNan == 0
  IO.println s!"keys without a native agreement: {noNative.toList.map (·.1)}"
  IO.println s!"keys without an interpreter agreement: {noInterp.toList.map (·.1)}"
  IO.println s!"TOTAL files {paths.length} (unparsable {fileErrors}) keys {rows.size} runs {tot.runs} (without an oracle record {missing}) interp agree {tot.iAgree} nan-agree {tot.iNan} known-deviation {tot.iKnown} disagree {tot.iDis} noncomparable {tot.iNone} native agree {tot.nAgree} disagree {tot.nDis} noncomparable {tot.nNone}"
  return if tot.iDis + tot.nDis + fileErrors + missing == 0 then 0 else 1

/-! ## Static coverage of existing runtests -/

/-- Keys of the functions with run lines among the parsed functions of `path`. -/
def fileKeys (path : String) : IO (List String) := do
  let pf := Clif.parseFile (← IO.FS.readFile path)
  let mut ks : List String := []
  for f in pf.funcs do
    if let .ok fn := f.func then
      if !fn.runs.isEmpty then
        for (k, _) in funcKeys fn do
          if !ks.contains k then ks := ks ++ [k]
  return ks

end ClifFuzz

open ClifFuzz in
def main (args : List String) : IO UInt32 := do
  match args with
  | "gen" :: rest =>
    let mut seed := 1
    let mut per := 2
    let mut runs := 8
    let mut mix := 40
    let mut out : Option String := none
    let mut perFile := 150
    let mut xs := rest
    for _ in [0:rest.length + 1] do
      match xs with
      | "--seed" :: n :: r => seed := n.toNat!; xs := r
      | "--per" :: n :: r => per := n.toNat!; xs := r
      | "--runs" :: n :: r => runs := n.toNat!; xs := r
      | "--mix" :: n :: r => mix := n.toNat!; xs := r
      | "--out-dir" :: o :: r => out := some o; xs := r
      | "--per-file" :: n :: r => perFile := max 1 n.toNat!; xs := r
      | [] => break
      | a :: _ => IO.eprintln s!"clif-fuzz gen: unknown argument {a}"; return 2
    let some outDir := out | IO.eprintln "clif-fuzz gen: --out-dir DIR required"; return 2
    IO.FS.createDirAll outDir
    let mut g : G := { gen := mkStdGen seed }
    let mut st : GenStats := {}
    -- one file per `perFile` targets (each target's functions and data objects together)
    let mut files : Array (Array Function × Array DataObject) := #[(#[], #[])]
    let mut k := 0
    let jobs := (allTargets.flatMap fun t => (List.replicate per t)) ++ List.replicate mix mixTarget
    for t in jobs do
      let ((fs, ds, st'), g') := (genOne t s!"fz{seed}_{k}" runs st).run g
      g := g'
      st := st'
      if k > 0 && k % perFile == 0 then files := files.push (#[], #[])
      k := k + 1
      files := files.modify (files.size - 1) fun (a, b) => (a ++ fs.toArray, b ++ ds.toArray)
    for h : i in [0:files.size] do
      let (funcs, data) := files[i]
      let prog : Program := { header := ["test interpret", "test run", "target aarch64"],
                              data := data.toList, funcs := funcs.toList }
      let n := toString i
      IO.FS.writeFile s!"{outDir}/fuzz{seed}_{String.ofList (List.replicate (3 - n.length) '0')}{n}.clif" (Clif.print prog)
    for b in st.bad do IO.println s!"generator: {b}"
    IO.println s!"clif-fuzz seed {seed}: files {files.size} functions {st.funcs} runs {st.runs} (trapping {st.traps}) dropped-stuck {st.stuck} rejected {st.bad.size}"
    return if st.bad.isEmpty then 0 else 1
  | "compare" :: rest =>
    let mut interp : Option String := none
    let mut native : Option String := none
    let mut report : Option String := none
    let mut verbose := false
    let mut files : List String := []
    let mut xs := rest
    for _ in [0:rest.length + 1] do
      match xs with
      | "--interp-dir" :: f :: r => interp := some f; xs := r
      | "--native-dir" :: f :: r => native := some f; xs := r
      | "--report" :: f :: r => report := some f; xs := r
      | "-v" :: r => verbose := true; xs := r
      | [] => break
      | f :: r => files := files ++ [f]; xs := r
    compareMain files interp native report verbose
  | "coverage" :: rest =>
    -- `coverage --universe GEN_DIR [--native-list LIST] FILE...`
    let mut univ : Option String := none
    let mut nativeList : List String := []
    let mut files : List String := []
    let mut xs := rest
    for _ in [0:rest.length + 1] do
      match xs with
      | "--universe" :: f :: r => univ := some f; xs := r
      | "--native-list" :: f :: r =>
        nativeList := ((← IO.FS.readFile f).splitOn "\n").filterMap fun l =>
          let l := l.trimAscii.toString
          if l.isEmpty then none else some l
        xs := r
      | f :: r => files := files ++ [f]; xs := r
      | [] => break
    let some u := univ | IO.eprintln "clif-fuzz coverage: --universe GEN_DIR required"; return 2
    let mut ukeys : Array (String × Bool) := #[]
    for ent in ← System.FilePath.readDir u do
      if ent.path.extension != some "clif" then continue
      let pf := Clif.parseFile (← IO.FS.readFile ent.path)
      for pfn in pf.funcs do
        if let .ok f := pfn.func then
          for (k, e) in funcKeys f do
            if !ukeys.any (·.1 == k) then ukeys := ukeys.push (k, e)
    let mut iCount : Std.HashMap String Nat := {}
    let mut nCount : Std.HashMap String Nat := {}
    for f in files do
      let ks ← fileKeys f
      let isNative := nativeList.any fun n => f.endsWith n || n.endsWith (System.FilePath.mk f).fileName.get!
      for k in ks do
        iCount := iCount.insert k (iCount.getD k 0 + 1)
        if isNative then nCount := nCount.insert k (nCount.getD k 0 + 1)
    let rows := ukeys.qsort (fun a b => a.1 < b.1)
    IO.println "key\tE\tinterp_files\tnative_files"
    for (k, e) in rows do
      IO.println s!"{k}\t{if e then "E" else "-"}\t{iCount.getD k 0}\t{nCount.getD k 0}"
    let iCov := rows.filter fun (k, _) => iCount.getD k 0 > 0
    let nCov := rows.filter fun (k, _) => nCount.getD k 0 > 0
    let eRows := rows.filter (·.2)
    IO.println s!"COVERAGE universe {rows.size} (E {eRows.size}) interp-checked {iCov.size} (E {(iCov.filter (·.2)).size}) native-checked {nCov.size} (E {(nCov.filter (·.2)).size})"
    return 0
  | _ =>
    IO.eprintln "usage: clif-fuzz gen|compare|coverage ... (see FVTest/Clif/Fuzz.lean)"
    return 2

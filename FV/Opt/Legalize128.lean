import FV.Clif
import Std.Data.HashMap

/-!
# `Opt.Legalize128`: rewrite `i128` away before the backend (rust-route step 5)

The Lean backend's value model is one vreg per value and its ABI layer (`sigArgs`,
`sigArgLocs`, `lowerFunction`) rejects `i128`, so the 41 remaining corpus functions cannot be
compiled. Like Cranelift's legalizer, this pass rewrites `i128` away *before* the backend:
every `i128` value becomes a pair of `i64` values (`lo`, `hi`), every `i128` instruction
becomes the equivalent `i64` code, and `i128` signatures become two `i64` parameters/returns
each — with an unused `i64` parameter/return reproducing the AAPCS64 even/odd register-pair
alignment whenever a pair would start at an odd register. Division/remainder become calls to
the `__udivti3`/`__divti3`/`__umodti3`/`__modti3` runtime helpers (implemented in
`scripts/rust-clif/rust-runtime.c` and given a byte-exact semantics in `Clif.Rust.env`).

The output is plain `i8..i64` CLIF, so the existing backend compiles it unchanged; the
theorems and proof files are untouched, and functions that needed legalisation are flagged
unverified (`i128 legalized (outside backend_correct)`).

Semantics (all against `Clif.Sem`, which is what `Clif.run` executes — the differential
`clif-filetest --legalize128` mode runs every run line through both):

* `iadd`/`isub` via the carry/borrow chain (`icmp ult` of the wrapped low sum/difference);
  `imul` via the cross products (`imul` + `umulhi`); `umulhi` via the cross products plus
  the two carries, and `smulhi` minus the sign corrections `s_x·y`, `s_y·x`;
* `band`/`bor`/`bxor`/`bnot` pairwise; `ineg` = `(~x + 1) mod 2^128`; `iabs` by `select`;
  `clz`/`ctz`/`popcnt`/`cls`/`bitrev`/`bswap` from the halves;
* shifts/rotates by the amount mod 128 (`(lo + hi·2^64) mod w = lo mod w` for the
  `i128`-typed amount of a narrower shift, since `w` divides 64), with a `select` for the
  half-crossing amount and a zeroing `select` for the amount-0 edge of the cross-half
  contribution;
* `icmp` lexicographically (the high halves with the same condition code, the low halves
  unsigned when the high halves are equal);
* `uextend`/`sextend` (`hi = 0` or `sshr lo, 63`), `ireduce` takes `lo`, `iconcat`/`isplit`
  are the pair itself, `bitcast.i128` is the identity, `select`/`bmask`/`bitselect`
  decompose pairwise, and an `i128` `brif`/`trapz`/`trapnz` condition is
  `(lo != 0) | (hi != 0)`;
* loads/stores of `i128` become two `i64` accesses at `+0`/`+8` (little-endian);
* `udiv`/`sdiv`/`urem`/`srem` at `i128` call the helper; `Clif.Rust.env` gives it the
  trapping semantics of the opcodes it replaces (`int_divz`, and `int_ovf` for
  `sdiv(i128::MIN, -1)`), so `Clif.run` original and legalised agree.

An instruction this pass does not implement (atomics at `i128`, float conversions, …) makes
the legalisation fail: the function is left alone and reported unsupported by the backend,
exactly as before.
-/

namespace Opt.Legalize128

open Clif

/-! ## Types of values, and "does the function mention i128" -/

/-- Types of the values defined in `f` (block parameters and instruction results). -/
def typeMapOf (f : Function) : Std.HashMap ValueId Ty := Id.run do
  let sigOf := fun r => (f.externs.lookup r).map (·.sig)
  let declOf := fun s => f.sigDecls.lookup s
  let mut m : Std.HashMap ValueId Ty := {}
  for b in f.blocks do
    for (v, t) in b.params do m := m.insert v t
    for st in b.body do
      if let some ts := st.inst.resultTypes sigOf declOf then
        for (r, t) in st.results.zip ts do m := m.insert r t
  return m

/-- Does a signature mention `i128`? -/
def sig128 (s : Signature) : Bool := (s.params ++ s.returns).any (·.ty == .i128)

/-- Does the instruction (its controlling type or any operand) mention `i128`? -/
def inst128 (ty : ValueId → Option Ty) : Inst → Bool
  | .iconst t _ => t == .i128
  | .unary _ t x => t == .i128 || ty x == some .i128
  | .binary op t x y => t == .i128 || ty x == some .i128 || ty y == some .i128
  | .div _ t x y => t == .i128 || ty x == some .i128 || ty y == some .i128
  | .overflow _ t x y => t == .i128 || ty x == some .i128 || ty y == some .i128
  | .carry _ t x y _ => t == .i128 || ty x == some .i128 || ty y == some .i128
  | .uaddOverflowTrap t x y _ => t == .i128 || ty x == some .i128 || ty y == some .i128
  | .icmp _ t x y => t == .i128 || ty x == some .i128 || ty y == some .i128
  | .select t c x y | .selectSpectreGuard t c x y =>
    t == .i128 || ty c == some .i128 || ty x == some .i128 || ty y == some .i128
  | .bitselect t c x y =>
    t == .i128 || ty c == some .i128 || ty x == some .i128 || ty y == some .i128
  | .bmask t x => t == .i128 || ty x == some .i128
  | .extend _ t x => t == .i128 || ty x == some .i128
  | .ireduce t x => t == .i128 || ty x == some .i128
  | .iconcat t lo hi =>
    t.double? == some .i128 || ty lo == some .i128 || ty hi == some .i128
  | .isplit t x => t == .i128 || ty x == some .i128
  | .load _ t _ p _ => t == .i128 || ty p == some .i128
  | .store _ t _ x p _ => t == .i128 || ty x == some .i128 || ty p == some .i128
  | .stackAddr t _ _ => t == .i128
  | .call .. | .callIndirect .. => false  -- the signatures are checked separately
  | .funcAddr t _ => t == .i128
  | .atomicRmw _ t _ p x => t == .i128 || ty p == some .i128 || ty x == some .i128
  | .atomicCas t _ p e x =>
    t == .i128 || ty p == some .i128 || ty e == some .i128 || ty x == some .i128
  | .atomicLoad t _ p => t == .i128 || ty p == some .i128
  | .atomicStore t _ x p => t == .i128 || ty x == some .i128 || ty p == some .i128
  | .fence => false
  | .bitcast t _ x => t == .i128 || ty x == some .i128
  | .trapz c _ | .trapnz c _ => ty c == some .i128
  | .nop => false
  | .symbolValue t _ => t == .i128

/-- Does `f` mention `i128` anywhere (its signature, an extern's, a `sigN` declaration, a
block parameter, or an instruction operand/result)? -/
def mentions128 (f : Function) : Bool :=
  sig128 f.sig || f.externs.any (fun e => sig128 e.2.sig) ||
    f.sigDecls.any (fun d => sig128 d.2) ||
  let m := typeMapOf f
  f.blocks.any fun b =>
    b.params.any (·.2 == .i128) ||
    b.body.any fun st => inst128 (fun v => m[v]?) st.inst

/-! ## The legaliser state -/

structure St where
  /-- The pair `(lo, hi)` of an `i128` value. -/
  pair : Std.HashMap ValueId (ValueId × ValueId) := {}
  /-- `isplit.i128` results become aliases of the source's pair halves. -/
  alias : Std.HashMap ValueId ValueId := {}
  /-- Defining instruction of a value (`iconst` only; shift-amount constant folding). -/
  defOf : Std.HashMap ValueId Inst := {}
  next : ValueId := 0
  nextFn : FnRef := 0
  /-- `__*ti3` helper declarations added for `div`/`rem` (by name). -/
  helper : Std.HashMap String FnRef := {}
  extraExts : List (FnRef × ExtFunc) := []
  /-- A shared `iconst.i64 0`, defined at the start of the entry block: the value passed
  for a padding parameter/return (the register it occupies is skipped by the callee). -/
  zero : ValueId := 0
  /-- Statements emitted for the block being rewritten (in order). -/
  out : List Stmt := []

abbrev M := StateT St (Except String)

def fresh : M ValueId := do
  let st ← get
  set { st with next := st.next + 1 }
  return st.next

def allocPair : M (ValueId × ValueId) := do
  let a ← fresh
  let b ← fresh
  return (a, b)

/-- Follow `alias` chains (acyclic: an alias target is a component of the pair of the
`isplit` source, whose definition dominates the `isplit`). -/
def resolveAlias (st : St) : Nat → ValueId → ValueId
  | 0, v => v
  | fuel + 1, v => match st.alias[v]? with
    | some w => resolveAlias st fuel w
    | none => v

/-- A use of a value that is not an `i128` value: through the alias map. -/
def u1 (v : ValueId) : M ValueId := do
  let st ← get
  return resolveAlias st (st.alias.size + 1) v

/-- The `(lo, hi)` pair of an `i128` value. -/
def pairOf (v : ValueId) : M (ValueId × ValueId) := do
  let st ← get
  match st.pair[v]? with
  | none => throw s!"legalize128: v{v} is not an i128 value"
  | some (a, b) =>
    let fuel := st.alias.size + 1
    return (resolveAlias st fuel a, resolveAlias st fuel b)

def emit1 (r : ValueId) (i : Inst) : M Unit :=
  modify fun s => { s with out := s.out ++ [{ results := [r], inst := i }] }

def emitS (st' : Stmt) : M Unit :=
  modify fun s => { s with out := s.out ++ [st'] }

def emitN (l : List Stmt) : M Unit :=
  modify fun s => { s with out := s.out ++ l }

/-- `bmask` via `select`: `bmask` is not in the emitter subset, so the all-ones/zero pair
is a select of the condition (an `icmp` result, `i8` 0/1). -/
def bmaskEmit (r : ValueId) (t : Ty) (c : ValueId) : M Unit := do
  let m1 ← fresh
  emit1 m1 (.iconst t (BitVec.ofInt t.width (-1)))
  let z ← fresh
  emit1 z (.iconst t (BitVec.ofInt t.width 0))
  emit1 r (.select t c m1 z)

/-- `iconst.i64 n` as a fresh value. -/
def kI64 (n : Int) : M ValueId := do
  let r ← fresh
  emit1 r (.iconst .i64 (BitVec.ofInt 64 n))
  return r

def s1 (r : ValueId) (i : Inst) : Stmt := { results := [r], inst := i }

/-- The `iconst` that defines `v`, if any (shift-amount constant folding). -/
def constOfDef (v : ValueId) : M (Option Int) := do
  let st ← get
  match st.defOf[v]? with
  | some (.iconst _ imm) => pure (some imm.toInt)
  | _ => pure none

def liftE {α : Type} (r : Except String α) : M α :=
  match r with
  | .ok a => pure a
  | .error e => throw e

/-! ## The ABI expansion of a signature

AAPCS64 passes/returns an `i128` in an even/odd register pair; when the next free register
is odd one is skipped (Cranelift's aarch64 `compute_arg_locs`: `next_xreg % 2 != 0`). The
legalised signature reproduces this with an unused `i64` parameter/return occupying exactly
the skipped register, which the callee ignores. An `sret` parameter does not consume the
`x0..x7` sequence (`sigArgLocs`). A pair that would not fit in the registers makes the
legalisation fail (the function stays unsupported, as before). -/

/-- The legalised slots of one parameter/return: itself, or a pair with an optional pad. -/
inductive SlotEl where
  | val (p : AbiParam)
  | pad
  | lo
  | hi
  deriving Repr, Inhabited

/-- The slots of every parameter, in order; `k` counts the register slots consumed by the
normal parameters so far. -/
def expandGroups (ps : List AbiParam) : Except String (List (List SlotEl)) :=
  go ps 0
where
  go : List AbiParam → Nat → Except String (List (List SlotEl))
    | [], _ => return []
    | p :: ps, k =>
      if p.ty == .i128 then
        if p.ext != .none then throw "legalize128: i128 argument with an extension"
        else if p.purpose != .normal then throw "legalize128: special-purpose i128 argument"
        else if 8 < k + 2 then throw "legalize128: i128 argument would be passed on the stack"
        else do
          let rest ← go ps (if k % 2 == 1 then k + 3 else k + 2)
          return (if k % 2 == 1 then [.pad, .lo, .hi] else [.lo, .hi]) :: rest
      else do
        let rest ← go ps (if p.purpose != .sret then k + 1 else k)
        return [.val p] :: rest

/-- The `AbiParam` of a slot. -/
def elTy : SlotEl → AbiParam
  | .val p => p
  | _ => { ty := .i64 }

def expandSig (s : Signature) : Except String Signature := do
  let pg ← expandGroups s.params
  let rg ← expandGroups s.returns
  return { s with params := pg.flatMap (·.map elTy), returns := rg.flatMap (·.map elTy) }

/-- The parameters of a (legalised) entry block: block parameters for the slots, with the
pair values of `i128` parameters. -/
def groupParams : List SlotEl → ValueId → M (List (ValueId × Ty))
  | [.val p], v => return [(v, p.ty)]
  | [.pad], _ => do
    let w ← fresh
    return [(w, .i64)]
  | [.lo, .hi], v => do
    let (a, b) ← pairOf v
    return [(a, .i64), (b, .i64)]
  | [.pad, .lo, .hi], v => do
    let w ← fresh
    let (a, b) ← pairOf v
    return [(w, .i64), (a, .i64), (b, .i64)]
  | _, _ => throw "legalize128: bad slot group"

def paramsOf : List (List SlotEl) → List (ValueId × Ty) → M (List (ValueId × Ty))
  | [], [] => return []
  | g :: gs, p :: ps => do
    let mine ← groupParams g p.1
    let rest ← paramsOf gs ps
    return mine ++ rest
  | _, _ => throw "legalize128: parameter slots do not match the signature"

/-- The values passed for the slots of one argument: itself, zero for a pad, the pair for
an `i128`. -/
def groupArg : List SlotEl → ValueId → M (List ValueId)
  | [.val _], v => return [← u1 v]
  | [.pad], _ => do
    let st ← get
    return [st.zero]
  | [.lo, .hi], v => do
    let (a, b) ← pairOf v
    return [a, b]
  | [.pad, .lo, .hi], v => do
    let st ← get
    let (a, b) ← pairOf v
    return [st.zero, a, b]
  | _, _ => throw "legalize128: bad slot group"

def argsOf : List (List SlotEl) → List ValueId → M (List ValueId)
  | [], [] => return []
  | g :: gs, v :: vs => do
    let mine ← groupArg g v
    let rest ← argsOf gs vs
    return mine ++ rest
  | _, _ => throw "legalize128: argument slots do not match the signature"

/-- The results of a (legalised) call: one value per slot, with the pair halves recorded as
the pair of the original `i128` result. -/
def groupRet : List SlotEl → ValueId → M (List ValueId)
  | [.val _], r => return [r]
  | [.pad], _ => do
    let w ← fresh
    return [w]
  | [.lo, .hi], r => do
    let a ← fresh
    let b ← fresh
    modify fun s => { s with pair := s.pair.insert r (a, b) }
    return [a, b]
  | [.pad, .lo, .hi], r => do
    let w ← fresh
    let a ← fresh
    let b ← fresh
    modify fun s => { s with pair := s.pair.insert r (a, b) }
    return [w, a, b]
  | _, _ => throw "legalize128: bad slot group"

def retsOf : List (List SlotEl) → List ValueId → M (List ValueId)
  | [], [] => return []
  | g :: gs, r :: rs => do
    let mine ← groupRet g r
    let rest ← retsOf gs rs
    return mine ++ rest
  | _, _ => throw "legalize128: return slots do not match the signature"

/-- The block parameters of a non-entry block: `i128` parameters split into their pair. -/
def blockParamsOf : List (ValueId × Ty) → M (List (ValueId × Ty))
  | [] => return []
  | (v, t) :: ps => do
    if t == .i128 then do
      let (a, b) ← pairOf v
      let more ← blockParamsOf ps
      return (a, .i64) :: (b, .i64) :: more
    else do
      let more ← blockParamsOf ps
      return (v, t) :: more

/-! ## Per-opcode helpers -/

/-- Condition operand of `brif`/`select`/… : an `i128` condition is `(lo != 0) | (hi != 0)`.
Returns the emitted statements and the `i8` condition value. -/
def condOf (ty : ValueId → Option Ty) (c : ValueId) : M (List Stmt × ValueId) := do
  if ty c == some .i128 then
    let (lo, hi) ← pairOf c
    let z ← kI64 0
    let a ← fresh
    let b ← fresh
    let r ← fresh
    return ([s1 a (.icmp .ne .i64 lo z), s1 b (.icmp .ne .i64 hi z),
             s1 r (.binary .bor .i8 a b)], r)
  else
    return ([], ← u1 c)

/-- `icmp.cc` at `i128`: lexicographic. `eq`/`ne` compare both halves directly; the other
conditions compare the high halves with the strict code (the `*gt`/`*ge` codes with the
operands swapped), then the low halves non-strictly when the high halves are equal. -/
def icmp128 (cc : IntCC) (r : ValueId) (xl xh yl yh : ValueId) : M Unit := do
  if cc == .eq || cc == .ne then do
    let a ← fresh
    emit1 a (.icmp cc .i64 xh yh)
    let b ← fresh
    emit1 b (.icmp cc .i64 xl yl)
    emit1 r (.binary (if cc == .eq then .band else .bor) .i8 a b)
  else do
    let swap : Bool := cc == .sgt || cc == .sge || cc == .ugt || cc == .uge
    let strict : IntCC := if cc == .slt || cc == .sle || cc == .sgt || cc == .sge then .slt else .ult
    let nonstrict : IntCC :=
      if cc == .sle || cc == .sge || cc == .ule || cc == .uge then .ule else .ult
    let (axl, axh, ayl, ayh) : ValueId × ValueId × ValueId × ValueId :=
      if swap then (yl, yh, xl, xh) else (xl, xh, yl, yh)
    let p ← fresh
    emit1 p (.icmp strict .i64 axh ayh)
    let e ← fresh
    emit1 e (.icmp .eq .i64 axh ayh)
    let l ← fresh
    emit1 l (.icmp nonstrict .i64 axl ayl)
    let el ← fresh
    emit1 el (.binary .band .i8 e l)
    emit1 r (.binary .bor .i8 p el)

/-- `r = c ? x : y` for a pair (two `select`s with the same condition). -/
def selectPair (c : ValueId) (rl rh : ValueId) (xl xh yl yh : ValueId) : M Unit := do
  emit1 rl (.select .i64 c xl yl)
  emit1 rh (.select .i64 c xh yh)

/-- Unsigned `x + y` at 128 bits into the pair `(rl, rh)`. -/
def iaddPair (rl rh xl xh yl yh : ValueId) : M Unit := do
  emit1 rl (.binary .iadd .i64 xl yl)
  let c8 ← fresh
  emit1 c8 (.icmp .ult .i64 rl xl)
  let c64 ← fresh
  emit1 c64 (.extend .uextend .i64 c8)
  let t ← fresh
  emit1 t (.binary .iadd .i64 xh yh)
  emit1 rh (.binary .iadd .i64 t c64)

/-- Unsigned `x - y` at 128 bits into the pair `(rl, rh)`. -/
def isubPair (rl rh xl xh yl yh : ValueId) : M Unit := do
  emit1 rl (.binary .isub .i64 xl yl)
  let b8 ← fresh
  emit1 b8 (.icmp .ult .i64 xl rl)
  let b64 ← fresh
  emit1 b64 (.extend .uextend .i64 b8)
  let t ← fresh
  emit1 t (.binary .isub .i64 xh yh)
  emit1 rh (.binary .isub .i64 t b64)

/-- Unsigned (or, with a signed `cc`, signed) `x < y` at 128 bits, as an `i8` value. -/
def cmpPair (cc : IntCC) (xl xh yl yh : ValueId) : M ValueId := do
  let hlt ← fresh
  emit1 hlt (.icmp cc .i64 xh yh)
  let heq ← fresh
  emit1 heq (.icmp .eq .i64 xh yh)
  let llt ← fresh
  emit1 llt (.icmp .ult .i64 xl yl)
  let hl ← fresh
  emit1 hl (.binary .band .i8 heq llt)
  let r ← fresh
  emit1 r (.binary .bor .i8 hlt hl)
  return r

/-- High half of the unsigned 128-bit product `(xl, xh) × (yl, yh)`: `rl` becomes 0 and
`rh` the high half. -/
def umulhiPair (rl rh xl xh yl yh : ValueId) : M Unit := do
  let a ← fresh
  emit1 a (.binary .umulhi .i64 xl yl)
  let m1 ← fresh
  emit1 m1 (.binary .imul .i64 xh yl)
  let m2 ← fresh
  emit1 m2 (.binary .imul .i64 xl yh)
  let m ← fresh
  emit1 m (.binary .iadd .i64 m1 m2)
  let c1 ← fresh
  emit1 c1 (.icmp .ult .i64 m m1)
  let s ← fresh
  emit1 s (.binary .iadd .i64 m a)
  let c2 ← fresh
  emit1 c2 (.icmp .ult .i64 s m)
  let c1v ← fresh
  emit1 c1v (.extend .uextend .i64 c1)
  let c2v ← fresh
  emit1 c2v (.extend .uextend .i64 c2)
  let t ← fresh
  emit1 t (.binary .iadd .i64 s c1v)
  let t2 ← fresh
  emit1 t2 (.binary .iadd .i64 t c2v)
  let h ← fresh
  emit1 h (.binary .imul .i64 xh yh)
  emit1 rl (.iconst .i64 (BitVec.ofInt 64 0))
  emit1 rh (.binary .iadd .i64 t2 h)

/-- The high half of the product of the pairs `(xl, xh) × (yl, yh)`: for `smulhi`, the
unsigned high half minus `s_x·y` and `s_y·x` (`s` = the sign of the operand; the
subtrahends are the full 128-bit values, at the position of the high half). -/
def mulhi128 (signed : Bool) (rl rh : ValueId) (xl xh yl yh : ValueId) : M Unit := do
  if !signed then
    umulhiPair rl rh xl xh yl yh
  else do
    let (blo, bhi) ← allocPair
    umulhiPair blo bhi xl xh yl yh
    let z ← kI64 0
    let sx ← fresh
    emit1 sx (.icmp .slt .i64 xh z)
    let sy ← fresh
    emit1 sy (.icmp .slt .i64 yh z)
    -- t = b - y; t' = sx ? t : b; u = t' - x; result = sy ? u : t'
    let (tlo, thi) ← allocPair
    isubPair tlo thi blo bhi yl yh
    let (t'lo, t'hi) ← allocPair
    selectPair sx t'lo t'hi tlo thi blo bhi
    let (ulo, uhi) ← allocPair
    isubPair ulo uhi t'lo t'hi xl xh
    selectPair sy rl rh ulo uhi t'lo t'hi

/-- `smin`/`smax`/`umin`/`umax` at 128 bits (the condition is the strict 128-bit compare
of `x` against `y`, signed for the `s*` operations). -/
def minmax128 (op : BinaryOp) (rl rh : ValueId) (xl xh yl yh : ValueId) : M Unit := do
  let cc : IntCC := if op == .umin || op == .umax then .ult else .slt
  let c ← cmpPair cc xl xh yl yh
  -- smin/umin: x < y ? x : y ; smax/umax: x < y ? y : x
  if op == .smin || op == .umin then selectPair c rl rh xl xh yl yh
  else selectPair c rl rh yl yh xl xh

/-- `bitselect c, x, y` at 128 bits: pairwise `(c & x) | (~c & y)`. -/
def bitselect128 (rl rh cl ch xl xh yl yh : ValueId) : M Unit := do
  let nlo ← fresh
  emit1 nlo (.unary .bnot .i64 cl)
  let nhi ← fresh
  emit1 nhi (.unary .bnot .i64 ch)
  let a1 ← fresh
  emit1 a1 (.binary .band .i64 cl xl)
  let a2 ← fresh
  emit1 a2 (.binary .band .i64 nlo yl)
  emit1 rl (.binary .bor .i64 a1 a2)
  let b1 ← fresh
  emit1 b1 (.binary .band .i64 ch xh)
  let b2 ← fresh
  emit1 b2 (.binary .band .i64 nhi yh)
  emit1 rh (.binary .bor .i64 b1 b2)

/-- The `i128` unary rewrites (see the module doc). -/
def un128 : UnaryOp → ValueId → ValueId → ValueId → ValueId → M Unit
  | .bnot, rl, rh, xl, xh => do
    emit1 rl (.unary .bnot .i64 xl)
    emit1 rh (.unary .bnot .i64 xh)
  | .ineg, rl, rh, xl, xh => do
    let m1 ← kI64 (-1)
    let one ← kI64 1
    let nlo ← fresh
    emit1 nlo (.binary .bxor .i64 xl m1)
    let nhi ← fresh
    emit1 nhi (.binary .bxor .i64 xh m1)
    emit1 rl (.binary .iadd .i64 nlo one)
    let c8 ← fresh
    emit1 c8 (.icmp .eq .i64 nlo m1)
    let c64 ← fresh
    emit1 c64 (.extend .uextend .i64 c8)
    emit1 rh (.binary .iadd .i64 nhi c64)
  | .iabs, rl, rh, xl, xh => do
    let z ← kI64 0
    let sx ← fresh
    emit1 sx (.icmp .slt .i64 xh z)
    let m1 ← kI64 (-1)
    let one ← kI64 1
    let nlo ← fresh
    emit1 nlo (.binary .bxor .i64 xl m1)
    let nhi ← fresh
    emit1 nhi (.binary .bxor .i64 xh m1)
    let nlo' ← fresh
    emit1 nlo' (.binary .iadd .i64 nlo one)
    let c8 ← fresh
    emit1 c8 (.icmp .eq .i64 nlo m1)
    let c64 ← fresh
    emit1 c64 (.extend .uextend .i64 c8)
    let nhi' ← fresh
    emit1 nhi' (.binary .iadd .i64 nhi c64)
    selectPair sx rl rh nlo' nhi' xl xh
  | .clz, rl, rh, xl, xh => do
    let z ← kI64 0
    let zh ← fresh
    emit1 zh (.icmp .ne .i64 xh z)
    let ch ← fresh
    emit1 ch (.unary .clz .i64 xh)
    let cl ← fresh
    emit1 cl (.unary .clz .i64 xl)
    let s64 ← kI64 64
    let sum ← fresh
    emit1 sum (.binary .iadd .i64 s64 cl)
    emit1 rl (.select .i64 zh ch sum)
    emit1 rh (.iconst .i64 (BitVec.ofInt 64 0))
  | .ctz, rl, rh, xl, xh => do
    let z ← kI64 0
    let zl ← fresh
    emit1 zl (.icmp .ne .i64 xl z)
    let czl ← fresh
    emit1 czl (.unary .ctz .i64 xl)
    let czh ← fresh
    emit1 czh (.unary .ctz .i64 xh)
    let s64 ← kI64 64
    let sum ← fresh
    emit1 sum (.binary .iadd .i64 s64 czh)
    emit1 rl (.select .i64 zl czl sum)
    emit1 rh (.iconst .i64 (BitVec.ofInt 64 0))
  | .cls, rl, rh, xl, xh => do
    -- cls(x) = clz(x ^ (x >>> 1)) - 1
    let one ← kI64 1
    let a1 ← fresh
    emit1 a1 (.binary .ushr .i64 xl one)
    let b1 ← fresh
    emit1 b1 (.binary .ishl .i64 xh (← kI64 63))
    let lo1 ← fresh
    emit1 lo1 (.binary .bor .i64 a1 b1)
    let hi1 ← fresh
    emit1 hi1 (.binary .sshr .i64 xh one)
    let dlo ← fresh
    emit1 dlo (.binary .bxor .i64 xl lo1)
    let dhi ← fresh
    emit1 dhi (.binary .bxor .i64 xh hi1)
    let z ← kI64 0
    let zh ← fresh
    emit1 zh (.icmp .ne .i64 dhi z)
    let ch ← fresh
    emit1 ch (.unary .clz .i64 dhi)
    let cl ← fresh
    emit1 cl (.unary .clz .i64 dlo)
    let s64 ← kI64 64
    let sum ← fresh
    emit1 sum (.binary .iadd .i64 s64 cl)
    let c ← fresh
    emit1 c (.select .i64 zh ch sum)
    emit1 rl (.binary .isub .i64 c one)
    emit1 rh (.iconst .i64 (BitVec.ofInt 64 0))
  | .popcnt, rl, rh, xl, xh => do
    let a ← fresh
    emit1 a (.unary .popcnt .i64 xl)
    let b ← fresh
    emit1 b (.unary .popcnt .i64 xh)
    emit1 rl (.binary .iadd .i64 a b)
    emit1 rh (.iconst .i64 (BitVec.ofInt 64 0))
  | .bitrev, rl, rh, xl, xh => do
    emit1 rl (.unary .bitrev .i64 xh)
    emit1 rh (.unary .bitrev .i64 xl)
  | .bswap, rl, rh, xl, xh => do
    emit1 rl (.unary .bswap .i64 xh)
    emit1 rh (.unary .bswap .i64 xl)

/-- The `i128` binary rewrites without shifts (see the module doc). -/
def bin128 : BinaryOp → ValueId → ValueId → ValueId → ValueId → ValueId → ValueId → M Unit
  | .band, rl, rh, xl, xh, yl, yh => do
    emit1 rl (.binary .band .i64 xl yl)
    emit1 rh (.binary .band .i64 xh yh)
  | .bor, rl, rh, xl, xh, yl, yh => do
    emit1 rl (.binary .bor .i64 xl yl)
    emit1 rh (.binary .bor .i64 xh yh)
  | .bxor, rl, rh, xl, xh, yl, yh => do
    emit1 rl (.binary .bxor .i64 xl yl)
    emit1 rh (.binary .bxor .i64 xh yh)
  | .iadd, rl, rh, xl, xh, yl, yh => iaddPair rl rh xl xh yl yh
  | .isub, rl, rh, xl, xh, yl, yh => isubPair rl rh xl xh yl yh
  | .imul, rl, rh, xl, xh, yl, yh => do
    emit1 rl (.binary .imul .i64 xl yl)
    let l1 ← fresh
    emit1 l1 (.binary .imul .i64 xl yh)
    let l2 ← fresh
    emit1 l2 (.binary .imul .i64 xh yl)
    let m ← fresh
    emit1 m (.binary .iadd .i64 l1 l2)
    let a ← fresh
    emit1 a (.binary .umulhi .i64 xl yl)
    emit1 rh (.binary .iadd .i64 m a)
  | .umulhi, rl, rh, xl, xh, yl, yh => umulhiPair rl rh xl xh yl yh
  | .smulhi, rl, rh, xl, xh, yl, yh => mulhi128 true rl rh xl xh yl yh
  | .smin, rl, rh, xl, xh, yl, yh => minmax128 .smin rl rh xl xh yl yh
  | .smax, rl, rh, xl, xh, yl, yh => minmax128 .smax rl rh xl xh yl yh
  | .umin, rl, rh, xl, xh, yl, yh => minmax128 .umin rl rh xl xh yl yh
  | .umax, rl, rh, xl, xh, yl, yh => minmax128 .umax rl rh xl xh yl yh
  | op, _, _, _, _, _, _ => throw "legalize128: saturating arithmetic at i128"

/-! ## Shifts and rotates

The amount is taken mod 128; the two 64-bit halves shift by `s = amount mod 64`, and when
the amount is ≥ 64 the halves cross. The cross-half contribution `b >>> (64 - s)` is
computed with the raw amount `64 - s ∈ [1, 64]` (an `i64` shift masks 64 to 0, which gives
the wrong value for `s = 0`) and zeroed by a `select` on `s != 0`; for constant amounts the
`s = 0` case emits no contribution at all. `rotr` by `a` is `rotl` by `128 - a`. -/

/-- The shift amount: a constant in `[0, 128)`, or an `i64` value. For `rotr` the `rotl`
amount is produced (`128 - a`, 0 stays 0). -/
def amt128 (op0 : BinaryOp) (ty : ValueId → Option Ty) (y : ValueId) :
    M (Nat ⊕ ValueId) := do
  let raw : Nat ⊕ ValueId ←
    if ty y == some .i128 then
      let (lo, _) ← pairOf y
      match ← constOfDef lo with
      -- (lo + hi·2^64) mod 128 = lo mod 128 (2^64 ≡ 0 mod 128)
      | some a => pure (Sum.inl (a.toNat % 128))
      | none => do
        let m ← kI64 127
        let amt ← fresh
        emit1 amt (.binary .band .i64 lo m)
        pure (Sum.inr amt)
    else
      match ← constOfDef y with
      | some a => pure (Sum.inl (a.toNat % 128))
      | none => do
        let w := (ty y).getD .i64
        let y64 ← if w == .i64 then pure (← u1 y) else do
          let r ← fresh
          emit1 r (.extend .uextend .i64 (← u1 y))
          pure r
        let m ← kI64 127
        let amt ← fresh
        emit1 amt (.binary .band .i64 y64 m)
        pure (Sum.inr amt)
  match raw with
  | Sum.inl n => return Sum.inl (if op0 == .rotr then (128 - n) % 128 else n)
  | Sum.inr a =>
    if op0 == .rotr then do
      let isz ← fresh
      emit1 isz (.icmp .eq .i64 a (← kI64 0))
      let t ← fresh
      emit1 t (.binary .isub .i64 (← kI64 128) a)
      let r ← fresh
      emit1 r (.select .i64 isz a t)
      return Sum.inr r
    else
      return Sum.inr a

/-- The shared variables of a variable-amount shift: `s` (the amount mod 64), `big`
(amount ≥ 64), and `nz` (the amount's low half is non-zero). -/
def shiftVars (amt : ValueId) : M (ValueId × ValueId × ValueId) := do
  let m63 ← kI64 63
  let s ← fresh
  emit1 s (.binary .band .i64 amt m63)
  let b64 ← kI64 64
  let big ← fresh
  emit1 big (.icmp .uge .i64 amt b64)
  let nz ← fresh
  emit1 nz (.icmp .ne .i64 s (← kI64 0))
  return (s, big, nz)

/-- The cross-half contribution of the shift `sh` by `64 - s` (`ushr` for a left shift,
`ishl` for a right shift/rotate), zeroed when `s = 0`. -/
def crossVar (sh : BinaryOp) (nz b s : ValueId) : M ValueId := do
  let d ← fresh
  emit1 d (.binary .isub .i64 (← kI64 64) s)
  let c ← fresh
  emit1 c (.binary sh .i64 b d)
  let z ← fresh
  emit1 z (.select .i64 nz c (← kI64 0))
  return z

/-- A constant amount (in `[0, 128)`); `op` is the (already normalised) operation. Each
result half is defined by a single instruction (a shift by 0 copies the input). -/
def constShift (op : BinaryOp) (rl rh xl xh : ValueId) (n : Nat) : M Unit := do
  match op with
  | .ishl =>
    if n < 64 then do
      emit1 rl (.binary .ishl .i64 xl (← kI64 n))
      if n == 0 then
        emit1 rh (.binary .ishl .i64 xh (← kI64 n))
      else do
        let h ← fresh
        emit1 h (.binary .ishl .i64 xh (← kI64 n))
        let c ← fresh
        emit1 c (.binary .ushr .i64 xl (← kI64 (64 - n)))
        emit1 rh (.binary .bor .i64 h c)
    else do
      emit1 rl (.iconst .i64 (BitVec.ofInt 64 0))
      emit1 rh (.binary .ishl .i64 xl (← kI64 (n - 64)))
  | .ushr =>
    if n < 64 then do
      emit1 rh (.binary .ushr .i64 xh (← kI64 n))
      if n == 0 then emit1 rl (.binary .ushr .i64 xl (← kI64 n)) else do
        let l ← fresh
        emit1 l (.binary .ushr .i64 xl (← kI64 n))
        let c ← fresh
        emit1 c (.binary .ishl .i64 xh (← kI64 (64 - n)))
        emit1 rl (.binary .bor .i64 l c)
    else do
      emit1 rh (.iconst .i64 (BitVec.ofInt 64 0))
      emit1 rl (.binary .ushr .i64 xh (← kI64 (n - 64)))
  | .sshr =>
    if n < 64 then do
      emit1 rh (.binary .sshr .i64 xh (← kI64 n))
      if n == 0 then emit1 rl (.binary .ushr .i64 xl (← kI64 n)) else do
        let l ← fresh
        emit1 l (.binary .ushr .i64 xl (← kI64 n))
        let c ← fresh
        emit1 c (.binary .ishl .i64 xh (← kI64 (64 - n)))
        emit1 rl (.binary .bor .i64 l c)
    else do
      emit1 rh (.binary .sshr .i64 xh (← kI64 63))
      emit1 rl (.binary .sshr .i64 xh (← kI64 (n - 64)))
  | _ => do
    -- rotl (the normalised form of rotl/rotr)
    if n < 64 then do
      if n == 0 then do
        emit1 rl (.binary .ishl .i64 xl (← kI64 n))
        emit1 rh (.binary .ishl .i64 xh (← kI64 n))
      else do
        let a ← fresh
        emit1 a (.binary .ishl .i64 xl (← kI64 n))
        let b ← fresh
        emit1 b (.binary .ishl .i64 xh (← kI64 n))
        let c ← fresh
        emit1 c (.binary .ushr .i64 xh (← kI64 (64 - n)))
        let d ← fresh
        emit1 d (.binary .ushr .i64 xl (← kI64 (64 - n)))
        emit1 rl (.binary .bor .i64 a c)
        emit1 rh (.binary .bor .i64 b d)
    else do
      let m := n - 64
      if m == 0 then do
        emit1 rl (.binary .ishl .i64 xh (← kI64 m))
        emit1 rh (.binary .ishl .i64 xl (← kI64 m))
      else do
        let a ← fresh
        emit1 a (.binary .ishl .i64 xh (← kI64 m))
        let b ← fresh
        emit1 b (.binary .ishl .i64 xl (← kI64 m))
        let c ← fresh
        emit1 c (.binary .ushr .i64 xl (← kI64 (64 - m)))
        let d ← fresh
        emit1 d (.binary .ushr .i64 xh (← kI64 (64 - m)))
        emit1 rl (.binary .bor .i64 a c)
        emit1 rh (.binary .bor .i64 b d)

/-- A variable-amount shift (`op` normalised; `s` in `[0, 64)`, `big`/`nz` as in
`shiftVars`). -/
def varShift (op : BinaryOp) (rl rh xl xh s big nz : ValueId) : M Unit := do
  match op with
  | .ishl =>
    let shl ← fresh
    emit1 shl (.binary .ishl .i64 xl s)
    let shh ← fresh
    emit1 shh (.binary .ishl .i64 xh s)
    let cr ← crossVar .ushr nz xl s
    let hs ← fresh
    emit1 hs (.binary .bor .i64 shh cr)
    let zero ← kI64 0
    emit1 rl (.select .i64 big zero shl)
    emit1 rh (.select .i64 big shl hs)
  | .ushr =>
    let shh ← fresh
    emit1 shh (.binary .ushr .i64 xh s)
    let shl ← fresh
    emit1 shl (.binary .ushr .i64 xl s)
    let cr ← crossVar .ishl nz xh s
    let ls ← fresh
    emit1 ls (.binary .bor .i64 shl cr)
    let zero ← kI64 0
    emit1 rl (.select .i64 big shh ls)
    emit1 rh (.select .i64 big zero shh)
  | .sshr =>
    let shh ← fresh
    emit1 shh (.binary .sshr .i64 xh s)
    let shl ← fresh
    emit1 shl (.binary .ushr .i64 xl s)
    let cr ← crossVar .ishl nz xh s
    let ls ← fresh
    emit1 ls (.binary .bor .i64 shl cr)
    let hb ← fresh
    emit1 hb (.binary .sshr .i64 xh (← kI64 63))
    emit1 rl (.select .i64 big shh ls)
    emit1 rh (.select .i64 big hb shh)
  | _ =>
    -- rotl (the normalised form of rotl/rotr): the big case swaps the halves
    let a ← fresh
    emit1 a (.binary .ishl .i64 xl s)
    let b ← fresh
    emit1 b (.binary .ishl .i64 xh s)
    let c ← crossVar .ushr nz xh s
    let d ← crossVar .ushr nz xl s
    let la ← fresh
    emit1 la (.binary .bor .i64 a c)
    let lb ← fresh
    emit1 lb (.binary .bor .i64 b d)
    emit1 rl (.select .i64 big lb la)
    emit1 rh (.select .i64 big la lb)

/-- A shift/rotate at `i128`. -/
def shift128 (op0 : BinaryOp) (ty : ValueId → Option Ty) (rl rh : ValueId)
    (xl xh y : ValueId) : M Unit := do
  let op : BinaryOp := if op0 == .rotr then .rotl else op0
  match ← amt128 op0 ty y with
  | Sum.inl n => constShift op rl rh xl xh n
  | Sum.inr a =>
    let (s, big, nz) ← shiftVars a
    varShift op rl rh xl xh s big nz

/-! ## Division and remainder via the runtime helpers -/

/-- The helper of a `div` at `i128`. -/
def divHelper : DivOp → String
  | .udiv => "__udivti3" | .sdiv => "__divti3" | .urem => "__umodti3" | .srem => "__modti3"

/-- The declared signature of a `__*ti3` helper: two 128-bit arguments as `i64` pairs,
returning one 128-bit value as an `i64` pair. -/
def helperSig : Signature where
  params := [{ ty := .i64 }, { ty := .i64 }, { ty := .i64 }, { ty := .i64 }]
  returns := [{ ty := .i64 }, { ty := .i64 }]
  callConv := none

/-- The function reference of the `__*ti3` helper, declaring it if needed. -/
def helperFn (name : String) : M FnRef := do
  let st ← get
  match st.helper[name]? with
  | some fn => return fn
  | none =>
    let fn := st.nextFn
    let ext : ExtFunc := { name, sig := helperSig }
    modify fun s => { s with nextFn := s.nextFn + 1, helper := s.helper.insert name fn, extraExts := s.extraExts ++ [(fn, ext)] }
    return fn

/-! ## The statement rewriter -/

/-- The arguments of a branch to `bc`: `i128` arguments split into their pair. -/
def rewriteBC (f : Function) (bc : BlockCall) : M BlockCall := do
  let some tb := f.block? bc.block | throw s!"legalize128: unknown block{bc.block}"
  let rec go : List ValueId → List (ValueId × Ty) → M (List ValueId)
    | [], [] => return []
    | v :: vs, (w, t) :: ps => do
      if t == .i128 then do
        let (a, b) ← pairOf v
        let more ← go vs ps
        return a :: b :: more
      else do
        let more ← go vs ps
        return (← u1 v) :: more
    | _, _ => throw s!"legalize128: arity of block{bc.block}"
  let args ← go bc.args tb.params
  return { bc with args }

/-- The rewrite of one statement: the emitted statements replace it (an empty list drops
it; the original results are kept when their types do not change). -/
def rewriteStmt (f : Function) (ty : ValueId → Option Ty) (s : Stmt) : M Unit := do
  match s.inst with
  | .iconst .. => emitS s
  | .unary op t x =>
    if t == .i128 then do
      let (rl, rh) ← pairOf s.results.head!
      let (xl, xh) ← pairOf x
      un128 op rl rh xl xh
    else
      emitS { s with inst := .unary op t (← u1 x) }
  | .binary op t x y =>
    if t == .i128 then do
      let (rl, rh) ← pairOf s.results.head!
      let (xl, xh) ← pairOf x
      if op.isShift then shift128 op ty rl rh xl xh y
      else do
        let (yl, yh) ← pairOf y
        bin128 op rl rh xl xh yl yh
    else if op.isShift && ty y == some .i128 then do
      -- the amount is `i128`: `(lo + hi·2^64) mod w = lo mod w` (w divides 64)
      let (yl, _) ← pairOf y
      let m ← fresh
      emit1 m (.iconst .i64 (BitVec.ofNat 64 (t.width - 1)))
      let y' ← fresh
      emit1 y' (.binary .band .i64 yl m)
      emitS { s with inst := .binary op t (← u1 x) y' }
    else if ty x == some .i128 || ty y == some .i128 then
      throw "legalize128: i128 operand of a non-i128 binary instruction"
    else
      emitS { s with inst := .binary op t (← u1 x) (← u1 y) }
  | .div op t x y =>
    if t == .i128 then do
      let fn ← helperFn (divHelper op)
      let (xl, xh) ← pairOf x
      let (yl, yh) ← pairOf y
      let (rl, rh) ← pairOf s.results.head!
      emitS { results := [rl, rh], inst := .call fn [xl, xh, yl, yh] }
    else if ty x == some .i128 || ty y == some .i128 then
      throw "legalize128: i128 operand of a non-i128 division"
    else
      emitS { s with inst := .div op t (← u1 x) (← u1 y) }
  | .overflow .. | .carry .. | .uaddOverflowTrap .. => throw "legalize128: not in E"
  | .icmp cc t x y =>
    if t == .i128 then do
      let (xl, xh) ← pairOf x
      let (yl, yh) ← pairOf y
      icmp128 cc s.results.head! xl xh yl yh
    else
      emitS { s with inst := .icmp cc t (← u1 x) (← u1 y) }
  | .select t c x y | .selectSpectreGuard t c x y =>
    if t == .i128 then do
      let (rl, rh) ← pairOf s.results.head!
      let (xl, xh) ← pairOf x
      let (yl, yh) ← pairOf y
      let (cs, c') ← condOf ty c
      emitN cs
      selectPair c' rl rh xl xh yl yh
    else if ty x == some .i128 || ty y == some .i128 then
      throw "legalize128: i128 operand of a non-i128 select"
    else do
      let (cs, c') ← condOf ty c
      emitN cs
      emitS { s with inst := .select t c' (← u1 x) (← u1 y) }
  | .bitselect t c x y =>
    if t == .i128 then do
      let (rl, rh) ← pairOf s.results.head!
      let (cl, ch) ← pairOf c
      let (xl, xh) ← pairOf x
      let (yl, yh) ← pairOf y
      bitselect128 rl rh cl ch xl xh yl yh
    else if ty c == some .i128 || ty x == some .i128 || ty y == some .i128 then
      throw "legalize128: i128 operand of a non-i128 bitselect"
    else
      emitS { s with inst := .bitselect t (← u1 c) (← u1 x) (← u1 y) }
  | .bmask t x =>
    -- the truthiness of an `i128` operand is `(lo != 0) | (hi != 0)`; `bmask` itself is
    -- not in the emitter subset, so the result is a select of the condition
    if t == .i128 then do
      let (rl, rh) ← pairOf s.results.head!
      let c ← if ty x == some .i128 then do
        let (lo, hi) ← pairOf x
        let z ← kI64 0
        let a ← fresh
        emit1 a (.icmp .ne .i64 lo z)
        let b ← fresh
        emit1 b (.icmp .ne .i64 hi z)
        let c ← fresh
        emit1 c (.binary .bor .i8 a b)
        pure c
      else pure (← u1 x)
      bmaskEmit rl .i64 c
      bmaskEmit rh .i64 c
    else if ty x == some .i128 then do
      let (lo, hi) ← pairOf x
      let z ← kI64 0
      let a ← fresh
      emit1 a (.icmp .ne .i64 lo z)
      let b ← fresh
      emit1 b (.icmp .ne .i64 hi z)
      let c ← fresh
      emit1 c (.binary .bor .i8 a b)
      bmaskEmit s.results.head! t c
    else
      emitS { s with inst := .bmask t (← u1 x) }
  | .extend op t x =>
    if t == .i128 then do
      let some w := ty x | throw "legalize128: extend with an untyped operand"
      let (rl, rh) ← pairOf s.results.head!
      if op == .uextend then do
        let x' ← u1 x
        if w == .i64 then
          emit1 rl (.binary .bor .i64 x' x')  -- a copy of x'
        else
          emit1 rl (.extend .uextend .i64 x')
        emit1 rh (.iconst .i64 (BitVec.ofInt 64 0))
      else do
        let x' ← u1 x
        if w == .i64 then
          emit1 rl (.binary .bor .i64 x' x')
        else
          emit1 rl (.extend .sextend .i64 x')
        emit1 rh (.binary .sshr .i64 rl (← kI64 63))
    else if ty x == some .i128 then
      throw "legalize128: i128 operand of a non-i128 extend"
    else
      emitS { s with inst := .extend op t (← u1 x) }
  | .ireduce t x =>
    if ty x == some .i128 then do
      let (lo, _) ← pairOf x
      if t == .i64 then
        -- `ireduce.i64` of an `i128` value is the pair's low half itself: an alias
        modify fun st => { st with alias := st.alias.insert s.results.head! lo }
      else
        emitS { s with inst := .ireduce t lo }
    else
      emitS { s with inst := .ireduce t (← u1 x) }
  | .iconcat t lo hi =>
    -- the controlling type is the operand type; the result has twice the width
    if t == .i64 then pure ()  -- the pair of the result is (lo, hi): dropped
    else throw "legalize128: iconcat with a non-i128 result"
  | .isplit t x =>
    if t == .i128 then pure ()  -- the results alias the pair of x: dropped
    else throw "legalize128: isplit at a non-i128 type"
  | .load op t flags p off =>
    if t == .i128 then do
      let (rl, rh) ← pairOf s.results.head!
      let p' ← u1 p
      emit1 rl (.load .load .i64 flags p' off)
      emit1 rh (.load .load .i64 flags p' (off + 8))
    else if ty p == some .i128 then
      throw "legalize128: i128 address"
    else
      emitS { s with inst := .load op t flags (← u1 p) off }
  | .store op t flags x p off =>
    if t == .i128 then do
      let (xl, xh) ← pairOf x
      let p' ← u1 p
      emitS { results := [], inst := .store .store .i64 flags xl p' off }
      emitS { results := [], inst := .store .store .i64 flags xh p' (off + 8) }
    else if ty x == some .i128 || ty p == some .i128 then
      throw "legalize128: i128 operand of a non-i128 store"
    else
      emitS { s with inst := .store op t flags (← u1 x) (← u1 p) off }
  | .stackAddr t slot off =>
    if t == .i128 then throw "legalize128: i128 stack_addr"
    else emitS s
  | .call fn args => do
    let some ext := f.externs.lookup fn | throw s!"legalize128: unknown fn{fn}"
    if sig128 ext.sig then do
      let gs ← liftE (expandGroups ext.sig.params)
      let rg ← liftE (expandGroups ext.sig.returns)
      let args' ← argsOf gs args
      let results ← retsOf rg s.results
      emitS { s with results, inst := .call fn args' }
    else
      emitS { s with inst := .call fn (← args.mapM u1) }
  | .callIndirect sig callee args => do
    let some dsig := f.sigDecls.lookup sig | throw s!"legalize128: unknown sig{sig}"
    if sig128 dsig then do
      let gs ← liftE (expandGroups dsig.params)
      let rg ← liftE (expandGroups dsig.returns)
      let args' ← argsOf gs args
      let results ← retsOf rg s.results
      emitS { s with results, inst := .callIndirect sig (← u1 callee) args' }
    else
      emitS { s with inst := .callIndirect sig (← u1 callee) (← args.mapM u1) }
  | .funcAddr t fn =>
    if t == .i128 then throw "legalize128: i128 func_addr"
    else emitS s
  | .atomicRmw .. | .atomicCas .. | .atomicLoad .. | .atomicStore .. =>
    throw "legalize128: atomics are not legalised"
  | .fence => emitS s
  | .bitcast t flags x =>
    if t == .i128 && ty x == some .i128 then do
      -- the identity: the result's pair is the source's pair
      let p ← pairOf x
      modify fun st => { st with pair := st.pair.insert s.results.head! p }
    else if t == .i128 || ty x == some .i128 then
      throw "legalize128: i128 bitcast"
    else emitS s
  | .trapz c code => do
    let (cs, c') ← condOf ty c
    emitN cs
    emitS { s with inst := .trapz c' code }
  | .trapnz c code => do
    let (cs, c') ← condOf ty c
    emitN cs
    emitS { s with inst := .trapnz c' code }
  | .nop => emitS s
  | .symbolValue t gv =>
    if t == .i128 then throw "legalize128: i128 symbol_value"
    else emitS s

/-! ## The terminator and the function -/

/-- The rewrite of a terminator (its condition statements are emitted into `out`). -/
def rewriteTerm (f : Function) (ty : ValueId → Option Ty) (rg : List (List SlotEl))
    (t : Terminator) : M Terminator := do
  match t with
  | .jump bc => return .jump (← rewriteBC f bc)
  | .brif c t2 e => do
    let (cs, c') ← condOf ty c
    emitN cs
    return .brif c' (← rewriteBC f t2) (← rewriteBC f e)
  | .brTable x d tbl =>
    return .brTable (← u1 x) (← rewriteBC f d) (← tbl.mapM (rewriteBC f))
  | .ret vs => return .ret (← argsOf rg vs)
  | .trap _ => return t
  | .returnCall .. => throw "legalize128: return_call is not supported"
  | .tryCall _ args et | .tryCallIndirect _ args et => do
    -- values of other types pass through (renamed); i128 call arguments, results, payloads
    -- or successor parameters are not legalised
    let sig128 := match f.sigDecls.lookup et.sig with
      | some s => (s.params ++ s.returns).any (·.ty == .i128)
      | none => true
    let dest128 := et.dests.any fun d => match f.block? d.block with
      | some b => b.params.any (·.2 == .i128)
      | none => true
    let vals := (match t with | .tryCallIndirect c .. => [c] | _ => []) ++ args ++ et.vals
    if sig128 || dest128 || vals.any (ty · == some .i128) then
      throw "legalize128: try_call with i128 values is not supported"
    let st ← get
    let g := resolveAlias st (st.alias.size + 1)
    return match t with
      | .tryCallIndirect c .. => .tryCallIndirect (g c) (args.map g) (et.mapVals g)
      | .tryCall fn .. => .tryCall fn (args.map g) (et.mapVals g)
      | _ => t

/-- The biggest value id in `f` (fresh ids continue after it). -/
def maxValueId (f : Function) : ValueId :=
  f.blocks.foldl (fun acc b =>
    let acc := b.params.foldl (fun a p => max a p.1) acc
    b.body.foldl (fun a s => s.results.foldl (fun a2 r => max a2 r) a) acc) 0 + 1

/-- The biggest function-reference id in `f` (helper declarations continue after it). -/
def maxFnRef (f : Function) : FnRef :=
  f.externs.foldl (fun a e => max a e.1) 0 + 1

/-- Phase A1: the pair of every `i128` value (the results of `iconcat` are their operands;
the results of a `call`/`call_indirect` are assigned when the call is rewritten). -/
def phaseA1 (f : Function) : M Unit := do
  let sigOf := fun r => (f.externs.lookup r).map (·.sig)
  let declOf := fun s => f.sigDecls.lookup s
  for b in f.blocks do
    for (v, t) in b.params do
      if t == .i128 then
        let p ← allocPair
        modify fun s => { s with pair := s.pair.insert v p }
    for s in b.body do
      if let .iconst .. := s.inst then
        for r in s.results do
          modify fun st => { st with defOf := st.defOf.insert r s.inst }
      match s.inst with
      | .iconcat .i64 lo hi =>
        for r in s.results do
          modify fun st => { st with pair := st.pair.insert r (lo, hi) }
      | .isplit .i128 _ => pure ()
      | .bitcast .i128 _ _ => pure ()  -- the pair of the source, bound in phase B
      | .call .. | .callIndirect .. => pure ()
      | _ =>
        if let some ts := s.inst.resultTypes sigOf declOf then
          for (r, t) in s.results.zip ts do
            if t == .i128 then
              let p ← allocPair
              modify fun st => { st with pair := st.pair.insert r p }

/-- Phase A2: the results of an `isplit.i128` alias the pair halves of its source. -/
def phaseA2 (f : Function) : M Unit := do
  for b in f.blocks do
    for s in b.body do
      if let .isplit .i128 x := s.inst then
        let (a, b) ← pairOf x
        match s.results with
        | [r0, r1] =>
          modify fun st =>
            { st with alias := st.alias.insert r0 a |>.insert r1 b }
        | _ => throw "legalize128: isplit.i128 result arity"

/-- Phase B: rewrite the signature, the declarations, the blocks and the terminators. -/
def rewriteM (f : Function) : M Function := do
  let tyMap := typeMapOf f
  let ty : ValueId → Option Ty := fun v => tyMap[v]?
  -- the shared zero for pad values, defined at the start of the entry block
  let z ← fresh
  modify fun s => { s with zero := z }
  -- signature and declarations
  let newSig ← liftE (expandSig f.sig)
  let newExterns ← f.externs.mapM fun (r, e) => do
    let s ← liftE (expandSig e.sig)
    return (r, { e with sig := s })
  let newSigDecls ← f.sigDecls.mapM fun (i, s) => do
    let s' ← liftE (expandSig s)
    return (i, s')
  -- blocks
  let pg ← liftE (expandGroups f.sig.params)
  let rg ← liftE (expandGroups f.sig.returns)
  let mut newBlocks : List Block := []
  for (b, bi) in f.blocks.zipIdx do
    modify fun s => { s with out := [] }
    let params ← if bi == 0 then paramsOf pg b.params else blockParamsOf b.params
    if bi == 0 then
      emitS (s1 z (.iconst .i64 (BitVec.ofInt 64 0)))
    for s in b.body do
      rewriteStmt f ty s
    let term ← rewriteTerm f ty rg b.term
    let st ← get
    newBlocks := newBlocks ++ [{ b with params, body := st.out, term }]
  let st ← get
  return { f with sig := newSig, externs := newExterns ++ st.extraExts,
                  sigDecls := newSigDecls, blocks := newBlocks }

/-- The legalised function (an error makes the caller keep the original, which the backend
then reports unsupported as before). -/
def function128 (f : Function) : Except String Function := do
  if !(mentions128 f) then return f
  let (_, st) ← (phaseA1 f).run { next := maxValueId f + 1, nextFn := maxFnRef f + 1 }
  let (_, st) ← (phaseA2 f).run st
  let (f', _) ← (rewriteM f).run st
  return f'

/-- Legalise every parsed function of a file; returns the file and, for every function that
was legalised, the unverified reason. -/
def parsedFile128 (pf : Clif.ParsedFile) : Clif.ParsedFile × List (String × String) :=
  pf.funcs.foldl (fun (acc : Clif.ParsedFile × List (String × String)) p =>
    let push (f : Clif.ParsedFunction) : Clif.ParsedFile :=
      { acc.1 with funcs := acc.1.funcs ++ [f] }
    match p.func with
    | .ok f =>
      match function128 f with
      | .ok f' =>
        if f' == f then (push p, acc.2)
        else (push { p with func := .ok f' },
                acc.2 ++ [(p.name, "i128 legalized (outside backend_correct)")])
      | .error _ => (push p, acc.2)
    | .error _ => (push p, acc.2)) ({ pf with funcs := [] }, [])

/-! ## Run commands: the original's arguments and the legalised outcome -/

/-- The arguments of a run command of the original function, expanded for the legalised
signature (an `i128` argument becomes its pair, a pad gets zero). -/
def expandRunArgs (orig : Signature) (vs : List Val) : Except String (List Val) := do
  let gs ← expandGroups orig.params
  go gs vs
where
  go : List (List SlotEl) → List Val → Except String (List Val)
    | [], [] => return []
    | g :: gs, v :: vs => do
      let mine ← groupVal g v
      let rest ← go gs vs
      return mine ++ rest
    | _, _ => throw "legalize128: run arguments do not match the signature"
  groupVal : List SlotEl → Val → Except String (List Val)
    | [.val _], v => return [v]
    | [.pad], _ => return [Val.ofNat .i64 0]
    | [.lo, .hi], v =>
      match v.ty with
      | .i128 => return [⟨.i64, v.bits.extractLsb' 0 64⟩, ⟨.i64, v.bits.extractLsb' 64 64⟩]
      | _ => throw "legalize128: run argument is not i128"
    | [.pad, .lo, .hi], v =>
      match v.ty with
      | .i128 =>
        return [Val.ofNat .i64 0, ⟨.i64, v.bits.extractLsb' 0 64⟩,
                ⟨.i64, v.bits.extractLsb' 64 64⟩]
      | _ => throw "legalize128: run argument is not i128"
    | _, _ => throw "legalize128: bad slot group"

/-- A legalised run outcome mapped back to the original signature's shape. -/
def joinRunOutcome (orig : Signature) (o : Outcome) : Outcome :=
  match o with
  | .returned vs mem =>
    match (expandGroups orig.returns).toOption.bind (fun gs => joinVals gs vs) with
    | some vs' => .returned vs' mem
    | none => .stuck "legalize128: returned values do not match the signature"
  | _ => o
where
  joinVals : List (List SlotEl) → List Val → Option (List Val)
    | [], [] => some []
    | g :: gs, v :: vs =>
      match g with
      | [.val _] => (joinVals gs vs).map (v :: ·)
      | [.pad] => joinVals gs vs
      | [.lo, .hi] =>
        match v :: vs with
        | l :: h :: rest =>
          match l.as? .i64, h.as? .i64 with
          | some l', some h' => (joinVals gs rest).map (⟨.i128, h' ++ l'⟩ :: ·)
          | _, _ => none
        | _ => none
      | [.pad, .lo, .hi] =>
        match v :: vs with
        | _ :: l :: h :: rest =>
          match l.as? .i64, h.as? .i64 with
          | some l', some h' => (joinVals gs rest).map (⟨.i128, h' ++ l'⟩ :: ·)
          | _, _ => none
        | _ => none
      | _ => none
    | _, _ => none

end Opt.Legalize128

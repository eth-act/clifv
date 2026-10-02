import FV.Opt.Legalize128

/-!
# `Opt.Legal.check`: the validator of `Opt.Legalize128`

`Opt.Legalize128` (untrusted) rewrites every `i128` value of a function `f` into a pair of
`i64` values and returns the legalised function `g` with a certificate (`Cert`: the pair of
every `i128` value and the shared zero of the pad values). `check f g cert` decides whether
`g` is a legalisation of `f` this module knows to be correct; the refinement theorem
(`Opt.Legal.check_refines`, `FV/Opt/Proof/LegalSim.lean`) holds for every accepted pair, and
`lean-backend` flags the rejected ones unverified.

The check is structural, block by block: `g` has the blocks of `f` (same ids, same order), the
entry block starts with the shared zero, and every statement of `f` corresponds to a *segment*
of `g`'s block, decided by its `Plan`:

* `same`: the statement itself (no `i128` operand or result);
* `pure pat ins outs`: an instance of the canonical pattern `pat` (straight-line pure `i64`
  code over canonical value ids: inputs `0 ..< ins.length`, outputs next, temporaries after),
  renamed by `σ` (inputs ↦ `ins`, outputs ↦ `outs`, temporaries ↦ fresh values of `g`, read off
  the segment); the patterns are proven correct once (`FV/Opt/Proof/LegalPat.lean`);
* `load`/`store`: two `i64` accesses at `+0`/`+8`;
* `div`: a call of the `__*ti3` helper on the pairs;
* `call`: the call with its arguments/results expanded by the ABI groups (pads);
* `trap`: a pure condition pattern followed by `trapz`/`trapnz`.

Value ids: every value of `f` is below `T0 = maxValueId f`; pair components and the zero are
distinct values `≥ T0`; the temporaries and pads of `g` are *fresh* (`≥ T0`, not a pair
component, not the zero). So a write of `g` never clobbers the image of another value of `f`.
-/

namespace Opt.Legal

open Clif Opt.Legalize128

/-! ## Operands and renaming -/

/-- The value operands of an instruction. -/
def instOps : Inst → List ValueId
  | .iconst .. | .stackAddr .. | .fence | .nop | .symbolValue .. | .funcAddr ..
  | .tlsValue .. => []
  | .unary _ _ x | .bmask _ x | .extend _ _ x | .ireduce _ x | .isplit _ x
  | .load _ _ _ x _ | .atomicLoad _ _ x | .bitcast _ _ x | .trapz x _ | .trapnz x _ => [x]
  | .binary _ _ x y | .div _ _ x y | .overflow _ _ x y | .uaddOverflowTrap _ x y _
  | .icmp _ _ x y | .iconcat _ x y | .store _ _ _ x y _ | .atomicRmw _ _ _ x y
  | .atomicStore _ _ x y => [x, y]
  | .carry _ _ x y c => [x, y, c]
  | .select _ c x y | .selectSpectreGuard _ c x y | .bitselect _ c x y
  | .atomicCas _ _ c x y => [c, x, y]
  | .call _ args => args
  | .callIndirect _ c args => c :: args

/-- Rename the value operands of an instruction. -/
def renameInst (σ : ValueId → ValueId) : Inst → Inst
  | .iconst t k => .iconst t k
  | .unary op t x => .unary op t (σ x)
  | .binary op t x y => .binary op t (σ x) (σ y)
  | .div op t x y => .div op t (σ x) (σ y)
  | .overflow op t x y => .overflow op t (σ x) (σ y)
  | .carry op t x y c => .carry op t (σ x) (σ y) (σ c)
  | .uaddOverflowTrap t x y c => .uaddOverflowTrap t (σ x) (σ y) c
  | .icmp cc t x y => .icmp cc t (σ x) (σ y)
  | .select t c x y => .select t (σ c) (σ x) (σ y)
  | .selectSpectreGuard t c x y => .selectSpectreGuard t (σ c) (σ x) (σ y)
  | .bitselect t c x y => .bitselect t (σ c) (σ x) (σ y)
  | .bmask t x => .bmask t (σ x)
  | .extend op t x => .extend op t (σ x)
  | .ireduce t x => .ireduce t (σ x)
  | .iconcat t x y => .iconcat t (σ x) (σ y)
  | .isplit t x => .isplit t (σ x)
  | .load op t fl p off => .load op t fl (σ p) off
  | .store op t fl x p off => .store op t fl (σ x) (σ p) off
  | .stackAddr t s off => .stackAddr t s off
  | .call fn args => .call fn (args.map σ)
  | .callIndirect s c args => .callIndirect s (σ c) (args.map σ)
  | .funcAddr t fn => .funcAddr t fn
  | .tlsValue t gv => .tlsValue t gv
  | .atomicRmw op t fl p x => .atomicRmw op t fl (σ p) (σ x)
  | .atomicCas t fl p e x => .atomicCas t fl (σ p) (σ e) (σ x)
  | .atomicLoad t fl p => .atomicLoad t fl (σ p)
  | .atomicStore t fl x p => .atomicStore t fl (σ x) (σ p)
  | .fence => .fence
  | .bitcast t fl x => .bitcast t fl (σ x)
  | .trapz c code => .trapz (σ c) code
  | .trapnz c code => .trapnz (σ c) code
  | .nop => .nop
  | .symbolValue t gv => .symbolValue t gv

def renameStmt (σ : ValueId → ValueId) (s : Stmt) : Stmt :=
  { results := s.results.map σ, inst := renameInst σ s.inst }

/-- The instructions a pattern may use: pure, non-trapping, no memory, no frame lookups. -/
def pureInst : Inst → Bool
  | .iconst .. | .unary .. | .binary .. | .icmp .. | .select .. | .extend .. | .ireduce .. =>
    true
  | _ => false

/-- The value operands of a terminator. -/
def termOps : Terminator → List ValueId
  | .jump bc => bc.args
  | .brif c t e => c :: t.args ++ e.args
  | .brTable x d tbl => x :: d.args ++ tbl.flatMap (·.args)
  | .ret xs => xs
  | .returnCall _ args => args
  | .trap _ => []
  | .tryCall _ args et => args ++ et.vals
  | .tryCallIndirect c args et => c :: args ++ et.vals

/-- The branch targets of a terminator. -/
def termDests : Terminator → List BlockCall
  | .jump bc => [bc]
  | .brif _ t e => [t, e]
  | .brTable _ d tbl => d :: tbl
  | _ => []

/-! ## The definitions of `f`: types, defining instructions -/

def sigOfF (f : Function) (r : FnRef) : Option Signature := (f.extern? r).map (·.sig)

def declOfF (f : Function) (s : Nat) : Option Signature := f.sigDecls.lookup s

/-- The definitions of a statement: each result with its type and the instruction. -/
def stmtDefs (f : Function) (st : Stmt) : List (ValueId × Option Ty × Option Inst) :=
  let tys := st.inst.resultTypes (sigOfF f) (declOfF f)
  st.results.zipIdx.map fun (r, i) => (r, tys.bind (·[i]?), some st.inst)

/-- The definitions of a block: its parameters and the results of its statements. -/
def blockDefs (f : Function) (b : Block) : List (ValueId × Option Ty × Option Inst) :=
  b.params.map (fun p => (p.1, some p.2, none)) ++ b.body.flatMap (stmtDefs f)

/-- Every definition of `f` (a value is defined once: `check` requires the keys distinct). -/
def defsOf (f : Function) : List (ValueId × Option Ty × Option Inst) :=
  f.blocks.flatMap (blockDefs f)

/-- The static type of a value of `f`. -/
def tyOf (f : Function) (v : ValueId) : Option Ty := ((defsOf f).lookup v).bind (·.1)

/-- The instruction defining a value of `f` (`none` for a block parameter). -/
def defInst (f : Function) (v : ValueId) : Option Inst := ((defsOf f).lookup v).bind (·.2)

/-- The unsigned value of the `iconst` defining `v`. -/
def constOf (f : Function) (v : ValueId) : Option Nat :=
  match defInst f v with
  | some (.iconst _ k) => some k.toNat
  | _ => none

/-- The constant low half of an `i128` value defined by `iconcat` of a constant. -/
def concatConst (f : Function) (v : ValueId) : Option Nat :=
  match defInst f v with
  | some (.iconcat .i64 lo _) => constOf f lo
  | _ => none

/-- Every value id mentioned in `f`. -/
def idsOf (f : Function) : List ValueId :=
  f.blocks.flatMap fun b =>
    b.params.map (·.1) ++ b.body.flatMap (fun st => st.results ++ instOps st.inst) ++ termOps b.term

/-! ## The context of a check -/

structure Ctx where
  f : Function
  g : Function
  cert : Cert

namespace Ctx

/-- Every value of `f` is below `T0`. -/
def T0 (C : Ctx) : Nat := maxValueId C.f

def pair (C : Ctx) (v : ValueId) : Option (ValueId × ValueId) := C.cert.pairs.lookup v

def zero (C : Ctx) : ValueId := C.cert.zero

def comps (C : Ctx) : List ValueId := C.cert.pairs.flatMap fun (_, a, b) => [a, b]

/-- A value of `g` that is the image of no value of `f`: temporaries, pads. -/
def fresh (C : Ctx) (t : ValueId) : Bool :=
  decide (C.T0 ≤ t) && t != C.zero && !C.comps.contains t

/-- A non-`i128` value (its image is itself). -/
def plain (C : Ctx) (v : ValueId) : Bool := (C.pair v).isNone

end Ctx

/-! ## Canonical patterns

Canonical ids: inputs `0 ..< nIn`, outputs `nIn ..< nIn + nOut`, temporaries after. The
statement order is the legaliser's emission order (`Opt.Legalize128`). -/

/-- `r = inst` -/
def S (r : ValueId) (i : Inst) : Stmt := { results := [r], inst := i }

/-- `r = iconst.i64 n` (`kI64`) -/
def K (r : ValueId) (n : Int) : Stmt := S r (.iconst .i64 (BitVec.ofInt 64 n))

def bin (op : BinaryOp) (t : Ty) (x y : ValueId) : Inst := .binary op t x y

namespace Pat

/-! ### Conditions: an `i128` condition is `(lo != 0) | (hi != 0)` -/

/-- `condOf` (inputs `lo hi` = `0 1`, output `c` = `2`). -/
def cond : List Stmt :=
  [K 3 0, S 4 (.icmp .ne .i64 0 3), S 5 (.icmp .ne .i64 1 3), S 2 (bin .bor .i8 4 5)]

/-! ### Unary (inputs `xl xh` = `0 1`, outputs `rl rh` = `2 3`) -/

def unary : UnaryOp → List Stmt
  | .bnot => [S 2 (.unary .bnot .i64 0), S 3 (.unary .bnot .i64 1)]
  | .ineg => [K 4 (-1), K 5 1, S 6 (bin .bxor .i64 0 4), S 7 (bin .bxor .i64 1 4),
      S 2 (bin .iadd .i64 6 5), S 8 (.icmp .eq .i64 6 4), S 9 (.extend .uextend .i64 8),
      S 3 (bin .iadd .i64 7 9)]
  | .iabs => [K 4 0, S 5 (.icmp .slt .i64 1 4), K 6 (-1), K 7 1, S 8 (bin .bxor .i64 0 6),
      S 9 (bin .bxor .i64 1 6), S 10 (bin .iadd .i64 8 7), S 11 (.icmp .eq .i64 8 6),
      S 12 (.extend .uextend .i64 11), S 13 (bin .iadd .i64 9 12),
      S 2 (.select .i64 5 10 0), S 3 (.select .i64 5 13 1)]
  | .clz => [K 4 0, S 5 (.icmp .ne .i64 1 4), S 6 (.unary .clz .i64 1),
      S 7 (.unary .clz .i64 0), K 8 64, S 9 (bin .iadd .i64 8 7), S 2 (.select .i64 5 6 9),
      S 3 (.iconst .i64 (BitVec.ofInt 64 0))]
  | .ctz => [K 4 0, S 5 (.icmp .ne .i64 0 4), S 6 (.unary .ctz .i64 0),
      S 7 (.unary .ctz .i64 1), K 8 64, S 9 (bin .iadd .i64 8 7), S 2 (.select .i64 5 6 9),
      S 3 (.iconst .i64 (BitVec.ofInt 64 0))]
  | .cls => [K 4 1, S 5 (bin .ushr .i64 0 4), K 6 63, S 7 (bin .ishl .i64 1 6),
      S 8 (bin .bor .i64 5 7), S 9 (bin .sshr .i64 1 4), S 10 (bin .bxor .i64 0 8),
      S 11 (bin .bxor .i64 1 9), K 12 0, S 13 (.icmp .ne .i64 11 12),
      S 14 (.unary .clz .i64 11), S 15 (.unary .clz .i64 10), K 16 64,
      S 17 (bin .iadd .i64 16 15), S 18 (.select .i64 13 14 17), S 2 (bin .isub .i64 18 4),
      S 3 (.iconst .i64 (BitVec.ofInt 64 0))]
  | .popcnt => [S 4 (.unary .popcnt .i64 0), S 5 (.unary .popcnt .i64 1),
      S 2 (bin .iadd .i64 4 5), S 3 (.iconst .i64 (BitVec.ofInt 64 0))]
  | .bitrev => [S 2 (.unary .bitrev .i64 1), S 3 (.unary .bitrev .i64 0)]
  | .bswap => [S 2 (.unary .bswap .i64 1), S 3 (.unary .bswap .i64 0)]

/-! ### Binary (inputs `xl xh yl yh` = `0 1 2 3`, outputs `rl rh` = `4 5`) -/

/-- `cmpPair cc` (strict `x < y`, result in `r`). -/
def cmp (cc : IntCC) (r : ValueId) (t : ValueId) : List Stmt :=
  [S t (.icmp cc .i64 1 3), S (t + 1) (.icmp .eq .i64 1 3), S (t + 2) (.icmp .ult .i64 0 2),
   S (t + 3) (bin .band .i8 (t + 1) (t + 2)), S r (bin .bor .i8 t (t + 3))]

/-- `binary op` at `i128`, `none` for the operations `Opt.Legalize128` does not legalise. -/
def binary : BinaryOp → Option (List Stmt)
  | .band => some [S 4 (bin .band .i64 0 2), S 5 (bin .band .i64 1 3)]
  | .bor => some [S 4 (bin .bor .i64 0 2), S 5 (bin .bor .i64 1 3)]
  | .bxor => some [S 4 (bin .bxor .i64 0 2), S 5 (bin .bxor .i64 1 3)]
  | .iadd => some [S 4 (bin .iadd .i64 0 2), S 6 (.icmp .ult .i64 4 0),
      S 7 (.extend .uextend .i64 6), S 8 (bin .iadd .i64 1 3), S 5 (bin .iadd .i64 8 7)]
  | .isub => some [S 4 (bin .isub .i64 0 2), S 6 (.icmp .ult .i64 0 4),
      S 7 (.extend .uextend .i64 6), S 8 (bin .isub .i64 1 3), S 5 (bin .isub .i64 8 7)]
  | .imul => some [S 4 (bin .imul .i64 0 2), S 6 (bin .imul .i64 0 3),
      S 7 (bin .imul .i64 1 2), S 8 (bin .iadd .i64 6 7), S 9 (bin .umulhi .i64 0 2),
      S 5 (bin .iadd .i64 8 9)]
  | .smin => some (cmp .slt 6 7 ++ [S 4 (.select .i64 6 0 2), S 5 (.select .i64 6 1 3)])
  | .umin => some (cmp .ult 6 7 ++ [S 4 (.select .i64 6 0 2), S 5 (.select .i64 6 1 3)])
  | .smax => some (cmp .slt 6 7 ++ [S 4 (.select .i64 6 2 0), S 5 (.select .i64 6 3 1)])
  | .umax => some (cmp .ult 6 7 ++ [S 4 (.select .i64 6 2 0), S 5 (.select .i64 6 3 1)])
  | _ => none

/-! ### `icmp` at `i128` (inputs `xl xh yl yh` = `0 1 2 3`, output `r` = `4`) -/

def icmp (cc : IntCC) : List Stmt :=
  if cc == .eq || cc == .ne then
    [S 5 (.icmp cc .i64 1 3), S 6 (.icmp cc .i64 0 2),
     S 4 (bin (if cc == .eq then .band else .bor) .i8 5 6)]
  else
    let swap : Bool := cc == .sgt || cc == .sge || cc == .ugt || cc == .uge
    let strict : IntCC :=
      if cc == .slt || cc == .sle || cc == .sgt || cc == .sge then .slt else .ult
    let nonstrict : IntCC :=
      if cc == .sle || cc == .sge || cc == .ule || cc == .uge then .ule else .ult
    let (axl, axh, ayl, ayh) : ValueId × ValueId × ValueId × ValueId :=
      if swap then (2, 3, 0, 1) else (0, 1, 2, 3)
    [S 5 (.icmp strict .i64 axh ayh), S 6 (.icmp .eq .i64 axh ayh),
     S 7 (.icmp nonstrict .i64 axl ayl), S 8 (bin .band .i8 6 7), S 4 (bin .bor .i8 5 8)]

/-! ### Selects -/

/-- `select` at `i128`, `i128` condition (inputs `cl ch xl xh yl yh` = `0..5`, outputs
`rl rh` = `6 7`). -/
def select128c : List Stmt :=
  [K 8 0, S 9 (.icmp .ne .i64 0 8), S 10 (.icmp .ne .i64 1 8), S 11 (bin .bor .i8 9 10),
   S 6 (.select .i64 11 2 4), S 7 (.select .i64 11 3 5)]

/-- `select` at `i128`, narrow condition (inputs `c xl xh yl yh` = `0..4`, outputs `5 6`). -/
def select128 : List Stmt := [S 5 (.select .i64 0 1 3), S 6 (.select .i64 0 2 4)]

/-- A narrow `select` with an `i128` condition (inputs `cl ch x y` = `0..3`, output `4`). -/
def selectc (t : Ty) : List Stmt :=
  [K 5 0, S 6 (.icmp .ne .i64 0 5), S 7 (.icmp .ne .i64 1 5), S 8 (bin .bor .i8 6 7),
   S 4 (.select t 8 2 3)]

/-- `bitselect` at `i128` (inputs `cl ch xl xh yl yh` = `0..5`, outputs `6 7`). -/
def bitselect : List Stmt :=
  [S 8 (.unary .bnot .i64 0), S 9 (.unary .bnot .i64 1), S 10 (bin .band .i64 0 2),
   S 11 (bin .band .i64 8 4), S 6 (bin .bor .i64 10 11), S 12 (bin .band .i64 1 3),
   S 13 (bin .band .i64 9 5), S 7 (bin .bor .i64 12 13)]

/-! ### `bmask` (`bmaskEmit r t c`: all-ones or zero by a select on `c`) -/

def bmaskEmit (r : ValueId) (t : Ty) (c : ValueId) (m z : ValueId) : List Stmt :=
  [S m (.iconst t (BitVec.ofInt t.width (-1))), S z (.iconst t (BitVec.ofInt t.width 0)),
   S r (.select t c m z)]

/-- `bmask.i128` of an `i128` value (inputs `xl xh` = `0 1`, outputs `2 3`). -/
def bmask128c : List Stmt :=
  [K 4 0, S 5 (.icmp .ne .i64 0 4), S 6 (.icmp .ne .i64 1 4), S 7 (bin .bor .i8 5 6)] ++
    bmaskEmit 2 .i64 7 8 9 ++ bmaskEmit 3 .i64 7 10 11

/-- `bmask.i128` of a narrow value (input `x` = `0`, outputs `1 2`). -/
def bmask128 : List Stmt := bmaskEmit 1 .i64 0 3 4 ++ bmaskEmit 2 .i64 0 5 6

/-- A narrow `bmask.t` of an `i128` value (inputs `xl xh` = `0 1`, output `2`). -/
def bmaskc (t : Ty) : List Stmt :=
  [K 3 0, S 4 (.icmp .ne .i64 0 3), S 5 (.icmp .ne .i64 1 3), S 6 (bin .bor .i8 4 5)] ++
    bmaskEmit 2 t 6 7 8

/-! ### Width changes and copies -/

/-- `extend op .i128 x` with `x : w` (input `x` = `0`, outputs `1 2`). -/
def extend (op : ExtendOp) (w64 : Bool) : List Stmt :=
  let lo : Inst := if w64 then bin .bor .i64 0 0 else .extend op .i64 0
  match op with
  | .uextend => [S 1 lo, S 2 (.iconst .i64 (BitVec.ofInt 64 0))]
  | .sextend => [S 1 lo, K 3 63, S 2 (bin .sshr .i64 1 3)]

/-- `ireduce.t` of an `i128` value (input `xl` = `0`, output `1`). -/
def ireduce (t : Ty) : List Stmt :=
  [S 1 (if t == .i64 then bin .bor .i64 0 0 else .ireduce t 0)]

/-- Two copies (`iconcat`, `isplit`, `bitcast.i128`; inputs `0 1`, outputs `2 3`). -/
def copy2 : List Stmt := [S 2 (bin .bor .i64 0 0), S 3 (bin .bor .i64 1 1)]

/-! ### Shifts and rotates -/

/-- A narrow shift by an `i128` amount (inputs `x yl` = `0 1`, output `2`). -/
def shiftNarrow (op : BinaryOp) (t : Ty) : List Stmt :=
  [S 3 (.iconst .i64 (BitVec.ofNat 64 (t.width - 1))), S 4 (bin .band .i64 1 3),
   S 2 (bin op t 0 4)]

/-- `constShift op n` (`op` normalised: `rotr` is `rotl`; inputs `xl xh` = `0 1`, outputs
`rl rh` = `2 3`). -/
def constShift (op : BinaryOp) (n : Nat) : List Stmt :=
  match op with
  | .ishl =>
    if n < 64 then
      if n == 0 then [K 4 n, S 2 (bin .ishl .i64 0 4), K 5 n, S 3 (bin .ishl .i64 1 5)]
      else [K 4 n, S 2 (bin .ishl .i64 0 4), K 5 n, S 6 (bin .ishl .i64 1 5),
        K 7 (64 - n : Nat), S 8 (bin .ushr .i64 0 7), S 3 (bin .bor .i64 6 8)]
    else [S 2 (.iconst .i64 (BitVec.ofInt 64 0)), K 4 (n - 64 : Nat),
      S 3 (bin .ishl .i64 0 4)]
  | .ushr =>
    if n < 64 then
      if n == 0 then [K 4 n, S 3 (bin .ushr .i64 1 4), K 5 n, S 2 (bin .ushr .i64 0 5)]
      else [K 4 n, S 3 (bin .ushr .i64 1 4), K 5 n, S 6 (bin .ushr .i64 0 5),
        K 7 (64 - n : Nat), S 8 (bin .ishl .i64 1 7), S 2 (bin .bor .i64 6 8)]
    else [S 3 (.iconst .i64 (BitVec.ofInt 64 0)), K 4 (n - 64 : Nat),
      S 2 (bin .ushr .i64 1 4)]
  | .sshr =>
    if n < 64 then
      if n == 0 then [K 4 n, S 3 (bin .sshr .i64 1 4), K 5 n, S 2 (bin .ushr .i64 0 5)]
      else [K 4 n, S 3 (bin .sshr .i64 1 4), K 5 n, S 6 (bin .ushr .i64 0 5),
        K 7 (64 - n : Nat), S 8 (bin .ishl .i64 1 7), S 2 (bin .bor .i64 6 8)]
    else [K 4 63, S 3 (bin .sshr .i64 1 4), K 5 (n - 64 : Nat), S 2 (bin .sshr .i64 1 5)]
  | _ =>
    if n < 64 then
      if n == 0 then [K 4 n, S 2 (bin .ishl .i64 0 4), K 5 n, S 3 (bin .ishl .i64 1 5)]
      else [K 4 n, S 6 (bin .ishl .i64 0 4), K 5 n, S 7 (bin .ishl .i64 1 5),
        K 8 (64 - n : Nat), S 9 (bin .ushr .i64 1 8), K 10 (64 - n : Nat),
        S 11 (bin .ushr .i64 0 10), S 2 (bin .bor .i64 6 9), S 3 (bin .bor .i64 7 11)]
    else
      let m := n - 64
      if m == 0 then [K 4 m, S 2 (bin .ishl .i64 1 4), K 5 m, S 3 (bin .ishl .i64 0 5)]
      else [K 4 m, S 6 (bin .ishl .i64 1 4), K 5 m, S 7 (bin .ishl .i64 0 5),
        K 8 (64 - m : Nat), S 9 (bin .ushr .i64 0 8), K 10 (64 - m : Nat),
        S 11 (bin .ushr .i64 1 10), S 2 (bin .bor .i64 6 9), S 3 (bin .bor .i64 7 11)]

/-- How a variable amount is made an `i64` in `[0, 128)`: from the low half of an `i128`
amount / an `i64` amount (`band a, 127`), or a narrower one (`uextend` first). -/
inductive AmtKind where
  | wide
  | narrow
  deriving DecidableEq, Repr

/-- The amount prefix of a variable shift (input amount `a` = `2`; the rotate amount in
`r`, temporaries from `t`): `amt128` for a variable amount. Returns the statements, the
amount value and the next temporary. -/
def amt (k : AmtKind) (rotr : Bool) (t : ValueId) : List Stmt × ValueId × ValueId :=
  let (pre, a, t) : List Stmt × ValueId × ValueId :=
    match k with
    | .wide => ([K t 127, S (t + 1) (bin .band .i64 2 t)], t + 1, t + 2)
    | .narrow => ([S t (.extend .uextend .i64 2), K (t + 1) 127,
        S (t + 2) (bin .band .i64 t (t + 1))], t + 2, t + 3)
  if rotr then
    (pre ++ [K t 0, S (t + 1) (.icmp .eq .i64 a t), K (t + 2) 128,
      S (t + 3) (bin .isub .i64 (t + 2) a), S (t + 4) (.select .i64 (t + 1) a (t + 3))],
     t + 4, t + 5)
  else (pre, a, t)

/-- `crossVar sh nz b s` (result `t + 3`). -/
def cross (sh : BinaryOp) (nz b s t : ValueId) : List Stmt :=
  [K t 64, S (t + 1) (bin .isub .i64 t s), S (t + 2) (bin sh .i64 b (t + 1)),
   K (t + 4) 0, S (t + 3) (.select .i64 nz (t + 2) (t + 4))]

/-- `shiftVars amt` then `varShift op` (inputs `xl xh` = `0 1`, outputs `rl rh` = `3 4`,
amount `a`, temporaries from `t`). -/
def varShift (op : BinaryOp) (a t : ValueId) : List Stmt :=
  let s := t + 1
  let big := t + 3
  let nz := t + 5
  let vars := [K t 63, S s (bin .band .i64 a t), K (t + 2) 64, S big (.icmp .uge .i64 a (t + 2)),
    K (t + 4) 0, S nz (.icmp .ne .i64 s (t + 4))]
  let u := t + 6
  vars ++ match op with
  | .ishl =>
    [S u (bin .ishl .i64 0 s), S (u + 1) (bin .ishl .i64 1 s)] ++ cross .ushr nz 0 s (u + 2) ++
      [S (u + 7) (bin .bor .i64 (u + 1) (u + 5)), K (u + 8) 0,
       S 3 (.select .i64 big (u + 8) u), S 4 (.select .i64 big u (u + 7))]
  | .ushr =>
    [S u (bin .ushr .i64 1 s), S (u + 1) (bin .ushr .i64 0 s)] ++ cross .ishl nz 1 s (u + 2) ++
      [S (u + 7) (bin .bor .i64 (u + 1) (u + 5)), K (u + 8) 0,
       S 3 (.select .i64 big u (u + 7)), S 4 (.select .i64 big (u + 8) u)]
  | .sshr =>
    [S u (bin .sshr .i64 1 s), S (u + 1) (bin .ushr .i64 0 s)] ++ cross .ishl nz 1 s (u + 2) ++
      [S (u + 7) (bin .bor .i64 (u + 1) (u + 5)), K (u + 8) 63,
       S (u + 9) (bin .sshr .i64 1 (u + 8)),
       S 3 (.select .i64 big u (u + 7)), S 4 (.select .i64 big (u + 9) u)]
  | _ =>
    [S u (bin .ishl .i64 0 s), S (u + 1) (bin .ishl .i64 1 s)] ++
      cross .ushr nz 1 s (u + 2) ++ cross .ushr nz 0 s (u + 7) ++
      [S (u + 12) (bin .bor .i64 u (u + 5)), S (u + 13) (bin .bor .i64 (u + 1) (u + 10)),
       S 3 (.select .i64 big (u + 13) (u + 12)), S 4 (.select .i64 big (u + 12) (u + 13))]

/-- A variable-amount shift at `i128` (inputs `xl xh a` = `0 1 2`, outputs `3 4`). -/
def varShiftFull (op0 : BinaryOp) (k : AmtKind) : List Stmt :=
  let (pre, a, t) := amt k (op0 == .rotr) 5
  pre ++ varShift (if op0 == .rotr then .rotl else op0) a t

end Pat

/-! ## Statement plans -/

/-- How a statement of `f` is rewritten (`planOf`). -/
inductive Plan where
  /-- The statement itself. -/
  | same
  /-- An instance of a canonical pure pattern. -/
  | pure (pat : List Stmt) (ins outs : List ValueId)
  /-- Two `i64` loads at `+0`/`+8`. -/
  | load (rl rh p : ValueId) (flags : MemFlags) (off : Int)
  /-- Two `i64` stores at `+0`/`+8`. -/
  | store (xl xh p : ValueId) (flags : MemFlags) (off : Int)
  /-- A call of the `__*ti3` helper. -/
  | div (op : DivOp) (xl xh yl yh rl rh : ValueId)
  /-- A call with its arguments/results expanded by the ABI groups. -/
  | call (fn : FnRef) (e : ExtFunc) (args : List ValueId) (rg : List (List SlotEl))
      (results : List ValueId)
  /-- A pure condition pattern, then `trapz`/`trapnz` (`nz`) on its result. -/
  | trap (lo hi : ValueId) (nz : Bool) (code : TrapCode)
  /-- A `call_indirect` without `i128` operands or results: the statement itself, with the same
  call-site signature in `g`. -/
  | callInd

namespace Plan

/-- The length of the segment of a plan. -/
def len : Plan → Nat
  | .same => 1
  | .pure pat _ _ => pat.length
  | .load .. => 2
  | .store .. => 2
  | .div .. => 1
  | .call .. => 1
  | .trap .. => Pat.cond.length + 1
  | .callInd => 1

end Plan

/-- The ABI groups of a signature's parameters/returns. -/
def groups (ps : List AbiParam) : Option (List (List SlotEl)) := (expandGroups ps).toOption

/-- The expanded signature. -/
def sigExp (s : Signature) : Option Signature := (expandSig s).toOption

/-- The values passed for the arguments `vs` by the groups `gs` (`argsOf`). -/
def expandArgs (C : Ctx) : List (List SlotEl) → List ValueId → Option (List ValueId)
  | [], [] => some []
  | [.val _] :: gs, v :: vs => if C.plain v then (v :: ·) <$> expandArgs C gs vs else none
  | [.lo, .hi] :: gs, v :: vs =>
    match C.pair v with
    | some (a, b) => ([a, b] ++ ·) <$> expandArgs C gs vs
    | none => none
  | [.pad, .lo, .hi] :: gs, v :: vs =>
    match C.pair v with
    | some (a, b) => ([C.zero, a, b] ++ ·) <$> expandArgs C gs vs
    | none => none
  | _, _ => none

/-- The results of an expanded call are those of the source by the groups `rg` (`retsOf`;
pads are fresh values of `g`). -/
def retsOk (C : Ctx) : List (List SlotEl) → List ValueId → List ValueId → Bool
  | [], [], [] => true
  | [.val _] :: gs, r :: rs, r' :: rs' => C.plain r && r' == r && retsOk C gs rs rs'
  | [.lo, .hi] :: gs, r :: rs, a :: b :: rs' =>
    C.pair r == some (a, b) && retsOk C gs rs rs'
  | [.pad, .lo, .hi] :: gs, r :: rs, w :: a :: b :: rs' =>
    C.fresh w && C.pair r == some (a, b) && retsOk C gs rs rs'
  | _, _, _ => false

/-- The shift amount of a constant shift, if the amount is a known constant (`amt128`). -/
def constAmt (C : Ctx) (y : ValueId) : Option Nat :=
  if C.plain y then (· % 128) <$> constOf C.f y else (· % 128) <$> concatConst C.f y

/-- The plan of a statement of `f` (mirrors `Opt.Legalize128.rewriteStmt`). -/
def planOf (C : Ctx) (s : Stmt) : Option Plan :=
  let P := C.pair
  let same : Option Plan :=
    if (instOps s.inst ++ s.results).all C.plain then some .same else none
  match s.inst, s.results with
  | .unary op .i128 x, [r] => do
    let (xl, xh) ← P x
    let (rl, rh) ← P r
    some (.pure (Pat.unary op) [xl, xh] [rl, rh])
  | .binary op .i128 x y, [r] => do
    let (xl, xh) ← P x
    let (rl, rh) ← P r
    if op.isShift then
      let op' : BinaryOp := if op == .rotr then .rotl else op
      match constAmt C y with
      | some n =>
        let n' := if op == .rotr then (128 - n) % 128 else n
        some (.pure (Pat.constShift op' n') [xl, xh] [rl, rh])
      | none =>
        match P y with
        | some (yl, _) => some (.pure (Pat.varShiftFull op .wide) [xl, xh, yl] [rl, rh])
        | none =>
          match tyOf C.f y with
          | some .i64 => some (.pure (Pat.varShiftFull op .wide) [xl, xh, y] [rl, rh])
          | some .i8 | some .i16 | some .i32 =>
            some (.pure (Pat.varShiftFull op .narrow) [xl, xh, y] [rl, rh])
          | _ => none
    else
      let (yl, yh) ← P y
      let pat ← Pat.binary op
      some (.pure pat [xl, xh, yl, yh] [rl, rh])
  | .binary op t x y, [r] =>
    match P y with
    | some (yl, _) =>
      if op.isShift && t != .i128 && C.plain x && C.plain r then
        some (.pure (Pat.shiftNarrow op t) [x, yl] [r])
      else none
    | none => same
  | .div op .i128 x y, [r] => do
    let (xl, xh) ← P x
    let (yl, yh) ← P y
    let (rl, rh) ← P r
    some (.div op xl xh yl yh rl rh)
  | .icmp cc .i128 x y, [r] => do
    let (xl, xh) ← P x
    let (yl, yh) ← P y
    if C.plain r then some (.pure (Pat.icmp cc) [xl, xh, yl, yh] [r]) else none
  | .select .i128 c x y, [r] | .selectSpectreGuard .i128 c x y, [r] => do
    let (xl, xh) ← P x
    let (yl, yh) ← P y
    let (rl, rh) ← P r
    match P c with
    | some (cl, ch) => some (.pure Pat.select128c [cl, ch, xl, xh, yl, yh] [rl, rh])
    | none => some (.pure Pat.select128 [c, xl, xh, yl, yh] [rl, rh])
  | .select t c x y, [r] | .selectSpectreGuard t c x y, [r] =>
    match P c with
    | some (cl, ch) =>
      if t != .i128 && C.plain x && C.plain y && C.plain r then
        some (.pure (Pat.selectc t) [cl, ch, x, y] [r])
      else none
    | none => same
  | .bitselect .i128 c x y, [r] => do
    let (cl, ch) ← P c
    let (xl, xh) ← P x
    let (yl, yh) ← P y
    let (rl, rh) ← P r
    some (.pure Pat.bitselect [cl, ch, xl, xh, yl, yh] [rl, rh])
  | .bmask .i128 x, [r] => do
    let (rl, rh) ← P r
    match P x with
    | some (xl, xh) => some (.pure Pat.bmask128c [xl, xh] [rl, rh])
    | none => some (.pure Pat.bmask128 [x] [rl, rh])
  | .bmask t x, [r] =>
    match P x with
    | some (xl, xh) => if C.plain r then some (.pure (Pat.bmaskc t) [xl, xh] [r]) else none
    | none => same
  | .extend op .i128 x, [r] => do
    let (rl, rh) ← P r
    if C.plain x then
      match tyOf C.f x with
      | some .i64 => some (.pure (Pat.extend op true) [x] [rl, rh])
      | some .i8 | some .i16 | some .i32 => some (.pure (Pat.extend op false) [x] [rl, rh])
      | _ => none
    else none
  | .ireduce t x, [r] =>
    match P x with
    | some (xl, _) => if C.plain r then some (.pure (Pat.ireduce t) [xl] [r]) else none
    | none => same
  | .iconcat .i64 lo hi, [r] => do
    let (rl, rh) ← P r
    if C.plain lo && C.plain hi then some (.pure Pat.copy2 [lo, hi] [rl, rh]) else none
  | .isplit .i128 x, [r0, r1] => do
    let (xl, xh) ← P x
    if C.plain r0 && C.plain r1 then some (.pure Pat.copy2 [xl, xh] [r0, r1]) else none
  | .bitcast .i128 _ x, [r] => do
    let (xl, xh) ← P x
    let (rl, rh) ← P r
    some (.pure Pat.copy2 [xl, xh] [rl, rh])
  | .load .load .i128 flags p off, [r] => do
    let (rl, rh) ← P r
    if C.plain p && flags.endianness != some .big then some (.load rl rh p flags off)
    else none
  | .store .store .i128 flags x p off, [] => do
    let (xl, xh) ← P x
    if C.plain p && flags.endianness != some .big then some (.store xl xh p flags off)
    else none
  | .call fn args, rs => do
    let e ← C.f.extern? fn
    let gs ← groups e.sig.params
    let rg ← groups e.sig.returns
    let args' ← expandArgs C gs args
    some (.call fn e args' rg rs)
  | .trapz c code, [] =>
    match P c with
    | some (lo, hi) => some (.trap lo hi false code)
    | none => same
  | .trapnz c code, [] =>
    match P c with
    | some (lo, hi) => some (.trap lo hi true code)
    | none => same
  | .callIndirect _ callee args, rs =>
    if (callee :: args ++ rs).all C.plain then some .callInd else none
  | .funcAddr _ fn, _ =>
    -- the address of the declaration's symbol: the same name in `g` (`sigExp` keeps names)
    if (C.g.extern? fn).map (·.name) == (C.f.extern? fn).map (·.name) then same else none
  | .unary _ .i128 _, _ | .binary _ .i128 _ _, _
  | .div _ .i128 _ _, _ | .icmp _ .i128 _ _, _ | .bitselect .i128 _ _ _, _
  | .select .i128 _ _ _, _ | .selectSpectreGuard .i128 _ _ _, _ | .bmask .i128 _, _
  | .extend _ .i128 _, _ | .iconcat .., _ | .isplit .., _ | .bitcast .i128 _ _, _
  | .load _ .i128 _ _ _, _ | .store _ .i128 _ _ _ _, _ | .iconst .i128 _, _
  | .stackAddr .i128 _ _, _ | .symbolValue .i128 _, _ => none
  | _, _ => same

/-! ## Segment checks -/

/-- The canonical ids a pattern writes. -/
def written (pat : List Stmt) : List ValueId := pat.flatMap (·.results)

/-- The temporaries of a pattern instance, read off the segment by position. -/
def guessTemps (n : Nat) (pat seg : List Stmt) : List (ValueId × ValueId) :=
  (pat.zip seg).flatMap fun (p, t) => (p.results.zip t.results).filter (n ≤ ·.1)

/-- The renaming of a pattern instance. -/
def sigma (ins outs : List ValueId) (tm : List (ValueId × ValueId)) (c : ValueId) : ValueId :=
  if h : c < ins.length then ins[c]
  else if h2 : c - ins.length < outs.length then outs[c - ins.length]
  else (tm.lookup c).getD c

/-- `seg` is an instance of the pure pattern `pat` with inputs `ins` and outputs `outs`: the
renaming is injective on the ids the pattern writes (and distinct from the inputs), the
pattern writes no input, and temporaries are renamed to fresh values. -/
def pureOk (C : Ctx) (pat : List Stmt) (ins outs : List ValueId) (seg : List Stmt) : Bool :=
  let n := ins.length + outs.length
  let σ := sigma ins outs (guessTemps n pat seg)
  let w := written pat
  let used := List.range ins.length ++ w
  seg == pat.map (renameStmt σ) &&
  pat.all (fun st => pureInst st.inst && st.results.length == 1) &&
  w.all (fun c => decide (ins.length ≤ c)) &&
  w.all (fun c => used.all fun d => c == d || σ c != σ d) &&
  w.all (fun c => decide (c < n) || C.fresh (σ c))

/-- The helper declaration a `div` at `i128` calls. -/
def helperExt (op : DivOp) : ExtFunc := { name := divHelper op, sig := helperSig }

/-- The segment of a statement matches its plan. -/
def segOk (C : Ctx) (s : Stmt) : Plan → List Stmt → Bool
  | .same, seg => seg == [s]
  | .pure pat ins outs, seg => pureOk C pat ins outs seg
  | .load rl rh p fl off, seg =>
    seg == [S rl (.load .load .i64 fl p off), S rh (.load .load .i64 fl p (off + 8))] &&
      rl != rh && rl != p
  | .store xl xh p fl off, seg =>
    seg == [{ results := [], inst := .store .store .i64 fl xl p off },
            { results := [], inst := .store .store .i64 fl xh p (off + 8) }]
  | .div op xl xh yl yh rl rh, [st] =>
    match st.inst with
    | .call fn args =>
      args == [xl, xh, yl, yh] && st.results == [rl, rh] && rl != rh &&
        C.g.extern? fn == some (helperExt op)
    | _ => false
  | .call fn e args rg rs, [st] =>
    st.inst == .call fn args && retsOk C rg rs st.results && decide st.results.Nodup &&
      (match sigExp e.sig with
       | some s' => C.g.extern? fn == some { e with sig := s' }
       | none => false)
  | .callInd, seg =>
    seg == [s] && match s.inst with
      | .callIndirect sig _ _ => C.g.sigDecls.lookup sig == C.f.sigDecls.lookup sig
      | _ => false
  | .trap lo hi nz code, seg =>
    match seg.getLast? with
    | some { results := [], inst := .trapz c code' } =>
      !nz && code' == code && C.fresh c && pureOk C Pat.cond [lo, hi] [c] seg.dropLast
    | some { results := [], inst := .trapnz c code' } =>
      nz && code' == code && C.fresh c && pureOk C Pat.cond [lo, hi] [c] seg.dropLast
    | _ => false
  | _, _ => false

/-- The id of the entry block of `f`. -/
def Ctx.entryId? (C : Ctx) : Option BlockId := C.f.entry?.map (·.id)

/-- The arguments of a branch to a block with parameters `ps` (`rewriteBC`). -/
def expandBC (C : Ctx) : List ValueId → List (ValueId × Ty) → Option (List ValueId)
  | [], [] => some []
  | v :: vs, (_, t) :: ps =>
    if t == .i128 then
      match C.pair v with
      | some (a, b) => ([a, b] ++ ·) <$> expandBC C vs ps
      | none => none
    else if C.plain v then (v :: ·) <$> expandBC C vs ps else none
  | _, _ => none

/-- The first expanded slot of return group `i` (`Legalize128.rewriteTryDest`'s `starts`). -/
def groupStart (rg : List (List SlotEl)) (i : Nat) : Nat := ((rg.take i).map (·.length)).sum

/-- The arguments of a `try_call`'s normal-return successor with parameters `ps`, the call's
return groups `rg` (`Legalize128.rewriteTryDest`): an `i128` value as its pair, the `i128`
return `retN` as the two slots of its pair (after a pad), other returns at their slot; no
exception payloads (`Clif.tryNormal` is stuck on them). -/
def expandTry (C : Ctx) (rg : List (List SlotEl)) :
    List TryArg → List (ValueId × Ty) → Option (List TryArg)
  | [], [] => some []
  | .val v :: as, (_, t) :: ps =>
    if t == .i128 then
      match C.pair v with
      | some (a, b) => ([.val a, .val b] ++ ·) <$> expandTry C rg as ps
      | none => none
    else if C.plain v then (.val v :: ·) <$> expandTry C rg as ps else none
  | .ret i :: as, (_, t) :: ps =>
    match rg[i]? with
    | some [.val _] =>
      if t != .i128 then (.ret (groupStart rg i) :: ·) <$> expandTry C rg as ps else none
    | some [.lo, .hi] =>
      if t == .i128 then
        ([.ret (groupStart rg i), .ret (groupStart rg i + 1)] ++ ·) <$> expandTry C rg as ps
      else none
    | some [.pad, .lo, .hi] =>
      if t == .i128 then
        ([.ret (groupStart rg i + 1), .ret (groupStart rg i + 2)] ++ ·) <$> expandTry C rg as ps
      else none
    | _ => none
  | _, _ => none

/-- A branch of `f` and its rewrite: same target (never the entry block), arguments split. -/
def bcOk (C : Ctx) (bc bc' : BlockCall) : Bool :=
  bc'.block == bc.block && C.entryId? != some bc.block &&
    match C.f.block? bc.block with
    | some B => expandBC C bc.args B.params == some bc'.args
    | none => false

/-- A terminator of `f`, and the condition statements and terminator of `g`. -/
def termOk (C : Ctx) : Terminator → List Stmt → Terminator → Bool
  | .jump bc, ts, .jump bc' => ts.isEmpty && bcOk C bc bc'
  | .brif c t e, ts, .brif c' t' e' =>
    bcOk C t t' && bcOk C e e' &&
      match C.pair c with
      | some (lo, hi) => C.fresh c' && pureOk C Pat.cond [lo, hi] [c'] ts
      | none => ts.isEmpty && c' == c && C.plain c
  | .brTable x d tbl, ts, .brTable x' d' tbl' =>
    ts.isEmpty && x' == x && C.plain x && bcOk C d d' && tbl.length == tbl'.length &&
      (tbl.zip tbl').all fun (a, b) => bcOk C a b
  | .ret vs, ts, .ret vs' =>
    ts.isEmpty &&
      match groups C.f.sig.returns with
      | some rg => expandArgs C rg vs == some vs'
      | none => false
  | .trap c, ts, .trap c' => ts.isEmpty && c' == c
  | .tryCall fn args et, ts, .tryCall fn' args' et' =>
    -- as `call`: arguments and returns expanded by the callee's groups; the normal-return
    -- successor's arguments by `expandTry`; the results' fresh values (`Clif.tryNormal`, at
    -- `freshValue`) are above every value of `f` and, in `g`, above every value `g` defines,
    -- the pad zero and the pairs (so the call's results never overwrite a related value)
    ts.isEmpty && fn' == fn && et'.sig == et.sig && et'.normal.block == et.normal.block &&
      C.entryId? != some et.normal.block &&
      decide (C.T0 ≤ C.f.freshValue) && decide (C.T0 ≤ C.g.freshValue) &&
      decide (C.zero < C.g.freshValue) && C.comps.all (fun a => decide (a < C.g.freshValue)) &&
      match C.f.extern? fn, C.g.sigDecls.lookup et.sig, C.f.block? et.normal.block with
      | some e, some d', some B =>
        match sigExp e.sig, groups e.sig.params, groups e.sig.returns with
        | some s', some gs, some rg =>
          C.g.extern? fn == some { e with sig := s' } &&
            AbiParam.tys d'.params == AbiParam.tys s'.params &&
            AbiParam.tys d'.returns == AbiParam.tys s'.returns &&
            expandArgs C gs args == some args' &&
            expandTry C rg et.normal.args B.params == some et'.normal.args
        | _, _, _ => false
      | _, _, _ => false
  | _, _, _ => false

/-- Statements `ss` and terminator `t` of `f` against statements `ts` and terminator `t'` of
`g`. -/
def codeOk (C : Ctx) : List Stmt → Terminator → List Stmt → Terminator → Bool
  | [], t, ts, t' => termOk C t ts t'
  | s :: ss, t, ts, t' =>
    match planOf C s with
    | some pl => segOk C s pl (ts.take pl.len) && codeOk C ss t (ts.drop pl.len) t'
    | none => false

/-- The parameters of the entry block (`paramsOf` of the signature's groups). -/
def entryParamsOk (C : Ctx) : List (List SlotEl) → List (ValueId × Ty) → List (ValueId × Ty) →
    Bool
  | [], [], [] => true
  | [.val p] :: gs, (v, t) :: ps, (v', t') :: ps' =>
    v' == v && t' == t && t == p.ty && C.plain v && entryParamsOk C gs ps ps'
  | [.lo, .hi] :: gs, (v, t) :: ps, (a, ta) :: (b, tb) :: ps' =>
    t == .i128 && C.pair v == some (a, b) && ta == .i64 && tb == .i64 &&
      entryParamsOk C gs ps ps'
  | [.pad, .lo, .hi] :: gs, (v, t) :: ps, (w, tw) :: (a, ta) :: (b, tb) :: ps' =>
    t == .i128 && C.fresh w && tw == .i64 && C.pair v == some (a, b) && ta == .i64 &&
      tb == .i64 && entryParamsOk C gs ps ps'
  | _, _, _ => false

/-- The parameters of a non-entry block (`blockParamsOf`). -/
def paramsOk (C : Ctx) : List (ValueId × Ty) → List (ValueId × Ty) → Bool
  | [], [] => true
  | (v, t) :: ps, (a, ta) :: ps' =>
    if t == .i128 then
      match C.pair v, ps' with
      | some (a0, b0), (b, tb) :: ps' =>
        a == a0 && b == b0 && ta == .i64 && tb == .i64 && paramsOk C ps ps'
      | _, _ => false
    else a == v && ta == t && C.plain v && paramsOk C ps ps'
  | _, _ => false

/-- The shared zero of the pad values (first statement of the entry block of `g`). -/
def Ctx.zeroStmt (C : Ctx) : Stmt := S C.zero (.iconst .i64 (BitVec.ofInt 64 0))

/-- A block of `f` and its rewrite. -/
def blockOk (C : Ctx) (isEntry : Bool) (b b' : Block) : Bool :=
  b'.id == b.id && decide (b'.params.map (·.1)).Nodup &&
    if isEntry then
      match groups C.f.sig.params, b'.body with
      | some gs, z :: rest =>
        entryParamsOk C gs b.params b'.params && z == C.zeroStmt &&
          codeOk C b.body b.term rest b'.term
      | _, _ => false
    else paramsOk C b.params b'.params && codeOk C b.body b.term b'.body b'.term

/-- The certificate: pair components are distinct values `≥ T0` (not values of `f`), distinct
from the zero, and different values have disjoint pairs. -/
def certOk (C : Ctx) : Bool :=
  decide (C.T0 ≤ C.zero) &&
  C.cert.pairs.all (fun (_, a, b) =>
    a != b && decide (C.T0 ≤ a) && decide (C.T0 ≤ b) && a != C.zero && b != C.zero) &&
  C.cert.pairs.all fun (v, a, b) => C.cert.pairs.all fun (w, c, d) =>
    v == w || (a != c && a != d && b != c && b != d)

/-- **The validator.** `g` (with certificate `cert`) is a legalisation of `f` covered by the
refinement theorem. -/
def check (f g : Function) (cert : Cert) : Bool :=
  let C : Ctx := ⟨f, g, cert⟩
  g.name == f.name && g.slots == f.slots && g.globals == f.globals &&
  sigExp f.sig == some g.sig &&
  decide ((defsOf f).map (·.1)).Nodup &&
  (idsOf f).all (fun v => decide (v < C.T0)) &&
  certOk C &&
  g.blocks.length == f.blocks.length &&
  match f.blocks, g.blocks with
  | b :: bs, b' :: bs' =>
    blockOk C true b b' && (bs.zip bs').all fun (x, y) => blockOk C false x y
  | _, _ => false

end Opt.Legal

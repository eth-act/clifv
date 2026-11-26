import FV.Opt.Check
import FV.Clif.Run

/-!
# `Opt.MidVal`: a per-function validator for Cranelift's mid-end, without rewrite rules (#1119)

`check f g` decides whether `g` (cg_clif's optimised dump, the output of Cranelift's
`Context::optimize` at `opt_level=speed_and_size`) can stand for `f` (the unoptimised dump after
`Opt.ConstPhi.run`, i.e. after Cranelift's own `eliminate_unreachable_code` and
`remove_constant_phis`). Cranelift's mid-end is not trusted and not re-implemented: the checker
only compares the pair. This file is the executable definition (stage 1 of #1119: measurement
first); the soundness theorem is stated in `docs/contracts/midval.md`.

What it accepts (every other difference is a rejection with a reason, `Reject`):

* **Same skeleton, same CFG.** Both functions have the same header and the same blocks (ids,
  order, parameter types). Per block, the *skeleton* statements (everything that is not a
  `pureK` node: memory accesses, calls, traps, trapping arithmetic, multi-result instructions)
  appear in the same order and are equal once every operand is replaced by its *term*, and the
  terminators are equal the same way.
* **Terms** (`Tm`, hash-consed): a block parameter is `param b i`, a skeleton result is
  `res b k j` (statement `k` of `f`'s block `b`), a pure node is `node i` with term operands.
  Both sides get terms from their own definitions, so value renaming, value aliases, GVN,
  removal of dead pure nodes and any placement of pure nodes (hoisting, sinking,
  rematerialised constants) are invisible. Pure nodes that can be `stuck` in `Clif.run`
  (`symbol_value`, `func_addr`, `tls_value`, `partialK`) are accepted in `g` only where `f`
  evaluated the same term no later (same block and no later skeleton segment, or a dominating
  block).
* **Removed skeleton statements of `f`** (`g` has no counterpart):
  - a load whose location is known (`Key`: memory version, address term, offset, type, access
    kind, explicit byte order) from a dominating store or load of the same version: its result
    is the known value (redundant-load elimination, store-to-load forwarding);
  - a store of the value already known at its location: memory is unchanged (idempotent store);
  - a load without a trap code (`notrap`): its result becomes an opaque `poison` term that no
    compared position may use (`Clif.run` is `stuck` on a bad `notrap` access, never traps);
  - a trapping instruction with idempotent effects (`udiv`/`sdiv`/`urem`/`srem`,
    `uadd_overflow_trap`, `trapz`/`trapnz`, `fcvt_to_{u,s}int`) equal to a dominating one: its
    result is the earlier one's.
* **Memory versions** (`versions`, on `g`): Cranelift 0.135.0's `LastStores` with one region
  (cg_clif sets no alias region): a store, call, `call_indirect`, atomic, `fence` or
  `try_call`/`try_call_indirect` starts a new version; at a block whose predecessors end in
  different versions a new version (`merge b`) starts. Explicit traps keep the version. Removed
  stores of `f` are idempotent (memory unchanged), so `g`'s versions are `f`'s memory states.

* **Normalisation** (stage 2, the default normaliser `Norm.stdT f`), on both sides: first a
  multiplication by `2^s` (or `x + x`) of a shift by a constant as one shift or mask (family 6,
  `fam6Mul`), then constant evaluation (`evalConst`: a pure node whose operands are all constants
  is the constant `Clif.evalInst` gives it), then single-node algebraic rules (`Norm.alg2`: `icmp`
  canonical forms, `isub 0 x`, `imul x 2`/`ishl x 1`, `bmask` of an `icmp`, `bxor x -1`;
  `Norm.alg`: `select` of an `icmp` with constant arms 1/0, `imul` by a power of two, `iadd` of a
  `stack_addr` and a constant, `ireduce` of an extension of a typed node), then the typed rules
  (`typedStep`: `select` of an integer term with constant arms 1/0, `ireduce` of an extension of
  an atom), which read an atom's static type in `f` (`atomTy`), then family 4 (`Norm.base`,
  `Norm.narrowN`: a neutral constant is dropped, `x+0`, `x*1`, …, typed; constants added to `x`
  are added up, `isub x k` is `iadd x (-k)`; a constant moves to the right of a commutative
  operation; `ireduce` of a ring operation is the operation on the narrowed operands, typed, a
  neutral constant it leaves dropped), then family 5 (`x + (-y)` is `x - y`, `(-x) * k` is
  `x * (-k)`, `ireduce` of an `ireduce` of a wider typed term is one `ireduce`), then family 6
  (a shift amount's extension or truncation dropped, typed; constants of `band`, `bor`, `bxor`,
  `imul` reassociated, `imul (ishl x k) c` is `imul x (c << k)`).

Not accepted: any other ISLE rewrite (new pure terms at compared positions, changed
terminators, removed blocks), dead-store elimination, readonly loads moved across writes.
-/

namespace Opt.MidVal

open Clif

/-! ## Terms, versions, memory locations -/

/-- A symbolic value (module doc). `node` holds an instruction whose operands are term ids. -/
inductive Tm where
  | param (b i : Nat)
  | res (b k j : Nat)
  | node (i : Inst)
  | poison (b k : Nat)
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- A memory version (`LastStores::last_fence`): the function entry, the writer at statement
`k` of block `b` (`k` = body length: the block's `try_call` terminator), or the merge at the
entry of block `b`. -/
inductive Ver where
  | entry
  | at (b k : Nat)
  | merge (b : Nat)
  deriving BEq, DecidableEq, Hashable, Repr, Inhabited

/-- The access kind of a memory location (Cranelift's `extending_opcode`): `load`/`store`
share `plain`; an extending load or a narrow store has its own. -/
inductive Kind where
  | plain
  | ld (op : LoadOp)
  | st (op : StoreOp)
  deriving BEq, DecidableEq, Hashable, Repr, Inhabited

/-- A memory location at a version (Cranelift's `MemoryLoc`; the address is a term). -/
structure Key where
  ver : Ver
  addr : Nat
  off : Int
  ty : Ty
  kind : Kind
  endian : Option Endianness
  deriving DecidableEq, Hashable, Repr

def loadKind : LoadOp → Kind
  | .load => .plain
  | op => .ld op

def storeKind : StoreOp → Kind
  | .store => .plain
  | op => .st op

/-! ## Instruction classes -/

/-- Single-result, memory-free, non-trapping instructions: they may be placed anywhere their
operands are available (Cranelift's `is_pure_for_egraph` minus loads). -/
def pureK (i : Inst) : Bool :=
  isPure i || match i with
    | .funcAddr .. | .tlsValue .. => true
    | .float op _ _ => op != .fcvtToUint && op != .fcvtToSint
    | _ => false

/-- The float pure nodes are typed so that `Clif.evalFloat` cannot be `stuck` (`Opt.check`
types only the `isPure` nodes): `ty` gives the operand types. Other instructions: `true`. -/
def floatTyped (ty : ValueId → Option Ty) : Inst → Bool
  | .float op t args =>
    let isF (x : Ty) : Bool := x == .f32 || x == .f64
    match op, args.map ty with
    | .fpromote, [some a] => t == .f64 && a == .f32
    | .fdemote, [some a] => t == .f32 && a == .f64
    | .fcvtToUintSat, [some a] | .fcvtToSintSat, [some a] => t.isInt && isF a
    | .fcvtFromUint, [some a] | .fcvtFromSint, [some a] => a.isInt && isF t
    | .fcmp _, [some a, some b] => isF t && a == t && b == t
    | .fcvtToUint, _ | .fcvtToSint, _ => true
    | op, tys => isF t && tys.length == op.arity && tys.all (· == some t) &&
      (op == .fma || (FSem.unary op).isSome || (FSem.binary op).isSome)
  | _ => true

/-- Pure nodes whose evaluation can be `stuck` (a symbol missing from the link-time image). -/
def partialK : Inst → Bool
  | .symbolValue .. | .funcAddr .. | .tlsValue .. => true
  | _ => false

/-- Trapping instructions with idempotent effects (Cranelift's `side_effects_idempotent`):
a second copy with the same operands neither traps nor changes anything. -/
def mergeK : Inst → Bool
  | .div .. | .uaddOverflowTrap .. | .trapz .. | .trapnz .. => true
  | .float op _ _ => op == .fcvtToUint || op == .fcvtToSint
  | _ => false

/-- Instructions that start a new memory version. -/
def writerK : Inst → Bool
  | .store .. | .atomicRmw .. | .atomicCas .. | .atomicLoad .. | .atomicStore .. | .fence
  | .call .. | .callIndirect .. => true
  | _ => false

/-- The shape of an instruction (operands erased). -/
def shape (i : Inst) : Inst := mapOperands (fun _ => 0) i

/-- A short opcode name for reasons. -/
def opName (i : Inst) : String :=
  match i with
  | .iconst .. => "iconst" | .unary .. => "unary" | .binary .. => "binary" | .div .. => "div"
  | .overflow .. => "overflow" | .carry .. => "carry" | .uaddOverflowTrap .. => "uadd_overflow_trap"
  | .icmp .. => "icmp" | .select .. => "select" | .selectSpectreGuard .. => "select_spectre_guard"
  | .bitselect .. => "bitselect" | .bmask .. => "bmask" | .extend .. => "extend"
  | .ireduce .. => "ireduce" | .iconcat .. => "iconcat" | .isplit .. => "isplit"
  | .load .. => "load" | .store .. => "store" | .stackAddr .. => "stack_addr" | .call .. => "call"
  | .callIndirect .. => "call_indirect" | .funcAddr .. => "func_addr"
  | .atomicRmw .. => "atomic_rmw" | .atomicCas .. => "atomic_cas" | .atomicLoad .. => "atomic_load"
  | .atomicStore .. => "atomic_store" | .fence => "fence" | .bitcast .. => "bitcast"
  | .trapz .. => "trapz" | .trapnz .. => "trapnz" | .nop => "nop"
  | .symbolValue .. => "symbol_value" | .tlsValue .. => "tls_value" | .float op _ _ => op.name

def termName : Terminator → String
  | .jump .. => "jump" | .brif .. => "brif" | .brTable .. => "br_table" | .ret .. => "return"
  | .returnCall .. => "return_call" | .trap .. => "trap" | .tryCall .. => "try_call"
  | .tryCallIndirect .. => "try_call_indirect"

/-- The last component of a `repr` (`Clif.BinaryOp.iadd` ↦ `iadd`). -/
def lastName {α : Type} [Repr α] (a : α) : String :=
  ((toString (repr a)).splitOn ".").getLast!

/-- An opcode name with its operation (reasons only). -/
def detName (i : Inst) : String :=
  match i with
  | .unary op .. => lastName op | .binary op .. => lastName op | .div op .. => lastName op
  | .icmp cc .. => s!"icmp_{lastName cc}" | .extend op .. => lastName op
  | .load op .. => lastName op | .store op .. => lastName op
  | i => opName i

/-- The head of a term (reasons only). -/
def tmHead : Tm → String
  | .param .. => "param" | .res .. => "res" | .poison .. => "poison" | .node i => detName i

/-- Where two terms first differ, descending through equal heads: `fhead→ghead` (reasons
only: the root of the rewrite Cranelift applied). -/
def diffHeads (tms : Array Tm) : Nat → Nat → Nat → String
  | 0, a, b => s!"{tmHead tms[a]!}→{tmHead tms[b]!}"
  | fuel + 1, a, b =>
    match tms[a]!, tms[b]! with
    | .node i, .node j =>
      if shape i == shape j then
        match ((operands i).zip (operands j)).find? (fun (x, y) => x != y) with
        | some (x, y) => diffHeads tms fuel x y
        | none => detName i
      else s!"{detName i}→{detName j}"
    | x, y => s!"{tmHead x}→{tmHead y}"

/-- The first differing operand pair of two operand lists, as `diffHeads`. -/
def diffOps (tms : Array Tm) (xs ys : List Nat) : String :=
  match (xs.zip ys).find? (fun (x, y) => x != y) with
  | some (x, y) => diffHeads tms 64 x y
  | none => "arity"

/-! ## Well-formedness of the validator's inputs (`wfCheck`)

`Opt.check` with two differences, both following `Clif.run`: a `call_indirect`'s result types are
the returns of its declared signature (`sigDeclOf`; `Opt.check` passes no signature table to
`Inst.resultTypes`, so it rejects every function with a `call_indirect`), and a `bitcast` needs
an operand of the result's width (`pureTypedM`; `Opt.pureTyped` asks for the result type itself,
while `Clif.evalInst` evaluates `f32 ↔ i32` and `f64 ↔ i64`). `Opt.check` is unchanged. -/

/-- The declared signature `sigN` of `f`. -/
def sigDeclOf (f : Function) (s : Nat) : Option Signature := f.sigDecls.lookup s

/-- Operand typing of pure nodes: `Opt.pureTyped`, except that a `bitcast`'s operand has the
result's width (`Clif.evalInst`'s condition). -/
def pureTypedM (ty : ValueId → Option Ty) (f : Function) : Inst → Bool
  | .bitcast t _ x => match ty x with
    | some s => s.width == t.width
    | none => false
  | i => pureTyped ty f i

/-- `Opt.wfCert` with `sigDeclOf` and `pureTypedM`. -/
def wfCertM (f : Function) (cfg : Cfg) (types : Std.HashMap ValueId Ty) : Bool :=
  let blocks := f.blocks
  let dmap := defMap f
  let dm := fun v => dmap.get? v
  let anc := ancB cfg.idom cfg.idom.size
  let rank := fun b => (cfg.rpoNum[b]?.join).getD 0
  let sigOf := fun r => (f.externs.lookup r).map (·.sig)
  let tm := fun v => types.get? v
  (blocks.zipIdx.all fun (b, i) => cfg.index.get? b.id == some i) &&
  ((defSites f).all fun (v, s) => dm v == some s) &&
  (cfg.idom[0]?.join).isNone &&
  ((List.range cfg.idom.size).all fun b => match cfg.idom[b]?.join with
    | some a => rank a < rank b
    | none => true) &&
  (blocks.zipIdx.all fun (b, i) =>
    b.params.all (fun p => tm p.1 == some p.2) &&
    (b.body.zipIdx.all fun (st, j) =>
      (operands st.inst).all (availB dm anc i j) &&
      (match st.inst.resultTypes sigOf (sigDeclOf f) with
       | some ts => ts.length == st.results.length && (st.results.zip ts).all fun (r, t) => tm r == some t
       | none => false) &&
      (!isPure st.inst || pureTypedM tm f st.inst)) &&
    (termOperands b.term).all (availB dm anc i b.body.length) &&
    (termSuccs b.term).all fun id => match cfg.index.get? id with
      | some j => (blocks[j]?.map (·.id)) == some id && match cfg.idom[j]?.join with
        | some c => anc c i
        | none => true
      | none => false)

/-- `Opt.checkCore` with `sigDeclOf` and `pureTypedM`. -/
def checkCoreM (f : Function) : Except String Info := do
  let cfg := Cfg.build f
  ensure (cfg.size > 0) "no blocks"
  ensure (cfg.index.size == cfg.size) "duplicate block ids"
  for i in [0:cfg.size] do
    ensure (cfg.reachable i) s!"unreachable block{cfg.ids[i]!}"
  let blocks := f.blocks.toArray
  let sigOf := fun r => (f.externs.lookup r).map (·.sig)
  let mut types : Std.HashMap ValueId Ty := {}
  let mut defBlock : Std.HashMap ValueId Nat := {}
  let mut pureDef : Std.HashMap ValueId Inst := {}
  for (b, i) in blocks.zipIdx do
    for (v, t) in b.params do
      ensure (!types.contains v) s!"v{v} defined twice"
      types := types.insert v t
      defBlock := defBlock.insert v i
    for st in b.body do
      let some ts := st.inst.resultTypes sigOf (sigDeclOf f) | throw s!"ill-formed instruction defining {st.results}"
      ensure (ts.length == st.results.length) s!"result arity of {st.results}"
      for (v, t) in st.results.zip ts do
        ensure (!types.contains v) s!"v{v} defined twice"
        types := types.insert v t
        defBlock := defBlock.insert v i
      if isPure st.inst then
        if let [v] := st.results then pureDef := pureDef.insert v st.inst
  ensure ((blocks[0]!.params.map (·.2)) == f.sig.params.map (·.ty)) "entry parameters ≠ signature"
  let ty := fun v => types.get? v
  for (b, i) in blocks.zipIdx do
    let mut seen : Std.HashSet ValueId := b.params.foldl (·.insert ·.1) {}
    let avail := fun (seen : Std.HashSet ValueId) (v : ValueId) =>
      seen.contains v || match defBlock.get? v with
        | some d => d != i && cfg.dominates d i
        | none => false
    for st in b.body do
      for v in operands st.inst do
        ensure (avail seen v) s!"block{b.id}: use of v{v} not dominated by its definition"
      if isPure st.inst then
        ensure (pureTypedM ty f st.inst) s!"block{b.id}: ill-typed pure instruction defining {st.results}"
      seen := st.results.foldl (·.insert ·) seen
    for v in termOperands b.term do
      ensure (avail seen v) s!"block{b.id}: terminator uses v{v}, not dominated by its definition"
    let calls : List BlockCall := match b.term with
      | .jump d => [d] | .brif _ t e => [t, e] | .brTable _ d t => d :: t | _ => []
    for bc in calls do
      let some j := cfg.index.get? bc.block | throw s!"unknown block{bc.block}"
      let ps := blocks[j]!.params
      ensure (ps.length == bc.args.length &&
        (ps.zip bc.args).all fun (p, a) => ty a == some p.2) s!"block{b.id}: arguments of block{bc.block}"
    if let .brTable x _ _ := b.term then
      ensure (ty x == some .i32) s!"block{b.id}: br_table index not i32"
  return { cfg, types, defBlock, pureDef }

/-- **The validator's well-formedness check**: `Opt.check` with `call_indirect` result types
from the function's signature declarations and the `bitcast` typing of `Clif.evalInst`
(section doc). -/
def wfCheck (f : Function) : Except String Info := do
  let info ← checkCoreM f
  ensure (wfCertM f info.cfg info.types) "certificate rejected (Opt.MidVal.wfCertM)"
  return info

/-! ## The hoisting mode's premise: the function's global values resolve

`Clif.run` is `stuck` on a `symbol_value`, `tls_value` or `func_addr` whose symbol the link-time
image lacks, so `g` may evaluate one where `f` has not yet only if it resolves.
`globalsResolve f syms` decides that for every such instruction of `f`, from `f` and the image's
symbol table `syms` (`Mem.symbols`), so that a tool holding the image (link-check) can decide it
per function. -/

/-- The instruction `i` of `f` resolves in `syms` (`true` for every other instruction). -/
def symResolves (f : Function) (syms : String → Option Nat) : Inst → Bool
  | .symbolValue _ gv => match f.globals.lookup gv with
    | some (.symbol name _ _) => (syms name).isSome
    | _ => false
  | .tlsValue _ gv => match f.globals.lookup gv with
    | some (.tlsSymbol name _ _) => (syms name).isSome
    | _ => false
  | .funcAddr _ fn => match f.extern? fn with
    | some e => (syms e.name).isSome
    | none => false
  | _ => true

/-- **The function's global values resolve** in the symbol table `syms` (section doc). -/
def globalsResolve (f : Function) (syms : String → Option Nat) : Bool :=
  f.blocks.all fun b => b.body.all fun st => symResolves f syms st.inst

/-- `f` contains the instruction `i`. -/
def hasInst (f : Function) (i : Inst) : Bool :=
  f.blocks.any fun b => b.body.any fun st => st.inst == i

/-! ## Memory versions (on `g`) -/

def meetV (b : Nat) : Option Ver → Ver → Ver
  | none, v => v
  | some u, v => if u == v then u else .merge b

/-- The version at the end of block `bi` entered at version `v`. -/
def exitVer (bi : Nat) (blk : Block) (v : Ver) : Ver := Id.run do
  let mut v := v
  for (st, k) in blk.body.zipIdx do
    if writerK st.inst then v := .at bi k
  if blk.term.isTry then v := .at bi blk.body.length
  return v

/-- Entry version of every block (Cranelift's `compute_block_input_states`, one region): a
fixpoint over the CFG; a block whose predecessors disagree gets `merge`. -/
def versions (g : Function) (cfg : Cfg) : Array Ver := Id.run do
  let blocks := g.blocks.toArray
  let n := blocks.size
  let mut ins : Array (Option Ver) := (Array.replicate n none).set! 0 (some .entry)
  for _ in [0:2 * n + 2] do
    let mut changed := false
    for bi in cfg.rpo do
      match ins[bi]?.join, blocks[bi]? with
      | some v, some blk =>
        let o := exitVer bi blk v
        for s in termSuccs blk.term do
          match cfg.index.get? s with
          | some si =>
            let old := ins[si]?.join
            let new := if si == 0 then .merge 0 else meetV si old o
            if old != some new then
              ins := ins.set! si (some new)
              changed := true
          | none => pure ()
      | _, _ => pure ()
    if !changed then break
  return ins.map (·.getD (.merge 0))

/-! ## Dominator tree intervals -/

/-- Preorder/postorder numbers of the dominator tree (from `idom`): `a` dominates `b` iff
`pre a ≤ pre b ∧ post b ≤ post a`. Also the preorder itself. -/
def domIntervals (idom : Array (Option Nat)) : Array Nat × Array Nat × Array Nat := Id.run do
  let n := idom.size
  let mut kids : Array (Array Nat) := Array.replicate n #[]
  for b in [0:n] do
    if let some (some a) := idom[b]? then kids := kids.modify a (·.push b)
  let mut pre := Array.replicate n 0
  let mut post := Array.replicate n 0
  let mut order : Array Nat := #[]
  let mut stack : Array (Nat × Nat) := #[(0, 0)]
  let mut c := 0
  for _ in [0:2 * n + 2] do
    match stack.back? with
    | none => break
    | some (b, i) =>
      if i == 0 then
        pre := pre.set! b c
        c := c + 1
        order := order.push b
      match (kids[b]!)[i]? with
      | some k =>
        stack := stack.pop.push (b, i + 1) |>.push (k, 0)
      | none =>
        post := post.set! b c
        c := c + 1
        stack := stack.pop
  return (pre, post, order)

/-! ## The check -/

/-- Why a pair is rejected: a class (`rewrite:…`, `alias:…`, `placement`, `shape:…`, `wf:…`)
and a detail. -/
abbrev Reject := String

/-- A **normaliser** of pure nodes: given the term table and a node (term operands), a term
of the same value under `Clif.evalInst`, or `none` (keep the node). This is the seam of stage 2
(#1119): the soundness theorem takes it with the one hypothesis that it preserves values
(`NormSound`); stage 1 used `Norm.id`, the default is `Norm.std` (constant evaluation), and
each further proven rewrite is one more `Norm` with its own preservation lemma. -/
abbrev Norm := Array Tm → Inst → Option Tm

/-- The identity normaliser (stage 1: no rewrite). -/
def Norm.id : Norm := fun _ _ => none

/-- One wrapper of a branch condition (family 3, #1119): `icmp cc ty y 0` (`zl = false`) or
`icmp cc ty 0 y` (`zl = true`) with `0` the constant of type `ty`, or `extend op ty y`. Around
`g`'s condition `y`, a chain of them rebuilds `f`'s (`condPrep`, `FV/Opt/MidValCond.lean`). -/
inductive Wrap where
  | icmp (cc : IntCC) (ty : Ty) (zl : Bool)
  | ext (op : ExtendOp) (ty : Ty)
  deriving DecidableEq, Repr, Inhabited

/-- The wrappers that keep a condition's truth (`Sem.truthy`) whenever they evaluate:
`y != 0`, `0 != y`, `y >u 0`, `0 <u y`, and the extensions. -/
def Wrap.ok : Wrap → Bool
  | .icmp .ne _ _ | .icmp .ugt _ false | .icmp .ult _ true | .ext .. => true
  | _ => false

structure St where
  tms : Array Tm := #[]
  ids : Std.HashMap Tm Nat := {}
  envF : Std.HashMap ValueId Nat := {}
  envG : Std.HashMap ValueId Nat := {}
  /-- Known memory values: location ↦ (value term, defining block). -/
  facts : Std.HashMap Key (Array (Nat × Nat)) := {}
  /-- Idempotent trapping instructions: node term ↦ (result term, defining block). -/
  merges : Std.HashMap Nat (Array (Option Nat × Nat)) := {}
  /-- Partial pure terms `f` evaluates: term ↦ (block, skeleton segment). -/
  partials : Std.HashMap Nat (Array (Nat × Nat)) := {}
  /-- The likely cause of a later rejection (reasons only): a load of `f` taken for a dead
  `notrap` load while `g`'s next statement was a load of another address. -/
  hint : Option Reject := none
  /-- The normaliser of pure nodes (`Norm`). -/
  norm : Norm := Norm.id
  /-- The facts a removal used (certificate emission, `FV/Opt/MidValCert.lean`): memory
  locations with their value, merged trapping nodes, partial terms, and the partial terms `g`
  evaluates before `f` does (hoisting mode). -/
  usedMem : Std.HashSet (Key × Nat) := {}
  usedMerge : Std.HashSet Nat := {}
  usedPart : Std.HashSet Nat := {}
  usedHoist : Std.HashSet Nat := {}
  /-- Family 3 (`checkRun … (cond := true)`): a `brif` of `f` whose condition is `g`'s under
  truth-keeping wrappers (`condChain`) is not a rejection; the block's wrapper chain (innermost
  first) is recorded in `conds` (the hints of `condPrep`). -/
  cond : Bool := false
  conds : Array (BlockId × List Wrap) := #[]
  /-- The static type of an atom (`atomTy f`): the checker interns the terms `selTyped` looks
  up (`internSelAux`). -/
  aty : Tm → Option Ty := fun _ => none

/-- The checker's monad; the state survives a rejection (for `St.hint`). -/
abbrev M := ExceptT Reject (StateM St)

def liftE {α : Type} : Except Reject α → M α
  | .ok a => pure a
  | .error r => throw r

/-- The constant a term stands for: a node `iconst` (`f32const`/`f64const` included). -/
def constOf (tms : Array Tm) (o : Nat) : Option Val :=
  match tms[o]? with
  | some (.node (.iconst ty imm)) => some ⟨ty, imm⟩
  | _ => none

/-- The frame in which `evalConst` evaluates a node: its operands `ops` hold the constants
`vals`; no function, no slots (a pure node with operands reads neither). -/
def constFrame (ops : List Nat) (vals : List Val) : Frame :=
  { func := default, regs := fun x => (ops.zip vals).lookup x, slots := [], body := [],
    term := .ret [] }

/-- **Constant evaluation** (stage 2, family 1): a pure, non-partial node with operands, all of
them constants (`constOf`), is replaced by its value under `Clif.evalInst` (no rewrite rule:
the semantics itself, so wrap-around, shift amounts, signedness, float bit patterns are
`evalInst`'s). Sound: `normSound_evalConst` (`FV/Opt/Proof/MidValNormConst.lean`). -/
def evalConst : Norm := fun tms i =>
  let ops := operands i
  if ops.isEmpty || !isPure i || partialK i then none
  else match ops.mapM (constOf tms) with
    | none => none
    | some vals => match evalInst (constFrame ops vals) Mem.empty i with
      | .ok ([v], _) => some (.node (.iconst v.ty v.bits))
      | _ => none

/-! ## Stage 2, family 2: single-node algebraic rules

A rule maps a node (term operands) to a node over existing terms that has the same value under
`Clif.evalInst` in every frame (`algStep`). A rule may name a term other than the node's
operands (`findTm`: the first id of that term, whose operands are earlier); the checker interns
such terms first (`auxTms`). It reads the structure of an operand only through `nodeAt` (a node
whose operands are earlier) and `constAt` (a constant of a given type). `Norm.guard` keeps a
result only when every occurrence of it in the table has its operands earlier (what the term
values need); the checker's table is hash-consed and grows by appending, so this holds for every
result it interns. -/

/-- The operand ids of a term (a node's operands; none for an atom). -/
def Tm.ops : Tm → List Nat
  | .node i => operands i
  | _ => []

/-- The first id of term `x` in the table, if `x`'s operands are earlier. -/
def findTm (tms : Array Tm) (x : Tm) : Option Nat :=
  ((List.range tms.size).find? fun a => tms[a]? == some x).bind fun a =>
    if x.ops.all (· < a) then some a else none

/-- Every occurrence of `x` in the table has its operands earlier. -/
def ordered (tms : Array Tm) (x : Tm) : Bool :=
  (List.range tms.size).all fun t => tms[t]? != some x || x.ops.all (· < t)

/-- A normaliser's result, kept only if `ordered`. -/
def Norm.guard (n : Norm) : Norm := fun tms i =>
  match n tms i with
  | some x => if ordered tms x then some x else none
  | none => none

/-- The instruction of term `c`, if it is a node whose operands are earlier. -/
def nodeAt (tms : Array Tm) (c : Nat) : Option Inst :=
  match tms[c]? with
  | some (.node j) => if (operands j).all (· < c) then some j else none
  | _ => none

/-- The bits of term `o`, if it is a constant of type `ty`. -/
def constAt (tms : Array Tm) (ty : Ty) (o : Nat) : Option (BitVec ty.width) :=
  (constOf tms o).bind (·.as? ty)

/-- Family 3: the wrappers (outermost first) that make `f`'s condition term `a` out of `g`'s
`b`, each `Wrap.ok` with its constant `0`; `fuel` bounds the descent (operands are earlier). -/
def condChain (tms : Array Tm) : Nat → Nat → Nat → Option (List Wrap)
  | 0, a, b => if a == b then some [] else none
  | fuel + 1, a, b =>
    if a == b then some [] else
    match nodeAt tms a with
    | some (.icmp cc ty x y) =>
      if (Wrap.icmp cc ty false).ok && constAt tms ty y == some 0 then
        (condChain tms fuel x b).map (.icmp cc ty false :: ·)
      else if (Wrap.icmp cc ty true).ok && constAt tms ty x == some 0 then
        (condChain tms fuel y b).map (.icmp cc ty true :: ·)
      else none
    | some (.extend op ty c) => (condChain tms fuel c b).map (.ext op ty :: ·)
    | _ => none

/-- The comparison with the opposite outcome. -/
def IntCC.inv : IntCC → IntCC
  | .eq => .ne | .ne => .eq | .slt => .sge | .sge => .slt | .sgt => .sle | .sle => .sgt
  | .ult => .uge | .uge => .ult | .ugt => .ule | .ule => .ugt

/-- `k` with `2 ^ k = v`, `0 < k`. -/
def pow2Log (v : Nat) : Option Nat :=
  if 0 < Nat.log2 v && 2 ^ Nat.log2 v == v then some (Nat.log2 v) else none

/-- The comparison term a `select ty c vx vy` of an `icmp` `c` stands for: `c` itself when
`(vx, vy) = (1, 0)`, the inverted comparison (if interned) when `(0, 1)`. -/
def selPick (tms : Array Tm) (c : Nat) (cc : IntCC) (cty : Ty) (a b : Nat) {w : Nat}
    (vx vy : BitVec w) : Option Nat :=
  if vx == 1 && vy == 0 then some c
  else if vx == 0 && vy == 1 then findTm tms (.node (.icmp (IntCC.inv cc) cty a b)) else none

/-- An `i8` comparison term `n` at type `ty`: itself at `i8`, `uextend ty n` at a wider type. -/
def selWrap (tms : Array Tm) (ty : Ty) (n : Nat) : Option Tm :=
  if ty == .i8 then tms[n]? else if 8 < ty.width then some (.node (.extend .uextend ty n)) else none

/-- `select ty c 1 0` with `c` an `icmp` (an `i8` 0/1): `c` itself at `i8`, `uextend ty c` at a
wider type; `select ty c 0 1`: the same of the inverted `icmp` (Cranelift 0.135.0's
`select`-of-`icmp` rules, `opts/selects.isle`/`icmp.isle`). -/
def selIcmp (tms : Array Tm) (ty : Ty) (c x y : Nat) : Option Tm :=
  match nodeAt tms c with
  | some (.icmp cc cty a b) =>
    match constAt tms ty x, constAt tms ty y with
    | some vx, some vy => (selPick tms c cc cty a b vx vy).bind (selWrap tms ty)
    | _, _ => none
  | _ => none

/-- `imul ty x c` with `c` the constant `2^k` of type `ty`, `0 < k < width`: `ishl ty x k`, the
amount a constant of type `ty` (Cranelift's `imul`-by-power-of-two rule, `opts/arithmetic.isle`). -/
def mulPow2 (tms : Array Tm) (ty : Ty) (x c : Nat) : Option Tm :=
  match constAt tms ty c with
  | some b => match pow2Log b.toNat with
    | some k =>
      if k < ty.width then
        (findTm tms (.node (.iconst ty (BitVec.ofNat ty.width k)))).map fun kc =>
          .node (.binary .ishl ty x kc)
      else none
    | none => none
  | none => none

/-- `iadd ty s c` with `s` a `stack_addr ty slot off` and `c` a constant of type `ty`:
`stack_addr ty slot (off + c)`, `c` read as signed (Cranelift's `stack_addr` offset folding). -/
def addStack (tms : Array Tm) (ty : Ty) (s c : Nat) : Option Tm :=
  match nodeAt tms s, constAt tms ty c with
  | some (.stackAddr ty' slot off), some b =>
    if ty' == ty then some (.node (.stackAddr ty slot (off + b.toInt))) else none
  | _, _ => none

/-- The result type of a node, whenever it evaluates (`Inst.resultTypes` of a pure node). -/
def nodeTy : Inst → Option Ty
  | .iconst ty _ | .unary _ ty _ | .binary _ ty _ _ | .select ty .. | .bmask ty _
  | .extend _ ty _ | .ireduce ty _ | .bitcast ty .. => some ty
  | .icmp .. => some .i8
  | _ => none

/-- `ireduce ty (extend op uty x)` with `x` a node of type `xt`, `xt` and `ty` narrower than
`uty`: `x` when `xt = ty`, `extend op ty x` when `xt` is narrower than `ty`, `ireduce ty x` when
wider (Cranelift's `ireduce`-of-extend rules, `opts/extends.isle`). `x` must be a node: the type
of an atom is not in the table, and the rewrite is false for an operand of another width. -/
def redExt (tms : Array Tm) (ty : Ty) (u : Nat) : Option Tm :=
  match nodeAt tms u with
  | some (.extend op uty x) =>
    match nodeAt tms x with
    | some j =>
      match nodeTy j with
      | some xt =>
        if xt.width < uty.width && ty.width < uty.width then
          if xt == ty then some (.node j)
          else if xt.width < ty.width then some (.node (.extend op ty x))
          else if ty.width < xt.width then some (.node (.ireduce ty x))
          else none
        else none
      | none => none
    | none => none
  | _ => none

/-- The single-node rules (unguarded; `Norm.alg` guards them). -/
def algStep (tms : Array Tm) : Inst → Option Tm
  | .select ty c x y => selIcmp tms ty c x y
  | .binary .imul ty x y => (mulPow2 tms ty x y).orElse fun _ => mulPow2 tms ty y x
  | .binary .iadd ty x y => (addStack tms ty x y).orElse fun _ => addStack tms ty y x
  | .ireduce ty u => redExt tms ty u
  | _ => none

/-! ### Family 2, second set: comparisons, negation, doubling, masks

Cranelift's canonical forms of `icmp` (constant on the right; `ult x 1` is `eq x 0`; an `icmp`
compared with `0`/`1` is itself or its inversion), `isub 0 x = ineg x`, `imul x 2 = iadd x x`
(and `ishl x 1`, so that `g`'s shift by one meets it),
`bmask` of an `icmp` is its negation, `bxor x -1 = bnot x`. Like the first set, each result has
the node's value under `Clif.evalInst` in every frame. -/

/-- The comparison with its operands swapped. -/
def IntCC.swap : IntCC → IntCC
  | .eq => .eq | .ne => .ne | .slt => .sgt | .sgt => .slt | .sle => .sge | .sge => .sle
  | .ult => .ugt | .ugt => .ult | .ule => .uge | .uge => .ule

/-- `icmp cc ty a b` with `a` a constant and `b` not: `icmp (swap cc) ty b a`. -/
def icmpSwap (tms : Array Tm) (cc : IntCC) (ty : Ty) (a b : Nat) : Option Tm :=
  match constOf tms a, constOf tms b with
  | some _, none => some (.node (.icmp (IntCC.swap cc) ty b a))
  | _, _ => none

/-- The `icmp` a term `u` of type `ty` is a 0/1 copy of: `u` itself (an `icmp`, `ty = i8`), or
the operand of `uextend ty c` with `c` an `icmp` and `ty` wider than `i8`. -/
def boolAt (tms : Array Tm) (ty : Ty) (u : Nat) : Option Inst :=
  match nodeAt tms u with
  | some (.icmp cc cty a b) => if ty == .i8 then some (.icmp cc cty a b) else none
  | some (.extend .uextend ty' c) =>
    if ty' == ty && 8 < ty.width then
      match nodeAt tms c with
      | some (.icmp cc cty a b) => some (.icmp cc cty a b)
      | _ => none
    else none
  | _ => none

/-- `icmp eq/ne ty u k` with `u` a 0/1 copy of an `icmp` (`boolAt`) and `k` the constant `0` or
`1` of type `ty`: that `icmp` (`eq 1`, `ne 0`) or its inversion (`eq 0`, `ne 1`). -/
def icmpBool (tms : Array Tm) (cc : IntCC) (ty : Ty) (u k : Nat) : Option Tm :=
  match boolAt tms ty u, constAt tms ty k with
  | some (.icmp cc' cty a b), some kv =>
    if (cc == .eq && kv == 1) || (cc == .ne && kv == 0) then some (.node (.icmp cc' cty a b))
    else if (cc == .eq && kv == 0) || (cc == .ne && kv == 1) then
      some (.node (.icmp (IntCC.inv cc') cty a b))
    else none
  | _, _ => none

/-- `icmp ult ty x 1` is `icmp eq ty x 0`, `icmp uge ty x 1` is `icmp ne ty x 0` (the constant
`0` interned first); `icmp ugt ty x 0` is `icmp ne ty x 0`, `icmp ule ty x 0` is `icmp eq ty x 0`. -/
def icmpUnit (tms : Array Tm) (cc : IntCC) (ty : Ty) (x k : Nat) : Option Tm :=
  match constAt tms ty k with
  | some kv =>
    if kv == 1 && (cc == .ult || cc == .uge) then
      (findTm tms (.node (.iconst ty 0))).map fun z =>
        .node (.icmp (if cc == .ult then .eq else .ne) ty x z)
    else if kv == 0 && (cc == .ugt || cc == .ule) then
      some (.node (.icmp (if cc == .ugt then .ne else .eq) ty x k))
    else none
  | none => none

/-- `icmp cc ty a b` with `a` a constant and `b` not whose swap `icmp (swap cc) ty b a` is one of
`icmpUnit`'s forms (`icmp ult 0, x`, `icmp uge 0, x`, `icmp ugt 1, x`, `icmp ule 1, x`):
`icmpUnit`'s result for the swap. One normaliser step then reaches the form `icmpUnit` gives
`g`'s comparison with 0 (`icmpSwap` alone stops at `icmp ugt x, 0`, while the branch-condition
copy of `g`, `condPrep`, rebuilds `icmp ugt c, 0`, which `icmpUnit` makes `icmp ne c, 0`). -/
def icmpSwapUnit (tms : Array Tm) (cc : IntCC) (ty : Ty) (a b : Nat) : Option Tm :=
  match constOf tms a, constOf tms b with
  | some _, none => icmpUnit tms (IntCC.swap cc) ty b a
  | _, _ => none

/-- `isub ty z x` with `z` the constant `0`: `ineg ty x`. -/
def subNeg (tms : Array Tm) (ty : Ty) (z x : Nat) : Option Tm :=
  match constAt tms ty z with
  | some zv => if zv == 0 then some (.node (.unary .ineg ty x)) else none
  | none => none

/-- `imul ty x c` with `c` the constant `2`: `iadd ty x x`. -/
def mulTwo (tms : Array Tm) (ty : Ty) (x c : Nat) : Option Tm :=
  match constAt tms ty c with
  | some cv => if cv == 2 then some (.node (.binary .iadd ty x x)) else none
  | none => none

/-- `ishl ty x c` with `c` a constant whose amount (modulo the width) is `1`: `iadd ty x x`
(the normal form `mulTwo` gives `imul x 2`). -/
def shlOne (tms : Array Tm) (ty : Ty) (x c : Nat) : Option Tm :=
  match constOf tms c with
  | some K => if K.bits.toNat % ty.width == 1 then some (.node (.binary .iadd ty x x)) else none
  | none => none

/-- `bmask i8 c` with `c` an `icmp`: `ineg i8 c`. -/
def bmaskBool (tms : Array Tm) (ty : Ty) (c : Nat) : Option Tm :=
  match nodeAt tms c with
  | some (.icmp ..) => if ty == .i8 then some (.node (.unary .ineg .i8 c)) else none
  | _ => none

/-- `bxor ty x m` with `m` the all-ones constant of type `ty`: `bnot ty x`. -/
def xorNot (tms : Array Tm) (ty : Ty) (x m : Nat) : Option Tm :=
  match constAt tms ty m with
  | some mv => if mv == BitVec.allOnes ty.width then some (.node (.unary .bnot ty x)) else none
  | none => none

/-- The second set of single-node rules (unguarded; `Norm.alg2` guards them). -/
def algStep2 (tms : Array Tm) : Inst → Option Tm
  | .icmp cc ty a b =>
    (icmpSwapUnit tms cc ty a b).orElse fun _ => (icmpSwap tms cc ty a b).orElse fun _ =>
      (icmpBool tms cc ty a b).orElse fun _ => icmpUnit tms cc ty a b
  | .binary .isub ty z x => subNeg tms ty z x
  | .binary .imul ty x y => (mulTwo tms ty x y).orElse fun _ => mulTwo tms ty y x
  | .binary .ishl ty x c => shlOne tms ty x c
  | .binary .bxor ty x y => (xorNot tms ty x y).orElse fun _ => xorNot tms ty y x
  | .bmask ty c => bmaskBool tms ty c
  | _ => none

/-- The terms `algStep`/`algStep2` look up besides the node's operands (the checker interns them
first). -/
def auxTms (tms : Array Tm) : Inst → List Tm
  | .select _ c _ _ => match nodeAt tms c with
    | some (.icmp cc cty a b) => [.node (.icmp (IntCC.inv cc) cty a b)]
    | _ => []
  | .binary .imul ty x y =>
    [x, y].filterMap fun o => (constAt tms ty o).bind fun b =>
      (pow2Log b.toNat).map fun k => .node (.iconst ty (BitVec.ofNat ty.width k))
  | .icmp cc ty a k =>
    if ((cc == .ult || cc == .uge) && constAt tms ty k == some 1) ||
        ((cc == .ugt || cc == .ule) && constAt tms ty a == some 1) then [.node (.iconst ty 0)]
    else []
  | _ => []

/-- The algebraic rules, guarded. -/
def Norm.alg : Norm := Norm.guard algStep

/-- The second set, guarded. -/
def Norm.alg2 : Norm := Norm.guard algStep2

/-- One normaliser, then another where the first leaves the node alone. -/
def Norm.orElse (a b : Norm) : Norm := fun tms i => (a tms i).orElse fun _ => b tms i

/-- The constant evaluation and the single-node algebraic rules (`evalConst`, then family 2:
`Norm.alg2`, then `Norm.alg`); proved sound (`normSound_std`). -/
def Norm.std : Norm := Norm.orElse evalConst (Norm.orElse Norm.alg2 Norm.alg)

/-! ### The typed rules

An atom's value in a frame of `f` may have any type, so a rule whose truth depends on the width
of an atom holds only in the frames where the atom holds a value of its static type (`atomTy`):
its soundness obligation is `NormSoundT f` (`FV/Opt/Proof/MidValTerm.lean`), which the simulation
discharges from `wfCheck`'s typing. -/

/-- The static type of an atom of `f`: a block parameter's declared type, a statement result's
`Inst.resultTypes` (calls through the extern signatures, `call_indirect` through `sigDeclOf`);
`none` for nodes and `poison`. -/
def atomTy (f : Function) : Tm → Option Ty
  | .param b i => (f.blocks[b]?).bind fun blk => (blk.params[i]?).map (·.2)
  | .res b k j => (f.blocks[b]?).bind fun blk => (blk.body[k]?).bind fun st =>
      (st.inst.resultTypes (fun r => (f.externs.lookup r).map (·.sig)) (sigDeclOf f)).bind
        (·[j]?)
  | _ => none

/-- The static type of term `u`: a node's `nodeTy` (operands earlier), an atom's `aty`. -/
def tyAt (aty : Tm → Option Ty) (tms : Array Tm) (u : Nat) : Option Ty :=
  match tms[u]? with
  | some (.node j) => if (operands j).all (· < u) then nodeTy j else none
  | some a => aty a
  | none => none

/-- The comparison a `select` with constant arms `vx`, `vy` stands for: `ne` for `1, 0`, `eq`
for `0, 1`. -/
def selCC {w : Nat} (vx vy : BitVec w) : Option IntCC :=
  if vx == 1 && vy == 0 then some .ne else if vx == 0 && vy == 1 then some .eq else none

/-- `select ty c 1 0` (`select ty c 0 1`) with `c` a term of integer type `tc` that is not an
`icmp`: `icmp ne tc c 0` (`icmp eq tc c 0`) at `i8`, its `uextend ty` at a wider type
(Cranelift 0.135.0's `select`-to-`icmp` rules, `opts/selects.isle`). The comparison and the
constant `0` are looked up (`findTm`); the checker interns them (`internSelAux`). -/
def selTyped (aty : Tm → Option Ty) (tms : Array Tm) (ty : Ty) (c x y : Nat) : Option Tm :=
  match nodeAt tms c with
  | some (.icmp ..) => none
  | _ =>
    match tyAt aty tms c, constAt tms ty x, constAt tms ty y with
    | some tc, some vx, some vy =>
      if tc.isInt then
        (selCC vx vy).bind fun cc =>
          (findTm tms (.node (.iconst tc 0))).bind fun z =>
            (findTm tms (.node (.icmp cc tc c z))).bind fun n => selWrap tms ty n
      else none
    | _, _, _ => none

/-- `ireduce ty (extend op uty x)` with `x` a term of static type `xt` by `aty` (an atom: `atomTy`
gives nodes no type; a node `x` is `redExt`'s), `xt` and `ty` narrower than `uty`: as `redExt`
(`x` when `xt = ty`, `extend op ty x` when narrower, `ireduce ty x` when wider). -/
def redTyped (aty : Tm → Option Ty) (tms : Array Tm) (ty : Ty) (u : Nat) : Option Tm :=
  match nodeAt tms u with
  | some (.extend op uty x) =>
    match tms[x]?, (tms[x]?).bind aty with
    | some a, some xt =>
      if xt.width < uty.width && ty.width < uty.width then
        if xt == ty then some a
        else if xt.width < ty.width then some (.node (.extend op ty x))
        else if ty.width < xt.width then some (.node (.ireduce ty x))
        else none
      else none
    | _, _ => none
  | _ => none

/-- The typed rules (unguarded; `Norm.stdT` guards them). -/
def typedStep (aty : Tm → Option Ty) (tms : Array Tm) : Inst → Option Tm
  | .select ty c x y => selTyped aty tms ty c x y
  | .ireduce ty u => redTyped aty tms ty u
  | _ => none

/-! ### Family 4: neutral constants, affine constants, constants on the right, narrowed `ireduce`

The most frequent `rewrite:operand` shapes of the 121,879 release pairs (#1119, agent
MidendNorm5), after Cranelift 0.135.0's `opts/arithmetic.isle` (`x+0`, `x*1`, …), `cprop.isle`
(constants to the right, reassociated constants) and the narrowing of `ireduce` over an
arithmetic operation. Each step is a normaliser of its own with its soundness lemma
(`FV/Opt/Proof/MidValNormFam4.lean`). -/

/-- `k` is a right neutral element of `op`: `Sem.binary op x k = x` for every `x`. -/
def rNeutral {w : Nat} (op : BinaryOp) (k : BitVec w) : Bool :=
  match op with
  | .iadd | .isub | .bor | .bxor => k == 0
  | .imul => k == 1
  | .band => k == BitVec.allOnes w
  | _ => false

/-- `op` is commutative: `Sem.binary op x y = Sem.binary op y x`. -/
def commOp : BinaryOp → Bool
  | .iadd | .imul | .band | .bor | .bxor | .umin | .umax | .smin | .smax => true
  | _ => false

/-- `op ty x k` with `k` a neutral constant of type `ty` (`rNeutral`) and `x` a term of static
type `ty` (`tyAt`): `x`. -/
def idPick (aty : Tm → Option Ty) (tms : Array Tm) (op : BinaryOp) (ty : Ty) (x k : Nat) :
    Option Tm :=
  match constAt tms ty k with
  | some kv => if rNeutral op kv && tyAt aty tms x == some ty then tms[x]? else none
  | none => none

/-- `op ty a b` with `b` a neutral constant, or `a` one and `op` commutative (`idPick`). -/
def idTyped (aty : Tm → Option Ty) (tms : Array Tm) (op : BinaryOp) (ty : Ty) (a b : Nat) :
    Option Tm :=
  (idPick aty tms op ty a b).orElse fun _ => if commOp op then idPick aty tms op ty b a else none

/-- **Neutral constants** (typed; Cranelift's `x+0`, `x-0`, `x*1`, `x|0`, `x^0`, `x&-1` and
their commuted forms): the operand itself. Without the typing the rewrite is false: an `iadd.i64`
of an `i32` value is `stuck`, the value is not. -/
def idStep (aty : Tm → Option Ty) (tms : Array Tm) : Inst → Option Tm
  | .binary op ty a b => idTyped aty tms op ty a b
  | _ => none

/-- `x` is `iadd ty y k1` with `k1` a constant of type `ty`: `(y, k1 + k)`. -/
def foldAdd (tms : Array Tm) (ty : Ty) (x : Nat) (k : BitVec ty.width) : Option (Nat × Val) :=
  match nodeAt tms x with
  | some (.binary .iadd ty' y k1) =>
    if ty' == ty then (constAt tms ty k1).map fun v => (y, ⟨ty, v + k⟩) else none
  | _ => none

/-- The affine form `(y, K)` (value `y + K`, `K` of the node's type) of `iadd ty x k`,
`iadd ty k x` whose `x` is an `iadd` with a constant (the constants added up), and of
`isub ty x k` (`x + (-k)`, the constants added up when `x` is such an `iadd`). -/
def affPlan (tms : Array Tm) : Inst → Option (Nat × Val)
  | .binary .iadd ty a b =>
    match constAt tms ty b, constAt tms ty a with
    | some kb, _ => foldAdd tms ty a kb
    | none, some ka => foldAdd tms ty b ka
    | none, none => none
  | .binary .isub ty a b =>
    match constAt tms ty b with
    | some kb => (foldAdd tms ty a (-kb)).orElse fun _ => some (a, ⟨ty, -kb⟩)
    | none => none
  | _ => none

/-- **Affine constants** (Cranelift's reassociation of constants, `cprop.isle`): a node with an
affine form `(y, K)` (`affPlan`) is `iadd ty y K`, the constant `K` looked up (`findTm`; the
checker interns it first, `affAux`). -/
def affStep (tms : Array Tm) (i : Inst) : Option Tm :=
  (affPlan tms i).bind fun (y, K) =>
    (findTm tms (.node (.iconst K.ty K.bits))).map fun kc => .node (.binary .iadd K.ty y kc)

/-- The constant `affStep` looks up. -/
def affAux (tms : Array Tm) (i : Inst) : List Tm :=
  (affPlan tms i).toList.map fun (_, K) => .node (.iconst K.ty K.bits)

/-- **Constants on the right** (Cranelift's `cprop.isle` commutativity rules): `op ty k x` with
`op` commutative, `k` a constant and `x` not: `op ty x k`. -/
def swapStep (tms : Array Tm) : Inst → Option Tm
  | .binary op ty a b =>
    if commOp op && (constOf tms a).isSome && (constOf tms b).isNone then
      some (.node (.binary op ty b a))
    else none
  | _ => none

/-- The operations whose result truncated is the operation on the truncated operands. -/
def ringOp : BinaryOp → Bool
  | .iadd | .isub | .imul | .band | .bor | .bxor => true
  | _ => false

/-- The term standing for `ireduce ty a` under the normaliser `n`: what `n` makes of the node,
else the node itself (`findTm`). -/
def redOf (n : Norm) (tms : Array Tm) (ty : Ty) (a : Nat) : Option Nat :=
  findTm tms ((n tms (.ireduce ty a)).getD (.node (.ireduce ty a)))

/-- `op ty a' b'` with `b'` a neutral constant of `op` at type `ty` (`rNeutral`), or `a'` one and
`op` commutative: the other term. In `narrowStep` both terms stand for an `ireduce ty`, so the
other one has type `ty` whenever it has a value, and needs no static type (family 6). -/
def narrowId (tms : Array Tm) (op : BinaryOp) (ty : Ty) (a' b' : Nat) : Option Tm :=
  match constAt tms ty b' with
  | some kv => if rNeutral op kv then tms[a']? else none
  | none =>
    match constAt tms ty a' with
    | some kv => if commOp op && rNeutral op kv then tms[b']? else none
    | none => none

/-- **Narrowed `ireduce`** (typed): `ireduce ty (op wty a b)` with `op` a ring operation and `a`,
`b` of static type `wty` wider than `ty`: `op ty a' b'` with `a'`, `b'` the terms of
`ireduce ty a`, `ireduce ty b` under `n` (`redOf`; the checker interns them first,
`narrowAux`), then `narrowId`, `affStep` or `swapStep` on that node. -/
def narrowStep (n : Norm) (aty : Tm → Option Ty) (tms : Array Tm) : Inst → Option Tm
  | .ireduce ty u =>
    match nodeAt tms u with
    | some (.binary op wty a b) =>
      if ringOp op && ty.width < wty.width && tyAt aty tms a == some wty &&
          tyAt aty tms b == some wty then
        (redOf n tms ty a).bind fun a' => (redOf n tms ty b).map fun b' =>
          let j := Inst.binary op ty a' b'
          ((narrowId tms op ty a' b').orElse fun _ =>
            (affStep tms j).orElse fun _ => swapStep tms j).getD (.node j)
      else none
    | _ => none
  | _ => none

/-- The terms `narrowStep` looks up: `ireduce ty a`, `ireduce ty b`. -/
def narrowAux (tms : Array Tm) : Inst → List Tm
  | .ireduce ty u =>
    match nodeAt tms u with
    | some (.binary op wty a b) =>
      if ringOp op && ty.width < wty.width then [.node (.ireduce ty a), .node (.ireduce ty b)]
      else []
    | _ => []
  | _ => []

/-! ### Family 5: negations and nested truncations

Three more shapes of the `rewrite:operand` tail (#1119 issuecomment-7165335641, agent
MidendNext3), after Cranelift 0.135.0's `opts/arithmetic.isle` (`x + (-y)`, `(-x) * k`) and
`opts/extends.isle` (`ireduce` of `ireduce`); each keeps the operands of the node, so it holds in
every frame where they are typed (`FV/Opt/Proof/MidValNormFam5.lean`). -/

/-- `iadd ty a (ineg ty y)`, or `iadd ty (ineg ty y) b`: `isub ty a y` (`isub ty b y`). -/
def addNeg (tms : Array Tm) (ty : Ty) (a b : Nat) : Option Tm :=
  match nodeAt tms b with
  | some (.unary .ineg ty' y) => if ty' == ty then some (.node (.binary .isub ty a y)) else none
  | _ =>
    match nodeAt tms a with
    | some (.unary .ineg ty' y) => if ty' == ty then some (.node (.binary .isub ty b y)) else none
    | _ => none

/-- `imul ty a k` with `a` an `ineg ty x` and `k` a constant of type `ty`: `(x, -k)`. -/
def mulNegPlan (tms : Array Tm) (ty : Ty) (a b : Nat) : Option (Nat × BitVec ty.width) :=
  match nodeAt tms a, constAt tms ty b with
  | some (.unary .ineg ty' x), some k => if ty' == ty then some (x, -k) else none
  | _, _ => none

/-- `imul ty (ineg ty x) k`: `imul ty x (-k)` (`mulNegPlan`; the constant `-k` looked up, the
checker interns it first, `fam5Aux`). -/
def mulNeg (tms : Array Tm) (ty : Ty) (a b : Nat) : Option Tm :=
  (mulNegPlan tms ty a b).bind fun (x, k) =>
    (findTm tms (.node (.iconst ty k))).map fun kc => .node (.binary .imul ty x kc)

/-- `ireduce ty (ireduce ty2 x)` with `x` of static type `xt` (`tyAt`), `ty` narrower than `ty2`
and `ty2` narrower than `xt`: `ireduce ty x`. Without the typing the rewrite is false: for an
`x` of a width between `ty`'s and `ty2`'s the inner `ireduce` has no value, the result has one. -/
def redRed (aty : Tm → Option Ty) (tms : Array Tm) (ty : Ty) (u : Nat) : Option Tm :=
  match nodeAt tms u with
  | some (.ireduce ty2 x) =>
    match tyAt aty tms x with
    | some xt =>
      if ty.width < ty2.width && ty2.width < xt.width then some (.node (.ireduce ty x)) else none
    | none => none
  | _ => none

/-- **Family 5** (typed through `redRed`): `addNeg`, `mulNeg`, `redRed`. -/
def fam5Step (aty : Tm → Option Ty) (tms : Array Tm) : Inst → Option Tm
  | .binary .iadd ty a b => addNeg tms ty a b
  | .binary .imul ty a b => mulNeg tms ty a b
  | .ireduce ty u => redRed aty tms ty u
  | _ => none

/-- The constant `fam5Step` looks up (`mulNeg`'s `-k`). -/
def fam5Aux (tms : Array Tm) : Inst → List Tm
  | .binary .imul ty a b => (mulNegPlan tms ty a b).toList.map fun (_, k) => .node (.iconst ty k)
  | _ => []

/-! ### Family 6: shifts and bitwise constants

The shapes around shifts and masks in the `rewrite:operand` tail (#1119
issuecomment-7200665739, agent MidendNext5), after Cranelift 0.135.0's `opts/shifts.isle` and
`opts/cprop.isle`. Each keeps the operands of the node, so it holds in every frame where they are
typed (`FV/Opt/Proof/MidValNormFam6.lean`):

* `fam6Mul` (first in `Norm.base`: `Norm.alg` turns `imul x 2^s` into `ishl x s` and the result
  is not normalised again): `imul ty a 2^s` and `iadd ty a a` (`s = 1`) with `a` a shift by a
  constant are the shift of `a` by `s` (`shlPlan`): `(y << k) << s` is `y << (k mod w + s)` below
  the width `w`, `(y >> s) << s` (`ushr` or `sshr`) is `y & (-1 << s)` at a width of at most 64;
* `shAmt` (typed): a shift or rotation amount given as an `uextend`/`sextend` of a narrower term
  or an `ireduce` of a wider term of at most 64 bits is that term (the amount counts modulo the
  width, which divides `2^8`, and the low 8 bits are kept);
* `reStep`: `op (op x k1) k2` is `op x (k1 op k2)` for `band`, `bor`, `bxor`, `imul`, and
  `imul (ishl x k) c` is `imul x (c << (k mod w))`;
* `narrowId` (in `narrowStep`): a neutral constant the narrowing of `ireduce` leaves. -/

/-- `imul ty a c` with `c` the constant `2^s` of type `ty`, `0 < s < width`, or `iadd ty a a`
(`s = 1`): `(a, s)`, the node being `a << s`. -/
def mulShAmt (tms : Array Tm) (ty : Ty) : BinaryOp → Nat → Nat → Option (Nat × Nat)
  | .imul, a, c =>
    match constAt tms ty c with
    | some k =>
      if 2 ^ k.toNat.log2 == k.toNat && 0 < k.toNat.log2 && k.toNat.log2 < ty.width then
        some (a, k.toNat.log2)
      else none
    | none => none
  | .iadd, a, b => if a == b then some (a, 1) else none
  | _, _, _ => none

/-- `a << s` for `a` a shift of `y` of type `ty` by a constant `K`: `ishl ty y K'` with `K' = K mod
w + s` (a constant of `K`'s type) when that is below the width `w`; `band ty y M` with `M = -1 <<
s` when `a` is an `ushr`/`sshr` by `s` at a width of at most 64 (`shifts.isle`). The node's
operator, `y` and its constant. -/
def shlPlan (tms : Array Tm) (ty : Ty) (a s : Nat) : Option (BinaryOp × Nat × Val) :=
  match nodeAt tms a with
  | some (.binary op ty' y k) =>
    match constOf tms k with
    | some K =>
      if ty' != ty then none
      else if op == .ishl then
        if K.bits.toNat % ty.width + s < ty.width then
          some (.ishl, y, ⟨K.ty, BitVec.ofNat K.ty.width (K.bits.toNat % ty.width + s)⟩)
        else none
      else if (op == .ushr || op == .sshr) && K.bits.toNat == s && ty.width ≤ 64 then
        some (.band, y, ⟨ty, BitVec.allOnes ty.width <<< s⟩)
      else none
    | none => none
  | _ => none

/-- **Shifts written as multiplications** (module doc of family 6): the node `shlPlan` gives for
`mulShAmt`'s `(a, s)`, its constant looked up (the checker interns it first, `fam6Aux`). -/
def fam6Mul (tms : Array Tm) : Inst → Option Tm
  | .binary op ty a b =>
    (mulShAmt tms ty op a b).bind fun (a', s) => (shlPlan tms ty a' s).bind fun (op', y, K) =>
      (findTm tms (.node (.iconst K.ty K.bits))).map fun kc => .node (.binary op' ty y kc)
  | _ => none

/-- **Shift amounts** (typed; `shifts.isle`): `op ty x b` with `op` a shift or rotation and `b` an
`uextend`/`sextend` of a term `y` of a narrower static type, or an `ireduce` of a term `y` of a
wider static type of at most 64 bits: `op ty x y`. Without the typing the rewrite is false: an
extension of a `y` that is not narrower has no value, `op ty x y` may have one. -/
def shAmt (aty : Tm → Option Ty) (tms : Array Tm) : Inst → Option Tm
  | .binary op ty x b =>
    if op.isShift then
      match nodeAt tms b with
      | some (.extend _ ety y) =>
        match tyAt aty tms y with
        | some yt => if yt.width < ety.width then some (.node (.binary op ty x y)) else none
        | none => none
      | some (.ireduce rty y) =>
        match tyAt aty tms y with
        | some yt =>
          if rty.width < yt.width && yt.width ≤ 64 then some (.node (.binary op ty x y)) else none
        | none => none
      | _ => none
    else none
  | _ => none

/-- The constant `k1 op k2` for the associative `band`, `bor`, `bxor`, `imul`. -/
def reOp {w : Nat} (op : BinaryOp) (k1 k2 : BitVec w) : Option (BitVec w) :=
  match op with
  | .band => some (k1 &&& k2)
  | .bor => some (k1 ||| k2)
  | .bxor => some (k1 ^^^ k2)
  | .imul => some (k1 * k2)
  | _ => none

/-- `op ty (op ty x k1) k2` with `op` one of `band`, `bor`, `bxor`, `imul` and `k1`, `k2`
constants of type `ty`: `(x, k1 op k2)` (`cprop.isle`); `imul ty (ishl ty x k) k2` with `k` a
constant: `(x, k2 << (k mod w))`. -/
def rePlan (tms : Array Tm) (op : BinaryOp) (ty : Ty) (a b : Nat) :
    Option (Nat × BitVec ty.width) :=
  match constAt tms ty b, nodeAt tms a with
  | some k2, some (.binary op' ty' x k) =>
    if ty' != ty then none
    else if op' == op then (constAt tms ty k).bind fun k1 => (reOp op k1 k2).map fun c => (x, c)
    else if op == .imul && op' == .ishl then
      (constOf tms k).map fun K => (x, k2 <<< (K.bits.toNat % ty.width))
    else none
  | _, _ => none

/-- **Constants reassociated** (module doc of family 6): `op ty x c` for `rePlan`'s `(x, c)`, the
constant looked up (the checker interns it first, `fam6Aux`). -/
def reStep (tms : Array Tm) : Inst → Option Tm
  | .binary op ty a b =>
    (rePlan tms op ty a b).bind fun (x, c) =>
      (findTm tms (.node (.iconst ty c))).map fun kc => .node (.binary op ty x kc)
  | _ => none

/-- **Family 6** after family 5 (typed through `shAmt`): `shAmt`, then `reStep`. -/
def fam6Step (aty : Tm → Option Ty) (tms : Array Tm) (i : Inst) : Option Tm :=
  (shAmt aty tms i).orElse fun _ => reStep tms i

/-- The constants family 6 looks up (`shlPlan`'s and `rePlan`'s). -/
def fam6Aux (tms : Array Tm) : Inst → List Tm
  | .binary op ty a b =>
    (((mulShAmt tms ty op a b).bind fun (a', s) => shlPlan tms ty a' s).toList.map
      fun (_, _, K) => .node (.iconst K.ty K.bits)) ++
    (rePlan tms op ty a b).toList.map fun (_, c) => .node (.iconst ty c)
  | _ => []

/-- Everything but the narrowing: family 6's shifts written as multiplications (`fam6Mul`), then
`Norm.std`, the typed rules, then family 4's neutral constants, affine constants and constants on
the right, then families 5 and 6. -/
def Norm.base (f : Function) : Norm :=
  Norm.orElse
    (Norm.orElse (Norm.orElse (Norm.guard fam6Mul) Norm.std) (Norm.guard (typedStep (atomTy f))))
    (Norm.orElse (Norm.guard (idStep (atomTy f)))
      (Norm.orElse (Norm.guard affStep)
        (Norm.orElse (Norm.guard swapStep)
          (Norm.orElse (Norm.guard (fam5Step (atomTy f))) (Norm.guard (fam6Step (atomTy f)))))))

/-- `Norm.base`, then the narrowing with the operands' terms under `Norm.narrowN f k`
(`k` nested narrowings). -/
def Norm.narrowN (f : Function) : Nat → Norm
  | 0 => Norm.base f
  | k + 1 => Norm.orElse (Norm.base f) (Norm.guard (narrowStep (Norm.narrowN f k) (atomTy f)))

/-- **The validator's default normaliser** for `f` (the default `norm` of `check`, `emit`,
`checkCert`, `checkCertSyms`): `Norm.std`, the typed rules with `f`'s atom types, family 4
(`Norm.base`, then up to three nested narrowings, `Norm.narrowN`); proved sound under typing
(`normSoundT_stdT`). -/
def Norm.stdT (f : Function) : Norm := Norm.narrowN f 3

/-- Intern a term (normalised, if a node), without auxiliary terms. -/
def intern1 (t : Tm) : M Nat := do
  let s ← get
  let t := match t with
    | .node i => (s.norm s.tms i).getD t
    | _ => t
  match s.ids.get? t with
  | some i => pure i
  | none =>
    let i := s.tms.size
    set { s with tms := s.tms.push t, ids := s.ids.insert t i }
    pure i

/-- The terms `selTyped` looks up for `select ty c x y` (`iconst tc 0`, then the comparison of
`c` with it), interned first when its arms are the constants `1, 0` or `0, 1`. -/
def internSelAux (ty : Ty) (c x y : Nat) : M Unit := do
  let s ← get
  match nodeAt s.tms c with
  | some (.icmp ..) => pure ()
  | _ =>
    match tyAt s.aty s.tms c, constAt s.tms ty x, constAt s.tms ty y with
    | some tc, some vx, some vy =>
      if tc.isInt then
        if let some cc := selCC vx vy then
          let z ← intern1 (.node (.iconst tc 0))
          discard (intern1 (.node (.icmp cc tc c z)))
    | _, _, _ => pure ()

/-- The node `narrowStep` builds for `ireduce ty u` (before `affStep`/`swapStep`), its operands'
terms under `n`, if any. -/
def narrowNode (n : Norm) (tms : Array Tm) : Inst → Option Inst
  | .ireduce ty u =>
    match nodeAt tms u with
    | some (.binary op wty a b) =>
      if ringOp op && ty.width < wty.width then
        (redOf n tms ty a).bind fun a' => (redOf n tms ty b).map fun b' => .binary op ty a' b'
      else none
    | _ => none
  | _ => none

/-- Intern a term; for a node, first the terms a rule may look up (`auxTms`, `internSelAux`,
`affAux`, `fam5Aux`, `fam6Aux`; `narrowAux` interned the same way, `d` levels deep, then the
constant `affStep` looks up for the narrowed node). -/
def internD : Nat → Tm → M Nat
  | 0, t => do
    if let .node i := t then
      for a in auxTms (← get).tms i do discard (intern1 a)
      if let .select ty c x y := i then internSelAux ty c x y
      for a in fam5Aux (← get).tms i do discard (intern1 a)
      for a in fam6Aux (← get).tms i do discard (intern1 a)
    intern1 t
  | d + 1, t => do
    if let .node i := t then
      for a in auxTms (← get).tms i do discard (intern1 a)
      if let .select ty c x y := i then internSelAux ty c x y
      for a in affAux (← get).tms i do discard (intern1 a)
      for a in fam5Aux (← get).tms i do discard (intern1 a)
      for a in fam6Aux (← get).tms i do discard (intern1 a)
      for a in narrowAux (← get).tms i do discard (internD d a)
      let s ← get
      if let some j := narrowNode s.norm s.tms i then
        for a in affAux s.tms j do discard (intern1 a)
    intern1 t

/-- Intern a term with its auxiliary terms (`internD`, four levels). -/
def intern (t : Tm) : M Nat := internD 4 t

/-- The term of `v` on one side. -/
def termOf (env : Std.HashMap ValueId Nat) (side : String) (v : ValueId) : Except Reject Nat :=
  match env.get? v with
  | some t => pure t
  | none => throw s!"wf:undefined {side} v{v}"

def mapM' (env : Std.HashMap ValueId Nat) (side : String) (i : Inst) : Except Reject Inst := do
  for v in operands i do discard (termOf env side v)
  pure (mapOperands (fun v => env.getD v 0) i)

def mapTermM (env : Std.HashMap ValueId Nat) (side : String) (t : Terminator) :
    Except Reject Terminator := do
  for v in termOperands t do discard (termOf env side v)
  pure (mapTerm (fun v => env.getD v 0) t)

/-- Context of one function pair. -/
structure Ctx where
  pre : Array Nat
  post : Array Nat
  ver : Array Ver
  /-- Value types of `f` and `g` (`wfCheck`). -/
  fty : ValueId → Option Ty
  gty : ValueId → Option Ty
  /-- The partial pure nodes `g` may evaluate anywhere (the hoisting mode: the instructions
  `f` contains, `hasInst f`; otherwise none). -/
  hoistable : Inst → Bool := fun _ => false

def Ctx.dom (c : Ctx) (a b : Nat) : Bool :=
  c.pre[a]! ≤ c.pre[b]! && c.post[b]! ≤ c.post[a]!

/-- The instruction of a `node` term (`nop` otherwise; reasons only). -/
def Tm.inst : Tm → Inst
  | .node i => i
  | _ => .nop

/-- A fact at `key` usable in block `b`. -/
def lookupFact (c : Ctx) (key : Key) (b : Nat) : M (Option Nat) := do
  let s ← get
  let r := ((s.facts.getD key #[]).find? fun (_, d) => c.dom d b).map (·.1)
  if let some v := r then modify fun s => { s with usedMem := s.usedMem.insert (key, v) }
  pure r

def addFact (key : Key) (t b : Nat) : M Unit :=
  modify fun s => { s with facts := s.facts.insert key ((s.facts.getD key #[]).push (t, b)) }

/-- The memory location an access of `f` (term operands) reads or writes. -/
def keyOf (ver : Ver) : Inst → Option (Key × Option Nat)
  | .load op ty fl p off => some ({ ver, addr := p, off, ty, kind := loadKind op, endian := fl.endianness }, none)
  | .store op ty fl x p off => some ({ ver, addr := p, off, ty, kind := storeKind op, endian := fl.endianness }, some x)
  | _ => none

/-- Bind the results of a pure statement on one side. -/
def bindPure (c : Ctx) (side : String) (st : Stmt) (bi seg : Nat) (fSide : Bool) : M Unit := do
  let s ← get
  let env := if fSide then s.envF else s.envG
  -- totality: `g` may evaluate a pure node where `f` does not, so every pure node must be
  -- unable to be `stuck` on its (checked) operand types; `Opt.check` types the `isPure` ones
  if !floatTyped (if fSide then c.fty else c.gty) st.inst then
    throw s!"wf:{side} float typing"
  let i ← liftE (mapM' env side st.inst)
  let t ← intern (.node i)
  match st.results with
  | [r] =>
    if fSide then
      modify fun s => { s with envF := s.envF.insert r t }
      if partialK st.inst then
        modify fun s => { s with partials := s.partials.insert t ((s.partials.getD t #[]).push (bi, seg)) }
    else
      modify fun s => { s with envG := s.envG.insert r t }
  | _ => throw s!"wf:pure arity {side}"

def bindRes (fSide : Bool) (rs : List ValueId) (bi k : Nat) : M (List Nat) := do
  let mut ts := []
  for (r, j) in rs.zipIdx do
    let t ← intern (.res bi k j)
    ts := ts ++ [t]
    if fSide then modify fun s => { s with envF := s.envF.insert r t }
    else modify fun s => { s with envG := s.envG.insert r t }
  pure ts

/-- The reason when `f`'s skeleton statement `s` (class `cls` if `g`'s next statement has
another shape) has no counterpart: an operand rewrite when `g`'s next statement has the same
shape, a moved `can_move` load, else `cls`. -/
def missReason (fid : BlockId) (s : Stmt) (gt? : Option Stmt) (cls : String) (det : String := "") :
    Reject :=
  match gt? with
  | some t =>
    if shape t.inst == shape s.inst then s!"rewrite:operand {opName s.inst} {det} block{fid}"
    else if movedLoad t.inst then s!"alias:load-moved block{fid}"
    else s!"{cls} {opName s.inst}/{opName t.inst} block{fid}"
  | none => if movedLoad s.inst then s!"alias:load-moved block{fid}"
    else s!"{cls} {opName s.inst} block{fid}"
where
  movedLoad : Inst → Bool
    | .load _ _ fl _ _ => fl.canMove
    | _ => false

/-- Bind the result of `f`'s statement `s` (at most one) to term `t`. -/
def bindF (s : Stmt) (t : Nat) : M Unit :=
  match s.results with
  | [r] => modify fun st => { st with envF := st.envF.insert r t }
  | [] => pure ()
  | _ => throw "wf:arity"

/-- `f`'s skeleton statement `s` (term operands `s'`) at statement `k` of block `bi`, memory
version `ver`, has no counterpart in `g` (whose next statement is `gt?`): accept it when its
removal is justified (module doc), else reject. -/
def removeF (c : Ctx) (fid : BlockId) (bi k : Nat) (ver : Ver) (s : Stmt) (s' : Inst)
    (gt? : Option Stmt) (t'? : Option Inst) : M Unit := do
  let tms := (← get).tms
  let det := match t'? with
    | some t' => diffOps tms (operands s') (operands t')
    | none => ""
  match s' with
  | .load _ _ fl _ _ =>
    let some (key, _) := keyOf ver s' | throw "wf:internal"
    if let some v ← lookupFact c key bi then
      bindF s v
    else if fl.trapCode.isNone then
      bindF s (← intern (.poison bi k))
      if let some t := gt? then
        if shape t.inst == shape s.inst && (← get).hint.isNone then
          modify fun st => { st with hint := some s!"rewrite:operand load(poisoned) {det} block{fid}" }
    else throw (missReason fid s gt? "alias:load" det)
  | .store _ _ _ x _ _ =>
    let some (key, _) := keyOf ver s' | throw "wf:internal"
    if (← lookupFact c key bi) != some x then throw (missReason fid s gt? "alias:store" det)
  | i =>
    if !mergeK i then throw (missReason fid s gt? "rewrite:skeleton-removed" det)
    let nt ← intern (.node s')
    let some (rt, _) := ((← get).merges.getD nt #[]).find? (fun (_, d) => c.dom d bi)
      | throw (missReason fid s gt? "rewrite:skeleton-removed" det)
    modify fun st => { st with usedMerge := st.usedMerge.insert nt }
    match rt with
    | some v => bindF s v
    | none => if s.results.isEmpty then pure () else throw "wf:merge arity"

/-- `g` evaluates the partial term `pt` in block `bi` before `f`'s skeleton segment `seg`
(layout index `bi`, block id `fid`): accepted when `f` evaluated it no later (same block and no
later segment, or a dominating block), or, in the hoisting mode, when `f` contains its
instruction (`Ctx.hoistable`; the soundness theorem of that mode assumes the function's global
values resolve, `globalsResolve`). -/
def place (c : Ctx) (bi seg : Nat) (fid : BlockId) (pt : Nat) : M Unit := do
  let s ← get
  let ok := (s.partials.getD pt #[]).any fun (d, sf) =>
    (d == bi && sf ≤ seg) || (d != bi && c.dom d bi)
  if ok then
    modify fun st => { st with usedPart := st.usedPart.insert pt }
  else if c.hoistable (s.tms[pt]!.inst) then
    modify fun st => { st with usedHoist := st.usedHoist.insert pt }
  else throw s!"placement:{opName (s.tms[pt]!.inst)} block{fid}"

/-- Check one block (layout index `bi`). -/
def checkBlock (c : Ctx) (bi : Nat) (fb gb : Block) : M Unit := do
  if fb.params.map (·.2) != gb.params.map (·.2) then throw s!"shape:params block{fb.id}"
  for ((p, _), i) in fb.params.zipIdx do
    let t ← intern (.param bi i)
    modify fun s => { s with envF := s.envF.insert p t }
  for ((p, _), i) in gb.params.zipIdx do
    let t ← intern (.param bi i)
    modify fun s => { s with envG := s.envG.insert p t }
  let fs := fb.body.toArray
  let gs := gb.body.toArray
  let mut k := 0
  let mut k' := 0
  let mut seg := 0
  let mut ver := c.ver[bi]!
  -- partial pure terms of `g` awaiting the segment of the next match
  let mut pend : Array Nat := #[]
  for _ in [0:fs.size + gs.size + 2] do
    -- pure runs
    while k < fs.size do
      let st := fs[k]!
      if st.inst == .nop then
        k := k + 1
        continue
      if !pureK st.inst then break
      bindPure c "f" st bi seg true
      k := k + 1
    while k' < gs.size do
      let st := gs[k']!
      if st.inst == .nop then
        k' := k' + 1
        continue
      if !pureK st.inst then break
      bindPure c "g" st bi seg false
      if partialK st.inst then
        if let [r] := st.results then
          pend := pend.push ((← get).envG.getD r 0)
      k' := k' + 1
    match fs[k]?, gs[k']? with
    | none, none => break
    | some s, gt? =>
      let s' ← liftE (mapM' (← get).envF "f" s.inst)
      let t'? ← match gt? with
        | some t => do pure (some (← liftE (mapM' (← get).envG "g" t.inst)))
        | none => pure none
      let matched := match gt?, t'? with
        | some t, some t' => s' == t' && s.results.length == t.results.length
        | _, _ => false
      if matched then
        let some t := gt? | throw "wf:internal"
        -- pending partial terms of `g` are evaluated before this statement
        for pt in pend do place c bi seg fb.id pt
        pend := #[]
        let ts ← bindRes true s.results bi k
        discard (bindRes false t.results bi k)
        if writerK s.inst then ver := .at bi k'
        if let some (key, dat?) := keyOf ver s' then
          match dat? with
          | none => addFact key (ts.headD 0) bi
          | some x => addFact key x bi
        if mergeK s.inst then
          let nt ← intern (.node s')
          modify fun st => { st with merges := st.merges.insert nt ((st.merges.getD nt #[]).push (ts.head?, bi)) }
        k := k + 1
        k' := k' + 1
        seg := seg + 1
      else
        -- `f`'s statement has no counterpart in `g`
        removeF c fb.id bi k ver s s' gt? t'?
        k := k + 1
        seg := seg + 1
    | none, some t =>
      throw (missReason fb.id t none "rewrite:skeleton-added")
  for pt in pend do place c bi seg fb.id pt
  let ft ← liftE (mapTermM (← get).envF "f" fb.term)
  let gt ← liftE (mapTermM (← get).envG "g" gb.term)
  if ft != gt then
    let s ← get
    let chain := if s.cond then match ft, gt with
      | .brif c t e, .brif c' t' e' =>
        if t == t' && e == e' then condChain s.tms s.tms.size c c' else none
      | _, _ => none
      else none
    if let some ws := chain then
      modify fun st => { st with conds := st.conds.push (gb.id, ws.reverse) }
    else if termName fb.term == termName gb.term && termSuccs fb.term == termSuccs gb.term then
      throw s!"rewrite:operand {termName fb.term} {diffOps s.tms (termOperands ft) (termOperands gt)} block{fb.id}"
    else throw s!"rewrite:term {termName fb.term}/{termName gb.term} block{fb.id}"

/-- The check, returning its final state, context and `f`'s `wfCheck` info on acceptance
(certificate emission, `Opt.MidVal.emit`). `hoist`: the hoisting mode (`place`). `cond`: a
`brif` condition of `f` that is `g`'s under wrappers is recorded instead of rejected (family 3:
`St.conds`, the hints of `condPrep`; such a state is not a certificate's). -/
def checkRun (f g : Function) (norm : Norm := Norm.stdT f) (hoist : Bool := false)
    (cond : Bool := false) : Except Reject (St × Ctx × Info) := do
  if !(sameHeader f g && g.sigDecls == f.sigDecls) then throw "shape:header"
  let fi ← (wfCheck f).mapError (s!"wf:f {·}")
  let gi ← (wfCheck g).mapError (s!"wf:g {·}")
  if g.blocks.map (·.id) != f.blocks.map (·.id) then throw "rewrite:blocks"
  -- the entry block takes the function's arguments: the same parameters (ids and types)
  if g.blocks.head?.map (·.params) != f.blocks.head?.map (·.params) then throw "shape:entry params"
  if gi.cfg.idom != fi.cfg.idom then throw "rewrite:domtree"
  let (pre, post, order) := domIntervals fi.cfg.idom
  let c : Ctx := { pre, post, ver := versions g gi.cfg, fty := fi.types.get?, gty := gi.types.get?,
                   hoistable := fun i => hoist && partialK i && hasInst f i }
  let fbs := f.blocks.toArray
  let gbs := g.blocks.toArray
  let go : M Unit := do
    for bi in order do
      checkBlock c bi fbs[bi]! gbs[bi]!
  let (r, st) := (go.run).run { norm, cond, aty := atomTy f }
  match r, st.hint with
  | .ok (), _ => pure (st, c, fi)
  | .error e, some h => throw (if e.startsWith "wf:" || e.startsWith "placement" then e else h)
  | .error e, none => throw e

/-- **The validator** (module doc): `f` is the unoptimised function after `Opt.ConstPhi.run`,
`g` cg_clif's optimised one. `.ok ()` accepts `g` for `f`. `hoist`: also accept `g` evaluating
a `symbol_value`/`func_addr`/`tls_value` of `f` earlier than `f` does (`place`). -/
def check (f g : Function) (norm : Norm := Norm.stdT f) (hoist : Bool := false) : Except Reject Unit :=
  (checkRun f g norm hoist).map fun _ => ()

end Opt.MidVal

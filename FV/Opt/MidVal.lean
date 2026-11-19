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

Not accepted (stage 1): any ISLE rewrite (new pure terms at compared positions, changed
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
(#1119): the soundness theorem takes it with the one hypothesis that it preserves values;
stage 1 uses `Norm.id`, and each proven rewrite (constant evaluation, single `simplify` rules)
can be added as one more `Norm` with its own preservation lemma. -/
abbrev Norm := Array Tm → Inst → Option Tm

/-- The identity normaliser (stage 1). -/
def Norm.id : Norm := fun _ _ => none

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
  /-- The normaliser of pure nodes (`Norm`): the identity in stage 1. -/
  norm : Norm := Norm.id
  /-- The facts a removal used (certificate emission, `FV/Opt/MidValCert.lean`): memory
  locations with their value, merged trapping nodes, partial terms. -/
  usedMem : Std.HashSet (Key × Nat) := {}
  usedMerge : Std.HashSet Nat := {}
  usedPart : Std.HashSet Nat := {}

/-- The checker's monad; the state survives a rejection (for `St.hint`). -/
abbrev M := ExceptT Reject (StateM St)

def liftE {α : Type} : Except Reject α → M α
  | .ok a => pure a
  | .error r => throw r

/-- **Measurement variant only** (`midval-check --fold`): the value of a pure node whose
operands are all constants, by `Clif.evalInst` (no rewrite rule: the semantics itself). -/
def evalConst : Norm := fun tms i => do
  let ops := operands i
  if ops.isEmpty || !isPure i || partialK i then none
  let vals ← ops.mapM fun o => match (tms[o]? : Option Tm) with
    | some (Tm.node (Inst.iconst ty imm)) => some (Val.mk ty imm)
    | _ => (none : Option Val)
  let regs : Regs := fun x => (ops.zip vals).lookup x
  let fr : Frame := { func := default, regs, slots := [], body := [], term := .ret [] }
  match evalInst fr Mem.empty i with
  | .ok ([v], _) => some (.node (.iconst v.ty v.bits))
  | _ => none

def intern (t : Tm) : M Nat := do
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
  /-- Value types of `f` and `g` (`Opt.check`). -/
  fty : ValueId → Option Ty
  gty : ValueId → Option Ty

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
        for pt in pend do
          let ok := ((← get).partials.getD pt #[]).any fun (d, sf) =>
            (d == bi && sf ≤ seg) || (d != bi && c.dom d bi)
          if !ok then throw s!"placement:{opName ((← get).tms[pt]!.inst)} block{fb.id}"
          modify fun st => { st with usedPart := st.usedPart.insert pt }
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
  for pt in pend do
    let ok := ((← get).partials.getD pt #[]).any fun (d, sf) =>
      (d == bi && sf ≤ seg) || (d != bi && c.dom d bi)
    if !ok then throw s!"placement:{opName ((← get).tms[pt]!.inst)} block{fb.id}"
    modify fun st => { st with usedPart := st.usedPart.insert pt }
  let ft ← liftE (mapTermM (← get).envF "f" fb.term)
  let gt ← liftE (mapTermM (← get).envG "g" gb.term)
  if ft != gt then
    if termName fb.term == termName gb.term && termSuccs fb.term == termSuccs gb.term then
      throw s!"rewrite:operand {termName fb.term} {diffOps (← get).tms (termOperands ft) (termOperands gt)} block{fb.id}"
    else throw s!"rewrite:term {termName fb.term}/{termName gb.term} block{fb.id}"

/-- The check, returning its final state, context and `f`'s `wfCheck` info on acceptance
(certificate emission, `Opt.MidVal.emit`). -/
def checkRun (f g : Function) (norm : Norm := Norm.id) : Except Reject (St × Ctx × Info) := do
  if !(sameHeader f g && g.sigDecls == f.sigDecls) then throw "shape:header"
  let fi ← (wfCheck f).mapError (s!"wf:f {·}")
  let gi ← (wfCheck g).mapError (s!"wf:g {·}")
  if g.blocks.map (·.id) != f.blocks.map (·.id) then throw "rewrite:blocks"
  -- the entry block takes the function's arguments: the same parameters (ids and types)
  if g.blocks.head?.map (·.params) != f.blocks.head?.map (·.params) then throw "shape:entry params"
  if gi.cfg.idom != fi.cfg.idom then throw "rewrite:domtree"
  let (pre, post, order) := domIntervals fi.cfg.idom
  let c : Ctx := { pre, post, ver := versions g gi.cfg, fty := fi.types.get?, gty := gi.types.get? }
  let fbs := f.blocks.toArray
  let gbs := g.blocks.toArray
  let go : M Unit := do
    for bi in order do
      checkBlock c bi fbs[bi]! gbs[bi]!
  let (r, st) := (go.run).run { norm }
  match r, st.hint with
  | .ok (), _ => pure (st, c, fi)
  | .error e, some h => throw (if e.startsWith "wf:" || e.startsWith "placement" then e else h)
  | .error e, none => throw e

/-- **The validator** (module doc): `f` is the unoptimised function after `Opt.ConstPhi.run`,
`g` cg_clif's optimised one. `.ok ()` accepts `g` for `f`. -/
def check (f g : Function) (norm : Norm := Norm.id) : Except Reject Unit :=
  (checkRun f g norm).map fun _ => ()

end Opt.MidVal

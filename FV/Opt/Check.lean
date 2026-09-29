import FV.Opt.Cfg
import FV.Clif.Sem

/-!
# Well-formedness: the precondition of every pass

`Opt.check f` succeeds iff `f` (with every block reachable) is in strict SSA form and its pure
nodes are well-typed:

* every value is defined once (block parameter or instruction result);
* every use is dominated by its definition (same block: defined earlier; other block: the
  defining block strictly dominates the using block; block arguments are uses at the end of
  the branching block);
* result arities match `Inst.resultTypes`, branch arities and argument types match the target
  block's parameters, and the entry block's parameters match the signature;
* every pure node's operands have the types `Clif.evalInst` requires (so on a well-formed
  function a pure node never evaluates to `stuck`, except `symbol_value` of a symbol missing
  from the link-time image).

This is what makes the passes' rewrites semantically justified: dominance gives "the most
recent definition of each operand is the same at the old and the new position" (the GVN and
LICM arguments in `docs/contracts/midend.md`), typing gives "a moved or duplicated pure node
cannot fail". `Info` carries the facts the passes reuse.
-/

namespace Opt

open Clif

structure Info where
  cfg : Cfg
  /-- Type of every value. -/
  types : Std.HashMap ValueId Ty
  /-- Defining block (layout index) of every value. -/
  defBlock : Std.HashMap ValueId Nat
  /-- The pure node defining a value, if any. -/
  pureDef : Std.HashMap ValueId Inst
  deriving Inhabited

def ensure (b : Bool) (msg : String) : Except String Unit :=
  if b then pure () else throw msg

/-- Operand typing of pure nodes (mirrors `Clif.evalInst`); `ty v` is the type of `v`. -/
def pureTyped (ty : ValueId → Option Ty) (f : Function) : Inst → Bool
  | .iconst _ _ => true
  | .unary _ t x => ty x == some t
  | .binary op t x y => ty x == some t && (op.isShift && (ty y).isSome || ty y == some t)
  | .icmp _ t x y => ty x == some t && ty y == some t
  | .select t c x y => (ty c).isSome && ty x == some t && ty y == some t
  | .bitselect t c x y => ty c == some t && ty x == some t && ty y == some t
  | .bmask _ x => (ty x).isSome
  | .extend _ t x => match ty x with | some s => s.width < t.width | none => false
  | .ireduce t x => match ty x with | some s => t.width < s.width | none => false
  | .iconcat t lo hi => t.double?.isSome && ty lo == some t && ty hi == some t
  | .bitcast t _ x => ty x == some t
  | .stackAddr _ s _ => (f.slots.lookup s).isSome
  | .symbolValue _ gv => match f.globals.lookup gv with
    | some (.symbol ..) => true
    | _ => false
  | _ => true

/-! ## Declarative certificate (`FV/Opt/Proof/Dom*.lean`)

`check` also runs `wfCert`, a restatement of the facts the proofs use in a form they can
reason about: each value's unique definition site (`defSites`, looked up through a map that
must agree with every site), availability of every use through the dominator tree `idom`
(walked by `ancB`), the *edge certificate* (for every edge `u → b`, `idom b` is a tree ancestor
of `u`, which makes every tree ancestor of a block a dominator of it), strictly decreasing RPO
numbers along `idom` (so the tree is acyclic), unique block ids, and the typing of
definitions and pure nodes. -/

/-- Definition sites: `(v, i, 0)` for a parameter of block `i`, `(v, i, j + 1)` for a result
of statement `j` of block `i`. -/
def defSites (f : Function) : List (ValueId × Nat × Nat) :=
  f.blocks.zipIdx.flatMap fun (b, i) =>
    b.params.map (fun p => (p.1, i, 0)) ++
      b.body.zipIdx.flatMap fun (st, j) => st.results.map fun r => (r, i, j + 1)

/-- Definition site of every value (the last one in `defSites` order; `wfCert` checks that
there is only one). -/
def defMap (f : Function) : Std.HashMap ValueId (Nat × Nat) :=
  (defSites f).foldl (fun m (v, s) => m.insert v s) {}

/-- Is `a` an ancestor of `b` (reflexive) in the tree `idom`, within `fuel` steps up? -/
def ancB (idom : Array (Option Nat)) : Nat → Nat → Nat → Bool
  | 0, a, b => a == b
  | fuel + 1, a, b => a == b || match idom[b]?.join with
    | some c => ancB idom fuel a c
    | none => false

/-- Is `v` available before statement `k` of block `i` (`k` = body length: at the
terminator)? -/
def availB (dm : ValueId → Option (Nat × Nat)) (anc : Nat → Nat → Bool) (i k : Nat)
    (v : ValueId) : Bool :=
  match dm v with
  | some (d, t) => (d == i && t ≤ k) || (d != i && anc d i)
  | none => false

/-- The declarative well-formedness certificate (module section doc). -/
def wfCert (f : Function) (cfg : Cfg) (types : Std.HashMap ValueId Ty) : Bool :=
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
      (match st.inst.resultTypes sigOf (fun _ => none) with
       | some ts => ts.length == st.results.length && (st.results.zip ts).all fun (r, t) => tm r == some t
       | none => false) &&
      (!isPure st.inst || pureTyped tm f st.inst)) &&
    (termOperands b.term).all (availB dm anc i b.body.length) &&
    (termSuccs b.term).all fun id => match cfg.index.get? id with
      | some j => (blocks[j]?.map (·.id)) == some id && match cfg.idom[j]?.join with
        | some c => anc c i
        | none => true
      | none => false)

/-- The imperative part of `check`. -/
def checkCore (f : Function) : Except String Info := do
  let cfg := Cfg.build f
  ensure (cfg.size > 0) "no blocks"
  ensure (cfg.index.size == cfg.size) "duplicate block ids"
  for i in [0:cfg.size] do
    ensure (cfg.reachable i) s!"unreachable block{cfg.ids[i]!}"
  let blocks := f.blocks.toArray
  let sigOf := fun r => (f.externs.lookup r).map (·.sig)
  -- definitions
  let mut types : Std.HashMap ValueId Ty := {}
  let mut defBlock : Std.HashMap ValueId Nat := {}
  let mut pureDef : Std.HashMap ValueId Inst := {}
  for (b, i) in blocks.zipIdx do
    for (v, t) in b.params do
      ensure (!types.contains v) s!"v{v} defined twice"
      types := types.insert v t
      defBlock := defBlock.insert v i
    for st in b.body do
      let some ts := st.inst.resultTypes sigOf (fun _ => none) | throw s!"ill-formed instruction defining {st.results}"
      ensure (ts.length == st.results.length) s!"result arity of {st.results}"
      for (v, t) in st.results.zip ts do
        ensure (!types.contains v) s!"v{v} defined twice"
        types := types.insert v t
        defBlock := defBlock.insert v i
      if isPure st.inst then
        if let [v] := st.results then pureDef := pureDef.insert v st.inst
  ensure ((blocks[0]!.params.map (·.2)) == f.sig.params.map (·.ty)) "entry parameters ≠ signature"
  let ty := fun v => types.get? v
  -- uses
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
        ensure (pureTyped ty f st.inst) s!"block{b.id}: ill-typed pure instruction defining {st.results}"
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

/-- The well-formedness check (module doc): `checkCore` and the certificate `wfCert`. Expects
every block to be reachable (`removeUnreachable`); unreachable blocks are rejected. -/
def check (f : Function) : Except String Info := do
  let info ← checkCore f
  ensure (wfCert f info.cfg info.types) "certificate rejected (Opt.wfCert)"
  return info

end Opt

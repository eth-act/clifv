import FV.Opt.Check
import FV.Opt.OptimizeX

/-!
# `Opt.ConstPhi`: Cranelift's constant-phi removal (#990)

Cranelift's `Context::optimize` runs `eliminate_unreachable_code` and then
`remove_constant_phis` at every optimisation level (`cranelift/codegen/src/context.rs:189-190`,
`remove_constant_phis.rs`; byte-identical in cg_clif's Cranelift 0.136.1 and in wasmtime v49.0.1).
The pass removes each parameter of a non-entry block that can only hold one value, renames its
uses to that value and drops the matching argument of every edge into the block. It changes
the code Cranelift lowers (e.g. `runtests/br_table.clif %br_table_upper_reg`,
`runtests/brif.clif %brif_different_args` and `%fuzzgen_2`), so Lean runs it to produce the same
code.

This file is the executable part, without proofs:

* `solve` (untrusted): the analysis of `remove_constant_phis.rs` (Phase 2). Each parameter of a
  reachable non-entry block (Group A) starts at `AbsVal.none`. For every edge out of a reachable
  block, each argument is joined into the destination's parameter: a Group A value gives its
  current state, any other value `v` gives `one v`, a `try_call` result or exception payload
  (`TryArg.ret`/`.exn`, Cranelift's `BlockArg::TryCallRet`/`TryCallExn`) gives `many`. The
  iteration stops when nothing changes (the least fixed point, so the order of the visits does
  not change the result). The parameters at `one v` are the solution `[(p, v)]`.
* `apply f sol` (Phase 3): drop the solved parameters, rename every operand and argument by the
  solution (`σ`), and drop the arguments at the solved positions of every edge (`filterTerm`).
* `cpOk f sol`: the checker the correctness proof relies on (the solution is not trusted).
  `f` is well-formed (`Opt.check`: strict SSA, every block reachable); the solved parameters
  are distinct parameters of non-entry blocks; no solution value is solved itself; the
  definition of each solution value strictly dominates the block of its parameter; every edge
  into a block passes, at each solved position, a value (not a `try_call` result or payload)
  that renames to the solution; the result is well-formed; and a function with a `try_call` or
  `try_call_indirect` keeps its fresh value (where those calls bind their results,
  `Clif.Function.freshValue`).
* `run f` (the pass): when `freshOkB f`, remove the unreachable blocks (as Cranelift does
  first, `Opt.removeUnreachable`), solve, and apply the solution if it is not empty and
  `cpOk` accepts it; otherwise `f` unchanged.
-/

namespace Opt.ConstPhi

open Clif

/-! ## The analysis -/

/-- The abstract value of a parameter (`AbstractValue`): no value, exactly one value, or more
than one value flows to it. -/
inductive AbsVal where
  | none
  | one (v : ValueId)
  | many
  deriving DecidableEq, Repr, Inhabited

/-- `AbstractValue::join`. -/
def AbsVal.join : AbsVal → AbsVal → AbsVal
  | .none, b => b
  | a, .none => a
  | .many, _ => .many
  | _, .many => .many
  | .one a, .one b => if a = b then .one a else .many

/-- The edges of a terminator with their arguments (`branch_destination`, in Cranelift's
order): the destination block id and the arguments, `none` for a `try_call` result or
exception payload. -/
def edges : Terminator → List (BlockId × List (Option ValueId))
  | .jump d => [(d.block, d.args.map some)]
  | .brif _ t e => [(t.block, t.args.map some), (e.block, e.args.map some)]
  | .brTable _ d t => (d.block, d.args.map some) :: t.map fun c => (c.block, c.args.map some)
  | .tryCall _ _ et | .tryCallIndirect _ _ et =>
    et.dests.map fun d => (d.block, d.args.map fun | .val v => some v | _ => none)
  | _ => []

/-- One visit of the edges out of the reachable blocks (in reverse postorder), joining every
argument into its destination's parameter; `none` if an edge goes to the entry block or its
arity is not the destination's (Cranelift asserts both away). -/
def sweep (c : Cfg) (blocks : Array Block) (st : Std.HashMap ValueId AbsVal) :
    Option (Std.HashMap ValueId AbsVal × Bool) := Id.run do
  let mut st := st
  let mut changed := false
  for src in c.rpo do
    let some b := blocks[src]? | return none
    for (dst, args) in edges b.term do
      if args.isEmpty then continue
      let some di := c.index[dst]? | return none
      if di == 0 then return none
      let some db := blocks[di]? | return none
      if db.params.length != args.length then return none
      for ((formal, _), a) in db.params.zip args do
        let av : AbsVal := match a with
          | some v => st[v]?.getD (.one v)
          | none => .many
        let old := st[formal]?.getD .none
        let new := old.join av
        if new != old then
          changed := true
          st := st.insert formal new
  return some (st, changed)

/-- **The solution** (untrusted; module doc): the parameters of reachable non-entry blocks that
receive exactly one value, with that value, in layout order. Empty if the analysis does not
apply (an edge to the entry block, an arity mismatch, no fixed point within the bound). -/
def solve (f : Function) : List (ValueId × ValueId) := Id.run do
  let c := Cfg.build f
  let blocks := f.blocks.toArray
  let mut st : Std.HashMap ValueId AbsVal := {}
  let mut formals : Array ValueId := #[]
  for bi in c.rpo do
    if bi == 0 then continue
    let some b := blocks[bi]? | return []
    for (p, _) in b.params do
      st := st.insert p .none
      formals := formals.push p
  -- every change raises one formal (none < one < many): at most `2 · formals` changing sweeps
  let mut fixed := false
  for _ in [0:2 * formals.size + 2] do
    match sweep c blocks st with
    | none => return []
    | some (st', changed) =>
      st := st'
      if !changed then
        fixed := true
        break
  if !fixed then return []
  let inLayout := f.blocks.flatMap fun b => b.params.map (·.1)
  return inLayout.filterMap fun p => match (st[p]? : Option AbsVal) with
    | some (AbsVal.one v) => some (p, v)
    | _ => none

/-! ## The rewrite -/

/-- The solution as a map. -/
def solMap (sol : List (ValueId × ValueId)) : Std.HashMap ValueId ValueId :=
  sol.foldl (fun m (p, v) => m.insert p v) {}

/-- The renaming of a solution: a solved parameter to its value, every other value to itself. -/
def rename (m : Std.HashMap ValueId ValueId) (x : ValueId) : ValueId := m[x]?.getD x

/-- Keep the elements whose flag is `true`; elements past the flags are kept. -/
def filt {α : Type} : List Bool → List α → List α
  | b :: bs, x :: xs => if b then x :: filt bs xs else filt bs xs
  | [], xs => xs
  | _ :: _, [] => []

/-- For each block id (its first block in layout order), which parameters are kept. -/
def keepMap (m : Std.HashMap ValueId ValueId) (f : Function) :
    Std.HashMap BlockId (List Bool) :=
  f.blocks.foldl (fun acc b => if acc.contains b.id then acc
    else acc.insert b.id (b.params.map fun p => !m.contains p.1)) {}

/-- The kept-parameter flags of block `id` (`[]`, keeping every argument, for an unknown id). -/
def keepOf (k : Std.HashMap BlockId (List Bool)) (id : BlockId) : List Bool := k[id]?.getD []

def filterBC (k : Std.HashMap BlockId (List Bool)) (c : BlockCall) : BlockCall :=
  { c with args := filt (keepOf k c.block) c.args }

def filterTD (k : Std.HashMap BlockId (List Bool)) (d : TryDest) : TryDest :=
  { d with args := filt (keepOf k d.block) d.args }

def filterEt (k : Std.HashMap BlockId (List Bool)) (et : ExnTable) : ExnTable :=
  { et with normal := filterTD k et.normal, items := et.items.map fun
    | .tag n d => .tag n (filterTD k d)
    | .default d => .default (filterTD k d)
    | .context v => .context v }

/-- Drop the arguments at the removed positions of every edge. -/
def filterTerm (k : Std.HashMap BlockId (List Bool)) : Terminator → Terminator
  | .jump d => .jump (filterBC k d)
  | .brif c t e => .brif c (filterBC k t) (filterBC k e)
  | .brTable x d t => .brTable x (filterBC k d) (t.map (filterBC k))
  | .tryCall fn args et => .tryCall fn args (filterEt k et)
  | .tryCallIndirect c args et => .tryCallIndirect c args (filterEt k et)
  | t => t

/-- **The rewrite** (Phase 3): the solved parameters removed, every operand and argument
renamed, the removed positions' arguments dropped. -/
def apply (f : Function) (sol : List (ValueId × ValueId)) : Function :=
  let m := solMap sol
  let k := keepMap m f
  { f with blocks := f.blocks.map fun b =>
      { b with params := b.params.filter (fun p => !m.contains p.1),
               body := b.body.map fun s => { s with inst := mapOperands (rename m) s.inst },
               term := filterTerm k (mapTerm (rename m) b.term) } }

/-! ## The checker -/

/-- `f` has a `try_call` or `try_call_indirect` terminator. -/
def hasTry (f : Function) : Bool := f.blocks.any (·.term.isTry)

/-- **The checker** (module doc). -/
def cpOk (f : Function) (sol : List (ValueId × ValueId)) : Bool :=
  match check f with
  | .error _ => false
  | .ok fi =>
    let m := solMap sol
    let dmap := defMap f
    let idom := fi.cfg.idom
    let blocks := f.blocks.toArray
    let keys := sol.map (·.1)
    let g := apply f sol
    -- distinct parameters of non-entry blocks; no chains; the value's definition strictly
    -- dominates the parameter's block
    keys.Nodup && sol.all (fun (p, v) =>
      !m.contains v && match dmap[p]?, dmap[v]? with
        | some (bp, 0), some (dv, _) => bp != 0 && dv != bp && ancB idom idom.size dv bp
        | _, _ => false) &&
    -- every edge passes, at each solved position, a value renaming to the solution
    blocks.all (fun b => (edges b.term).all fun (dst, args) =>
      match fi.cfg.index[dst]? with
      | some di => match blocks[di]? with
        | some db => (db.params.zip args).all fun ((p, _), a) =>
            !m.contains p || match a with
              | some x => rename m x == rename m p
              | none => false
        | none => false
      | none => false) &&
    (check g).toBool &&
    (!hasTry f || g.freshValue == f.freshValue)

/-! ## The pass -/

/-- **Constant-phi removal** (module doc): `apply` of the solution on `f` without its
unreachable blocks when the solution is not empty and `cpOk` accepts it, else `f`. -/
def run (f : Function) : Function :=
  if !freshOkB f then f else
  let f1 := removeUnreachable f
  let sol := solve f1
  if sol.isEmpty then f
  else if cpOk f1 sol then apply f1 sol else f

end Opt.ConstPhi

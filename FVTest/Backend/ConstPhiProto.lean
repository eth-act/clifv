import FV.Opt.Cfg
import FV.Clif.Parse

/-!
LOCAL PROTOTYPE (unproved, uncommitted; #990 scoping): Cranelift's `remove_constant_phis`
(`cranelift/codegen/src/remove_constant_phis.rs`, run by `Context::optimize` at every opt level).
A parameter of a reachable non-entry block whose every incoming argument (from reachable blocks)
is one value `v` that is not such a parameter itself (or the parameter itself, or another
parameter with the same solution) is removed; its uses become `v`, and the matching arguments of
every edge into its block are dropped.
-/

namespace ConstPhiProto

open Clif Opt

inductive AV where
  | none | one (v : ValueId) | many
  deriving BEq, Inhabited, Repr

def AV.join : AV → AV → AV
  | .none, b => b
  | a, .none => a
  | .many, _ => .many
  | _, .many => .many
  | .one a, .one b => if a == b then .one a else .many

/-- The edges of a terminator with block arguments: destination and arguments (`none`: a
`try_call` return or exception payload, `BlockArg::TryCallRet`/`TryCallExn`, which is `Many`). -/
def edges : Terminator → List (BlockId × List (Option ValueId))
  | .jump d => [(d.block, d.args.map some)]
  | .brif _ t e => [(t.block, t.args.map some), (e.block, e.args.map some)]
  | .brTable _ d t => (d.block, d.args.map some) :: t.map fun c => (c.block, c.args.map some)
  | .tryCall _ _ et | .tryCallIndirect _ _ et =>
    et.dests.map fun d => (d.block, d.args.map fun | .val v => some v | _ => none)
  | _ => []

/-- The solution: removed parameter ↦ its single value. -/
def solve (f : Function) : Std.HashMap ValueId ValueId := Id.run do
  let c := Cfg.build f
  let blocks := f.blocks.toArray
  if blocks.isEmpty then return {}
  let mut st : Std.HashMap ValueId AV := {}
  for bi in c.rpo do
    if bi == 0 then continue
    for (p, _) in blocks[bi]!.params do
      st := st.insert p .none
  let fuel := 3 * st.size + 3
  for _ in [0:fuel] do
    let mut changed := false
    for src in c.rpo do
      for (dst, args) in edges blocks[src]!.term do
        if args.isEmpty then continue
        let some di := c.index.get? dst | continue
        if di == 0 then return {}
        let formals := blocks[di]!.params
        if formals.length != args.length then return {}
        for ((formal, _), a) in formals.zip args do
          let av := match a with
            | some v => (st.get? v).getD (.one v)
            | none => .many
          let old := (st.get? formal).getD .none
          let new := old.join av
          if new != old then
            changed := true
            st := st.insert formal new
    if !changed then break
  return st.fold (init := {}) fun m k v => match v with
    | .one w => m.insert k w
    | _ => m

/-- Remove the solved parameters, their arguments, and rename their uses. -/
def apply (f : Function) (sol : Std.HashMap ValueId ValueId) : Function :=
  if sol.isEmpty then f else
  let σ : ValueId → ValueId := fun v => (sol.get? v).getD v
  let keep : Std.HashMap BlockId (List Bool) :=
    f.blocks.foldl (fun m b => if m.contains b.id then m
      else m.insert b.id (b.params.map fun p => !sol.contains p.1)) {}
  let filt {α : Type} (dst : BlockId) (args : List α) : List α :=
    match keep.get? dst with
    | some ks => if ks.length == args.length then
        ((ks.zip args).filter (·.1)).map (·.2) else args
    | none => args
  let bc (c : BlockCall) : BlockCall := { c with args := filt c.block (c.args.map σ) }
  let td (d : TryDest) : TryDest :=
    { d with args := filt d.block (d.args.map fun | .val v => .val (σ v) | a => a) }
  let et (t : ExnTable) : ExnTable :=
    { t with normal := td t.normal, items := t.items.map fun
      | .tag n d => .tag n (td d)
      | .default d => .default (td d)
      | .context v => .context (σ v) }
  let term : Terminator → Terminator
    | .jump d => .jump (bc d)
    | .brif c t e => .brif (σ c) (bc t) (bc e)
    | .brTable x d t => .brTable (σ x) (bc d) (t.map bc)
    | .ret vs => .ret (vs.map σ)
    | .returnCall fn args => .returnCall fn (args.map σ)
    | .trap c => .trap c
    | .tryCall fn args t => .tryCall fn (args.map σ) (et t)
    | .tryCallIndirect c args t => .tryCallIndirect (σ c) (args.map σ) (et t)
  { f with blocks := f.blocks.map fun b =>
      { b with params := b.params.filter (fun p => !sol.contains p.1),
               body := b.body.map fun s => { s with inst := mapOperands σ s.inst },
               term := term b.term } }

def run (f : Function) : Function := apply f (solve f)

/-- The number of parameters `run` removes. -/
def removed (f : Function) : Nat := (solve f).size

def file (pf : ParsedFile) : ParsedFile :=
  { pf with funcs := pf.funcs.map fun p => match p.func with
      | .ok f => { p with func := .ok (run f) }
      | .error _ => p }

end ConstPhiProto

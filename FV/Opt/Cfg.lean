import FV.Opt.Basic

/-!
# Control-flow graph, dominator tree, natural loops

Blocks are identified by their *index* in layout order (`Function.blocks`); index 0 is the
entry block. Dominators are computed with the Cooper–Harvey–Kennedy iterative algorithm over
the reverse postorder. Unreachable blocks have no `rpoNum`, no `idom` and are ignored by every
analysis (`Opt.removeUnreachable` deletes them before the passes run).

All loops are bounded by explicit fuel derived from the graph size, so every function here is
total and computable without `partial`.
-/

namespace Opt

open Clif

structure Cfg where
  /-- Block ids in layout order. -/
  ids : Array BlockId
  /-- Block id → layout index (first occurrence). -/
  index : Std.HashMap BlockId Nat
  succs : Array (List Nat)
  preds : Array (List Nat)
  /-- Reachable blocks in reverse postorder (entry first). -/
  rpo : Array Nat
  /-- Position of each block in `rpo` (`none`: unreachable). -/
  rpoNum : Array (Option Nat)
  /-- Immediate dominator (`none` for the entry block and unreachable blocks). -/
  idom : Array (Option Nat)
  deriving Inhabited

namespace Cfg

def size (c : Cfg) : Nat := c.ids.size

def reachable (c : Cfg) (b : Nat) : Bool := (c.rpoNum[b]?.join).isSome

/-- Depth-first postorder from the entry block (successors in terminator order). -/
def postorder (succs : Array (List Nat)) : Array Nat := Id.run do
  let n := succs.size
  if n == 0 then return #[]
  let fuel := 2 * (n + succs.foldl (· + ·.length) 0) + 2
  let mut visited := (Array.replicate n false).set! 0 true
  let mut stack : Array (Nat × List Nat) := #[(0, succs[0]!)]
  let mut post : Array Nat := #[]
  for _ in [0:fuel] do
    match stack.back? with
    | none => break
    | some (b, []) =>
      post := post.push b
      stack := stack.pop
    | some (b, s :: rest) =>
      stack := stack.pop.push (b, rest)
      if !visited[s]! then
        visited := visited.set! s true
        stack := stack.push (s, succs[s]!)
  return post

/-- Cooper–Harvey–Kennedy: iterate `idom b := ⋂ preds` in RPO until stable. -/
def dominators (preds : Array (List Nat)) (rpo : Array Nat) (rpoNum : Array (Option Nat)) :
    Array (Option Nat) := Id.run do
  let n := preds.size
  if n == 0 then return #[]
  let num (b : Nat) : Nat := (rpoNum[b]?.join).getD n
  let mut idom : Array (Option Nat) := (Array.replicate n none).set! 0 (some 0)
  for _ in [0:n + 2] do
    let mut changed := false
    for b in rpo do
      if b == 0 then continue
      let mut new : Option Nat := none
      for p in preds[b]! do
        if idom[p]!.isNone then continue
        match new with
        | none => new := some p
        | some q =>
          -- intersect p q
          let mut a := p
          let mut c := q
          for _ in [0:2 * n + 2] do
            if a == c then break
            if num a > num c then a := idom[a]!.getD 0
            else c := idom[c]!.getD 0
          new := some a
      if new != idom[b]! then
        idom := idom.set! b new
        changed := true
    if !changed then break
  return idom.set! 0 none

def build (f : Function) : Cfg := Id.run do
  let ids := f.blocks.toArray.map (·.id)
  let index : Std.HashMap BlockId Nat :=
    ids.zipIdx.foldl (fun m (b, i) => if m.contains b then m else m.insert b i) {}
  let succs := f.blocks.toArray.map fun b => ((termSuccs b.term).filterMap index.get?).eraseDups
  let mut preds : Array (List Nat) := Array.replicate ids.size []
  for (ss, i) in succs.zipIdx do
    for s in ss do
      preds := preds.modify s (· ++ [i])
  let rpo := (postorder succs).reverse
  let mut rpoNum : Array (Option Nat) := Array.replicate ids.size none
  for (b, k) in rpo.zipIdx do
    rpoNum := rpoNum.set! b (some k)
  let idom := dominators preds rpo rpoNum
  return { ids, index, succs, preds, rpo, rpoNum, idom }

/-- Does block `a` dominate block `b` (reflexive)? `false` if either is unreachable. -/
def dominates (c : Cfg) (a b : Nat) : Bool := Id.run do
  if !c.reachable a || !c.reachable b then return false
  let mut x := b
  for _ in [0:c.size + 1] do
    if x == a then return true
    match c.idom[x]! with
    | some y => x := y
    | none => return false
  return false

/-- Children of each block in the dominator tree, in RPO order. -/
def domChildren (c : Cfg) : Array (List Nat) := Id.run do
  let mut ch : Array (List Nat) := Array.replicate c.size []
  for b in c.rpo.reverse do
    if let some d := c.idom[b]! then
      ch := ch.modify d (b :: ·)
  return ch

/-- Blocks in dominator-tree preorder (children in RPO order). Every block appears after its
immediate dominator. -/
def domPreorder (c : Cfg) : Array Nat := Id.run do
  if c.size == 0 then return #[]
  let ch := c.domChildren
  let mut out : Array Nat := #[]
  let mut stack : Array Nat := #[0]
  for _ in [0:c.size + 1] do
    match stack.back? with
    | none => break
    | some b =>
      stack := stack.pop
      out := out.push b
      stack := stack ++ (ch[b]!).reverse.toArray
  return out

/-- A natural loop: header and body (header included), as layout indices. -/
structure Loop where
  header : Nat
  body : Std.HashSet Nat

/-- Natural loops, one per header (bodies of back edges into the same header are merged).
A back edge is `b → h` with `h` dominating `b`. -/
def loops (c : Cfg) : Array Loop := Id.run do
  let mut out : Array Loop := #[]
  for h in c.rpo do
    let latches := c.preds[h]!.filter fun b => c.dominates h b
    if latches.isEmpty then continue
    let mut body : Std.HashSet Nat := ({} : Std.HashSet Nat).insert h
    let mut work := latches.toArray
    for _ in [0:c.size + 1] do
      if work.isEmpty then break
      let mut next : Array Nat := #[]
      for b in work do
        if body.contains b || !c.reachable b then continue
        body := body.insert b
        next := next ++ c.preds[b]!.toArray
      work := next
    out := out.push { header := h, body }
  return out

end Cfg

/-- The blocks reachable from the entry block. -/
def removeUnreachableRaw (f : Function) : Function :=
  let c := Cfg.build f
  { f with blocks := (f.blocks.zipIdx.filter fun (_, i) => c.reachable i).map (·.1) }

/-- The header of a function (everything but the blocks and run commands) is unchanged. -/
def sameHeader (f g : Function) : Bool :=
  g.name == f.name && g.sig == f.sig && g.slots == f.slots && g.globals == f.globals &&
    g.externs == f.externs

/-- Validator of `removeUnreachableRaw` (`FV/Opt/Proof/Unreachable.lean`): `g` keeps the header,
a subset of the blocks and the entry block of `f`, and every branch target of a kept block
resolves to the same block in `g` as in `f`. -/
def unreachableOk (f g : Function) : Bool :=
  sameHeader f g && g.blocks.head? == f.blocks.head? &&
    g.blocks.all (fun b => f.blocks.contains b &&
      (termSuccs b.term).all fun id => (g.block? id).isSome && g.block? id == f.block? id)

/-- Delete the blocks that are unreachable from the entry block. They are never executed by
`Clif.run` (blocks are looked up by id, only when branched to), so this preserves the
semantics exactly. The result is validated (`unreachableOk`); if validation fails, `f` is
returned unchanged. -/
def removeUnreachable (f : Function) : Function :=
  let g := removeUnreachableRaw f
  if unreachableOk f g then g else f

end Opt

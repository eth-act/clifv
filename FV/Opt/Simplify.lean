import FV.Opt.Check
import FV.Opt.Cost
import FV.Opt.Rules

/-!
# Simplify: rule-based rewriting of pure nodes (an acyclic e-graph, à la Cranelift)

The pass visits the blocks in reverse postorder (every block after its dominators) and the
statements of each block in order. For a pure statement `v = n` (operands renamed by the
substitution built so far) it does what Cranelift's `insert_pure_enode` /
`optimize_pure_enode` do (`egraph/mod.rs`):

1. insert `n` as the node of `v`;
2. call the rule set's `simplify` on `v`. Rules see each operand's *e-class* (its node plus
   the equivalent nodes recorded when it was rewritten) and create nodes with `make`, which
   are themselves simplified recursively (rewrite depth ≤ `rewriteLimit` = 5, Cranelift's
   `REWRITE_LIMIT`); created nodes are *virtual* until needed;
3. build the e-class of `v`: at most `matchesLimit` = 5 candidates, sorted by value number
   and deduplicated; a `subsume` candidate replaces the class; otherwise the class is `v` plus
   the candidates, up to `eclassLimit` = 5 nodes (`MATCHES_LIMIT`, `ECLASS_ENODE_LIMIT`);
4. extract the best member by `(cost, value number)` (`Opt.Cost`, Cranelift's
   `compute_best_values`);
5. if the best is `v`, keep the statement; otherwise *materialise* the best value in place
   (emit the virtual nodes its tree needs, in dependency order, right before the position of
   `v`; a virtual value already emitted in a block that does not dominate the current one is
   cloned under a fresh number) and rename `v` to it.

Differences from Cranelift, all on the conservative side: nodes are materialised where the
rewritten statement was (placement/remat/LICM are separate passes); `make` does not
deduplicate against earlier statements (the next GVN pass does); an e-class is only visible
to later matches through its representative when that representative was created by this
statement (so every node of a visible class can be materialised wherever the class is used).

**Invariant (for the proof).** Every emitted statement is a pure node whose operands are
defined at its position (dominance), and every renaming `v ↦ w` has `w` equal to `v` by the
rule set's obligation (`Opt.SimplifyFn`) — so each step is a local, value-preserving
replacement. Nodes outside `allowed` (e.g. outside the backend subset E) get infinite cost
and are never emitted.
-/

namespace Opt

open Clif

def rewriteLimit : Nat := 5
def matchesLimit : Nat := 5
def eclassLimit : Nat := 5

structure SimplifyStats where
  /-- Statements replaced by a different value. -/
  rewritten : Nat := 0
  /-- Statements materialised (new nodes emitted). -/
  emitted : Nat := 0
  /-- Rule-set errors (the statement is kept). -/
  errors : Nat := 0
  /-- Number of candidates per rule name (fired, whether chosen or not). -/
  fired : Std.HashMap String Nat := {}
  deriving Inhabited

structure SState where
  /-- The pure node of every value that has one (original statements and created nodes). -/
  defs : Std.HashMap ValueId Inst := {}
  /-- Other members of the e-class represented by a value (see module doc). -/
  alts : Std.HashMap ValueId (List ValueId) := {}
  types : Std.HashMap ValueId Ty := {}
  cost : Std.HashMap ValueId Cost := {}
  next : ValueId
  /-- `make` memo for the current statement: node ↦ its simplified value. -/
  memo : Std.HashMap Inst ValueId := {}
  /-- Values created while rewriting the current statement. -/
  made : Std.HashSet ValueId := {}
  /-- Output block (layout index) of every value defined in the output so far. -/
  avail : Std.HashMap ValueId Nat := {}
  /-- Value → e-class members found for it at its creation (current statement only). -/
  classes : Std.HashMap ValueId (List ValueId) := {}
  stats : SimplifyStats := {}

namespace SState

def costOf (st : SState) (v : ValueId) : Cost := (st.cost.get? v).getD 0

def enodes (st : SState) (v : ValueId) : List Inst :=
  ((st.defs.get? v).toList) ++ ((st.alts.get? v).getD []).filterMap st.defs.get?

/-- Insert a node under a fresh value (no simplification). -/
def insertNode (allowed : Inst → Bool) (st : SState) (n : Inst) : ValueId × SState :=
  let w := st.next
  let ty : Option Ty := match n with
    | .icmp .. => some .i8
    | _ => (n.resultTypes (fun _ => none)).bind List.head?
  let ok := allowed n && ty.isSome
  let c := if ok then (operands n).foldl (fun c x => Cost.add c (st.costOf x)) (Cost.ofInst n)
           else Cost.infinite
  (w, { st with next := w + 1, defs := st.defs.insert w n,
                types := match ty with | some t => st.types.insert w t | none => st.types,
                cost := st.cost.insert w c, made := st.made.insert w })

end SState

/-- Build the e-class of `v` from the rule candidates and return its best member
(steps 3–4 of the module doc); records the class of the best member. -/
def chooseBest (st : SState) (v : ValueId) (cands : List (ValueId × Bool)) : ValueId × SState :=
  let cands := (cands.take matchesLimit).filter (·.1 != v)
  let sorted := (cands.toArray.qsort (fun a b => a.1 < b.1)).toList
  let dedup := sorted.foldl (fun acc c => if acc.any (·.1 == c.1) then acc else acc ++ [c]) []
  let key := fun (x : ValueId) => (st.costOf x, x)
  let better := fun (x y : ValueId) => let (cx, ix) := key x; let (cy, iy) := key y
    cx < cy || (cx == cy && ix < iy)
  match dedup.find? (fun c => c.2 && st.costOf c.1 < Cost.infinite) with
  | some (s, _) => (s, st)
  | none =>
    let members := v :: (dedup.map (·.1)).take (eclassLimit - 1)
    let best := members.foldl (fun b x => if better x b then x else b) v
    (best, { st with classes := st.classes.insert best (members.filter (· != best)) })

/-- Simplify the value `v` of a freshly inserted node, with `d` levels of rewrite depth left
(`make` recurses with one level less). Returns the best value of `v`'s e-class. -/
def optimizeAt (rules : SimplifyFn) (allowed : Inst → Bool) : Nat → SState → ValueId → ValueId × SState
  | 0, st, v => (v, st)
  | d + 1, st, v =>
    let make := fun (st : SState) (n : Inst) =>
      match st.memo.get? n with
      | some w => (w, st)
      | none =>
        let (w, st) := st.insertNode allowed n
        let (b, st) := optimizeAt rules allowed d st w
        (b, { st with memo := st.memo.insert n b })
    match rules SState.enodes (fun st x => st.types.get? x) make st v with
    | .error _ =>
      (v, { st with stats := { st.stats with errors := st.stats.errors + 1 } })
    | .ok (cands, names, st) =>
      let fired := names.foldl (fun m n => m.insert n ((m.get? n).getD 0 + 1)) st.stats.fired
      chooseBest { st with stats := { st.stats with fired } } v cands

/-- Emit `x` at the current position of block `bi` (step 5 of the module doc): available
values are used as they are, virtual ones are emitted (or cloned) after their operands.
`none` if some leaf is neither available nor a pure node. -/
def materialize (cfg : Cfg) (allowed : Inst → Bool) (bi : Nat) :
    Nat → SState × Array Stmt → ValueId → Option (ValueId × SState × Array Stmt)
  | 0, _, _ => none
  | fuel + 1, (st, out), x =>
    match st.avail.get? x with
    | some d => if cfg.dominates d bi then some (x, st, out) else clone fuel st out x
    | none => clone fuel st out x
where
  clone (fuel : Nat) (st : SState) (out : Array Stmt) (x : ValueId) :
      Option (ValueId × SState × Array Stmt) := do
    let n ← st.defs.get? x
    if !allowed n then none
    let (st, out, ops) ← (operands n).foldlM (init := (st, out, #[]))
      fun (st, out, ops) y => do
        let (y', st, out) ← materialize cfg allowed bi fuel (st, out) y
        pure (st, out, ops.push y')
    let opsL := ops.toList
    let n' := mapOperands (fun y => ((operands n).zip opsL).lookup y |>.getD y) n
    let (x', st) := if st.avail.contains x then (st.next, { st with next := st.next + 1 })
                    else (x, st)
    let st := { st with avail := st.avail.insert x' bi, defs := st.defs.insert x' n',
                        types := match st.types.get? x with
                          | some t => st.types.insert x' t | none => st.types,
                        cost := st.cost.insert x' (st.costOf x) }
    pure (x', st, out.push { results := [x'], inst := n' })

/-- The simplify pass. `allowed` restricts the nodes it may emit. -/
def simplify (rules : SimplifyFn) (allowed : Inst → Bool) (f : Function) (info : Info) :
    Function × SimplifyStats := Id.run do
  let cfg := info.cfg
  let blocks := f.blocks.toArray
  let mut st : SState := { next := maxValue f + 1, types := info.types }
  -- parameters and skeleton results are available in their blocks, with cost 0
  for (b, bi) in blocks.zipIdx do
    for (p, _) in b.params do st := { st with avail := st.avail.insert p bi }
    for s in b.body do
      if !(isPure s.inst && s.results.length == 1) then
        for r in s.results do st := { st with avail := st.avail.insert r bi }
  let mut subst : Subst := {}
  let mut out := blocks
  for bi in cfg.rpo do
    let b := blocks[bi]!
    let mut body : Array Stmt := #[]
    for s in b.body do
      let inst := mapOperands subst.find s.inst
      match s.results, isPure inst with
      | [v], true =>
        let c := (operands inst).foldl (fun c x => Cost.add c (st.costOf x)) (Cost.ofInst inst)
        st := { st with defs := st.defs.insert v inst, cost := st.cost.insert v c,
                        memo := {}, made := {}, classes := {} }
        let (best, st1) := optimizeAt rules allowed rewriteLimit st v
        let keep := fun (st : SState) =>
          { st with avail := st.avail.insert v bi }
        if best == v then
          st := keep st1
          body := body.push { s with inst }
        else
          match materialize cfg allowed bi (st1.defs.size + 1) (st1, #[]) best with
          | some (w, st2, emitted) =>
            st := { st2 with stats := { st2.stats with rewritten := st2.stats.rewritten + 1,
                                                        emitted := st2.stats.emitted + emitted.size } }
            body := body ++ emitted
            subst := subst.insert v w
          | none =>
            st := keep st1
            body := body.push { s with inst }
        -- make the class visible to later matches when its representative is new here
        let rep := subst.find v
        if rep == v || st1.made.contains best then
          let members := (st1.classes.get? best).getD []
          if !members.isEmpty then st := { st with alts := st.alts.insert rep members }
      | _, _ => body := body.push { s with inst }
    out := out.set! bi { b with body := body.toList, term := mapTerm subst.find b.term }
  return (subst.apply { f with blocks := out.toList }, st.stats)

end Opt

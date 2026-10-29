module

public import FV.Opt.Check
public import FV.Opt.Cost
public import FV.Opt.Rules

public section

/-!
# Simplify: rule-based rewriting of pure nodes (an acyclic e-graph, à la Cranelift)

The pass visits the blocks in reverse postorder (every block after its dominators) and the
statements of each block in order. For a pure statement `v = n` (operands renamed by the
substitution built so far) it does what Cranelift's `insert_pure_enode` /
`optimize_pure_enode` do (`egraph/mod.rs`):

1. insert `n` as the node of `v`;
2. unless an equal node was seen before (then its value is reused: hash-consing, Cranelift's
   GVN map), call the rule set's `simplify` on `v`. Rules see each operand's *e-class* (its node plus
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

Skeleton statements and terminators go through the rule set's `simplify_skeleton`
(`Opt.SkeletonFn`, chosen as `chooseSkel`; e.g. division by a constant, branches on constants,
branches to trap blocks). This can remove CFG edges; the dominator tree computed before the pass
stays valid (removing edges only adds dominance), and `Opt.optimize` removes the blocks that
became unreachable.

Differences from Cranelift, all on the conservative side: nodes are materialised where the
rewritten statement was (placement/remat/LICM are separate passes); an e-class is only visible
to later matches through its representative when that representative was created by this
statement (so every node of a visible class can be materialised wherever the class is used).
As in Cranelift (`insert_pure_enode`), a statement's node enters the hash-consing table only
after its rules ran, mapped to the best value of its class.

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
  /-- Skeleton instructions / terminators simplified. -/
  skeleton : Nat := 0
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
  /-- Hash-consing of nodes (Cranelift's GVN map): node ↦ the best value of its e-class.
  Global to the function; a hit whose definition does not dominate the use is cloned by
  `materialize`. -/
  memo : Std.HashMap Inst ValueId := {}
  /-- Values created while rewriting the current statement. -/
  made : Std.HashSet ValueId := {}
  /-- Output block (layout index) of every value defined in the output so far. -/
  avail : Std.HashMap ValueId Nat := {}
  /-- Value → e-class members found for it at its creation (current statement only). -/
  classes : Std.HashMap ValueId (List ValueId) := {}
  /-- Rematerialise constants: an `iconst` defined in another block is re-emitted in the
  using block instead of reused (Cranelift's `remat`). -/
  rematConst : Bool := false
  /-- `just_trap_block`: blocks whose body is pure and whose terminator is `trap`. -/
  trapBlocks : Std.HashMap BlockId TrapCode := {}
  stats : SimplifyStats := {}
  /-- The function being simplified (typing of made nodes). -/
  fn : Function
  /-- Partial nodes: nodes `make` records without simplifying them (never with the rule sets of
  `FV/Opt/Optimize.lean`; see `optimizeAt`). They are not in the rules' graph (`enodes`), not
  hash-consed and never candidates. -/
  partials : Std.HashMap ValueId Inst := {}

namespace SState

def costOf (st : SState) (v : ValueId) : Cost := (st.cost.get? v).getD 0

/-- Is `v` a constant to rematerialise per block? -/
def remat (st : SState) (v : ValueId) : Bool :=
  st.rematConst && match st.defs.get? v with
    | some (.iconst ..) => true
    | _ => false

@[expose] def enodes (st : SState) (v : ValueId) : List Inst :=
  ((st.defs.get? v).toList) ++ ((st.alts.get? v).getD []).filterMap st.defs.get?

/-- Insert a node under a fresh value (no simplification). -/
def insertNode (allowed : Inst → Bool) (st : SState) (n : Inst) : ValueId × SState :=
  let w := st.next
  let ty : Option Ty := match n with
    | .icmp .. => some .i8
    | _ => (n.resultTypes (fun _ => none) (fun _ => none)).bind List.head?
  let ok := allowed n && ty.isSome
  let c := if ok then (operands n).foldl (fun c x => Cost.add c (st.costOf x)) (Cost.ofInst n)
           else Cost.infinite
  (w, { st with next := w + 1, defs := st.defs.insert w n,
                types := match ty with | some t => st.types.insert w t | none => st.types,
                cost := st.cost.insert w c, made := st.made.insert w })

/-- `y` is a pure node of the graph or available in the output (a block parameter, a skeleton
result, or an emitted value): nodes over known values only are inserted (see `optimizeAt`). -/
def known (st : SState) (y : ValueId) : Bool := st.defs.contains y || st.avail.contains y

/-- A well-typed pure node (operand types from the graph). -/
def typedNode (st : SState) (n : Inst) : Bool :=
  isPure n && pureTyped (fun x => st.types.get? x) st.fn n

/-- A node over known values: only such nodes enter the graph (the proof of the pass needs
that the value of a node never depends on values the graph does not know yet). -/
def nodeOk (st : SState) (n : Inst) : Bool := (operands n).all st.known

/-- `y` has a node or is available, or is a partial node. -/
def inGraph (st : SState) (y : ValueId) : Bool := st.known y || st.partials.contains y

/-- A fresh value with no node: what `make` returns for a node over values outside the graph
(see `optimizeAt`). -/
def dummy (st : SState) : ValueId × SState := (st.next, { st with next := st.next + 1 })


/-- The type of the single result of a pure node. -/
def nodeTy (n : Inst) : Option Ty := (n.resultTypes (fun _ => none) (fun _ => none)).bind List.head?

/-- The candidates `optimizeAt` keeps for `v`: `v` itself, or known values of `v`'s type. -/
def candOk (st : SState) (v : ValueId) (c : ValueId × Bool) : Bool :=
  c.1 == v || (st.known c.1 && st.types.get? c.1 == st.types.get? v)

/-- Record `n` as the partial node of the fresh `st.next`, with its type (see `optimizeAt`). -/
def insertPartial (st : SState) (n : Inst) : ValueId × SState :=
  (st.next, { st with next := st.next + 1, partials := st.partials.insert st.next n,
                      types := match nodeTy n with
                        | some t => st.types.insert st.next t
                        | none => st.types })

end SState

/-- Build the e-class of `v` from the rule candidates and return its best member
(steps 3–4 of the module doc); records the class of the best member. -/
def chooseBest (st : SState) (v : ValueId) (cands : List (ValueId × Bool)) : ValueId × SState :=
  let cands := (cands.take matchesLimit).filter (·.1 != v)
  -- (the filter keeps every element: it states for the proof that sorting adds none)
  let sorted := (cands.toArray.qsort (fun a b => a.1 < b.1)).toList.filter cands.contains
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
(`make` recurses with one level less). Returns the best value of `v`'s e-class.

Guards (never taken with the rule sets of `FV/Opt/Optimize.lean`; the completeness proof needs
them, `Opt.SimpRulesProv`): `make` hash-conses, inserts and simplifies only well-typed pure nodes
over known values other than `v`. Any other node over graph values is recorded as a partial node
(`SState.insertPartial`: it keeps its value, but is not simplified, not hash-consed and never a
candidate), and a node over values outside the graph gets a fresh value with no node
(`SState.dummy`). Candidates other than `v` must be known values of `v`'s type. -/
@[expose] def optimizeAt (rules : SimplifyFn) (allowed : Inst → Bool) : Nat → SState → ValueId → ValueId × SState
  | 0, st, v => (v, st)
  | d + 1, st, v =>
    let make := fun (st : SState) (n : Inst) =>
      if !(operands n).all st.inGraph then st.dummy else
      if !st.nodeOk n || (operands n).contains v || !st.typedNode n then st.insertPartial n else
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
      let cands := cands.filter (st.candOk v)
      chooseBest { st with stats := { st.stats with fired } } v cands

/-- The state after emitting `x' = n'`, a copy of `x`, in block `bi`. -/
def SState.emit (st : SState) (bi : Nat) (x x' : ValueId) (n' : Inst) : SState :=
  { st with avail := st.avail.insert x' bi, defs := st.defs.insert x' n',
            types := match st.types.get? x with
              | some t => st.types.insert x' t
              | none => st.types,
            cost := st.cost.insert x' (st.costOf x) }

/-- `n` with its operands replaced by their materialised versions `ops` (in operand order). -/
def renameOps (n : Inst) (ops : List ValueId) : Inst :=
  mapOperands (fun y => ((operands n).zip ops).lookup y |>.getD y) n

/-- Emit `x` at the current position of block `bi` (step 5 of the module doc): available
values are used as they are, virtual ones are emitted (or cloned) after their operands.
`none` if some leaf is neither available nor a pure node. -/
def materialize (cfg : Cfg) (allowed : Inst → Bool) (bi : Nat) :
    Nat → SState × Array Stmt → ValueId → Option (ValueId × SState × Array Stmt)
  | 0, _, _ => none
  | fuel + 1, (st, out), x =>
    match st.avail.get? x with
    | some d =>
      if cfg.dominates d bi && !(d != bi && st.remat x) then some (x, st, out)
      else clone fuel st out x
    | none => clone fuel st out x
where
  clone (fuel : Nat) (st : SState) (out : Array Stmt) (x : ValueId) :
      Option (ValueId × SState × Array Stmt) :=
    match st.defs.get? x with
    | none => none
    | some n =>
      if !allowed n || !st.typedNode n || (st.types.get? x).isNone then none else
      let wasAvail := st.avail.contains x
      match (operands n).foldlM (init := (st, out, #[])) (fun (acc : SState × Array Stmt × Array ValueId) y =>
          match materialize cfg allowed bi fuel (acc.1, acc.2.1) y with
          | none => none
          | some (y', st, out) => some (st, out, acc.2.2.push y')) with
      | none => none
      | some (st, out, ops) =>
        -- (a value emitted while materialising its own operands: a cycle, never on real graphs)
        if !wasAvail && st.avail.contains x then none else
        let n' := renameOps n ops.toList
        if wasAvail then
          some (st.next, ({ st with next := st.next + 1 } : SState).emit bi x st.next n',
            out.push { results := [st.next], inst := n' })
        else some (x, st.emit bi x x n', out.push { results := [x], inst := n' })

/-- Materialise a list of values (`materialize` each, left to right). -/
def materializeAll (cfg : Cfg) (allowed : Inst → Bool) (bi : Nat) (st : SState)
    (xs : List ValueId) : Option (List (ValueId × ValueId) × SState × Array Stmt) :=
  xs.foldlM (init := ([], st, #[])) fun (m, st, out) x => do
    let (x', st, out) ← materialize cfg allowed bi (st.defs.size + 1) (st, out) x
    pure (m ++ [(x, x')], st, out)

def rename (m : List (ValueId × ValueId)) (x : ValueId) : ValueId := (m.lookup x).getD x

/-- Cranelift's `Cost::of_skeleton_op` for the instructions skeleton rules produce: opcode
cost 4, +10 if it can trap, + number of operands. -/
def skelCost : Isle.Opt.SkelInst → Nat
  | .inst i => (match i with
      | .div .. | .uaddOverflowTrap .. | .trapz .. | .trapnz .. => 14
      | .load .. => 24
      | _ => 4) + (operands i).length
  | .term t => 4 + (match t with | .brif .. | .brTable .. => 1 | _ => 0)

/-- Cranelift's choice among `simplify_skeleton` results (`simplify_skeleton_inst`): at most
`matchesLimit`, scanned from the last; `Remove*`, `ReplaceBranchCond`, `ReplaceWithTwo` are
taken at once, a `Replace*` only if its skeleton cost is below the best so far (initially the
original's). -/
def chooseSkel (orig : Isle.Opt.SkelInst) (cands : List Isle.Opt.SkelSimp) :
    Option Isle.Opt.SkelSimp :=
  go (cands.take matchesLimit).reverse none (skelCost orig)
where
  go : List Isle.Opt.SkelSimp → Option Isle.Opt.SkelSimp → Nat → Option Isle.Opt.SkelSimp
    | [], best, _ => best
    | c :: cs, best, bestCost =>
      match c with
      | .remove | .removeWithVal _ | .replaceBranchCond _ | .replaceWithTwo .. => some c
      | .replace i | .replaceWithVal i _ =>
        if skelCost i < bestCost then go cs (some c) (skelCost i) else go cs best bestCost

/-- The skeleton instructions and terminators the rules can simplify. -/
def skelCandidate : Isle.Opt.SkelInst → Bool
  | .inst (.div ..) | .inst (.uaddOverflowTrap ..) | .inst (.trapz ..) | .inst (.trapnz ..) => true
  | .term (.brif ..) | .term (.brTable ..) => true
  | _ => false

/-- The block calls of a terminator (`checkCore`'s `calls`). -/
def termCalls : Terminator → List BlockCall
  | .jump d => [d]
  | .brif _ t e => [t, e]
  | .brTable _ d t => d :: t
  | _ => []

/-- Not a `symbol_value`, `tls_value` or `func_addr` (the instructions reading the link-time
symbols). -/
def notSym : Inst → Bool
  | .symbolValue .. | .tlsValue .. | .funcAddr .. => false
  | _ => true

/-- A branch (the terminators the skeleton rules may rewrite). -/
def isBranch : Terminator → Bool
  | .jump .. | .brif .. | .brTable .. => true
  | _ => false

/-- A replacement instruction the pass may emit: over known values, not pure, not reading a
link-time symbol. -/
def skelInstOk (st : SState) (j : Inst) : Bool :=
  !isPure j && notSym j && (operands j).all st.known

/-- A replacement terminator of `t`: a branch over known values whose block calls go where
`t`'s go, with arguments of the same types, and whose `br_table` index is an `i32`. -/
def skelTermOk (st : SState) (t t' : Terminator) : Bool :=
  isBranch t' && (termOperands t').all st.known &&
    (termCalls t').all (fun bc' => (termCalls t).any fun bc =>
      bc'.block == bc.block && bc'.args.map st.types.get? == bc.args.map st.types.get?) &&
    match t' with
    | .brTable x _ _ => st.types.get? x == some .i32
    | _ => true

/-- A skeleton candidate the pass may apply to `i` (a guard never taken with the rule sets of
`FV/Opt/Optimize.lean`; the completeness proof needs it, `Opt.SkelRulesProv`): the values it
mentions are known, and its instructions and terminators are `skelInstOk`/`skelTermOk`. -/
def skelCandOk (st : SState) : Isle.Opt.SkelInst → Isle.Opt.SkelSimp → Bool
  | .inst _, .removeWithVal v => st.known v
  | .inst _, .replace (.inst j) => skelInstOk st j
  | .inst _, .replaceBranchCond c => st.known c
  | .inst _, .replaceWithTwo (.inst a) (.inst b) => skelInstOk st a && skelInstOk st b
  | .term t, .replace (.term t') => skelTermOk st t t'
  | .term _, .replaceBranchCond c => st.known c
  | .term t, .replaceWithTwo (.inst a) (.term t') => skelInstOk st a && skelTermOk st t t'
  | _, _ => true

/-- `make` for the skeleton rules: hash-cons, else insert and simplify (full depth); the
guards of `optimizeAt`. -/
def skelMake (rules : SimplifyFn) (allowed : Inst → Bool) (st : SState) (n : Inst) :
    ValueId × SState :=
  if !(operands n).all st.inGraph then st.dummy else
  if !st.nodeOk n || !st.typedNode n then st.insertPartial n else
  match st.memo.get? n with
  | some w => (w, st)
  | none =>
    let (w, st) := st.insertNode allowed n
    let (b, st) := optimizeAt rules allowed rewriteLimit { st with memo := st.memo.insert n w } w
    (b, { st with memo := st.memo.insert n b })

/-- Run the skeleton rules on `i`; the chosen simplification, if any (among the `skelCandOk`
candidates). -/
def runSkel (skel : SkeletonFn) (rules : SimplifyFn) (allowed : Inst → Bool) (st : SState)
    (i : Isle.Opt.SkelInst) : Option Isle.Opt.SkelSimp × SState :=
  if !skelCandidate i then (none, st) else
  match skel SState.enodes (fun st x => st.types.get? x) (skelMake rules allowed)
      (fun st b => st.trapBlocks.get? b) { st with made := {} } i with
  | .error _ => (none, { st with stats := { st.stats with errors := st.stats.errors + 1 } })
  | .ok (cands, names, st1) =>
    let c := chooseSkel i (cands.filter (skelCandOk st1 i))
    let fired := names.foldl (fun m n => m.insert n ((m.get? n).getD 0 + 1)) st1.stats.fired
    let st1 := { st1 with stats := { st1.stats with fired } }
    match c with
    | some _ => (c, { st1 with stats := { st1.stats with skeleton := st1.stats.skeleton + 1 } })
    | none => (none, st1)

/-- The fate of a skeleton statement (`skelStmt`), for the certificate (`Opt.SimpCert`). -/
inductive SkelOut where
  /-- Unchanged. -/
  | keep
  /-- Removed (no results). -/
  | remove
  /-- Removed; its single result is renamed to `v`. -/
  | removeWithVal (v : ValueId)
  /-- Replaced by `i` (same results), after zero or more rewrites. -/
  | replace (i : Inst)
  /-- Replaced by two result-free instructions. -/
  | two (a b : Inst)
  deriving Inhabited

/-- The outcome of a reprocessed replacement `i`: `keep` there means `replace i`. -/
def SkelOut.orReplace : SkelOut → Inst → SkelOut
  | .keep, i => .replace i
  | o, _ => o

/-- Simplify a skeleton statement (reprocessing its replacement up to `fuel` times): the
statements replacing it, the renamings of its results and the outcome. Anything that cannot be
applied (a node that cannot be materialised, a result arity or type change, an instruction
outside `skelOk`) keeps the statement. -/
def skelStmt (skel : SkeletonFn) (rules : SimplifyFn) (allowed skelOk : Inst → Bool) (cfg : Cfg)
    (bi : Nat) : Nat → SState → Stmt → Array Stmt × List (ValueId × ValueId) × SState × SkelOut
  | 0, st, s => (#[s], [], st, .keep)
  | fuel + 1, st, s =>
    let (c, st1) := runSkel skel rules allowed st (.inst s.inst)
    let keep := (#[s], [], st1, SkelOut.keep)
    let sameResults := fun (i : Inst) =>
      i.resultTypes (fun _ => none) (fun _ => none) == s.inst.resultTypes (fun _ => none) (fun _ => none)
    match c with
    | none => keep
    | some .remove => if s.results.isEmpty then (#[], [], st1, .remove) else keep
    | some (.removeWithVal v) =>
      match s.results with
      | [r] =>
        if st1.types.get? v != st1.types.get? r then keep else
        match materialize cfg allowed bi (st1.defs.size + 1) (st1, #[]) v with
        | some (v', st2, out) => (out, [(r, v')], st2, .removeWithVal v')
        | none => keep
      | _ => keep
    | some (.replace (.inst i)) =>
      if !skelOk i || !sameResults i then keep else
      match materializeAll cfg allowed bi st1 (operands i) with
      | some (m, st2, out) =>
        let i' := mapOperands (rename m) i
        let (more, sub, st3, o) := skelStmt skel rules allowed skelOk cfg bi fuel st2
          { s with inst := i' }
        (out ++ more, sub, st3, o.orReplace i')
      | none => keep
    | some (.replaceBranchCond c) =>
      let i := match s.inst with
        | .trapz _ code => some (Inst.trapz c code)
        | .trapnz _ code => some (Inst.trapnz c code)
        | _ => none
      match i with
      | none => keep
      | some i =>
        match materializeAll cfg allowed bi st1 [c] with
        | some (m, st2, out) =>
          let i' := mapOperands (rename m) i
          let (more, sub, st3, o) := skelStmt skel rules allowed skelOk cfg bi fuel st2
            { s with inst := i' }
          (out ++ more, sub, st3, o.orReplace i')
        | none => keep
    | some (.replaceWithTwo (.inst a) (.inst b)) =>
      if !s.results.isEmpty || !skelOk a || !skelOk b ||
          a.resultTypes (fun _ => none) (fun _ => none) != some [] ||
            b.resultTypes (fun _ => none) (fun _ => none) != some [] then keep
      else
        match materializeAll cfg allowed bi st1 (operands a ++ operands b) with
        | some (m, st2, out) =>
          let a' := mapOperands (rename m) a
          let b' := mapOperands (rename m) b
          (out ++ #[{ inst := a' }, { inst := b' }], [], st2, .two a' b')
        | none => keep
    | some _ => keep

/-- A conditional trap (`trapz`/`trapnz`: result-free, keeps memory). -/
def isTrapLike : Inst → Bool
  | .trapz .. | .trapnz .. => true
  | _ => false

/-- Simplify a terminator (reprocessing up to `fuel` times): statements to append to the
block body, the new terminator, and whether anything changed. -/
def skelTerm (skel : SkeletonFn) (rules : SimplifyFn) (allowed skelOk : Inst → Bool) (cfg : Cfg)
    (bi : Nat) : Nat → SState → Terminator → Array Stmt × Terminator × SState × Bool
  | 0, st, t => (#[], t, st, false)
  | fuel + 1, st, t =>
    let (c, st1) := runSkel skel rules allowed st (.term t)
    let keep := (#[], t, st1, false)
    match c with
    | some (.replace (.term t')) =>
      match materializeAll cfg allowed bi st1 (termOperands t') with
      | some (m, st2, out) =>
        let (more, t'', st3, _) := skelTerm skel rules allowed skelOk cfg bi fuel st2 (mapTerm (rename m) t')
        (out ++ more, t'', st3, true)
      | none => keep
    | some (.replaceBranchCond c) =>
      match t with
      | .brif _ th el =>
        match materializeAll cfg allowed bi st1 [c] with
        | some (m, st2, out) =>
          let (more, t'', st3, _) := skelTerm skel rules allowed skelOk cfg bi fuel st2
            (.brif (rename m c) th el)
          (out ++ more, t'', st3, true)
        | none => keep
      | _ => keep
    | some (.replaceWithTwo (.inst a) (.term t')) =>
      -- (`a` is a conditional trap: it keeps memory)
      if !skelOk a || !isTrapLike a then keep else
      match materializeAll cfg allowed bi st1 (operands a ++ termOperands t') with
      | some (m, st2, out) =>
        let (more, t'', st3, _) := skelTerm skel rules allowed skelOk cfg bi fuel st2 (mapTerm (rename m) t')
        (out ++ #[{ inst := mapOperands (rename m) a }] ++ more, t'', st3, true)
      | none => keep
    | _ => keep

/-- Is `b` a `just_trap_block` (pure body, `trap` terminator)? -/
def trapBlock? (b : Block) : Option TrapCode :=
  match b.term with
  | .trap code => if b.body.all (isPure ·.inst) then some code else none
  | _ => none

/-! ## The certificate

The pass records what it did with every statement and terminator (`Opt.SimpCert`); the
validator `Opt.simpOk` (`FV/Opt/Validate.lean`) checks the output against the input and this
record, and the proof (`FV/Opt/Proof/Simp*.lean`) shows that the recorded replacements are
justified by the rule obligations. -/

/-- What the pass did with a statement. `stmt` is the statement with its operands renamed. -/
inductive StmtLog where
  /-- Kept. -/
  | keep (stmt : Stmt)
  /-- The pure `v = n` replaced by `w`, after emitting `out`. -/
  | repl (stmt : Stmt) (w : ValueId) (out : Array Stmt)
  /-- A skeleton statement, replaced by `out` (outcome `o`). -/
  | skel (stmt : Stmt) (o : SkelOut) (out : Array Stmt)
  deriving Inhabited

/-- The statements the pass emitted for a statement. -/
def StmtLog.out : StmtLog → Array Stmt
  | .keep s => #[s]
  | .repl _ _ out => out
  | .skel _ _ out => out

/-- What the pass did with a block: its statements, then its terminator `term` (operands
renamed) replaced by `extra` statements and `term'` (`changed` = rewritten). -/
structure BlockLog where
  stmts : List StmtLog
  term : Terminator
  extra : Array Stmt
  term' : Terminator
  changed : Bool
  deriving Inhabited

/-- The record of a run of `simplify`: the final graph (nodes, types), the renaming, and the
logs of the processed blocks (by layout index). -/
structure SimpCert where
  defs : Std.HashMap ValueId Inst
  types : Std.HashMap ValueId Ty
  subst : Subst
  logs : Array (Option BlockLog)
  /-- The partial nodes (`SState.partials`). -/
  partials : Std.HashMap ValueId Inst := {}
  deriving Inhabited

/-! ## The pass -/

/-- The `just_trap_block`s of `f`, by block id. -/
def trapMap (f : Function) : Std.HashMap BlockId TrapCode :=
  f.blocks.foldl (fun m b => match trapBlock? b with
    | some c => m.insert b.id c | none => m) {}

/-- The leaves of the graph: block parameters and skeleton results, with their block. -/
def initAvail (f : Function) : Std.HashMap ValueId Nat :=
  f.blocks.zipIdx.foldl (fun av (b, bi) =>
    let av := b.params.foldl (fun av (p, _) => av.insert p bi) av
    b.body.foldl (fun av s =>
      if !(isPure s.inst && s.results.length == 1) then
        s.results.foldl (fun av r => av.insert r bi) av
      else av) av) {}

/-- The initial state: parameters and skeleton results are available in their blocks. -/
def initSState (f : Function) (info : Info) (rematConst : Bool) : SState :=
  { next := maxValue f + 1, types := info.types, trapBlocks := trapMap f, rematConst, fn := f,
    avail := initAvail f }

/-- Step 1: `inst` becomes the node of `v` (with its cost). -/
def pureInsert (st : SState) (v : ValueId) (inst : Inst) : SState :=
  let c := (operands inst).foldl (fun c x => Cost.add c (st.costOf x)) (Cost.ofInst inst)
  { st with defs := st.defs.insert v inst, cost := st.cost.insert v c, made := {}, classes := {} }

/-- A hash-consing hit for `inst` usable in block `bi` (a rematerialised constant of another block
is not reused). -/
def memoHit (st : SState) (bi : Nat) (inst : Inst) : Option ValueId :=
  match st.memo.get? inst with
  | some w => if st.remat w && st.avail.get? w != some bi then none else some w
  | none => none

/-- Steps 2–4 for the pure statement `v = inst` (already the node of `v` in `st`): the best
value of its class, and the state (the hash-consing table records it). -/
def pureBest (rules : SimplifyFn) (allowed : Inst → Bool) (bi : Nat) (st : SState) (v : ValueId)
    (inst : Inst) : ValueId × SState :=
  match memoHit st bi inst with
  | some w => (w, st)
  | none =>
    let (b, st1) := optimizeAt rules allowed rewriteLimit st v
    (b, { st1 with memo := st1.memo.insert inst b })

/-- Step 5: keep `v`, or materialise its best value `best` and rename `v` to it. -/
def pureEmit (cfg : Cfg) (allowed : Inst → Bool) (bi : Nat) (st1 : SState) (subst : Subst)
    (s : Stmt) (inst : Inst) (v best : ValueId) : SState × Subst × StmtLog :=
  let keep := { st1 with avail := st1.avail.insert v bi }
  if best == v then (keep, subst, StmtLog.keep { s with inst })
  else
    match materialize cfg allowed bi (st1.defs.size + 1) (st1, #[]) best with
    | some (w, st2, emitted) =>
      ({ st2 with stats := { st2.stats with rewritten := st2.stats.rewritten + 1,
                                              emitted := st2.stats.emitted + emitted.size } },
       subst.insert v w, StmtLog.repl { s with inst } w emitted)
    | none => (keep, subst, StmtLog.keep { s with inst })

/-- The value a statement `v = n` is renamed to by its record (`v` itself if kept). -/
def StmtLog.rep (lg : StmtLog) (v : ValueId) : ValueId :=
  match lg with
  | .repl _ w _ => w
  | _ => v

/-- Make the class of `best` visible to later matches when its representative is new here (the
representative is `subst'.find v`; renamings have no chains, which `simpOk` checks). -/
def pureAlts (st1 st : SState) (v best : ValueId) (lg : StmtLog) : SState :=
  let rep := lg.rep v
  if rep == v || st1.made.contains best then
    let members := (st1.classes.get? best).getD []
    if !members.isEmpty then { st with alts := st.alts.insert rep members } else st
  else st

/-- Process one statement of block `bi` (the module doc's steps 1–5, or the skeleton rules). -/
def stepStmt (rules : SimplifyFn) (skel : SkeletonFn) (allowed skelOk : Inst → Bool) (cfg : Cfg)
    (bi : Nat) (acc : SState × Subst) (s : Stmt) : SState × Subst × StmtLog :=
  let (st, subst) := acc
  let inst := mapOperands subst.find s.inst
  match s.results, isPure inst with
  | [v], true =>
    -- sanity (never fails on `check`ed input): a new value, a well-typed node over known
    -- values; otherwise the statement is kept outside the graph (and `simpOk` rejects)
    if st.inGraph v || st.next ≤ v || !(operands inst).all st.avail.contains || !st.typedNode inst ||
        st.types.get? v != SState.nodeTy inst then
      (st, subst, .keep { s with inst })
    else
    let st := pureInsert st v inst
    let (best, st1) := pureBest rules allowed bi st v inst
    let (st', subst', lg) := pureEmit cfg allowed bi st1 subst s inst v best
    (pureAlts st1 st' v best lg, subst', lg)
  | _, _ =>
    -- sanity (never fails on `check`ed input): operands known
    if !(operands inst).all st.known then (st, subst, .skel { s with inst } .keep #[{ s with inst }]) else
    let (stmts, sub, st1, o) := skelStmt skel rules allowed skelOk cfg bi rewriteLimit st { s with inst }
    (st1, sub.foldl (fun m (r, w) => m.insert r w) subst, .skel { s with inst } o stmts)

/-- Process block `bi`: its statements in order, then its terminator. -/
def stepBlock (rules : SimplifyFn) (skel : SkeletonFn) (allowed skelOk : Inst → Bool) (cfg : Cfg)
    (blocks : Array Block) (acc : SState × Subst × Array Block × Array (Option BlockLog))
    (bi : Nat) : SState × Subst × Array Block × Array (Option BlockLog) :=
  let (st, subst, out, logs) := acc
  let b := blocks[bi]!
  let (st, subst, lgs) := b.body.foldl (fun (acc : SState × Subst × Array StmtLog) s =>
    let (st, subst, lg) := stepStmt rules skel allowed skelOk cfg bi (acc.1, acc.2.1) s
    (st, subst, acc.2.2.push lg)) (st, subst, #[])
  let t := mapTerm subst.find b.term
  let (extra, term, st, changed) :=
    if (termOperands t).all st.known then skelTerm skel rules allowed skelOk cfg bi rewriteLimit st t
    else (#[], t, st, false)
  let body := lgs.foldl (fun acc lg => acc ++ lg.out) #[] ++ extra
  (st, subst, out.set! bi { b with body := body.toList, term },
   logs.set! bi (some { stmts := lgs.toList, term := t, extra, term' := term, changed }))

/-- The simplify pass, with its certificate. `allowed` restricts the nodes it may emit. -/
def simplify (rules : SimplifyFn) (skel : SkeletonFn) (allowed skelOk : Inst → Bool)
    (rematConst : Bool) (f : Function) (info : Info) : Function × SimplifyStats × SimpCert :=
  let blocks := f.blocks.toArray
  let (st, subst, out, logs) := info.cfg.rpo.foldl
    (stepBlock rules skel allowed skelOk info.cfg blocks)
    (initSState f info rematConst, {}, blocks, Array.replicate blocks.size none)
  (subst.apply { f with blocks := out.toList }, st.stats,
   { defs := st.defs, types := st.types, subst, logs, partials := st.partials })

end Opt

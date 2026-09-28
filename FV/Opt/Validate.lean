import FV.Opt.Check

/-!
# Per-pass validators (translation validation of the passes' output)

`Opt.optimizeReport` accepts a pass's output only if it passes `Opt.check` *and* the pass's
validator here; otherwise it keeps the last accepted function (`Report.passError`). The
validators state, in a form the proofs (`FV/Opt/Proof/*.lean`) can use directly, the invariants
`docs/contracts/midend.md` lists for the passes:

* `unreachableOk f g` (`removeUnreachable`, in `FV/Opt/Cfg.lean`, which validates itself).
* `editOk σ f g fi gi` (GVN, DCE, LICM): the blocks correspond one to one (same ids, parameters,
  and terminators up to the renaming `σ`); each body of `g` is the body of `f` with
  statements *kept* (renamed by `σ`, same results), *deleted* — removable with no result
  defined in `g` (DCE), or pure `v = n` with `σ v` available in `g` at that point and defined
  there by the renamed node `σ n` (GVN, LICM) — or *inserted* (pure, single-result, not
  `symbol_value`: LICM's hoisted nodes); and the definition of `σ v` in `g` is in a dominator
  of the definition of `v` in `f` (same dominator tree).
-/

namespace Opt

open Clif

/-! ## GVN, DCE, LICM -/

/-- A statement with renamed operands. -/
def renStmt (σ : ValueId → ValueId) (s : Stmt) : Stmt := { s with inst := mapOperands σ s.inst }

/-- An inserted statement: a single-result pure node other than `symbol_value`. -/
def insOk (t : Stmt) : Bool :=
  isPure t.inst && t.results.length == 1 && match t.inst with
    | .symbolValue .. => false
    | _ => true

/-- Context of the alignment of block `bi`: the renaming, and the target's definition sites,
dominator tree and blocks. -/
structure EditCtx where
  σ : ValueId → ValueId
  gdm : ValueId → Option (Nat × Nat)
  gidom : Array (Option Nat)
  gblocks : Array Block
  bi : Nat

namespace EditCtx

/-- `w` is defined in the target by the statement `w = n` (pure). -/
def pureAt (c : EditCtx) (w : ValueId) (n : Inst) : Bool :=
  match c.gdm w with
  | some (d, j + 1) =>
    match c.gblocks[d]? with
    | some b => match b.body[j]? with
      | some st => st.results == [w] && st.inst == n && isPure n
      | none => false
    | none => false
  | _ => false

/-- May source statement `s` be deleted, the target being before its statement `k'`? -/
def delOk (c : EditCtx) (s : Stmt) (k' : Nat) : Bool :=
  (removable s.inst && s.results.all fun r => (c.gdm (c.σ r)).isNone) ||
  (isPure s.inst && match s.results with
    | [v] => availB c.gdm (ancB c.gidom c.gidom.size) c.bi k' (c.σ v) &&
        c.pureAt (c.σ v) (mapOperands c.σ s.inst)
    | _ => false)

/-- Kept statement: same results (not renamed), renamed operands. -/
def keepOk (c : EditCtx) (s t : Stmt) : Bool :=
  t == renStmt c.σ s && s.results.all fun r => c.σ r == r

/-- Greedy alignment of a source body with a target body (target position `k'`). -/
def align (c : EditCtx) : List Stmt → List Stmt → Nat → Bool
  | [], [], _ => true
  | [], t :: ts, k' => insOk t && c.align [] ts (k' + 1)
  | s :: ss, [], k' => c.delOk s k' && c.align ss [] k'
  | s :: ss, t :: ts, k' =>
    if c.keepOk s t then c.align ss ts (k' + 1)
    else if c.delOk s k' then c.align ss (t :: ts) k'
    else insOk t && c.align (s :: ss) ts (k' + 1)
termination_by ss ts => ss.length + ts.length

end EditCtx

/-- The edit validator (module doc); `fi`/`gi` are the `check` results of `f` and `g`. -/
def editOk (σ : ValueId → ValueId) (f g : Function) (fi gi : Info) : Bool :=
  let gdm := (defMap g).get?
  let fdm := defMap f
  let gidom := gi.cfg.idom
  let gblocks := g.blocks.toArray
  sameHeader f g && gidom == fi.cfg.idom && g.blocks.length == f.blocks.length &&
    ((f.blocks.zip g.blocks).zipIdx.all fun ((b, b'), i) =>
      b'.id == b.id && b'.params == b.params && b.params.all (fun p => σ p.1 == p.1) &&
        b'.term == mapTerm σ b.term &&
        EditCtx.align { σ, gdm, gidom, gblocks, bi := i } b.body b'.body 0) &&
    (fdm.toList.all fun (v, d, _) => match gdm (σ v) with
      | some (d', _) => ancB gidom gidom.size d' d
      | none => true)

end Opt

import FV.Opt.Check
import FV.Opt.Simplify
import FV.Compile.Subset

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
* `simpOk f g info cert` (simplify, with the pass's record `Opt.SimpCert`): `g` is well-formed
  over `f`'s dominator tree, every block of `g` is what the record says the pass emitted for the
  block of `f` (renamed by the record's substitution, which has no chains), inserted statements
  are pure nodes of the record's graph, and every replaced value's replacement is available
  where the value was defined. That the recorded replacements preserve values is not checked
  here: it is the pass's own theorem (`FV/Opt/Proof/Simp*.lean`).
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

/-! ## Simplify -/

/-- The renaming of a chain-free substitution. -/
def Subst.step (s : Subst) (x : ValueId) : ValueId := (s.get? x).getD x

/-- No value is renamed to a renamed value. -/
def Subst.chainFree (s : Subst) : Bool := s.toList.all fun (_, w) => !s.contains w

/-- Not a call. -/
def notCall : Inst → Bool
  | .call .. => false
  | _ => true

/-- Not a `symbol_value` (the only instruction reading the link-time symbols). -/
def notSym : Inst → Bool
  | .symbolValue .. => false
  | _ => true

/-- A result-free conditional trap (it keeps memory): the prefixes of terminator rewrites. -/
def trapOk (t : Stmt) : Bool := t.results.isEmpty && match t.inst with
  | .trapz .. | .trapnz .. => true
  | _ => false

/-- A branch (the terminators the skeleton rules may rewrite). -/
def isBranch : Terminator → Bool
  | .jump .. | .brif .. | .brTable .. => true
  | _ => false

/-- A statement that is not a single-result pure node (its results are graph leaves). -/
def skeletonStmt (s : Stmt) : Bool := !(isPure s.inst && s.results.length == 1)

/-- Context of the check of one block. -/
structure SimpCtx where
  subst : Subst
  /-- Availability in the output block, before its statement `k`. -/
  avail : Nat → ValueId → Bool

namespace SimpCtx

def σ (c : SimpCtx) : ValueId → ValueId := c.subst.step

/-- No value of `xs` is renamed. -/
def fixed (c : SimpCtx) (xs : List ValueId) : Bool := xs.all fun x => !c.subst.contains x

/-- The record of source statement `s`, emitted from output position `k'` on. -/
def stmtOk (c : SimpCtx) (s : Stmt) (k' : Nat) : StmtLog → Bool
  | .keep s' => s' == renStmt c.σ s && c.fixed s.results
  | .repl s' w out =>
    s' == renStmt c.σ s && isPure s.inst && out.all insOk &&
      (match s.results with
       | [v] => c.subst.get? v == some w
       | _ => false) && c.avail (k' + out.size) w
  | .skel s' o out =>
    s' == renStmt c.σ s && skeletonStmt s && match o with
      | .keep => out == #[s'] && c.fixed s.results
      | .remove => notCall s.inst && notSym s.inst && s.results.isEmpty && out.all insOk
      | .removeWithVal v' =>
        notCall s.inst && notSym s.inst && out.all insOk && c.avail (k' + out.size) v' &&
          match s.results with
          | [r] => c.subst.get? r == some v'
          | _ => false
      | .replace i =>
        notCall s.inst && notSym s.inst && c.fixed s.results && c.fixed (operands i) &&
          out.size ≥ 1 && (out.extract 0 (out.size - 1)).all insOk &&
          out[out.size - 1]? == some { results := s.results, inst := i } && notCall i && notSym i
      | .two a b =>
        notCall s.inst && notSym s.inst && c.fixed (operands a ++ operands b) &&
          s.results.isEmpty && out.size ≥ 2 && (out.extract 0 (out.size - 2)).all insOk &&
          out[out.size - 2]? == some { inst := a } && out[out.size - 1]? == some { inst := b } &&
          notCall a && notCall b && notSym a && notSym b

/-- The records of a block's statements, from output position `k'` on. -/
def stmtsOk (c : SimpCtx) : List Stmt → List StmtLog → Nat → Bool
  | [], [], _ => true
  | s :: ss, lg :: lgs, k' => c.stmtOk s k' lg && c.stmtsOk ss lgs (k' + lg.out.size)
  | _, _, _ => false

/-- The record of a terminator (`BlockLog.term`, `extra`, `term'`). -/
def termOk (c : SimpCtx) (lg : BlockLog) : Bool :=
  if lg.changed then
    isBranch lg.term && c.fixed (termOperands lg.term') &&
      lg.extra.all (fun t => insOk t || (trapOk t && c.fixed (operands t.inst)))
  else lg.extra.isEmpty && lg.term' == lg.term

end SimpCtx

/-- The simplify validator (module doc); `fi` is `check f`. -/
def simpOk (f g : Function) (fi : Info) (cert : SimpCert) : Bool :=
  let σ := cert.subst.step
  let gdm := (defMap g).get?
  let gidom := fi.cfg.idom
  let D := cert.defs
  let L := initAvail f
  sameHeader f g && g.blocks.length == f.blocks.length && cert.subst.chainFree &&
    wfCert g fi.cfg cert.types &&
    (L.toList.all fun (x, _) => cert.types.get? x == fi.types.get? x) &&
    ((f.blocks.zip g.blocks).zipIdx.all fun ((b, b'), i) =>
      match cert.logs[i]? with
      | some (some lg) =>
        let c : SimpCtx := { subst := cert.subst,
                             avail := fun k w => availB gdm (ancB gidom gidom.size) i k w }
        b'.id == b.id && b'.params == b.params &&
        b'.body == ((lg.stmts.toArray.flatMap (·.out)) ++ lg.extra).toList.map (renStmt σ) &&
        b'.term == mapTerm σ lg.term' && lg.term == mapTerm σ b.term &&
        c.termOk lg && c.stmtsOk b.body lg.stmts 0 &&
        b.params.all (fun p => !D.contains p.1 && L.contains p.1 && !cert.subst.contains p.1) &&
        b.body.all (fun s => !skeletonStmt s || s.results.all fun r => !D.contains r) &&
        (b'.body.all fun t => match t.results with
          | [x] => !isPure t.inst || D.get? x == some t.inst
          | _ => true) &&
        b'.body.all fun t => !skeletonStmt t || t.results.all fun r => !D.contains r && L.contains r
      | _ => false)

/-! ## The backend subset -/

/-- The external function references a function calls. -/
def callees (f : Function) : List FnRef :=
  f.blocks.flatMap fun b => b.body.filterMap fun st => match st.inst with
    | .call fn _ => some fn
    | _ => none

/-- The optimised function `g` keeps what the backend theorem needs of the input `f`
(`E2E.backend_correct_opt`): the header, membership in the backend subset E (the simplifier only
emits E nodes into E functions), and the callees. -/
def keepsBackendSubset (f g : Function) : Bool :=
  sameHeader f g && (!Compile.functionE f || Compile.functionE g) &&
    (callees g).all (callees f).contains

end Opt

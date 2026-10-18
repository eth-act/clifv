import FV.Opt.Proof.CompleteSimpStmt
import FV.Opt.Proof.CompleteGuards

/-!
# Completeness of simplify: the facts recorded along the pass

The pass visits the blocks of `f` in reverse postorder and their statements in order. At a point
of the run (the block records `logs` so far, the current block `bi`, its first `j` statements
processed with records `lgs`), the *output view* is the processed blocks (`blockOf`) and the
current block's statements so far; a source value is *done* when its definition is in a processed
block or before statement `j` of `bi`; the *bad* values are the source values not done yet and the
renamed values (`Bad`).

This module states the facts kept along the run and that they only improve as the run proceeds
(`Prog`, the `*.mono` lemmas):

* `OutStmt`: an output statement's operands are available and placeable (so never renamed), its
  results typed, its node recorded, and it is a renamed source instruction or an allowed node;
* `TermOut`: an output terminator likewise, branching only where the source terminator branched,
  with arguments of the source's types;
* `SLogFact`/`StmtsFact`/`TermLogFact`: the Prop form of `Opt.SimpCtx.stmtOk`/`stmtsOk`/`termOk`
  with placeability for "not renamed" and view availability for `availB`.
-/

namespace Opt

open Clif

section Defs

variable (f : Function)

/-- The output block of a processed block `d` with record `lg`. -/
def blockOf (d : Nat) (lg : BlockLog) : Option Block :=
  (f.blocks[d]?).map fun b =>
    { b with body := ((lg.stmts.toArray.flatMap (·.out)) ++ lg.extra).toList, term := lg.term' }

/-- The processed blocks, and the current block `bi` without statements. -/
def V0 (logs : Array (Option BlockLog)) (bi : Nat) : Nat → Option Block := fun d =>
  match logs[d]? with
  | some (some lg) => blockOf f d lg
  | _ => if d = bi then (f.blocks[d]?).map fun b => { b with body := [] } else none

/-- The output statements of records. -/
def outsOf (lgs : List StmtLog) : List Stmt := lgs.flatMap fun lg => lg.out.toList

/-- A source value defined in a processed block or before statement `j` of block `bi`. -/
def Done (logs : Array (Option BlockLog)) (bi j : Nat) (y : ValueId) : Prop :=
  ∃ d t, (defMap f).get? y = some (d, t) ∧ ((∃ lg, logs[d]? = some (some lg)) ∨ (d = bi ∧ t ≤ j))

/-- The bad values: source values not done yet, and renamed values. -/
def Bad (logs : Array (Option BlockLog)) (bi j : Nat) (S : Subst) (y : ValueId) : Prop :=
  (y ≤ maxValue f ∧ ¬ Done f logs bi j y) ∨ S.contains y = true

end Defs

section Facts

variable (f : Function) (info : Info) (allowed skelOk : Inst → Bool) (idom : Array (Option Nat))

/-- A new instruction: the renaming of an allowed node or skeleton instruction. -/
def NewInst (i : Inst) : Prop :=
  ∃ n σ, (allowed n = true ∨ skelOk n = true) ∧ i = mapOperands σ n ∧ notCall n = true ∧
    isCallInd n = false

/-- An output statement at index `k` of block `d` (module doc). -/
structure OutStmt (V : Nat → Option Block) (B : ValueId → Prop) (st : SState) (d k : Nat)
    (t : Stmt) : Prop where
  uses : ∀ y ∈ operands t.inst, AvailAt idom V d k y ∧ Placed st B y
  results : ∃ ts, t.inst.resultTypes (sigOf f) (fun _ => none) = some ts ∧
    ts.length = t.results.length ∧ ∀ (n : Nat) r, t.results[n]? = some r → st.types.get? r = ts[n]?
  pure : isPure t.inst = true → pureTyped (fun y => st.types.get? y) f t.inst = true
  node : ∀ x, t.results = [x] → isPure t.inst = true → st.defs.get? x = some t.inst
  leaf : skeletonStmt t = true → ∀ r ∈ t.results,
    st.defs.get? r = none ∧ (initAvail f).contains r = true
  nodup : t.results.Nodup
  guard : (∃ b0, f.blocks[d]? = some b0 ∧ ∃ s0 ∈ b0.body, ∃ τ, t.inst = mapOperands τ s0.inst) ∨
    NewInst allowed skelOk t.inst

/-- The output terminator `t` of block `d` (source block `b0`), after `blen` statements. -/
structure TermOut (V : Nat → Option Block) (B : ValueId → Prop) (st : SState) (d blen : Nat)
    (b0 : Block) (t : Terminator) : Prop where
  uses : ∀ y ∈ termOperands t, AvailAt idom V d blen y ∧ Placed st B y
  succs : ∀ id ∈ termSuccs t, id ∈ termSuccs b0.term
  calls : ∀ bc ∈ termCalls t, ∃ bc0 ∈ termCalls b0.term, bc.block = bc0.block ∧
    bc.args.map (fun x => st.types.get? x) = bc0.args.map (fun x => info.types.get? x)
  brt : brTableOk st.types t
  guard : (∃ τ, t = mapTerm τ b0.term) ∨ (isBranch b0.term = true ∧ isBranch t = true)

/-- The record of a skeleton statement (`SimpCtx.stmtOk`, `.skel` case). -/
def SkelLog (V : Nat → Option Block) (B : ValueId → Prop) (st : SState) (S : Subst) (d k' : Nat)
    (s s' : Stmt) (out : Array Stmt) : SkelOut → Prop
  | .keep => out = #[s'] ∧ ∀ r ∈ s.results, Placed st B r
  | .remove => notCall s.inst = true ∧ notSym s.inst = true ∧ s.results = [] ∧
      ∀ t ∈ out.toList, insOk t = true
  | .removeWithVal v' => notCall s.inst = true ∧ notSym s.inst = true ∧
      (∀ t ∈ out.toList, insOk t = true) ∧ AvailAt idom V d (k' + out.size) v' ∧
      ∃ r, s.results = [r] ∧ S.get? r = some v'
  | .replace i => notCall s.inst = true ∧ notSym s.inst = true ∧ (∀ r ∈ s.results, Placed st B r) ∧
      (∀ y ∈ operands i, Placed st B y) ∧ out.size ≥ 1 ∧
      (∀ t ∈ (out.extract 0 (out.size - 1)).toList, insOk t = true) ∧
      out[out.size - 1]? = some { results := s.results, inst := i } ∧ notCall i = true ∧
      notSym i = true
  | .two a c => notCall s.inst = true ∧ notSym s.inst = true ∧
      (∀ y ∈ operands a ++ operands c, Placed st B y) ∧ s.results = [] ∧ out.size ≥ 2 ∧
      (∀ t ∈ (out.extract 0 (out.size - 2)).toList, insOk t = true) ∧
      out[out.size - 2]? = some { inst := a } ∧ out[out.size - 1]? = some { inst := c } ∧
      notCall a = true ∧ notCall c = true ∧ notSym a = true ∧ notSym c = true

/-- The record of a statement (`SimpCtx.stmtOk`), its source operands done (renamed or not bad). -/
def SLogFact (V : Nat → Option Block) (B : ValueId → Prop) (st : SState) (S : Subst) (d : Nat)
    (s : Stmt) (k' : Nat) (lg : StmtLog) : Prop :=
  (∀ y ∈ operands s.inst, S.contains y = true ∨ ¬ B y) ∧
  match lg with
  | .keep s' => s' = renStmt S.step s ∧ ∀ r ∈ s.results, Placed st B r
  | .repl s' w out => s' = renStmt S.step s ∧ isPure s.inst = true ∧
      (∀ t ∈ out.toList, insOk t = true) ∧ (∃ v, s.results = [v] ∧ S.get? v = some w) ∧
      AvailAt idom V d (k' + out.size) w
  | .skel s' o out => s' = renStmt S.step s ∧ skeletonStmt s = true ∧
      SkelLog idom V B st S d k' s s' out o

/-- The records of a block's statements (`SimpCtx.stmtsOk`). -/
def StmtsFact (V : Nat → Option Block) (B : ValueId → Prop) (st : SState) (S : Subst) (d : Nat) :
    List Stmt → List StmtLog → Nat → Prop
  | [], [], _ => True
  | s :: ss, lg :: lgs, k' => SLogFact idom V B st S d s k' lg ∧ StmtsFact V B st S d ss lgs (k' + lg.out.size)
  | _, _, _ => False

/-- The record of a terminator (`SimpCtx.termOk`, and `lg.term`). -/
def TermLogFact (B : ValueId → Prop) (st : SState) (S : Subst) (b0 : Block) (lg : BlockLog) : Prop :=
  (∀ y ∈ termOperands b0.term, S.contains y = true ∨ ¬ B y) ∧ lg.term = mapTerm S.step b0.term ∧
  if lg.changed then isBranch lg.term = true ∧ (∀ y ∈ termOperands lg.term', Placed st B y) ∧
    ∀ t ∈ lg.extra.toList, insOk t = true ∨ (trapOk t = true ∧ ∀ y ∈ operands t.inst, Placed st B y)
  else lg.extra = #[] ∧ lg.term' = lg.term

end Facts

end Opt

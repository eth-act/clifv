import FV.Opt.Proof.SimpGraph
import FV.Opt.Validate

/-!
# The semantic facts of a simplify run (`Opt.SimpFacts`)

The interface between the pass's loop invariant (`FV/Opt/Proof/SimpLoop.lean`: every run of
`Opt.simplify` with sound rule sets has these facts) and the run-time simulation
(`FV/Opt/Proof/SimpSim.lean`: `simpOk` and these facts give `FunSim f g`).

The facts are about the certificate's final graph `cert.defs`, evaluated by `den` (the least
valuation of the node equations, `FV/Opt/Proof/SimpDen.lean`) from any valuation `ρ` of the
leaves (block parameters and skeleton results, `initAvail f`) in any environment `fr`/`mem`
with all symbols defined (`SGood`):

* a replaced pure statement `v = n` (`StmtLog.repl`, replacement `w`): if `n` evaluates to `a`,
  then `w` has value `a`;
* a rewritten skeleton statement (`StmtLog.skel`): the outcome refines it (`SkelFact`, the
  composition of the `Opt.SkelRefines` steps of the chain `skelStmt` took);
* a rewritten terminator: the new terminator, after the conditional traps of `extra`, refines
  the old one modulo the trap blocks (`effTerm`, `Opt.BrRefines`).
-/

namespace Opt

open Clif

/-- Result-free instructions (conditional traps), then a terminator. -/
def effTerm (fr : Frame) (mem : Mem) : List Inst → Terminator → Res (BlockId × List Val × Mem)
  | [], t => termEval fr mem t
  | a :: as, t =>
    match evalInst fr mem a with
    | .ok ([], m) => effTerm fr m as t
    | .ok _ => .stuck "result"
    | .trap c => .trap c
    | .stuck msg => .stuck msg

/-- The instructions of the statements of `extra` that are not inserted pure nodes. -/
def effsOf (extra : Array Stmt) : List Inst :=
  extra.toList.filterMap fun t => if insOk t then none else some t.inst

/-- The outcome `o` of a skeleton statement `i` refines it (evaluated in `fr`/`mem`; `V` gives
the value of `removeWithVal`'s replacement). -/
def SkelFact (fr : Frame) (mem : Mem) (V : Valuation) (i : Inst) : SkelOut → Prop
  | .keep => True
  | .remove =>
    (∀ vs m, evalInst fr mem i = .ok (vs, m) → m = mem) ∧ ∀ c, evalInst fr mem i ≠ .trap c
  | .removeWithVal v =>
    (∀ vs m, evalInst fr mem i = .ok (vs, m) → m = mem ∧ ∃ a, vs = [a] ∧ V v = some a) ∧
      ∀ c, evalInst fr mem i ≠ .trap c
  | .replace i' => ResRefines (evalInst fr mem i) (evalInst fr mem i')
  | .two a b => ResRefines (evalInst fr mem i) (seqEval2 fr mem a b)

/-- The fact of one statement record. -/
def LogFact (fr : Frame) (mem : Mem) (V : Valuation) : StmtLog → Prop
  | .keep _ => True
  | .repl s' w _ => ∀ a, evalNode fr mem s'.inst = some a → V w = some a
  | .skel s' o _ => SkelFact fr mem V s'.inst o

/-- The facts of a block record. -/
def BlockFact (tb : BlockId → Option TrapCode) (fr : Frame) (mem : Mem) (V : Valuation)
    (lg : BlockLog) : Prop :=
  (∀ l ∈ lg.stmts, LogFact fr mem V l) ∧
    (lg.changed = true → BrRefines tb (termEval fr mem lg.term) (effTerm fr mem (effsOf lg.extra) lg.term'))

/-- The environments the facts hold in: `ρ` values exactly the leaves, consistently with the
types of `check f`. -/
structure SGood (f : Function) (info : Info) (ρ : Valuation) (fr : Frame) (mem : Mem) : Prop where
  env : GoodEnv f fr mem
  dom : ∀ x, (ρ x).isSome = (initAvail f).contains x
  ty : ∀ x a t, ρ x = some a → info.types.get? x = some t → a.ty = t

/-- The certificate graph as a partial map. -/
def SimpCert.graph (cert : SimpCert) : ValueId → Option Inst := fun x => cert.defs.get? x

/-- **The facts of a simplify run** (module doc). -/
structure SimpFacts (f : Function) (info : Info) (cert : SimpCert) : Prop where
  types : ∀ x t, info.types.get? x = some t → cert.types.get? x = some t
  facts : ∀ ρ fr mem, SGood f info ρ fr mem → ∀ (i : Nat) lg, cert.logs[i]? = some (some lg) →
    BlockFact (fun b => (trapMap f).get? b) (withRegs fr (den cert.graph ρ fr mem)) mem
      (den cert.graph ρ fr mem) lg

end Opt

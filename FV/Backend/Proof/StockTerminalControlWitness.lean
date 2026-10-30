import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.StockTerminalRoots

namespace Backend.Stock.Proof.TerminalControlWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Coverage Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
inductive Kind where
  | ret | trap | jump
  deriving DecidableEq,Repr
private def term : Kind → Clif.Terminator
  | .ret => .ret []
  | .trap => .trap (.user 9)
  | .jump => .jump ⟨1,[]⟩
private def function (k : Kind) : Clif.Function := {
  name := "stock_terminal_control_unsunk"
  sig := {callConv := some .systemV}
  blocks := if k = .jump then [{id := 0,term := term k},{id := 1,term := .ret []}]
    else [{id := 0,term := term k}] }
private def built (k : Kind) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function k)).toOption.getD (sinkCtx,#[],sinkState)
private def data (k : Kind) : V := (Backend.termData (term k)).toOption.getD (.op .unit)
private def context (k : Kind) := Driver.termCtx (built k).1 0 (data k)
private def name : Kind → String | .jump => "lower_branch" | _ => "lower"
private def arguments : Kind → List V | .jump => [.inst 0,.labels [1]] | _ => [.inst 0]
private def Observed (k : Kind) : Prop := (Stock.lower (function k)).isOk = true ∧
  (Stock.runTerm (context k) (name k) (arguments k) (built k).2.2).toOption.map
    (fun q => decide (q.2.1.sunk[0]! = false)) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed (k : Kind) : Observed k := by cases k <;> unfold Observed <;> decide +kernel
private theorem build (k : Kind) : Stock.buildCtx (function k) = .ok (built k) := by cases k <;> rfl
private theorem scope (k : Kind) : LowerScope (function k) := by cases k <;> apply lowerScope_of <;> decide +kernel
private theorem placeholder (k : Kind) : (built k).1.insts[0]? = some ⟨.op .unit,[],[],none⟩ := by cases k <;> rfl
private theorem prepared (k : Kind) : Backend.termData (term k) = .ok (data k) := by cases k <;> rfl
private theorem unsunk (k : Kind) : (built k).2.2.sunk[0]! = false := by cases k <;> rfl
end Kernel
private theorem clean_build {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : Clean (sourceIdentityCtx ctx) := by
  obtain ⟨original,before,legacy,spec,view⟩ := buildCtx_source build
  intro i info lookup
  change ctx.insts[i]? = some info at lookup
  rw [view.insts] at lookup
  exact Cov.clean_of_build legacy i info lookup

/-- Complete original functions inhabit return, trap and branch root contracts.
Each has a real context build, installed in-bounds empty-CLIF slot and successful
actual named root; its terminal bit is preserved by the new root theorem. -/
theorem stock_control_terminal_witness (k : Kind) :
    ∃ (f : Clif.Function) (result : Result) (ctx : Ctx) (initial next : State)
      (name : String) (args : List V) (out : Option V) (trace : List RuleId),
      Stock.lower f = .ok result ∧ LowerScope f ∧ MappedCtxInv f ctx ∧ Clean (sourceIdentityCtx ctx) ∧
      0 < ctx.insts.size ∧ ctx.insts[0]!.clif = none ∧ initial.sunk[0]! = false ∧
      Stock.runTerm ctx name args initial = .ok (out,next,trace) ∧ next.sunk[0]! = false := by
  have evidence := observed k
  unfold Observed at evidence
  cases run : Stock.lower (function k) with
  | error e => simp only [run,Except.isOk] at evidence; cases evidence.1
  | ok result =>
    have named := evidence.2
    cases call : Stock.runTerm (context k) (name k) (arguments k) (built k).2.2 with
    | error e => simp only [call,Except.toOption,Option.map_none] at named; cases named
    | ok q =>
      obtain ⟨out,next,trace⟩ := q
      have mapped : MappedCtxInv (function k) (context k) :=
        (buildCtx_mappedInv (scope k) (build k)).termCtx (placeholder k) (data k)
      have clean : Clean (sourceIdentityCtx (context k)) := clean_termCtx (clean_build (build k)) (prepared k) 0
      have slot : (context k).insts[0]? = some ⟨data k,[],[],none⟩ := termCtx_insts_self (placeholder k) (data k)
      have noClif : (context k).insts[0]!.clif = none := by simp only [getElem!_def,slot,Option.getD_some]
      have preserved : next.sunk[0]! = false := by
        cases k with
        | jump => exact stock_branch_terminal_unsunk mapped clean call noClif (unsunk .jump)
        | ret => exact stock_retTrap_terminal_unsunk mapped clean rfl (prepared .ret) slot call noClif (unsunk .ret)
        | trap => exact stock_retTrap_terminal_unsunk mapped clean rfl (prepared .trap) slot call noClif (unsunk .trap)
      refine ⟨function k,result,context k,(built k).2.2,next,name k,arguments k,out,trace,run,scope k,mapped,clean,
        ?_,noClif,unsunk k,call,preserved⟩
      have bound := Array.getElem?_eq_some_iff.mp slot
      exact Nat.pos_of_ne_zero (by intro zero; have := bound.1; omega)
end Backend.Stock.Proof.TerminalControlWitness

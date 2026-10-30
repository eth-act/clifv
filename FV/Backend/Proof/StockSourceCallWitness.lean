import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.StockSourceResults

namespace Backend.Stock.Proof.SourceCallWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def signature : Clif.Signature := {
  params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV }
private def statement : Clif.Stmt := ⟨[31],.call 0 [7]⟩
private def caller : Clif.Function := {
  name := "stock_source_call_result",sig := signature
  externs := [(0,{name := "stock_source_identity",sig := signature,colocated := true})]
  blocks := [{id := 0,params := [(7,.i64)],body := [statement],term := .ret [31]}] }
private def callee : Clif.Function := {
  name := "stock_source_identity",sig := signature
  blocks := [{id := 0,params := [(101,.i64)],term := .ret [101]}] }
private def value (word : BitVec 64) : Clif.Val := ⟨.i64,word⟩
private def before (word : BitVec 64) : Clif.Frame := {
  func := caller,regs := Clif.Regs.empty.set 7 (value word),slots := [],body := [statement],term := .ret [31] }
private def saved (word : BitVec 64) : Clif.Frame := {before word with body := []}
private def after (word : BitVec 64) : Clif.Frame := {saved word with regs := (saved word).regs.set 31 (value word)}
private def active (word : BitVec 64) : Clif.State := {
  frame := {func := callee,regs := Clif.Regs.empty.set 101 (value word),slots := [],body := [],term := .ret [101]}
  callers := [(saved word,[31])],mem := Clif.Mem.empty }
private def program : Clif.Program := {funcs := [callee]}
private def environment : Clif.Env := {extern := fun name =>
  if name = callee.name then Option.some (fun vals cm => .returned vals cm) else none}
private def lowerBoth : Except String (Result × Result) := do
  let c ← Stock.lower caller
  let d ← Stock.lower callee
  pure (c,d)
private def Observed : Prop := lowerBoth.toOption.map (fun q =>
  decide (q.1.blockScans.size = 1 ∧ q.2.blockScans.size = 1) &&
  q.1.scans.any (fun event => event.inst == 0 &&
    event.output.step.any (fun step => step.decision == .emitted))) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
end Kernel

private theorem callerDominated : Dominated caller := by
  constructor
  · change ([7,31] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b found
    cases bi with
    | zero =>
      simp [caller] at found
      subst b
      constructor
      · intro j stm present
        cases j with
        | zero =>
          simp [caller] at present
          subst stm
          intro x member
          have same : x = 7 := by simpa [statement,Driver.instArgs] using member
          subst x
          simp [availOf,caller,statement,defsBefore,defsFrom]
        | succ j => simp [caller] at present
      · intro x member
        have same : x = 31 := by simpa [abiTerm,Driver.termArgs,caller,signature,sretRet,sigRets] using member
        subst x
        simp [availOf,caller,statement,defsBefore,defsFrom]
    | succ bi => simp [caller] at found
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := caller) (ctx := ctx) (gn := id)).cand tl x available
    have length : caller.blocks.length = 1 := rfl
    omega

/-- Complete real caller/callee Stock lowering inhabits source result binding
for both an external call and an internal callee return, over arbitrary words.
The original caller inputs, actual source entry/call/return and inherited7/new31
values are included, without treating a call as an ordinary evalInst. -/
theorem stock_source_call_result_witness (word : BitVec 64) : ∃ c d : Result,
    Stock.lower caller = .ok c ∧ Stock.lower callee = .ok d ∧ LowerScope caller ∧ LowerScope callee ∧
    Dominated caller ∧ c.blockScans.size = 1 ∧ d.blockScans.size = 1 ∧
    Clif.enterFunc caller [value word] Clif.Mem.empty = .ok (before word,Clif.Mem.empty) ∧
    Clif.step environment {funcs := []} ⟨before word,[],Clif.Mem.empty⟩ = .next ⟨after word,[],Clif.Mem.empty⟩ ∧
    Clif.step Clif.Env.empty program ⟨before word,[],Clif.Mem.empty⟩ = .next (active word) ∧
    Clif.step Clif.Env.empty program (active word) = .next ⟨after word,[],Clif.Mem.empty⟩ ∧
    Clif.step Clif.Env.empty program ⟨after word,[],Clif.Mem.empty⟩ = .done [value word] Clif.Mem.empty ∧
    SourceDefinedAt caller c.ctx 0 0 (before word) ∧ SourceDefinedAt caller c.ctx 0 1 (after word) ∧
    (after word).regs 7 = some (value word) ∧ (after word).regs 31 = some (value word) ∧
    ∀ next, Clif.returnValues (active word) [value word] Clif.Mem.empty = .next next →
      SourceDefinedAt caller c.ctx 0 1 next.frame := by
  have actual := observed
  unfold Observed lowerBoth at actual
  cases crun : Stock.lower caller with
  | error err => simp only [crun,bind,Except.bind,Except.toOption,Option.map_none] at actual; cases actual
  | ok c =>
    cases drun : Stock.lower callee with
    | error err => simp only [crun,drun,bind,Except.bind,Except.toOption,Option.map_none] at actual; cases actual
    | ok d =>
      simp only [crun,drun,bind,Except.bind,pure,Except.pure,Except.toOption,Option.map_some,
        Option.some.injEq,Bool.and_eq_true,decide_eq_true_eq] at actual
      have entered : Clif.enterFunc caller [value word] Clif.Mem.empty = .ok (before word,Clif.Mem.empty) := rfl
      have defined := source_defined_enterFunc callerDominated c.ctx entered
      have continued := source_defined_continueWith callerDominated.ssa c.ctx (bi := 0) (j := 0)
        (b := caller.blocks[0]!) (stm := statement) rfl rfl
        (s := ⟨before word,[],Clif.Mem.empty⟩) (next := ⟨after word,[],Clif.Mem.empty⟩)
        defined (show Clif.continueWith ⟨before word,[],Clif.Mem.empty⟩ [] [31] [value word] Clif.Mem.empty =
          .next ⟨after word,[],Clif.Mem.empty⟩ from rfl)
      refine ⟨c,d,rfl,rfl,lowerScope_of (by decide +kernel),lowerScope_of (by decide +kernel),
        callerDominated,actual.1.1,actual.1.2,entered,rfl,rfl,rfl,rfl,defined,continued.1,rfl,rfl,?_⟩
      intro next returned
      exact (source_defined_returnValues callerDominated.ssa c.ctx (bi := 0) (j := 0)
        (b := caller.blocks[0]!) (stm := statement) rfl rfl (s := active word) rfl
        (show SourceDefinedAt caller c.ctx 0 0 (saved word) from defined) returned).1
end Backend.Stock.Proof.SourceCallWitness

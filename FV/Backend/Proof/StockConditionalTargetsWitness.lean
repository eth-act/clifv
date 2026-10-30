import FV.Backend.Proof.StockConditionalRootTargets
import FV.Backend.Proof.StockPerEdgeCheckerWitness

namespace Backend.Stock.Proof.ConditionalTargetsWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private def conditionalFunction : Clif.Function := {
  name := "stock_per_successor_migration"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],term := .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩},
    {id := 1,params := [(31,.i64)],term := .ret [31]}, {id := 2,params := [(47,.i64)],term := .ret [47]}] }
private def compare : V := .data 58 4 [.data 59 10 [],.data 93 0 [],.reg .xzr,
  .reg (.vreg 192 .int),.op (.imm12 ⟨0,false⟩)]
private def condition (kind : Fin 6) : V := match kind.val with
  | 0 => .data 123 0 [.reg (.vreg 192 .int),.data 93 0 []]
  | 1 => .data 123 1 [.reg (.vreg 192 .int),.data 93 1 []]
  | 2 => .data 123 2 [.data 47 1 [compare],.data 96 0 []]
  | 3 => .data 123 3 [.data 47 1 [compare],.data 96 0 [],.data 96 1 []]
  | 4 => .data 123 4 [.data 47 1 [compare],.data 96 0 [],.data 96 1 []]
  | _ => .data 123 2 [.data 47 2 [compare,compare],.data 96 0 []]
private def helperArgs (kind : Fin 6) : List V := [condition kind,.label 2,.label 1]
private def conditionalBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx conditionalFunction).toOption.getD (sinkCtx,#[],sinkState)
private theorem conditional_build : Stock.buildCtx conditionalFunction = .ok conditionalBuilt := rfl
private theorem lower_build {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) :
    ∃ ranges,Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  exact ⟨_,by assumption⟩


private def execute (ctx : Ctx) (st : State) (kind : Fin 6) :
    Except Err ((V × State × Array RuleId) × (V × State × Array RuleId)) := do
  let (some descriptor,middle,tr) ←
    (applyTerm program (Stock.sem ctx) {} 200 46 722 (helperArgs kind)).run (st,#[])
    | throw (.malformed "conditional descriptor missing")
  let (some out,next,final) ←
    (applyTerm program (Stock.sem ctx) {} 200 13 242 [descriptor]).run (middle,tr)
    | throw (.malformed "conditional emission missing")
  pure ((descriptor,middle,tr),(out,next,final))

private theorem execute_success (kind : Fin 6) :
    (execute conditionalBuilt.1 conditionalBuilt.2.2 kind).toOption.isSome = true := by
  have cases : kind.val = 0 ∨ kind.val = 1 ∨ kind.val = 2 ∨ kind.val = 3 ∨ kind.val = 4 ∨ kind.val = 5 := by omega
  rcases cases with h | h | h | h | h | h <;>
    simp only [execute,helperArgs,condition,h] <;> decide +kernel

/-- All five conditional-result forms, and the two-flag-instruction producer
that yields a three-instruction descriptor, construct and emit successfully
from a complete original-scope/dominated source driver's actual context and
initial state. The two structural proof roots apply to those actual runs. -/
theorem stock_conditional_targets_witness (kind : Fin 6) :
    ∃ (result : Result) (descriptor out : V) (middle next : State) (tr final : Array RuleId)
      (condition : V) (last : MInst),
      Stock.lower conditionalFunction = .ok result ∧ LowerScope conditionalFunction ∧ Dominated conditionalFunction ∧
      (applyTerm program (Stock.sem result.ctx) {} 200 46 722 (helperArgs kind)).run (result.initial,#[]) =
        .ok (some descriptor,middle,tr) ∧
      (applyTerm program (Stock.sem result.ctx) {} 200 13 242 [descriptor]).run (middle,tr) =
        .ok (some out,next,final) ∧
      ConditionalTargets.RawLast (.data 58 118 [.label 2,.label 1,condition]) descriptor ∧
      next.base.emitted.back? = some last ∧ last.isTerminator = true ∧ last.targets = [2,1] := by
  obtain ⟨result,run,scope,dominated,_⟩ := PerEdgeCheckerWitness.stock_per_edge_checker_witness
  change Stock.lower conditionalFunction = .ok result at run
  change LowerScope conditionalFunction at scope
  change Dominated conditionalFunction at dominated
  obtain ⟨ranges,build⟩ := lower_build run
  have same := Except.ok.inj (build.symm.trans conditional_build)
  have context := congrArg Prod.fst same
  have initial := congrArg (fun p => p.2.2) same
  have success := execute_success kind
  rw [← context,← initial] at success
  unfold execute at success
  cases construct : (applyTerm program (Stock.sem result.ctx) {} 200 46 722 (helperArgs kind)).run (result.initial,#[]) with
  | error e => simp [construct,Except.toOption] at success
  | ok q =>
    obtain ⟨descriptor,middle,tr⟩ := q
    cases descriptor with
    | none => simp [construct,Except.toOption] at success
    | some descriptor =>
      cases emit : (applyTerm program (Stock.sem result.ctx) {} 200 13 242 [descriptor]).run (middle,tr) with
      | error e => simp [construct,emit,Except.toOption] at success
      | ok q =>
        obtain ⟨out,next,final⟩ := q
        cases out with
        | none => simp [construct,emit,Except.toOption] at success
        | some out =>
          have c : ApplyInternal program (Stock.sem result.ctx) {} 199 46 722
              [condition kind,.label 2,.label 1] (result.initial,#[]) descriptor (middle,tr) := construct
          have e : ApplyInternal program (Stock.sem result.ctx) {} 199 13 242
              [descriptor] (middle,tr) out (next,final) := emit
          obtain ⟨condition,shape⟩ := ConditionalTargets.stock_conditional_descriptor_targets (run := c) rfl (by decide)
          obtain ⟨last,back,ends,targets⟩ := ConditionalTargets.stock_conditional_emitted_targets (construct := c) (emit := e) rfl
            (by decide) (by decide)
          exact ⟨result,descriptor,out,middle,next,tr,final,condition,last,run,scope,dominated,
            construct,emit,shape,back,ends,targets⟩

private def rootCtx (ctx : Ctx) : Ctx := Driver.termCtx ctx 0
  ((Backend.termData conditionalFunction.blocks[0]!.term).toOption.getD (.op .unit))
private theorem root_success :
    (Stock.runTerm (rootCtx conditionalBuilt.1) "lower_branch" [.inst 0,.labels [2,1]] conditionalBuilt.2.2).toOption.map
      (fun q => q.1.isSome && (q.2.2.getLast? == some rule_lower_3231.id)) = some true := by decide +kernel

/-- The actual named branch run of a complete conditional source driver selects
ordinary brif and inhabits its target theorem, with no helper receipt supplied. -/
theorem stock_selected_brif_targets_witness :
    ∃ (result : Result) (out : V) (next : State) (trace : List RuleId),
      Stock.lower conditionalFunction = .ok result ∧ LowerScope conditionalFunction ∧ Dominated conditionalFunction ∧
      Stock.runTerm (rootCtx result.ctx) "lower_branch" [.inst 0,.labels [2,1]] result.initial = .ok (some out,next,trace) ∧
      ∃ (selected : BranchSelection (rootCtx result.ctx) 0 [2,1] result.initial out next trace),
        selected.rule = rule_lower_3231 ∧
        ∃ last,next.base.emitted.back? = some last ∧ last.isTerminator = true ∧ last.targets = [2,1] := by
  obtain ⟨result,run,scope,dominated,_⟩ := PerEdgeCheckerWitness.stock_per_edge_checker_witness
  change Stock.lower conditionalFunction = .ok result at run
  change LowerScope conditionalFunction at scope
  change Dominated conditionalFunction at dominated
  obtain ⟨ranges,build⟩ := lower_build run
  have same := Except.ok.inj (build.symm.trans conditional_build)
  have context := congrArg Prod.fst same
  have initial := congrArg (fun p => p.2.2) same
  have success := root_success
  rw [← context,← initial] at success
  cases actual : Stock.runTerm (rootCtx result.ctx) "lower_branch" [.inst 0,.labels [2,1]] result.initial with
  | error e => simp only [actual,Except.toOption,Option.map_none] at success; cases success
  | ok q =>
    obtain ⟨out,next,trace⟩ := q
    cases out with
    | none => simp [actual,Except.toOption] at success
    | some out =>
      simp only [actual,Except.toOption,Option.map_some,Option.some.injEq,Option.isSome,
        Bool.true_and,beq_iff_eq] at success
      obtain ⟨selected⟩ := stock_named_branch_selection actual
      have fired : trace.getLast? = some selected.rule.id := by
        have eq := congrArg List.getLast? selected.fired
        simpa only [Array.toList_push,List.getLast?_append,List.getLast?_singleton,Option.some_or] using eq
      have id : selected.rule.id = rule_lower_3231.id := Option.some.inj (fired.symm.trans success)
      have member : selected.rule ∈ program.rulesOf T.lower_branch.id := by rw [selected.candidates]; simp
      rw [show T.lower_branch.id = 687 from rfl,data_program.r687] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      have root : selected.rule = rule_lower_3231 := by
        rcases member with h | h | h | h | h | h | h | h
        all_goals first | exact h | (rw [h] at id; exact False.elim (Nat.ne_of_beq_eq_false (by decide +kernel) id))
      exact ⟨result,out,next,trace,run,scope,dominated,actual,selected,root,
        ConditionalRoots.stock_selected_brif_targets selected root⟩

end Backend.Stock.Proof.ConditionalTargetsWitness

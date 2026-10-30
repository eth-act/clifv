import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.RegallocCSem
import FV.Backend.Proof.StockBranchRootTargets

namespace Backend.Stock.Proof.BranchTargetsWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000

private def ty (kind : Fin 3) : Clif.Ty := if kind.val = 2 then .i32 else .i64
private def sourceBody (kind : Fin 3) : List Clif.Stmt :=
  if kind.val = 2 then [] else
    [⟨[13],.iconst .i64 8⟩,⟨[17],.binary .band .i64 7 13⟩] ++
      if kind.val = 1 then [⟨[19],.iconst .i64 0⟩,⟨[23],.icmp .eq .i64 17 19⟩] else []
private def sourceTerm (kind : Fin 3) : Clif.Terminator :=
  if kind.val = 2 then .brTable 7 ⟨1,[7]⟩ [⟨2,[7]⟩,⟨3,[7]⟩]
  else .brif (if kind.val = 1 then 23 else 17) ⟨1,[7]⟩ ⟨2,[7]⟩
private def function (kind : Fin 3) : Clif.Function := {
  name := "stock_branch_target_cases"
  sig := {params := [⟨ty kind,.none,.normal⟩],returns := [⟨ty kind,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,ty kind)],body := sourceBody kind,term := sourceTerm kind},
    {id := 1,params := [(31,ty kind)],term := .ret [31]},
    {id := 2,params := [(47,ty kind)],term := .ret [47]}] ++
    if kind.val = 2 then [{id := 3,params := [(59,ty kind)],term := .ret [59]}] else [] }
private def built (kind : Fin 3) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function kind)).toOption.getD (sinkCtx,#[],sinkState)
private def labels (kind : Fin 3) : List Label := if kind.val = 2 then [3,2,1] else [2,1]
private def rootRule (kind : Fin 3) : Rule :=
  if kind.val = 2 then rule_lower_3277 else if kind.val = 1 then rule_lower_3257 else rule_lower_3251
private def rootCtx (ctx : Ctx) (kind : Fin 3) : Ctx := Driver.termCtx ctx (sourceBody kind).length
  ((Backend.termData (sourceTerm kind)).toOption.getD (.op .unit))
private theorem kind_cases (kind : Fin 3) : kind = 0 ∨ kind = 1 ∨ kind = 2 := by
  have cases : kind.val = 0 ∨ kind.val = 1 ∨ kind.val = 2 := by omega
  rcases cases with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))
private theorem build_ok (kind : Fin 3) : Stock.buildCtx (function kind) = .ok (built kind) := by
  have cases : kind.val = 0 ∨ kind.val = 1 ∨ kind.val = 2 := by omega
  rcases cases with h | h | h <;> simp only [function,ty,sourceBody,sourceTerm,built,h] <;> rfl
private theorem source_scope (kind : Fin 3) : LowerScope (function kind) := by
  rcases kind_cases kind with rfl | rfl | rfl <;> exact lowerScope_of (by decide +kernel)
private def legacyBuilt (kind : Fin 3) : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx (function kind)).toOption.getD (sinkCtx,#[],default)
private theorem legacy_build (kind : Fin 3) : Backend.buildCtx (function kind) = .ok (legacyBuilt kind) := by
  rcases kind_cases kind with rfl | rfl | rfl <;> rfl
private theorem source_dominated (kind : Fin 3) : Dominated (function kind) := by
  constructor
  · rcases kind_cases kind with rfl | rfl | rfl <;> decide +kernel
  · intro ctx ranges st build bi b found
    rcases kind_cases kind with rfl | rfl | rfl
    all_goals
      have bound : bi < 4 := by
        have bound := lt_of_getElem? found
        simp [function] at bound
        omega
      have cases : bi = 0 ∨ bi = 1 ∨ bi = 2 ∨ bi = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      all_goals
        simp [function] at found
        all_goals
          subst b
          constructor
          · intro j stm present x member
            have bound : j < 4 := by
              have bound := lt_of_getElem? present
              simp [sourceBody] at bound <;> omega
            have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
            rcases cases with rfl | rfl | rfl | rfl
            all_goals
              simp [sourceBody] at present
              all_goals
                subst stm
                simp [Driver.instArgs] at member
                all_goals first
                | solve | rcases member with rfl | rfl <;> simp [availOf,function,sourceBody,defsBefore,defsFrom]
                | solve | subst x; simp [availOf,function,sourceBody,defsBefore,defsFrom]
          · intro x member
            simp [abiTerm,Driver.termArgs,sretRet,sigRets,function,sourceTerm] at member
            first
            | solve | rcases member with rfl | rfl <;> simp [availOf,function,sourceBody,defsBefore,defsFrom]
            | solve | subst x; simp [availOf,function,sourceBody,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    have fixed := (inFix_fixOk (f := function kind) (ctx := ctx) (gn := id)).cand tl x available
    have limit : (function kind).blocks.length ≤ 4 := by
      rcases kind_cases kind with rfl | rfl | rfl <;> decide +kernel
    have cases : tl = 1 ∨ tl = 2 ∨ tl = 3 := by omega
    have context : ctx = (legacyBuilt kind).1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans (legacy_build kind)))
    rw [context] at member
    have closed : (valueDefs (function kind)).all (fun x => (defArgs (legacyBuilt kind).1 x).all
        (fun y => !(parsOf (function kind) tl).contains y)) = true := by
      rcases kind_cases kind with rfl | rfl | rfl
      all_goals rcases cases with rfl | rfl | rfl <;> decide +kernel
    have atValue := List.all_eq_true.mp closed x fixed.2.2.2.1
    have atArgument := List.all_eq_true.mp atValue y member
    simpa using atArgument
private theorem lower_ok (kind : Fin 3) : (Stock.lower (function kind)).isOk = true := by
  rcases kind_cases kind with rfl | rfl | rfl <;> decide +kernel
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

private theorem root_success (kind : Fin 3) :
    (Stock.runTerm (rootCtx (built kind).1 kind) "lower_branch"
      [.inst (sourceBody kind).length,.labels (labels kind)] (built kind).2.2).toOption.map
      (fun q => q.1.isSome && (q.2.2.getLast? == some (rootRule kind).id)) = some true := by
  rcases kind_cases kind with rfl | rfl | rfl <;> decide +kernel

/-- Complete original-scope/dominated sources execute both priority test-bit
rules and table dispatch. Actual named runs choose the expected roots and
inhabit the selected-rule and rule-independent named target theorems. -/
theorem stock_branch_named_targets_witness (kind : Fin 3) :
    ∃ (result : Result) (out : V) (next : State) (trace : List RuleId),
      Stock.lower (function kind) = .ok result ∧ LowerScope (function kind) ∧ Dominated (function kind) ∧
      Stock.runTerm (rootCtx result.ctx kind) "lower_branch"
        [.inst (sourceBody kind).length,.labels (labels kind)] result.initial = .ok (some out,next,trace) ∧
      ∃ (selected : BranchSelection (rootCtx result.ctx kind) (sourceBody kind).length
          (labels kind) result.initial out next trace),
        selected.rule = rootRule kind ∧
        ∃ last,next.base.emitted.back? = some last ∧ last.isTerminator = true ∧ last.targets = labels kind := by
  have success := lower_ok kind
  cases run : Stock.lower (function kind) with
  | error e => simp only [run,Except.isOk] at success; cases success
  | ok result =>
    obtain ⟨ranges,build⟩ := lower_build run
    have same := Except.ok.inj (build.symm.trans (build_ok kind))
    have context := congrArg Prod.fst same
    have initial := congrArg (fun p => p.2.2) same
    have success := root_success kind
    rw [← context,← initial] at success
    cases actual : Stock.runTerm (rootCtx result.ctx kind) "lower_branch"
        [.inst (sourceBody kind).length,.labels (labels kind)] result.initial with
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
        have id : selected.rule.id = (rootRule kind).id := Option.some.inj (fired.symm.trans success)
        have member : selected.rule ∈ program.rulesOf T.lower_branch.id := by rw [selected.candidates]; simp
        rw [show T.lower_branch.id = 687 from rfl,data_program.r687] at member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        have cases : kind.val = 0 ∨ kind.val = 1 ∨ kind.val = 2 := by omega
        rcases cases with h | h | h
        all_goals
          have root : selected.rule = rootRule kind := by
            simp [rootRule,h] at id ⊢
            rcases member with r | r | r | r | r | r | r | r
            all_goals first | exact r | (rw [r] at id; exact False.elim (Nat.ne_of_beq_eq_false (by decide +kernel) id))
          refine ⟨result,out,next,trace,rfl,source_scope kind,source_dominated kind,actual,selected,root,?_⟩
        · have chosen : selected.rule = rule_lower_3251 := by simpa [rootRule,h] using root
          exact BranchRootTargets.stock_selected_test_bit_targets selected false chosen
        · have chosen : selected.rule = rule_lower_3257 := by simpa [rootRule,h] using root
          exact BranchRootTargets.stock_selected_test_bit_targets selected true chosen
        · have chosen : selected.rule = rule_lower_3277 := by simpa [rootRule,h] using root
          exact BranchRootTargets.stock_selected_table_targets selected chosen

private def bitKind (zero : Bool) : Fin 3 := if zero then 1 else 0
private def bitArgs : List V := [.label 2,.label 1,.reg (.vreg 192 .int),.int 3]
private def bitExecute (ctx : Ctx) (st : State) (zero : Bool) :
    Except Err ((V × State × Array RuleId) × (V × State × Array RuleId)) := do
  let (some descriptor,middle,tr) ←
    (applyTerm program (Stock.sem ctx) {} 200 46 (if zero then 668 else 667) bitArgs).run (st,#[])
    | throw (.malformed "test-bit descriptor missing")
  let (some out,next,final) ←
    (applyTerm program (Stock.sem ctx) {} 200 13 242 [descriptor]).run (middle,tr)
    | throw (.malformed "test-bit emission missing")
  pure ((descriptor,middle,tr),(out,next,final))
private theorem bit_success (zero : Bool) :
    (bitExecute (built (bitKind zero)).1 (built (bitKind zero)).2.2 zero).toOption.isSome = true := by
  cases zero <;> decide +kernel

/-- Both test-bit builders and real emitters succeed using complete source
programs' actual contexts/initial states; no emitted-shape premise is assumed. -/
theorem stock_test_bit_helper_targets_witness (zero : Bool) :
    ∃ (result : Result) (descriptor out : V) (middle next : State) (tr final : Array RuleId) (last : MInst),
      Stock.lower (function (bitKind zero)) = .ok result ∧ LowerScope (function (bitKind zero)) ∧
      Dominated (function (bitKind zero)) ∧
      ApplyInternal program (Stock.sem result.ctx) {} 199 46 (if zero then 668 else 667)
        [.label 2,.label 1,.reg (.vreg 192 .int),.int 3] (result.initial,#[]) descriptor (middle,tr) ∧
      ApplyInternal program (Stock.sem result.ctx) {} 199 13 242 [descriptor] (middle,tr) out (next,final) ∧
      next.base.emitted.back? = some last ∧ last.isTerminator = true ∧ last.targets = [2,1] := by
  have success := lower_ok (bitKind zero)
  cases run : Stock.lower (function (bitKind zero)) with
  | error e => simp only [run,Except.isOk] at success; cases success
  | ok result =>
    obtain ⟨ranges,build⟩ := lower_build run
    have same := Except.ok.inj (build.symm.trans (build_ok (bitKind zero)))
    have context := congrArg Prod.fst same
    have initial := congrArg (fun p => p.2.2) same
    have success := bit_success zero
    rw [← context,← initial] at success
    unfold bitExecute at success
    cases construct : (applyTerm program (Stock.sem result.ctx) {} 200 46 (if zero then 668 else 667) bitArgs).run (result.initial,#[]) with
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
            have c : ApplyInternal program (Stock.sem result.ctx) {} 199 46 (if zero then 668 else 667)
                [.label 2,.label 1,.reg (.vreg 192 .int),.int 3] (result.initial,#[]) descriptor (middle,tr) := construct
            have e : ApplyInternal program (Stock.sem result.ctx) {} 199 13 242 [descriptor] (middle,tr) out (next,final) := emit
            obtain ⟨last,back,ends,targets⟩ := BranchHelperTargets.stock_test_bit_emitted_targets rfl zero
              (fuel := 199) (emitFuel := 199) (by decide) (by decide) c e
            exact ⟨result,descriptor,out,middle,next,tr,final,last,rfl,source_scope _,source_dominated _,c,e,back,ends,targets⟩

private def tableArgs (large : Bool) : List V :=
  [.int (if large then 5001 else 2),.reg (.vreg 192 .int),.label 3,.labels [2,1]]
private theorem table_success (large : Bool) :
    ((applyTerm program (Stock.sem (built 2).1) {} 500 13 670 (tableArgs large)).run ((built 2).2.2,#[])).toOption.map
      (fun q => q.1.isSome) = some true := by cases large <;> decide +kernel

/-- Table dispatch succeeds through both its immediate and materialized-bound
paths from a complete table source's actual context and initial state, and
inhabits the structural target theorem. Large-bound case concerns arbitrary
helper arguments; no source-value relation is claimed for that extra case. -/
theorem stock_table_helper_targets_witness (large : Bool) :
    ∃ (result : Result) (out : V) (next : State) (trace : Array RuleId) (last : MInst),
      Stock.lower (function 2) = .ok result ∧ LowerScope (function 2) ∧ Dominated (function 2) ∧
      ApplyInternal program (Stock.sem result.ctx) {} 499 13 670
        [.int (if large then 5001 else 2),.reg (.vreg 192 .int),.label 3,.labels [2,1]]
        (result.initial,#[]) out (next,trace) ∧
      next.base.emitted.back? = some last ∧ last.isTerminator = true ∧ last.targets = [3,2,1] := by
  have success := lower_ok 2
  cases run : Stock.lower (function 2) with
  | error e => simp only [run,Except.isOk] at success; cases success
  | ok result =>
    obtain ⟨ranges,build⟩ := lower_build run
    have same := Except.ok.inj (build.symm.trans (build_ok 2))
    have context := congrArg Prod.fst same
    have initial := congrArg (fun p => p.2.2) same
    have success := table_success large
    rw [← context,← initial] at success
    cases actual : (applyTerm program (Stock.sem result.ctx) {} 500 13 670 (tableArgs large)).run (result.initial,#[]) with
    | error e => simp only [actual,Except.toOption,Option.map_none] at success; cases success
    | ok q =>
      obtain ⟨out,next,trace⟩ := q
      cases out with
      | none => simp only [actual,Except.toOption,Option.map_some,Option.isSome] at success; cases success
      | some out =>
        have call : ApplyInternal program (Stock.sem result.ctx) {} 499 13 670
            [.int (if large then 5001 else 2),.reg (.vreg 192 .int),.label 3,.labels [2,1]]
            (result.initial,#[]) out (next,trace) := actual
        obtain ⟨last,back,ends,targets⟩ := BranchHelperTargets.stock_table_impl_targets rfl (fuel := 499) (by decide) call
        exact ⟨result,out,next,trace,last,rfl,source_scope _,source_dominated _,call,back,ends,targets⟩

end Backend.Stock.Proof.BranchTargetsWitness

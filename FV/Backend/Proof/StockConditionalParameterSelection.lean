import FV.Backend.Proof.StockProjection
import FV.Backend.Proof.IselCovForm
import FV.Backend.Proof.StockConditionalCalls

namespace Backend.Stock.Proof.ParameterBranch
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem branch_ruleFmt_match {ctx : Ctx} {r : Rule} {fT : Nat}
    (format : ruleFmt r = some fT) (lo : 2447 ≤ fT) (hi : fT < 2447 + 36)
    {fuel ti : Nat} {rest : List V} {st next : State × Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule program (Stock.sem ctx) {} fuel r (.inst ti :: rest)).run st =
      .ok (some env, next)) :
    ∃ info fs, ctx.insts[ti]? = some info ∧ info.data = .data 152 (fT - 2447) fs := by
  have bound : fT - 2447 < 36 := by omega
  obtain ⟨term, lookup, kind⟩ := fmtKinds_program (fT - 2447) bound
  rw [show 2447 + (fT - 2447) = fT by omega] at lookup
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨env0, args, _⟩ := matchRule_some_inv matched
    rw [stock_matchArgs] at args
    unfold ruleFmt at format
    split at format
    · rename_i q qs shape
      rw [shape] at args
      obtain ⟨env1, head, _⟩ := matchArgs_cons_inv args
      exact rootFmt_match_k data_program format lookup kind head
    · cases format


private theorem other_format {ctx : Ctx} {i fT tag : Nat} {fields : List V}
    (slot : ctx.insts[i]? = some ⟨.data 152 tag fields,[],[],none⟩) {r : Rule}
    (format : ruleFmt r = some fT) (lo : 2447 ≤ fT) (hi : fT < 2447+36) (different : fT ≠ 2447+tag)
    {fuel : Nat} {st next : State × Array RuleId} {labels : List Label} {env : Isle.Interp.Env V}
    (matched : (matchRule program (Stock.sem ctx) {} fuel r [.inst i,.labels labels]).run st =
      .ok (some env,next)) : False := by
  obtain ⟨info,fs,source,shape⟩ := branch_ruleFmt_match format lo hi matched
  rw [slot] at source
  cases source
  simp only [V.data.injEq] at shape
  omega



private theorem test_bit_absurd {ctx : Ctx} {i c : Nat} {targets : V} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,targets],[],[],none⟩)
    (parameter : ctx.defInst? c = none) (zero : Bool)
    {fuel : Nat} {before next : State × Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule program (Stock.sem ctx) {} fuel
      (if zero then rule_lower_3257 else rule_lower_3251) [.inst i,.labels labels]).run before =
        .ok (some env,next)) : False := by
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨env0,args,_⟩ := matchRule_some_inv matched
    rw [stock_matchArgs] at args
    cases zero
    all_goals
      have hp := data_program
      isel_inv' hp [rule_lower_3251,rule_lower_3257,slot] at args
      have defined := ‹ctx.defInst? c = some _›
      rw [parameter] at defined
      cases defined

/-- The actual first matching rule of an original parameter brif is ordinary
brif. Other formats and both priority bit-test patterns are excluded by the
real terminator slot and absence of a source definition, without a rule input. -/
theorem parameter_selected {ctx : Ctx} {i c : Nat} {targets : V} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,targets],[],[],none⟩)
    (parameter : ctx.defInst? c = none)
    {before next : State} {out : V} {trace : List RuleId}
    (selected : BranchSelection ctx i labels before out next trace) :
    selected.rule = rule_lower_3231 := by
  have member : selected.rule ∈ program.rulesOf T.lower_branch.id := by rw [selected.candidates]; simp
  rw [show T.lower_branch.id = 687 from rfl,data_program.r687] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with root | root | root | root | root | root | root | root
  all_goals try exact root
  all_goals
    have matched := selected.matchedRun
    rw [root] at matched
  · exact False.elim (other_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (test_bit_absurd slot parameter false matched)
  · exact False.elim (test_bit_absurd slot parameter true matched)
  · exact False.elim (other_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2475) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2462) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2451) rfl (by decide) (by decide) (by decide) matched)

/-- A real named parameter branch derives its ordinary helper-call packet and
original condition provenance internally; callers provide no selected rule. -/
theorem named_calls {ctx : Ctx} {i c : Nat} {targets : V} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,targets],[],[],none⟩)
    (parameter : ctx.defInst? c = none)
    {before next : State} {out : V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst i,.labels labels] before = .ok (some out,next,trace)) :
    ∃ calls : ConditionalCalls.Calls ctx i labels before out next,calls.source = .value c := by
  obtain ⟨selected⟩ := stock_named_branch_selection run
  have root := parameter_selected slot parameter selected
  obtain ⟨calls⟩ := ConditionalCalls.selected_calls selected root
  obtain ⟨info,targetData,found,data⟩ := calls.sourceData
  rw [slot] at found
  cases found
  simp only [V.data.injEq,List.cons.injEq,and_true,true_and] at data
  exact ⟨calls,data.1.symm⟩

end Backend.Stock.Proof.ParameterBranch

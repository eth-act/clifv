import FV.Backend.Proof.IselCovForm
import FV.Backend.Proof.StockConditionalRootTargets
import FV.Backend.Proof.StockBranchRootTargets

namespace Backend.Stock.Proof.NamedBranchTargets
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
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


/-- Every actual successful brif named call chooses one of its three original
rules and ends in a terminator with exactly its original two labels. The rule
case and all helper receipts are derived internally. -/
theorem stock_named_brif_targets {ctx : Ctx} {i : Nat} {fields : List V} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 fields,[],[],none⟩)
    {st next : State} {out : V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst i,.labels labels] st = .ok (some out,next,trace)) :
    ∃ last,next.base.emitted.back? = some last ∧ last.isTerminator = true ∧ last.targets = labels := by
  obtain ⟨selected⟩ := stock_named_branch_selection run
  have member : selected.rule ∈ program.rulesOf T.lower_branch.id := by rw [selected.candidates]; simp
  rw [show T.lower_branch.id = 687 from rfl,data_program.r687] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with root | root | root | root | root | root | root | root
  · have matched := selected.matchedRun
    rw [root] at matched
    exact False.elim (other_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
  · exact BranchRootTargets.stock_selected_test_bit_targets selected false root
  · exact BranchRootTargets.stock_selected_test_bit_targets selected true root
  · have matched := selected.matchedRun
    rw [root] at matched
    exact False.elim (other_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
  · have matched := selected.matchedRun
    rw [root] at matched
    exact False.elim (other_format slot (fT := 2475) rfl (by decide) (by decide) (by decide) matched)
  · exact ConditionalRoots.stock_selected_brif_targets selected root
  · have matched := selected.matchedRun
    rw [root] at matched
    exact False.elim (other_format slot (fT := 2462) rfl (by decide) (by decide) (by decide) matched)
  · have matched := selected.matchedRun
    rw [root] at matched
    exact False.elim (other_format slot (fT := 2451) rfl (by decide) (by decide) (by decide) matched)

/-- Every actual successful table named call chooses the original dispatch rule
and retains the default-plus-table target order, without a rule certificate. -/
theorem stock_named_table_targets {ctx : Ctx} {i : Nat} {fields : List V} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 4 fields,[],[],none⟩)
    {st next : State} {out : V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst i,.labels labels] st = .ok (some out,next,trace)) :
    ∃ last,next.base.emitted.back? = some last ∧ last.isTerminator = true ∧ last.targets = labels := by
  obtain ⟨selected⟩ := stock_named_branch_selection run
  have member : selected.rule ∈ program.rulesOf T.lower_branch.id := by rw [selected.candidates]; simp
  rw [show T.lower_branch.id = 687 from rfl,data_program.r687] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with root | root | root | root | root | root | root | root
  all_goals try exact BranchRootTargets.stock_selected_table_targets selected root
  all_goals
    have matched := selected.matchedRun
    rw [root] at matched
  · exact False.elim (other_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2452) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2452) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2475) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2452) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2462) rfl (by decide) (by decide) (by decide) matched)

end Backend.Stock.Proof.NamedBranchTargets

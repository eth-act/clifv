import FV.Backend.Proof.StockComparisonZeroComputedSelection
import FV.Backend.Proof.StockSelectConditionCalls

/-! Branches on a plain computed condition: rule selection (#140, CB-11).

A `brif c` whose condition `c` is a wide value is lowered by the base rule `lower_brif` (3231),
`is_nonzero_cmp c` (650) and `is_nonzero c` (651), which emit one `cbnz` on the register of `c`.
Three rules look through the definition of `c` before this:

* `tbnz` (`lower_branch` rule 3251) needs `c = band _ x (iconst n)` with a one-bit mask `n`;
* `tbz` (`lower_branch` rule 3257) needs `c = icmp eq (band _ x (iconst n)) (iconst 0)`;
* `is_nonzero_cmp` rule 4966 needs `c = icmp ..` or `c = uextend (icmp ..)` (rule 4965 is the
  `fcmp` analog, outside the source scope).

`PlainSource` excludes all three: `c` is not a `band` result (`NonBandSource`) and is not a
comparison origin (`SelectComparisonOrigin`). A parameter is plain (`plain_of_parameter`). The
overflow-flag rules of `is_nonzero` need an `i8` condition, so they do not apply to a wide one.
`plain_selected` is the analog of `ParameterBranch.parameter_selected`: under `PlainSource` the
first matching `lower_branch` rule is 3231. -/

namespace Backend.Stock.Proof.PlainBranch
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ComparisonBranch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

/-- `c` is not a `band` result and is neither an `icmp` result nor a `uextend` of one: no
`lower_branch` or `is_nonzero_cmp` rule looks through its definition. -/
def PlainSource (ctx : Ctx) (c : Nat) : Prop :=
  NonBandSource ctx c ∧ ∀ cc ty a b,¬ScalarSelect.SelectComparisonOrigin ctx c cc ty a b

/-- A source parameter is plain. -/
theorem plain_of_parameter {ctx : Ctx} {c : Nat} (parameter : ctx.defInst? c = none) : PlainSource ctx c := by
  refine ⟨nonband_of_parameter parameter,?_⟩
  intro cc ty a b origin
  simp [ScalarSelect.SelectComparisonOrigin,Ctx.defClif?,parameter] at origin

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

/-- Neither bit-test pattern matches a plain condition: `tbnz` needs a `band` condition, and `tbz`
needs an `icmp` condition. -/
private theorem plain_test_bit_absurd {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i c : Nat} {targets : V} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,targets],[],[],none⟩)
    (plain : PlainSource ctx c) (zero : Bool)
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
      obtain ⟨defined⟩ : Nonempty (ctx.defInst? c = some _) := ⟨‹_›⟩
      obtain ⟨found⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹_›⟩
      obtain ⟨cl,clif,raw⟩ := ctxInv_clif inv.identityView defined found
    · obtain ⟨shape⟩ : Nonempty (V.data 152 2 _ = _) := ⟨‹_›⟩
      rw [← shape] at raw
      obtain ⟨ty1,a1,b1,rfl,_,_⟩ := instData_binary_inv (cop := .band) variantNames_Band rfl raw
      exact plain.1 _ _ defined found ty1 a1 b1 clif
    · obtain ⟨shape⟩ : Nonempty (V.data 152 14 _ = _) := ⟨‹_›⟩
      rw [← shape] at raw
      obtain ⟨cc,ty,a,b,rfl,_,_⟩ := instData_icmp_inv raw
      exact plain.2 cc ty a b (Or.inl (by simp [Ctx.defClif?,defined,found,clif]))

/-- The actual first matching rule of a brif on a plain condition is ordinary brif (3231). Other
formats are excluded by the real terminator slot, both bit-test patterns by `PlainSource`. -/
theorem plain_selected {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i c : Nat} {targets : V} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,targets],[],[],none⟩)
    (plain : PlainSource ctx c)
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
  · exact False.elim (plain_test_bit_absurd inv slot plain false matched)
  · exact False.elim (plain_test_bit_absurd inv slot plain true matched)
  · exact False.elim (other_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2475) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2462) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2451) rfl (by decide) (by decide) (by decide) matched)

/-- A real named branch on a plain condition derives its ordinary helper-call packet and original
condition provenance internally. -/
theorem plain_named_calls {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i c : Nat} {targets : V} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,targets],[],[],none⟩)
    (plain : PlainSource ctx c)
    {before next : State} {out : V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst i,.labels labels] before = .ok (some out,next,trace)) :
    ∃ calls : ConditionalCalls.Calls ctx i labels before out next,calls.source = .value c := by
  obtain ⟨selected⟩ := stock_named_branch_selection run
  have root := plain_selected inv slot plain selected
  obtain ⟨calls⟩ := ConditionalCalls.selected_calls selected root
  obtain ⟨info,targetData,found,data⟩ := calls.sourceData
  rw [slot] at found
  cases found
  simp only [V.data.injEq,List.cons.injEq,and_true,true_and] at data
  exact ⟨calls,data.1.symm⟩

end Backend.Stock.Proof.PlainBranch

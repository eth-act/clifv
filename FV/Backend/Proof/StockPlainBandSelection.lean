import FV.Backend.Proof.StockPlainConditionSelection
import FV.Backend.Proof.StockTestBitSelection

/-! Branches on a plain computed condition that may be a `band`: rule selection (#140, CB-15).

`PlainSource` (CB-11) excludes every `band` condition (`NonBandSource`). Only one `band` form is
looked through by a `lower_branch` rule before ordinary `brif` (3231): the `tbnz` rule 3251 needs
`c = band _ x k`, `k = iconst n` and `test_and_compare_bit_const (value_type x) n` (`tcbc`), and
this is exactly `TestBitMetadata` (CB-13). `test_bit_metadata_of_match` derives it from an actual
match of rule 3251, including its `if-let`. So `PlainSource'` excludes only that form: `c` is
not a one-bit test (`¬TestBitMetadata`), and `c` is not a comparison origin, which excludes the
`tbz` rule 3257 and the comparison rules of `is_nonzero_cmp`. A `band` with a register mask, or
with a constant mask that does not have exactly one set bit below the width of `x`, is plain.
`PlainSource.weak` shows that `PlainSource` implies `PlainSource'`. `plain_selected'` is
`plain_selected` under `PlainSource'`. -/

namespace Backend.Stock.Proof.PlainBranch
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ComparisonBranch Backend.Stock.Proof.TestBitBranch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

/-- `c` is not a one-bit test of rule 3251 (`TestBitMetadata`), and is neither an `icmp` result
nor a `uextend` of one. A `band` whose mask is not such a one-bit constant is allowed. -/
def PlainSource' (ctx : Ctx) (c : Nat) : Prop :=
  ¬TestBitMetadata ctx c ∧ ∀ cc ty a b,¬ScalarSelect.SelectComparisonOrigin ctx c cc ty a b

/-- A condition that is not a `band` result is not a one-bit test. -/
theorem not_test_bit_of_nonband {ctx : Ctx} {c : Nat} (nonband : NonBandSource ctx c) :
    ¬TestBitMetadata ctx c := by
  rintro ⟨ty,x,k,ty',imm,t,bit,band,_,_,_⟩
  cases defined : ctx.defInst? c with
  | none => simp [Ctx.defClif?,defined] at band
  | some j =>
    cases found : ctx.insts[j]? with
    | none => simp [Ctx.defClif?,defined,found] at band
    | some info =>
      have clif : info.clif = some (.binary .band ty x k) := by
        simpa [Ctx.defClif?,defined,found] using band
      exact nonband j info defined found ty x k clif

/-- **`PlainSource` implies `PlainSource'`.** -/
theorem PlainSource.weak {ctx : Ctx} {c : Nat} (plain : PlainSource ctx c) : PlainSource' ctx c :=
  ⟨not_test_bit_of_nonband plain.1,plain.2⟩

attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl

/-- The Stock `test_and_compare_bit_const` constructor is `tcbc` and keeps the state. -/
theorem stock_ctor_tcbc_iff (ctx : Ctx) (st : State) (t : CTy) (n : Int) (v : V) (st' : State) :
    Stock.externCtor ctx T.test_and_compare_bit_const [.ty t,.int n] st = .ok (v,st') ↔
      ∃ bit,tcbc t n = some bit ∧ v = .int bit ∧ st' = st := by
  rw [stock_ctor_baseOnly ctx _ _ st (by decide)]
  constructor
  · intro h
    split at h
    · rename_i v' base legacy
      obtain ⟨bit,bitEq,rfl,rfl⟩ := (ctor_tcbc_iff st.base t n v' base).mp legacy
      cases h
      exact ⟨bit,bitEq,rfl,rfl⟩
    · cases h
    · cases h
  · intro ⟨bit,bitEq,hv,hs⟩
    rw [hv,hs]
    have legacy := (ctor_tcbc_iff (ctx := ctx) st.base t n (.int bit) st.base).mpr ⟨bit,bitEq,rfl,rfl⟩
    simp only [legacy]

/-- **An actual match of the `tbnz` rule (3251) is a one-bit test.** The match of the arguments
gives `c = band _ x k`, `k = iconst imm` and the type of `x`; the `if-let` gives `tcbc`. -/
theorem test_bit_metadata_of_match {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i c : Nat} {targets : V} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,targets],[],[],none⟩)
    {fuel : Nat} (enough : 100 ≤ fuel) {before next : State × Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule program (Stock.sem ctx) {} fuel rule_lower_3251 [.inst i,.labels labels]).run before =
        .ok (some env,next)) : TestBitMetadata ctx c := by
  obtain ⟨fuel,rfl⟩ : ∃ m,fuel = m+100 := ⟨fuel-100,by omega⟩
  rw [show fuel+100 = (fuel+99)+1 by omega] at matched
  obtain ⟨env0,args,iflets⟩ := matchRule_some_inv matched
  clear matched
  rw [stock_matchArgs] at args
  have hp := data_program
  isel_inv' hp [rule_lower_3251,slot] at args
  obtain ⟨hj1⟩ : Nonempty (ctx.defInst? c = some _) := ⟨‹_›⟩
  obtain ⟨hi1⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹ctx.insts[_]? = some _›⟩
  obtain ⟨cl1,hcl1,hdat1⟩ := ctxInv_clif inv.identityView hj1 hi1
  obtain ⟨hd1⟩ : Nonempty (V.data 152 2 _ = _) := ⟨‹_›⟩
  rw [← hd1] at hdat1
  obtain ⟨ty1,a,b,rfl,he1,hfs1⟩ := instData_binary_inv (cop := .band) variantNames_Band rfl hdat1
  simp only [List.cons.injEq,and_true] at hfs1
  subst hfs1
  repeat (isel_inv_simp [] at * <;> isel_destruct <;> subst_vars)
  obtain ⟨hj2⟩ : Nonempty (ctx.defInst? b = some _) := ⟨‹_›⟩
  obtain ⟨hd2⟩ : Nonempty (V.data 152 35 _ = _) := ⟨‹_›⟩
  obtain ⟨hi2⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹ctx.insts[_]? = some _›⟩
  obtain ⟨ty2,imm,rfl,he2,hcl2⟩ := iconst_data_inv inv.identityView hj2 hi2 hd2
  repeat (isel_inv_simp [sem_ctor,stock_ctor_tcbc_iff] at * <;> isel_destruct <;> subst_vars)
  obtain ⟨hta⟩ : Nonempty (ctx.valueType? a = some _) := ⟨‹_›⟩
  obtain ⟨htc⟩ : Nonempty (tcbc _ _ = some _) := ⟨‹_›⟩
  exact ⟨ty1,a,b,ty2,imm,_,_,by simp [Ctx.defClif?,hj1,hi1,hcl1],by simp [Ctx.defClif?,hj2,hi2,hcl2],hta,htc⟩

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

/-- The `tbz` rule (3257) needs an `icmp` condition, which `PlainSource'` excludes. -/
private theorem zero_test_absurd {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i c : Nat} {targets : V} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,targets],[],[],none⟩)
    (plain : PlainSource' ctx c)
    {fuel : Nat} {before next : State × Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule program (Stock.sem ctx) {} fuel rule_lower_3257 [.inst i,.labels labels]).run before =
        .ok (some env,next)) : False := by
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨env0,args,_⟩ := matchRule_some_inv matched
    rw [stock_matchArgs] at args
    have hp := data_program
    isel_inv' hp [rule_lower_3257,slot] at args
    obtain ⟨defined⟩ : Nonempty (ctx.defInst? c = some _) := ⟨‹_›⟩
    obtain ⟨found⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹_›⟩
    obtain ⟨cl,clif,raw⟩ := ctxInv_clif inv.identityView defined found
    obtain ⟨shape⟩ : Nonempty (V.data 152 14 _ = _) := ⟨‹_›⟩
    rw [← shape] at raw
    obtain ⟨cc,ty,a,b,rfl,_,_⟩ := instData_icmp_inv raw
    exact plain.2 cc ty a b (Or.inl (by simp [Ctx.defClif?,defined,found,clif]))

/-- **The actual first matching rule of a brif on a `PlainSource'` condition is ordinary brif
(3231).** Other formats are excluded by the real terminator slot; an actual match of `tbnz`
(3251) would be a one-bit test, and `tbz` (3257) needs a comparison. -/
theorem plain_selected' {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i c : Nat} {targets : V} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,targets],[],[],none⟩)
    (plain : PlainSource' ctx c)
    {before next : State} {out : V} {trace : List RuleId}
    (selected : BranchSelection ctx i labels before out next trace) :
    selected.rule = rule_lower_3231 := by
  have member : selected.rule ∈ program.rulesOf T.lower_branch.id := by rw [selected.candidates]; simp
  have bound := selected.fuelBound
  rw [show T.lower_branch.id = 687 from rfl,data_program.r687] at member bound
  simp only [List.length_cons,List.length_nil] at bound
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with root | root | root | root | root | root | root | root
  all_goals try exact root
  all_goals
    have matched := selected.matchedRun
    rw [root] at matched
  · exact False.elim (other_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (plain.1 (test_bit_metadata_of_match inv slot (by omega) matched))
  · exact False.elim (zero_test_absurd inv slot plain matched)
  · exact False.elim (other_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2475) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2462) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2451) rfl (by decide) (by decide) (by decide) matched)

/-- `plain_named_calls` under `PlainSource'`: a real named branch on such a condition derives its
ordinary helper-call packet and original condition provenance. -/
theorem plain_named_calls' {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i c : Nat} {targets : V} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,targets],[],[],none⟩)
    (plain : PlainSource' ctx c)
    {before next : State} {out : V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst i,.labels labels] before = .ok (some out,next,trace)) :
    ∃ calls : ConditionalCalls.Calls ctx i labels before out next,calls.source = .value c := by
  obtain ⟨selected⟩ := stock_named_branch_selection run
  have root := plain_selected' inv slot plain selected
  obtain ⟨calls⟩ := ConditionalCalls.selected_calls selected root
  obtain ⟨info,targetData,found,data⟩ := calls.sourceData
  rw [slot] at found
  cases found
  simp only [V.data.injEq,List.cons.injEq,and_true,true_and] at data
  exact ⟨calls,data.1.symm⟩

end Backend.Stock.Proof.PlainBranch

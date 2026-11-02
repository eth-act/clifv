import FV.Backend.Proof.StockComparisonBranchSelection
import FV.Backend.Proof.StockCmpNonconstantSelection

/-! Comparison branches on computed operands: rule selection (#140, CB-8).

`comparison_selected` excludes the two bit-test rules of `lower_branch` with a parameter as the
first `icmp` operand. Here the operands may be computed. The `tbnz` rule 3251 needs a `band`
condition, and the condition is an `icmp`. The `tbz` rule 3257 needs
`icmp eq (band x (iconst n)) (iconst 0)`, so a second operand that is not defined by an `iconst`
(`NonConstantSource`) excludes it. Then ordinary `brif` (rule 3231) is the first matching rule,
for any first operand. -/

namespace Backend.Stock.Proof.ComparisonBranch
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private theorem icmp_instData {f : Clif.Function} {cc : Clif.IntCC} {ty : Clif.Ty} {a b : Nat} {d : V}
    (h : instData f (.icmp cc ty a b) = .ok d) :
    d = .data 152 14 [.data 151 72 [],.values [a,b],.data 145 (ccIdx cc) []] := by
  simp only [instData] at h
  split at h
  · simp only [pure,Except.pure,Except.ok.injEq] at h
    rw [← h,mkVariant_intcc]
    rfl
  · cases h

attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem comparison_source {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {c : Nat} {cc : Clif.IntCC} {ty : Clif.Ty} {a b : Nat}
    (origin : ctx.defClif? c = some (.icmp cc ty a b)) :
    ∃ j info,ctx.defInst? c = some j ∧ ctx.insts[j]? = some info ∧
      info.data = .data 152 14 [.data 151 72 [],.values [a,b],.data 145 (ccIdx cc) []] := by
  cases defined : ctx.defInst? c with
  | none => simp [Ctx.defClif?,defined] at origin
  | some j =>
    cases found : ctx.insts[j]? with
    | none => simp [Ctx.defClif?,defined,found] at origin
    | some info =>
      have clif : info.clif = some (.icmp cc ty a b) := by
        simpa [Ctx.defClif?,defined,found] using origin
      exact ⟨j,info,rfl,found,icmp_instData (inv.data j info _ found clif)⟩

/-- A nonconstant operand has no defining `iconst` data. -/
theorem nonconstant_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {x j : Nat} {info : IInfo} (notConstant : NonConstantSource ctx x)
    (defined : ctx.defInst? x = some j) (found : ctx.insts[j]? = some info)
    {value : V} (data : info.data = .data 152 35 [.data 151 57 [],value]) : False := by
  obtain ⟨original,clif,raw⟩ := ctxInv_clif inv.identityView defined found
  rw [data] at raw
  obtain ⟨ty,c,rfl,fields⟩ := instData_iconst_inv raw
  exact notConstant j info defined found ty c clif

/-- A source parameter is a nonconstant operand. -/
theorem nonconstant_of_parameter {ctx : Ctx} {x : Nat} (parameter : ctx.defInst? x = none) :
    NonConstantSource ctx x := by
  intro j info defined
  rw [parameter] at defined
  cases defined

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

/-- Neither bit-test pattern matches a comparison condition whose second operand is not an
`iconst`: tbnz needs a `band` condition, and tbz needs the second operand to be `iconst 0`. -/
private theorem computed_test_bit_absurd {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i c : Nat} {targets : V} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,targets],[],[],none⟩)
    {cc : Clif.IntCC} {ty : Clif.Ty} {a b : Nat}
    (origin : ctx.defClif? c = some (.icmp cc ty a b)) (constantB : NonConstantSource ctx b) (zero : Bool)
    {fuel : Nat} {before next : State × Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule program (Stock.sem ctx) {} fuel
      (if zero then rule_lower_3257 else rule_lower_3251) [.inst i,.labels labels]).run before =
        .ok (some env,next)) : False := by
  obtain ⟨j,info,defined,found,data⟩ := comparison_source inv origin
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨env0,args,_⟩ := matchRule_some_inv matched
    rw [stock_matchArgs] at args
    cases zero
    all_goals
      have hp := data_program
      isel_inv' hp [rule_lower_3251,rule_lower_3257,slot] at args
      obtain ⟨defined'⟩ : Nonempty (ctx.defInst? c = some _) := ⟨‹_›⟩
      rw [defined] at defined'
      cases defined'
      obtain ⟨found'⟩ : Nonempty (ctx.insts[j]? = some _) := ⟨‹_›⟩
      rw [found] at found'
      cases found'
      obtain ⟨shape⟩ : Nonempty (V.data 152 _ _ = info.data) := ⟨‹_›⟩
      rw [data] at shape
      simp only [V.data.injEq,List.cons.injEq,true_and,and_true] at shape
    · omega
    · obtain ⟨rfl,-⟩ := shape
      obtain ⟨pair⟩ : Nonempty (externExtract ctx T.value_array_2 (.values [a,b]) _ = .ok _) := ⟨‹_›⟩
      rw [ext_value_array_2] at pair
      simp only [ExtResult.ok.injEq,List.cons.injEq,and_true] at pair
      obtain ⟨rfl,rfl⟩ := pair
      obtain ⟨definition⟩ : Nonempty (externExtract ctx T.def_inst (.value b) _ = .ok _) := ⟨‹_›⟩
      obtain ⟨k,definedB,nodeEq⟩ := (ext_def_inst_iff ctx _ b _).mp definition
      simp only [List.cons.injEq,and_true] at nodeEq
      subst nodeEq
      obtain ⟨instruction⟩ : Nonempty (externExtract ctx T.inst_data_value (.inst k) _ =
        .ok [_,.data 152 35 [.data 151 57 [],_]]) := ⟨‹_›⟩
      obtain ⟨infoB,foundB,fieldsB⟩ := (ext_inst_data_value_iff ctx _ k _).mp instruction
      have dataB := (List.cons.inj (List.cons.inj fieldsB).2).1
      exact nonconstant_data inv constantB definedB foundB dataB.symm

/-- The actual first matching rule of a brif whose condition is an original integer comparison
with a nonconstant second operand is ordinary brif. The first operand may be computed. -/
theorem comparison_selected_computed {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i c : Nat} {targets : V} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,targets],[],[],none⟩)
    {cc : Clif.IntCC} {ty : Clif.Ty} {a b : Nat}
    (origin : ctx.defClif? c = some (.icmp cc ty a b)) (constantB : NonConstantSource ctx b)
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
  · exact False.elim (computed_test_bit_absurd inv slot origin constantB false matched)
  · exact False.elim (computed_test_bit_absurd inv slot origin constantB true matched)
  · exact False.elim (other_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2475) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2462) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2451) rfl (by decide) (by decide) (by decide) matched)

/-- A real named comparison branch on a nonconstant second operand derives its ordinary
helper-call packet and original condition provenance internally. -/
theorem comparison_named_calls_computed {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i c : Nat} {targets : V} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,targets],[],[],none⟩)
    {cc : Clif.IntCC} {ty : Clif.Ty} {a b : Nat}
    (origin : ctx.defClif? c = some (.icmp cc ty a b)) (constantB : NonConstantSource ctx b)
    {before next : State} {out : V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst i,.labels labels] before = .ok (some out,next,trace)) :
    ∃ calls : ConditionalCalls.Calls ctx i labels before out next,calls.source = .value c := by
  obtain ⟨selected⟩ := stock_named_branch_selection run
  have root := comparison_selected_computed inv slot origin constantB selected
  obtain ⟨calls⟩ := ConditionalCalls.selected_calls selected root
  obtain ⟨info,targetData,found,data⟩ := calls.sourceData
  rw [slot] at found
  cases found
  simp only [V.data.injEq,List.cons.injEq,and_true,true_and] at data
  exact ⟨calls,data.1.symm⟩

end Backend.Stock.Proof.ComparisonBranch

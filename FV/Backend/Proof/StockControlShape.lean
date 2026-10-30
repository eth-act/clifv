import FV.Backend.Proof.StockSelectionReceipts
import FV.Backend.Proof.StockBranchSelection
import FV.Backend.Proof.IselTermFactsRules

namespace Backend.Stock.Proof.Control
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl

private theorem control_internal_split_first {p : Program} {cfg : Config} {σ : Type} {sem : Isle.Sem V σ}
    (hc : cfg.checkOverlap = false) {ty : TypeId} {t : TermId} {vs : List V} {term : Term}
    {flags : TermFlags} {ex : Option Extractor} (ht : termOf p t = .ok term)
    (hk : term.kind = .decl flags (some .internal) ex) (hm : flags.isMulti = false)
    {n : Nat} (hn : 22 + (p.rulesOf t).length ≤ n) {s s' : σ × Array RuleId} {v : V}
    (h : ApplyInternal p sem cfg n ty t vs s v s') :
    ∃ pre r post, p.rulesOf t = pre ++ r :: post ∧
      (∀ r' ∈ pre, ∃ m' s1, (matchRule p sem cfg (m' + 20) r' vs).run s = .ok (none, s1)) ∧
      ∃ m' n' env s1 st tr,
      (matchRule p sem cfg (m' + 20) r vs).run s = .ok (some env, s1) ∧
      (evalExpr p sem cfg (n' + 20) r.rhs env).run s1 = .ok (some v, (st, tr)) ∧
      s' = (st, tr.push r.id) ∧ n = n' + 20 := by
  obtain ⟨r, pre, post, hL, hpre, m, env, s1, st, tr, hmn, hmt, he, rfl⟩ :=
    applyTerm_internal_some_first hc ht hk hm h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 20 := ⟨m - 20, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 20 := ⟨n - 20, by omega⟩
  refine ⟨pre, r, post, hL, fun r' hr' => ?_, m', n', env, s1, st, tr, hmt, he, rfl, rfl⟩
  obtain ⟨k, hk, s2, h2⟩ := hpre r' hr'
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 20 := ⟨k - 20, by omega⟩
  exact ⟨k', s2, h2⟩


private theorem branch_target (ctx : Ctx) (st : State) (l : Label) (out : V) (next : State) :
    Stock.externCtor ctx T.branch_target [.label l] st = .ok (out,next) ↔ out = .label l ∧ next = st := by
  have actual : Stock.externCtor ctx T.branch_target [.label l] st = .ok (.label l,st) := rfl
  rw [actual]
  simp [eq_comm]

private theorem jump_builder {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 30 ≤ fuel) {target : V}
    {st next : State × Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg fuel 46 661 [target] st out next) :
    next.1 = st.1 ∧ out = .data 46 0 [.data 58 117 [target]] := by
  obtain ⟨_,_,_,rules,_,_,_,_,_,_,_,matched,rhs,rfl,rfl⟩ :=
    control_internal_split_first hc hp.t661 term_661_kind rfl (by rw [hp.r661]; simp; omega) run
  rw [hp.r661] at rules
  isel_rule_cases rules
  cases hp
  isel_inv [*,rule_inst_5371,sem_ctor,sem_mkData,sem_unData] at matched rhs

private theorem emit_side_effect {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 30 ≤ fuel) {i : V}
    {st next : State × Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg fuel 13 242 [.data 46 0 [i]] st out next) :
    ∃ m,MInst.ofV i = some m ∧ next.1 = {st.1 with base := st.1.base.emit m} ∧ out = .op .unit := by
  have emit : ∀ i st out next,Stock.externCtor ctx T.emit [i] st = .ok (out,next) ↔
      ∃ m,MInst.ofV i = some m ∧ out = .op .unit ∧ next = {st with base := st.base.emit m} := by
    intro i st out next
    rw [stock_ctor_baseOnly ctx T.emit [i] st (by decide)]
    have legacy : Backend.externCtor ctx T.emit [i] st.base = match MInst.ofV i with
      | some m => .ok (.op .unit,st.base.emit m)
      | none => .unmodeled s!"emit of {((i.variant?).map (·.2.1)).getD "?"}" := rfl
    rw [legacy]
    cases MInst.ofV i <;> simp [eq_comm]
  obtain ⟨_,_,_,rules,_,_,_,_,_,_,_,matched,rhs,rfl,rfl⟩ :=
    control_internal_split_first hc hp.t242 term_242_kind rfl (by rw [hp.r242]; simp; omega) run
  rw [hp.r242] at rules
  isel_rule_cases rules
  all_goals cases hp
  · isel_inv [*,rule_prelude_lower_522,sem_ctor,sem_mkData,sem_unData,emit] at matched rhs
    isel_destruct
    subst_vars
    obtain ⟨m,decoded,output,state⟩ := (emit _ _ _ _).mp (by assumption)
    exact ⟨m,decoded,state,output⟩
  · isel_inv [*,rule_prelude_lower_524,sem_ctor,sem_unData] at matched
  · isel_inv [*,rule_prelude_lower_527,sem_ctor,sem_unData] at matched

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


private theorem other_jump_format {ctx : Ctx} {i fT : Nat} {fields : List V}
    (slot : ctx.insts[i]? = some ⟨.data 152 15 fields,[],[],none⟩) {r : Rule}
    (format : ruleFmt r = some fT) (lo : 2447 ≤ fT) (hi : fT < 2447+36) (different : fT ≠ 2462)
    {fuel : Nat} {st next : State × Array RuleId} {labels : List Label} {env : Isle.Interp.Env V}
    (matched : (matchRule program (Stock.sem ctx) {} fuel r [.inst i,.labels labels]).run st =
      .ok (some env,next)) : False := by
  obtain ⟨info,fs,source,shape⟩ := branch_ruleFmt_match format lo hi matched
  rw [slot] at source
  cases source
  simp only [V.data.injEq] at shape
  omega

/-- A successful actual Stock branch root at a jump slot selects the original
jump rule and emits exactly its singleton jump target. The first-match choice,
helper runs and complete output state are derived from the named call. -/
theorem stock_named_jump_shape {ctx : Ctx} {i : Nat} {fields : List V} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 15 fields,[],[],none⟩)
    {st next : State} {out : V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst i,.labels labels] st = .ok (some out,next,trace)) :
    ∃ label,labels = [label] ∧ next = {st with base := st.base.emit (.jump label)} ∧
      out = .op .unit ∧ trace.getLast? = some rule_lower_3270.id := by
  obtain ⟨selected⟩ := stock_named_branch_selection run
  have member : selected.rule ∈ program.rulesOf T.lower_branch.id := by rw [selected.candidates]; simp
  rw [show T.lower_branch.id = 687 from rfl,data_program.r687] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  have chosen : selected.rule = rule_lower_3270 := by
    rcases member with root | root | root | root | root | root | root | root
    all_goals try exact root
    all_goals have matched := selected.matchedRun; rw [root] at matched
    · exact False.elim (other_jump_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
    · exact False.elim (other_jump_format slot (fT := 2452) rfl (by decide) (by decide) (by decide) matched)
    · exact False.elim (other_jump_format slot (fT := 2452) rfl (by decide) (by decide) (by decide) matched)
    · exact False.elim (other_jump_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
    · exact False.elim (other_jump_format slot (fT := 2475) rfl (by decide) (by decide) (by decide) matched)
    · exact False.elim (other_jump_format slot (fT := 2452) rfl (by decide) (by decide) (by decide) matched)
    · exact False.elim (other_jump_format slot (fT := 2451) rfl (by decide) (by decide) (by decide) matched)
  have count : (program.rulesOf T.lower_branch.id).length = 8 := by rw [show T.lower_branch.id = 687 from rfl,data_program.r687]; rfl
  have bound := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+20 := ⟨selected.matchFuel-20,by omega⟩
  have matched := selected.matchedRun
  have rhs := selected.rhsRun
  rw [chosen,fuelEq] at matched
  rw [chosen] at rhs
  have hp := data_program
  cases hp
  isel_inv [*,rule_lower_3270,sem_ctor,sem_extract,sem_unData,ext_single_target_iff,ctor_branch_target_iff] at matched rhs
  isel_destruct
  subst_vars
  repeat (isel_inv_simp [ext_single_target_iff,ctor_branch_target_iff] at * <;> isel_destruct <;> subst_vars)
  have envEq := ‹selected.env = _›
  have lookup := ‹selected.env[0]? = some (some _)›
  rw [envEq] at lookup
  simp at lookup
  cases lookup
  simp only [branch_target] at *
  isel_destruct
  subst_vars
  have built := ‹ApplyInternal _ _ _ _ 46 661 _ _ _ _›
  obtain ⟨state,builtEq⟩ := jump_builder data_program rfl (by omega) built
  simp only at state builtEq
  subst_vars
  have emitted := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi,decode,finish,output⟩ := emit_side_effect data_program rfl (by omega) emitted
  rw [ofV_jump] at decode
  cases decode
  refine ⟨?_,output,?_⟩
  · simpa only [‹selected.matched = st›,‹_ = selected.matched›] using finish
  · rw [selected.fired,chosen]
    simp only [Array.toList_push,List.getLast?_append,List.getLast?_singleton,Option.some_or]


private theorem udf_builder {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 30 ≤ fuel) {target : V}
    {st next : State × Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg fuel 46 528 [target] st out next) :
    next.1 = st.1 ∧ out = .data 46 0 [.data 58 123 [target]] := by
  obtain ⟨_,_,_,rules,_,_,_,_,_,_,_,matched,rhs,rfl,rfl⟩ :=
    control_internal_split_first hc hp.t528 term_528_kind rfl (by rw [hp.r528]; simp; omega) run
  rw [hp.r528] at rules
  isel_rule_cases rules
  cases hp
  isel_inv [*,rule_inst_3569,sem_ctor,sem_mkData,sem_unData] at matched rhs


private theorem output_none (ctx : Ctx) (st : State) (out : V) (next : State) :
    Stock.externCtor ctx T.output_none [] st = .ok (out,next) ↔ out = .regsVec [] ∧ next = st := by
  have actual : Stock.externCtor ctx T.output_none [] st = .ok (.regsVec [],st) := rfl
  rw [actual]
  simp [eq_comm]

private theorem side_effect {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 60 ≤ fuel) {i : V}
    {st next : State × Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg fuel 25 243 [.data 46 0 [i]] st out next) :
    ∃ m,MInst.ofV i = some m ∧ next.1 = {st.1 with base := st.1.base.emit m} ∧ out = .regsVec [] := by
  obtain ⟨_,_,_,rules,_,_,_,_,_,_,_,matched,rhs,rfl,rfl⟩ :=
    control_internal_split_first hc hp.t243 term_243_kind rfl (by rw [hp.r243]; simp; omega) run
  rw [hp.r243] at rules
  isel_rule_cases rules
  have keep := hp
  cases hp
  isel_inv [*,rule_prelude_lower_535,sem_ctor,sem_mkData,sem_unData,output_none] at matched rhs
  isel_destruct
  subst_vars
  have emitted := ‹ApplyInternal p (Stock.sem ctx) cfg _ 13 242 [.data 46 0 [i]] _ _ _›
  obtain ⟨mi,decode,state,_⟩ := emit_side_effect keep hc (run := emitted) (by omega)
  obtain ⟨output,same⟩ := (output_none ctx _ _ _).mp (by assumption)
  exact ⟨mi,decode,by simpa only [same] using state,output⟩

private theorem stock_lower_term_nomatch {ctx : Ctx} {ti : Nat} {t : Clif.Terminator}
    {data : V} (retTrap : retOrTrap t = true) (dataRun : Backend.termData t = .ok data)
    (slot : ctx.insts[ti]? = some ⟨data, [], [], none⟩) {r : Rule}
    (member : r ∈ program.rulesOf TId.lower) (notRoot : termRootRule r = false) :
    ∀ fuel st env next, (matchRule program (Stock.sem ctx) {} fuel r [.inst ti]).run st ≠
      .ok (some env, next) := by
  intro fuel st env next matched
  have checked := List.all_eq_true.mp lower_fmts r member
  simp only [lowerFmtOk, notRoot, Bool.false_or] at checked
  split at checked
  · rename_i fT format
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at checked
    obtain ⟨⟨⟨lo, hi⟩, notRet⟩, notTrap⟩ := checked
    obtain ⟨info, fields, source, shape⟩ := branch_ruleFmt_match format lo hi matched
    rw [slot] at source
    cases source
    obtain ⟨fields', rfl⟩ := termData_fmt dataRun
    simp only [V.data.injEq] at shape
    cases t <;> simp [retOrTrap] at retTrap <;> simp [termFmt] at shape <;>
      first | omega | simp [Backend.termData, throw, throwThe, MonadExceptOf.throw] at dataRun
  · cases checked



private def trapEnv (c : Clif.TrapCode) : Isle.Interp.Env V := #[some (.op (.trapCode c))]
private theorem trap_match (ctx : Ctx) {i : Nat} {c : Clif.TrapCode}
    (slot : ctx.insts[i]? = some ⟨.data 152 26 [.data 151 4 [],.op (.trapCode c)],[],[],none⟩)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule program (Stock.sem ctx) {} (n+2) rule_lower_2237 [.inst i]).run (st,tr) =
      .ok (some (trapEnv c),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base slot
  have hp := data_program
  cases hp
  isel_eval [*,trapEnv,rule_lower_2237,sem_extract,sem_unData]
  rfl

/-- Successful actual Stock trap lowering selects the mandatory original trap
root and emits exactly its UDF instruction with the original trap code. -/
theorem stock_named_trap_shape {ctx : Ctx} {i : Nat} {c : Clif.TrapCode}
    (slot : ctx.insts[i]? = some ⟨.data 152 26 [.data 151 4 [],.op (.trapCode c)],[],[],none⟩)
    {st next : State} {out : V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower" [.inst i] st = .ok (some out,next,trace)) :
    next = {st with base := st.base.emit (.udf c)} ∧ out = .regsVec [] ∧
      trace.getLast? = some rule_lower_2237.id := by
  obtain ⟨selected⟩ := stock_named_lower_selection run
  have chosen : selected.rule = rule_lower_2237 := by
    by_cases root : termRootRule selected.rule = true
    · simp only [termRootRule,Bool.or_eq_true,beq_iff_eq] at root
      rcases root with trap | ret
      · exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem mem_lower_2237 (by rw [trap]; rfl)
      · have eq := eq_of_mem_of_id lower_ids_nodup selected.rule_mem mem_lower_2574 (by rw [ret]; rfl)
        have matched := selected.matchedRun
        rw [eq] at matched
        obtain ⟨info,fs,found,shape⟩ := branch_ruleFmt_match (r := rule_lower_2574)
          (fT := 2465) rfl (by decide) (by decide) matched
        rw [slot] at found
        cases found
        cases shape
    · exact False.elim (stock_lower_term_nomatch (t := .trap c) rfl (termData_trap c) slot selected.rule_mem
        (Bool.eq_false_iff.mpr root) _ _ _ _ selected.matchedRun)
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+2 := ⟨selected.matchFuel-2,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq,trap_match ctx slot st #[] m] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,stateEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [chosen,← envEq,← stateEq,← traceEq] at rhs
  have get0 : (trapEnv c)[0]? = some (some (.op (.trapCode c))) := rfl
  have hp := data_program
  cases hp
  isel_inv [*,rule_lower_2237,sem_ctor] at rhs
  isel_destruct
  simp only [← envEq,get0,Option.some.injEq] at *
  subst_vars
  have built := ‹ApplyInternal _ _ _ _ 46 528 _ _ _ _›
  obtain ⟨state,builtEq⟩ := udf_builder data_program rfl (by omega) built
  simp only at state builtEq
  subst_vars
  have emitted := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  obtain ⟨mi,decode,finish,output⟩ := side_effect data_program rfl (by omega) emitted
  change some (.udf c) = some mi at decode
  cases decode
  refine ⟨?_,output,?_⟩
  · simpa only [state,← stateEq] using finish
  · rw [selected.last_rule,chosen]


end Backend.Stock.Proof.Control

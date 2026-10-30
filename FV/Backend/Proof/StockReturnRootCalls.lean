import FV.Backend.Proof.StockSelectionReceipts
import FV.Backend.Proof.StockCoverageTerms

/-! Derive the actual selected return root and its helper execution from the
original term-data slot. No root or helper certificate is supplied by callers. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl

private theorem stock_ruleFmt_match {ctx : Ctx} {r : Rule} {fT : Nat}
    (format : ruleFmt r = some fT) (lo : 2447 ≤ fT) (hi : fT < 2447 + 36)
    {fuel ti : Nat} {st next : State × Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule program (Stock.sem ctx) {} fuel r [.inst ti]).run st =
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
    obtain ⟨info, fields, source, shape⟩ := stock_ruleFmt_match format lo hi matched
    rw [slot] at source
    cases source
    obtain ⟨fields', rfl⟩ := termData_fmt dataRun
    simp only [V.data.injEq] at shape
    cases t <;> simp [retOrTrap] at retTrap <;> simp [termFmt] at shape <;>
      first | omega | simp [Backend.termData, throw, throwThe, MonadExceptOf.throw] at dataRun
  · cases checked


def returnRootEnv (xs : List Nat) : Isle.Interp.Env V := #[some (.values xs)]

/-- The actual return-root matcher preserves all scheduling state and trace. -/
theorem stock_return_root_match {p : Program} (hp : Data p) (ctx : Ctx)
    {i : Nat} {xs : List Nat}
    (slot : ctx.insts[i]? = some ⟨.data 152 18 [.data 151 7 [],.values xs],[],[],none⟩)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) rule_lower_2574 [.inst i]).run (st,tr) =
      .ok (some (returnRootEnv xs),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base slot
  cases hp
  isel_eval [*,returnRootEnv,rule_lower_2574,sem_extract,sem_unData,ext_value_list_slice_iff]
  rfl

/-- Successful actual return lowering chooses rule1037 and supplies its real
helper294 invocation with canonical original requests and complete Stock state. -/
theorem stock_return_selected_calls {ctx : Ctx} {i : Nat} {xs : List Nat}
    (slot : ctx.insts[i]? = some ⟨.data 152 18 [.data 151 7 [],.values xs],[],[],none⟩)
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules) :
    selected.rule = rule_lower_2574 ∧ selected.env = returnRootEnv xs ∧
      selected.matched = st ∧ selected.matchTrace = #[] ∧
      ∃ fuel,60 ≤ fuel ∧ ApplyInternal program (Stock.sem ctx) {} fuel 25 294 [.values xs]
        (st,#[]) out (next,selected.rhsTrace) := by
  have chosen : selected.rule = rule_lower_2574 := by
    by_cases root : termRootRule selected.rule = true
    · simp only [termRootRule,Bool.or_eq_true,beq_iff_eq] at root
      rcases root with trap | ret
      · have eq := eq_of_mem_of_id lower_ids_nodup selected.rule_mem mem_lower_2237 (by rw [trap]; rfl)
        have matched := selected.matchedRun
        rw [eq] at matched
        obtain ⟨info,fields,source,shape⟩ := stock_ruleFmt_match (r := rule_lower_2237)
          (fT := 2473) rfl (by decide) (by decide) matched
        rw [slot] at source
        cases source
        cases shape
      · exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem mem_lower_2574 (by rw [ret]; rfl)
    · exact False.elim (stock_lower_term_nomatch (t := .ret xs) rfl (termData_ret xs) slot selected.rule_mem
        (Bool.eq_false_iff.mpr root) _ _ _ _ selected.matchedRun)
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+2 := ⟨selected.matchFuel-2,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq,stock_return_root_match data_program ctx slot st #[] m] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,stateEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [chosen,← envEq,← stateEq,← traceEq] at rhs
  refine ⟨chosen,envEq.symm,stateEq.symm,traceEq.symm,?_⟩
  have get0 : (returnRootEnv xs)[0]? = some (some (.values xs)) := rfl
  have hp := data_program
  cases hp
  isel_inv [*,rule_lower_2574] at rhs
  isel_destruct
  simp only [← envEq,get0,Option.some.injEq] at *
  subst_vars
  refine ⟨999997,by decide,?_⟩
  simpa only [← stateEq,← traceEq] using (by assumption : ApplyInternal program (Stock.sem ctx) {} 999997 25 294 [.values xs] (selected.matched,selected.matchTrace) out (next,selected.rhsTrace))
end Backend.Stock.Proof

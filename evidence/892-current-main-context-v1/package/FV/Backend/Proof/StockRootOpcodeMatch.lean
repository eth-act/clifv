import FV.Backend.Proof.StockScopeRoots
import FV.Backend.Proof.StockRootOpcode
import FV.Backend.Proof.IselCtlUnmatch
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem opcode_pattern_match {p : Program} (hp : Data p) {ctx : Ctx}
    {q : Pattern} {code : Nat} (parsed : sourceOpcodePattern p q = some code)
    {st : LState} {i : Nat} {env env' : Isle.Interp.Env V}
    (matched : matchPat p (Backend.sem ctx) st q (.inst i) env = .ok (some env')) :
    ∃ info kf opfs rest, ctx.insts[i]? = some info ∧ info.data = .data 152 kf (.data 151 code opfs :: rest) := by
  unfold sourceOpcodePattern at parsed
  split at parsed
  · rename_i type fT oT tail
    split at parsed
    · rename_i format opcode formatLookup opcodeLookup
      split at parsed
      · rename_i kf ko formatKind opcodeKind
        cases parsed
        obtain ⟨fs,extracted,args⟩ := matchPat_extract_inv hp.t209 term_209_kind rfl matched
        rw [Backend.Proof.sem_extract] at extracted
        obtain ⟨info,source,rfl⟩ := ext_inst_data_value_inv extracted
        obtain ⟨e1,_,args2⟩ := matchArgs_cons_inv args
        obtain ⟨e2,formatMatch,_⟩ := matchArgs_cons_inv args2
        obtain ⟨fields,unFormat,fieldMatches⟩ := matchPat_enum_inv formatLookup formatKind formatMatch
        have data := sem_unData_inv unFormat
        cases fields with
        | nil => simp [matchArgs] at fieldMatches
        | cons first rest =>
          obtain ⟨e3,opMatch,_⟩ := matchArgs_cons_inv fieldMatches
          obtain ⟨opfs,unOp,_⟩ := matchPat_enum_inv opcodeLookup opcodeKind opMatch
          have opData := sem_unData_inv unOp
          exact ⟨info,kf,opfs,rest,source,by rw [data,opData]⟩
      · cases parsed
    · cases parsed
  · cases parsed
private theorem opcode_root_match {p : Program} (hp : Data p) {ctx : Ctx}
    {q : Pattern} {code : Nat} (hq : sourceRootOpcode p q = some code)
    {st : LState} {ti : Nat} {env env' : Isle.Interp.Env V}
    (h : matchPat p (Backend.sem ctx) st q (.inst ti) env = .ok (some env')) :
    ∃ info kf opfs rest, ctx.insts[ti]? = some info ∧ info.data = .data 152 kf (.data 151 code opfs :: rest) := by
  unfold sourceRootOpcode at hq
  split at hq
  · exact opcode_pattern_match hp hq (matchPat_bind_inv h).2
  · obtain ⟨e1, h1, -⟩ := matchAll_cons_inv (matchPat_and_inv h)
    exact opcode_pattern_match hp hq h1
  · obtain ⟨e1, -, h2⟩ := matchAll_cons_inv (matchPat_and_inv h)
    obtain ⟨e2, h3, -⟩ := matchAll_cons_inv h2
    obtain ⟨e3, -, h4⟩ := matchAll_cons_inv (matchPat_and_inv h3)
    obtain ⟨e4, h5, -⟩ := matchAll_cons_inv h4
    exact opcode_pattern_match hp hq h5
  · obtain ⟨e1, -, h2⟩ := matchAll_cons_inv (matchPat_and_inv h)
    obtain ⟨e2, h3, -⟩ := matchAll_cons_inv h2
    exact opcode_pattern_match hp hq h3
  · exact opcode_pattern_match hp hq h
private theorem opcode_args_match {p : Program} (hp : Data p) {ctx : Ctx}
    {r : Rule} {code : Nat} (parsed : sourceRuleOpcode p r = some code)
    {st : LState} {i : Nat} {env env' : Isle.Interp.Env V}
    (matched : matchArgs p (Backend.sem ctx) st r.args [.inst i] env = .ok (some env')) :
    ∃ info kf opfs rest, ctx.insts[i]? = some info ∧ info.data = .data 152 kf (.data 151 code opfs :: rest) := by
  cases args : r.args with
  | nil => simp [sourceRuleOpcode,args] at parsed
  | cons q tail =>
    simp only [sourceRuleOpcode,args,List.head?_cons,Option.bind_some] at parsed
    rw [args] at matched
    obtain ⟨e1,head,_⟩ := matchArgs_cons_inv matched
    exact opcode_root_match hp parsed head
/-- A rule's argument patterns match an instruction under the baseline embedding only if its
primary source opcode is the instruction's data opcode. -/
theorem stock_opcode_args_match {p : Program} (hp : Data p) {ctx : Ctx}
    {r : Rule} {code : Nat} (parsed : sourceRuleOpcode p r = some code)
    {st : LState} {i : Nat} {env env' : Isle.Interp.Env V}
    (matched : matchArgs p (Backend.sem ctx) st r.args [.inst i] env = .ok (some env')) :
    ∃ info kf opfs rest, ctx.insts[i]? = some info ∧ info.data = .data 152 kf (.data 151 code opfs :: rest) :=
  opcode_args_match hp parsed matched
/-- Real Stock first-match selection has the primary opcode of its original
source data, using original scope/closure and actual matching internally. -/
theorem stock_selected_source_opcode {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} {inst : Clif.Inst} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some inst) {kf code : Nat} {rest : List V}
    (data : info.data = .data 152 kf (.data 151 code [] :: rest))
    {before after : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i before out after trace) : sourceRuleOpcode program selected.rule = some code := by
  have closed := stock_selected_source_root_closure mapped source clif selected
  have checked := List.all_eq_true.mp stock_source_opcode_inventory selected.rule selected.rule_mem
  simp only [closed,Bool.not_true,Bool.false_or] at checked
  cases parsed : sourceRuleOpcode program selected.rule with
  | none => rw [parsed] at checked; cases checked
  | some actual =>
    have count : (program.rulesOf T.lower.id).length = 517 := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
    have enough := selected.fuelBound
    obtain ⟨fuel,fuelEq⟩ : ∃ fuel,selected.matchFuel = fuel+1 := ⟨selected.matchFuel-1,by omega⟩
    have matched := selected.matchedRun
    rw [fuelEq] at matched
    obtain ⟨bound,args,_⟩ := matchRule_some_inv matched
    rw [stock_matchArgs] at args
    obtain ⟨info',format,opfs,tail,found,shape⟩ := opcode_args_match data_program parsed args
    have sameInfo := Option.some.inj (found.symm.trans source)
    subst info'
    have equal := V.data.inj (data.symm.trans shape)
    have opEq := V.data.inj (List.cons.inj equal.2.2).1
    exact congrArg some opEq.2.1.symm
/-- The actual selected root belongs to the checked opcode candidate list;
no rule-id or reachable-root certificate is supplied by the caller. -/
theorem stock_selected_source_opcode_ids {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} {inst : Clif.Inst} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some inst) {kf code : Nat} {rest : List V}
    (data : info.data = .data 152 kf (.data 151 code [] :: rest))
    {before after : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i before out after trace) : selected.rule.id ∈ sourceOpcodeIds code := by
  have closed := stock_selected_source_root_closure mapped source clif selected
  rw [closureRoot_eq] at closed
  have opcode := stock_selected_source_opcode mapped source clif data selected
  unfold sourceOpcodeIds
  exact List.mem_map.mpr ⟨selected.rule,List.mem_filter.mpr ⟨selected.rule_mem,by simp only [closed,opcode,beq_self_eq_true,Bool.true_and]⟩,rfl⟩
/-- Real retained emitted source records carry only ids from their original
opcode family, derived from the actual selection and unchanged source scope. -/
theorem stock_lower_source_record_opcode_ids {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {inst : Clif.Inst} (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some inst) {kf code : Nat} {rest : List V}
    (data : info.data = .data 152 kf (.data 151 code [] :: rest))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    step.rules.getLast?.any (sourceOpcodeIds code).contains = true := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have member := stock_selected_source_opcode_ids (stock_lower_record_context run scope events).1 source clif data receipt.selected
  rw [receipt.rules,receipt.selected.last_rule]
  simpa only [Option.any_some,List.contains_iff_mem] using member
end Backend.Stock.Proof

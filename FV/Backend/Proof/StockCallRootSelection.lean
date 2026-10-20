import FV.Backend.Proof.StockCallAbiStatic
import FV.Backend.Proof.StockReturnRootCalls
namespace Backend.Stock.Proof.CallRootSelectionDraft
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl

private def checkedFormat (r : Rule) : Bool :=
  match ruleFmt r with
  | none => false
  | some f => decide (2447 ≤ f ∧ f < 2447+36) &&
      (if f == 2453 then callRootRule r || r.id == 1038 || r.id == 1039 else if f == 2454 then indRootRule r || r.id == 1040 else true)

private theorem checkedFormats : (program.rulesOf TId.lower).all checkedFormat = true := by
  rw [show TId.lower = 686 from rfl,data_program.r686]
  decide +kernel

private theorem matched_format {ctx : Ctx} {r : Rule} {fT : Nat}
    (format : ruleFmt r = some fT) (lo : 2447 ≤ fT) (hi : fT < 2447+36)
    {fuel ti : Nat} {st next : State × Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule program (Stock.sem ctx) {} fuel r [.inst ti]).run st = .ok (some env,next)) :
    ∃ info fs,ctx.insts[ti]? = some info ∧ info.data = .data 152 (fT-2447) fs := by
  have bound : fT-2447 < 36 := by omega
  obtain ⟨term,lookup,kind⟩ := fmtKinds_program (fT-2447) bound
  rw [show 2447+(fT-2447)=fT by omega] at lookup
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨env0,args,_⟩ := matchRule_some_inv matched
    rw [stock_matchArgs] at args
    unfold ruleFmt at format
    split at format
    · rename_i q qs shape
      rw [shape] at args
      obtain ⟨env1,head,_⟩ := matchArgs_cons_inv args
      exact rootFmt_match_k data_program format lookup kind head
    · cases format

/-- The actual selected direct-call root is one of the two real call rules.
The rule family follows from its successful match and actual source slot. -/
theorem stock_selected_call_rule {ctx : Ctx} {ti : Nat} {info : IInfo} {fs : List V}
    (slot : ctx.insts[ti]? = some info) (data : info.data = .data 152 6 (.data 151 8 [] :: fs))
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx ti st out next rules) :
    selected.rule = rule_lower_2508 ∨ selected.rule = rule_lower_2518 := by
  have checked := List.all_eq_true.mp checkedFormats selected.rule selected.rule_mem
  unfold checkedFormat at checked
  cases format : ruleFmt selected.rule with
  | none => rw [format] at checked; cases checked
  | some fT =>
    rw [format] at checked
    simp only [Bool.and_eq_true,decide_eq_true_eq] at checked
    obtain ⟨bounds,family⟩ := checked
    obtain ⟨actual,fields,lookup,shape⟩ := matched_format format bounds.1 bounds.2 selected.matchedRun
    rw [slot] at lookup; cases lookup
    rw [data] at shape
    have same : fT = 2453 := by simp only [V.data.injEq] at shape; omega
    subst fT
    simp only [beq_self_eq_true,ite_true,callRootRule,Bool.or_eq_true,beq_iff_eq] at family
    rcases family with ((direct | got) | tail) | tail
    · exact .inl (eq_of_mem_of_id lower_ids_nodup selected.rule_mem mem_lower_2508 direct)
    · exact .inr (eq_of_mem_of_id lower_ids_nodup selected.rule_mem mem_lower_2518 got)
    · have member : rule_lower_2580 ∈ program.rulesOf TId.lower := by
        rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel
      have equal := eq_of_mem_of_id lower_ids_nodup selected.rule_mem member tail
      have matched := selected.matchedRun
      have enough := selected.fuelBound
      have count : (program.rulesOf T.lower.id).length = 517 := by rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
      obtain ⟨fuel,fuelEq⟩ : ∃ fuel,selected.matchFuel = fuel+1000 := ⟨selected.matchFuel-1000,by omega⟩
      rw [equal,fuelEq] at matched
      have source := ext_inst_data_value ctx st.base slot
      rw [data] at source
      have opcode : termOf program 2294 = .ok T.«Opcode.ReturnCall» := by unfold program termOf; rfl
      have hp := data_program
      cases hp
      isel_inv [*,rule_lower_2580,sem_extract,sem_unData,source,T.«Opcode.ReturnCall»,T.«Opcode.ReturnCallIndirect»] at matched
      isel_destruct
      simp_all only [Option.some.injEq]
      subst_vars
      rename_i actualLookup sourceShape tailShape
      have impossible := sourceShape.trans tailShape.symm
      cases impossible

    · have member : rule_lower_2587 ∈ program.rulesOf TId.lower := by
        rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel
      have equal := eq_of_mem_of_id lower_ids_nodup selected.rule_mem member tail
      have matched := selected.matchedRun
      have enough := selected.fuelBound
      have count : (program.rulesOf T.lower.id).length = 517 := by rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
      obtain ⟨fuel,fuelEq⟩ : ∃ fuel,selected.matchFuel = fuel+1000 := ⟨selected.matchFuel-1000,by omega⟩
      rw [equal,fuelEq] at matched
      have source := ext_inst_data_value ctx st.base slot
      rw [data] at source
      have opcode : termOf program 2294 = .ok T.«Opcode.ReturnCall» := by unfold program termOf; rfl
      have hp := data_program
      cases hp
      isel_inv [*,rule_lower_2587,sem_extract,sem_unData,source,T.«Opcode.ReturnCall»,T.«Opcode.ReturnCallIndirect»] at matched
      isel_destruct
      simp_all only [Option.some.injEq]
      subst_vars
      rename_i actualLookup sourceShape tailShape
      have impossible := sourceShape.trans tailShape.symm
      cases impossible


/-- The actual selected indirect-call root is the real indirect-call rule;
neither a caller-selected rule nor an abstract helper certificate is needed. -/
theorem stock_selected_call_indirect_rule {ctx : Ctx} {ti : Nat} {info : IInfo} {fs : List V}
    (slot : ctx.insts[ti]? = some info) (data : info.data = .data 152 7 (.data 151 9 [] :: fs))
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx ti st out next rules) : selected.rule = rule_lower_2529 := by
  have checked := List.all_eq_true.mp checkedFormats selected.rule selected.rule_mem
  unfold checkedFormat at checked
  cases format : ruleFmt selected.rule with
  | none => rw [format] at checked; cases checked
  | some fT =>
    rw [format] at checked
    simp only [Bool.and_eq_true,decide_eq_true_eq] at checked
    obtain ⟨bounds,family⟩ := checked
    obtain ⟨actual,fields,lookup,shape⟩ := matched_format format bounds.1 bounds.2 selected.matchedRun
    rw [slot] at lookup; cases lookup
    rw [data] at shape
    have same : fT = 2454 := by simp only [V.data.injEq] at shape; omega
    subst fT
    simp [indRootRule] at family
    rcases family with ordinary | tail
    · exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem mem_lower_2529 ordinary
    · have member : rule_lower_2595 ∈ program.rulesOf TId.lower := by
        rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel
      have equal := eq_of_mem_of_id lower_ids_nodup selected.rule_mem member tail
      have matched := selected.matchedRun
      have enough := selected.fuelBound
      have count : (program.rulesOf T.lower.id).length = 517 := by rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
      obtain ⟨fuel,fuelEq⟩ : ∃ fuel,selected.matchFuel = fuel+1000 := ⟨selected.matchFuel-1000,by omega⟩
      rw [equal,fuelEq] at matched
      have source := ext_inst_data_value ctx st.base slot
      rw [data] at source
      have opcode : termOf program 2295 = .ok T.«Opcode.ReturnCallIndirect» := by unfold program termOf; rfl
      have hp := data_program
      cases hp
      isel_inv [*,rule_lower_2595,sem_extract,sem_unData,source,T.«Opcode.ReturnCall»,T.«Opcode.ReturnCallIndirect»] at matched
      isel_destruct
      simp_all only [Option.some.injEq]
      subst_vars
      rename_i actualLookup sourceShape tailShape
      have impossible := sourceShape.trans tailShape.symm
      cases impossible

end Backend.Stock.Proof.CallRootSelectionDraft

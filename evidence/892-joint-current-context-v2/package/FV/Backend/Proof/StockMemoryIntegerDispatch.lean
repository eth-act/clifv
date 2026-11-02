import FV.Backend.Proof.StockMemoryIntegerSelected
import FV.Backend.Proof.StockRootOpcodeMatch

namespace Backend.Stock.Memory.IntegerRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem inventory : sourceOpcodeIds 29 = [1041,1042,1043,1044,1047,1048] := by decide +kernel

/-- Original load opcode/type data determines the actual selected root internally.
The emitted-record adapter therefore needs no selected-ID input condition. -/
theorem stock_selected_integer_load_rule_offset (width : Width) {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {flags : Clif.MemFlags} {offset : Int}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.load .load width.sourceTy flags x offset))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = width.root := by
  obtain ⟨little,data,type⟩ := integer_load_source_data_offset width inv source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  rw [inventory] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨fuel,fuelEq⟩ : ∃ fuel,selected.matchFuel = fuel+1 := ⟨selected.matchFuel-1,by omega⟩
  have matched := selected.matchedRun
  rw [fuelEq] at matched
  obtain ⟨initial,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs] at args
  rcases member with h0 | h1 | h2 | h3 | h4 | h5
  · have candidate : rule_lower_2604 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h0
    cases width <;> first
    | exact chosen
    | rw [chosen] at args
      obtain ⟨first,head,_⟩ := matchArgs_cons_inv args
      obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl head
      rw [Backend.Proof.sem_extract] at extracted
      have expected := ext_inst_data_value ctx st.base source
      rw [type,Option.getD_some] at expected
      rw [expected] at extracted
      cases extracted
      obtain ⟨middle,typeMatch,_⟩ := matchArgs_cons_inv patterns
      have primitive : (Backend.sem ctx).prim 14 "I8" = some (.ty (.int 8)) := rfl
      have equal : ∀ a b,(Backend.sem ctx).eq a b = (a == b) := fun _ _ => rfl
      simp [matchPat,primitive,equal,Width.bits] at typeMatch
  · have candidate : rule_lower_2607 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h1
    cases width <;> first
    | exact chosen
    | rw [chosen] at args
      obtain ⟨first,head,_⟩ := matchArgs_cons_inv args
      obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl head
      rw [Backend.Proof.sem_extract] at extracted
      have expected := ext_inst_data_value ctx st.base source
      rw [type,Option.getD_some] at expected
      rw [expected] at extracted
      cases extracted
      obtain ⟨middle,typeMatch,_⟩ := matchArgs_cons_inv patterns
      have primitive : (Backend.sem ctx).prim 14 "I16" = some (.ty (.int 16)) := rfl
      have equal : ∀ a b,(Backend.sem ctx).eq a b = (a == b) := fun _ _ => rfl
      simp [matchPat,primitive,equal,Width.bits] at typeMatch
  · have candidate : rule_lower_2610 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h2
    cases width <;> first
    | exact chosen
    | rw [chosen] at args
      obtain ⟨first,head,_⟩ := matchArgs_cons_inv args
      obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl head
      rw [Backend.Proof.sem_extract] at extracted
      have expected := ext_inst_data_value ctx st.base source
      rw [type,Option.getD_some] at expected
      rw [expected] at extracted
      cases extracted
      obtain ⟨middle,typeMatch,_⟩ := matchArgs_cons_inv patterns
      have primitive : (Backend.sem ctx).prim 14 "I32" = some (.ty (.int 32)) := rfl
      have equal : ∀ a b,(Backend.sem ctx).eq a b = (a == b) := fun _ _ => rfl
      simp [matchPat,primitive,equal,Width.bits] at typeMatch
  · have candidate : rule_lower_2613 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h3
    cases width <;> first
    | exact chosen
    | rw [chosen] at args
      obtain ⟨first,head,_⟩ := matchArgs_cons_inv args
      obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl head
      rw [Backend.Proof.sem_extract] at extracted
      have expected := ext_inst_data_value ctx st.base source
      rw [type,Option.getD_some] at expected
      rw [expected] at extracted
      cases extracted
      obtain ⟨middle,typeMatch,_⟩ := matchArgs_cons_inv patterns
      have primitive : (Backend.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
      have equal : ∀ a b,(Backend.sem ctx).eq a b = (a == b) := fun _ _ => rfl
      simp [matchPat,primitive,equal,Width.bits] at typeMatch
  · have candidate : rule_lower_2625 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h4
    rw [chosen] at args
    obtain ⟨first,head,_⟩ := matchArgs_cons_inv args
    obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl head
    rw [Backend.Proof.sem_extract] at extracted
    have expected := ext_inst_data_value ctx st.base source
    rw [type,Option.getD_some] at expected
    rw [expected] at extracted
    cases extracted
    obtain ⟨middle,typeMatch,_⟩ := matchArgs_cons_inv patterns
    obtain ⟨fs,extraction,_⟩ := matchPat_extract_inv data_program.t129 term_129_kind rfl typeMatch
    rw [Backend.Proof.sem_extract] at extraction
    have impossible : Backend.externExtract ctx T.ty_float_or_vec (.ty (.int width.bits)) st.base = .fail := rfl
    rw [impossible] at extraction
    cases extraction
  · have candidate : rule_lower_2628 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h5
    rw [chosen] at args
    obtain ⟨first,head,_⟩ := matchArgs_cons_inv args
    obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl head
    rw [Backend.Proof.sem_extract] at extracted
    have expected := ext_inst_data_value ctx st.base source
    rw [type,Option.getD_some] at expected
    rw [expected] at extracted
    cases extracted
    obtain ⟨middle,typeMatch,_⟩ := matchArgs_cons_inv patterns
    obtain ⟨fs,extraction,_⟩ := matchPat_extract_inv data_program.t129 term_129_kind rfl typeMatch
    rw [Backend.Proof.sem_extract] at extraction
    have impossible : Backend.externExtract ctx T.ty_float_or_vec (.ty (.int width.bits)) st.base = .fail := rfl
    rw [impossible] at extraction
    cases extraction

/-- Preserve the original zero-offset theorem variant. -/
theorem stock_selected_integer_load_rule (width : Width) {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {flags : Clif.MemFlags}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.load .load width.sourceTy flags x 0))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = width.root := by
  exact stock_selected_integer_load_rule_offset width inv source clif selected

/-- An actual emitted load derives its selected ID directly from original source
metadata and whole-driver receipts, without a separate root certificate. -/
theorem stock_lower_integer_load_selected_id_offset (width : Width) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {x : Nat} {flags : Clif.MemFlags} {offset : Int}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load .load width.sourceTy flags x offset))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    step.rules.getLast? = some width.root.id := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have chosen := stock_selected_integer_load_rule_offset width (stock_lower_record_context run scope events).1 source clif receipt.selected
  rw [receipt.rules,receipt.selected.last_rule,chosen]

/-- Preserve the original zero-offset theorem variant. -/
theorem stock_lower_integer_load_selected_id (width : Width) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {x : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load .load width.sourceTy flags x 0))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    step.rules.getLast? = some width.root.id := by
  exact stock_lower_integer_load_selected_id_offset width run scope events records source clif recorded emitted

end Backend.Stock.Memory.IntegerRoots

import FV.Backend.Proof.StockMemorySelected
import FV.Backend.Proof.StockRootOpcodeMatch

namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem inventory : sourceOpcodeIds 29 = [1041,1042,1043,1044,1047,1048] := by decide +kernel

section SourceData
attribute [local semireducible] Isle.Aarch64.program
private theorem source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {flags : Clif.MemFlags}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.load .load .i32 flags x 0)) :
    flags.endianness ≠ some .big ∧
      info.data = .data 152 16 [.data 151 29 [],.value x,.op (.memFlags flags),.int 0] ∧
      info.resTys.head? = some (.int 32) := by
  have data := inv.data i info _ source clif
  have little : flags.endianness ≠ some .big := by
    intro big
    simp [instData,eTy,big] at data
  have shape : instData f (.load .load .i32 flags x 0) =
      .ok (.data 152 16 [.data 151 29 [],.value x,.op (.memFlags flags),.int 0]) := by
    change (if flags.endianness == some .big then Except.error "big-endian load" else
      Except.ok (V.data 152 16 [.data 151 29 [],.value x,.op (.memFlags flags),.int 0])) = _
    rw [show (flags.endianness == some .big) = false from by simpa using little]
    rfl
  obtain ⟨types,typed,resTys,length⟩ := inv.resTys i info _ source clif
  change some [.i32] = some types at typed
  cases typed
  exact ⟨little,Except.ok.inj (data.symm.trans shape),by rw [resTys]; rfl⟩
end SourceData

/-- Original load opcode/type data determines the actual selected root internally.
The emitted-record adapter therefore needs no selected-ID input condition. -/
theorem stock_selected_load_i32_rule {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {flags : Clif.MemFlags}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.load .load .i32 flags x 0))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = rule_lower_2610 := by
  obtain ⟨little,data,type⟩ := source_data inv source clif
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
    rw [chosen] at args
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
    simp [matchPat,primitive,equal] at typeMatch
  · have candidate : rule_lower_2607 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h1
    rw [chosen] at args
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
    simp [matchPat,primitive,equal] at typeMatch
  · have candidate : rule_lower_2610 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h2
    exact chosen
  · have candidate : rule_lower_2613 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h3
    rw [chosen] at args
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
    simp [matchPat,primitive,equal] at typeMatch
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
    have impossible : Backend.externExtract ctx T.ty_float_or_vec (.ty (.int 32)) st.base = .fail := rfl
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
    have impossible : Backend.externExtract ctx T.ty_float_or_vec (.ty (.int 32)) st.base = .fail := rfl
    rw [impossible] at extraction
    cases extraction

/-- An actual emitted load derives its selected ID directly from original source
metadata and whole-driver receipts, without a separate root certificate. -/
theorem stock_lower_load_i32_selected_id {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {x : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load .load .i32 flags x 0))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    step.rules.getLast? = some rule_lower_2610.id := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have chosen := stock_selected_load_i32_rule (stock_lower_record_context run scope events).1 source clif receipt.selected
  rw [receipt.rules,receipt.selected.last_rule,chosen]

end Backend.Stock.Memory

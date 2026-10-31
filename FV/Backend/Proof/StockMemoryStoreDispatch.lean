import FV.Backend.Proof.StockMemoryStoreMatch
import FV.Backend.Proof.StockRootOpcodeMatch
import FV.Backend.Proof.IselCtlRuleIds

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem store_type_pattern_matched {p : Program} (hp : Data p)
    {ctx : Ctx} {st : LState} {i value pointer width : Nat} {info : IInfo} {flags : Clif.MemFlags}
    (source : ctx.insts[i]? = some info)
    (data : info.data = .data 152 22
      [.data 151 30 [],.values [value,pointer],.op (.memFlags flags),.int 0])
    (typed : ctx.valueType? value = some (.int width))
    {typePattern : Pattern} {env env' : Isle.Interp.Env V}
    (matched : matchArgs p (Backend.sem ctx) st
      [.term 18 209 [.wildcard 14,.term 152 2469
        [.term 151 2314 [],.term 147 1614
          [.bind 15 0 (.term 15 2 [typePattern]),.bind 15 1 (.wildcard 15)],
          .term 137 103 [.bind 142 2 (.wildcard 142)],.bind 138 3 (.wildcard 138)]]]
      [.inst i] env = .ok (some env')) :
    ∃ before after,matchPat p (Backend.sem ctx) st typePattern (.ty (.int width)) before =
      .ok (some after) := by
  obtain ⟨first,head,_⟩ := matchArgs_cons_inv matched
  obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv hp.t209 term_209_kind rfl head
  rw [Backend.Proof.sem_extract] at extracted
  have expected := ext_inst_data_value ctx st source
  rw [data] at expected
  rw [expected] at extracted
  cases extracted
  obtain ⟨middle,_,rest⟩ := matchArgs_cons_inv patterns
  obtain ⟨next,format,_⟩ := matchArgs_cons_inv rest
  obtain ⟨fields,unData,fieldPatterns⟩ := matchPat_enum_inv hp.t2469 term_2469_kind format
  have known : (Backend.sem ctx).unData 152
      (.data 152 22 [.data 151 30 [],.values [value,pointer],.op (.memFlags flags),.int 0]) =
      some (22,[.data 151 30 [],.values [value,pointer],.op (.memFlags flags),.int 0]) := rfl
  rw [known] at unData
  have same : fields = [.data 151 30 [],.values [value,pointer],.op (.memFlags flags),.int 0] :=
    (congrArg Prod.snd (Option.some.inj unData)).symm
  rw [same] at fieldPatterns
  obtain ⟨afterOpcode,_,rest⟩ := matchArgs_cons_inv fieldPatterns
  obtain ⟨afterValues,values,_⟩ := matchArgs_cons_inv rest
  obtain ⟨operands,unpack,operandPatterns⟩ := matchPat_extract_inv hp.t1614 term_1614_kind rfl values
  rw [Backend.Proof.sem_extract] at unpack
  have unpacked := ext_value_array_2 ctx st value pointer
  rw [unpacked] at unpack
  cases unpack
  obtain ⟨afterValue,valueMatch,_⟩ := matchArgs_cons_inv operandPatterns
  have typeMatch := (matchPat_bind_inv valueMatch).2
  obtain ⟨types,lookup,typePatterns⟩ := matchPat_extract_inv hp.t2 term_2_kind rfl typeMatch
  rw [Backend.Proof.sem_extract] at lookup
  rw [ext_value_type ctx st typed] at lookup
  cases lookup
  obtain ⟨afterType,actual,_⟩ := matchArgs_cons_inv typePatterns
  exact ⟨_,_,actual⟩

private def plainKind : IntegerRoots.Width → Kind
  | .w8 => .plain8 | .w16 => .plain16 | .w32 => .plain32 | .w64 => .plain64
private theorem plain_opcode (width : IntegerRoots.Width) : (plainKind width).sourceOp = .store := by
  cases width <;> rfl
private theorem plain_index (width : IntegerRoots.Width) : (plainKind width).opcodeIndex = 30 := by
  cases width <;> rfl
private theorem plain_inventory :
    sourceOpcodeIds 30 = [1064,1065,1066,1067,1073,1074] := by
  decide +kernel

private theorem selected_plain_store_rule (width : IntegerRoots.Width)
    {ty : Clif.Ty} {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i value pointer : Nat} {info : IInfo} {flags : Clif.MemFlags}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.store .store ty flags value pointer 0))
    (typed : ctx.valueType? value = some (.int width.bits))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = (plainKind width).root := by
  obtain ⟨little,data⟩ := integer_store_source_data (plainKind width) inv source
    (by rw [plain_opcode]; exact clif)
  rw [plain_index] at data
  have member := stock_selected_source_opcode_ids inv source clif data selected
  rw [plain_inventory] at member
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
  · have candidate : rule_lower_2705 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h0
    rw [chosen] at args
    cases width <;> first
    | exact chosen
    | obtain ⟨before,after,failed⟩ := store_type_pattern_matched data_program source data typed args
      have primitive : (Backend.sem ctx).prim 14 "I8" = some (.ty (.int 8)) := rfl
      have equal : ∀ a b,(Backend.sem ctx).eq a b = (a == b) := fun _ _ => rfl
      simp [matchPat,primitive,equal,IntegerRoots.Width.bits] at failed
  · have candidate : rule_lower_2709 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h1
    rw [chosen] at args
    cases width <;> first
    | exact chosen
    | obtain ⟨before,after,failed⟩ := store_type_pattern_matched data_program source data typed args
      have primitive : (Backend.sem ctx).prim 14 "I16" = some (.ty (.int 16)) := rfl
      have equal : ∀ a b,(Backend.sem ctx).eq a b = (a == b) := fun _ _ => rfl
      simp [matchPat,primitive,equal,IntegerRoots.Width.bits] at failed
  · have candidate : rule_lower_2713 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h2
    rw [chosen] at args
    cases width <;> first
    | exact chosen
    | obtain ⟨before,after,failed⟩ := store_type_pattern_matched data_program source data typed args
      have primitive : (Backend.sem ctx).prim 14 "I32" = some (.ty (.int 32)) := rfl
      have equal : ∀ a b,(Backend.sem ctx).eq a b = (a == b) := fun _ _ => rfl
      simp [matchPat,primitive,equal,IntegerRoots.Width.bits] at failed
  · have candidate : rule_lower_2717 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h3
    rw [chosen] at args
    cases width <;> first
    | exact chosen
    | obtain ⟨before,after,failed⟩ := store_type_pattern_matched data_program source data typed args
      have primitive : (Backend.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
      have equal : ∀ a b,(Backend.sem ctx).eq a b = (a == b) := fun _ _ => rfl
      simp [matchPat,primitive,equal,IntegerRoots.Width.bits] at failed
  · have candidate : rule_lower_2746 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h4
    rw [chosen] at args
    obtain ⟨before,after,failed⟩ := store_type_pattern_matched data_program source data typed args
    obtain ⟨fields,extracted,_⟩ := matchPat_extract_inv data_program.t129 term_129_kind rfl failed
    rw [Backend.Proof.sem_extract] at extracted
    have impossible : Backend.externExtract ctx T.ty_float_or_vec (.ty (.int width.bits)) st.base = .fail := by
      cases width <;> rfl
    rw [impossible] at extracted
    cases extracted
  · have candidate : rule_lower_2750 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h5
    rw [chosen] at args
    obtain ⟨before,after,failed⟩ := store_type_pattern_matched data_program source data typed args
    obtain ⟨fields,extracted,_⟩ := matchPat_extract_inv data_program.t129 term_129_kind rfl failed
    rw [Backend.Proof.sem_extract] at extracted
    have impossible : Backend.externExtract ctx T.ty_float_or_vec (.ty (.int width.bits)) st.base = .fail := by
      cases width <;> rfl
    rw [impossible] at extracted
    cases extracted

private theorem selected_unique_store_rule (kind : Kind)
    (inventory : sourceOpcodeIds kind.opcodeIndex = [kind.root.id])
    {ty : Clif.Ty} {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i value pointer : Nat} {info : IInfo} {flags : Clif.MemFlags}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.store kind.sourceOp ty flags value pointer 0))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = kind.root := by
  obtain ⟨little,data⟩ := integer_store_source_data kind inv source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  rw [inventory] at member
  have equal := List.mem_singleton.mp member
  have candidate : kind.root ∈ program.rulesOf T.lower.id := by
    cases kind <;> rw [show T.lower.id = 686 from rfl,data_program.r686]
    all_goals decide +kernel
  exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate equal

/-- Original opcode and operand type determine all seven selected store roots internally. -/
theorem stock_selected_integer_store_rule (kind : Kind)
    {ty : Clif.Ty} {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i value pointer : Nat} {info : IInfo} {flags : Clif.MemFlags}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.store kind.sourceOp ty flags value pointer 0))
    (typed : kind.sourceOp = .store → ctx.valueType? value = some (.int kind.width.bits))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = kind.root := by
  cases kind with
  | plain8 => exact selected_plain_store_rule .w8 inv source clif (typed rfl) selected
  | plain16 => exact selected_plain_store_rule .w16 inv source clif (typed rfl) selected
  | plain32 => exact selected_plain_store_rule .w32 inv source clif (typed rfl) selected
  | plain64 => exact selected_plain_store_rule .w64 inv source clif (typed rfl) selected
  | narrow8 => exact selected_unique_store_rule .narrow8 (by decide +kernel) inv source clif selected
  | narrow16 => exact selected_unique_store_rule .narrow16 (by decide +kernel) inv source clif selected
  | narrow32 => exact selected_unique_store_rule .narrow32 (by decide +kernel) inv source clif selected

/-- A retained store derives its selected ID from the actual whole-driver selection receipt. -/
theorem stock_lower_integer_store_selected_id (kind : Kind) {ty : Clif.Ty}
    {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {value pointer : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.store kind.sourceOp ty flags value pointer 0))
    (typed : kind.sourceOp = .store → event.ctx.valueType? value = some (.int kind.width.bits))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    step.rules.getLast? = some kind.root.id := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have chosen := stock_selected_integer_store_rule kind (stock_lower_record_context run scope events).1
    source clif typed receipt.selected
  rw [receipt.rules,receipt.selected.last_rule,chosen]

end Backend.Stock.Memory.StoreRoots

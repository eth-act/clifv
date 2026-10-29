module

public import FV.Backend.Proof.StockRootOpcodeMatch
public import FV.Backend.Proof.StockUnarySourceValues

@[expose] public section

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
section Data
attribute [local semireducible] Isle.Aarch64.program
private theorem neg_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .ineg ty x)) :
    IW ty.width ∧ info.data = .data 152 29 [.data 151 75 [],.value x] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by simpa [Compile.instE,Compile.unaryTyE,Compile.unaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  · cases ty <;> simp [eTy,Clif.Ty.width,IW] at supported ⊢
  · have expected : instData f (.unary .ineg ty x) = .ok (.data 152 29 [.data 151 75 [],.value x]) := by
      simp only [instData,unaryOpcode,supported,ite_true]; rfl
    exact Except.ok.inj (raw.symm.trans expected)
end Data
section Data
attribute [local semireducible] Isle.Aarch64.program
private theorem bswap_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .bswap ty x)) :
    (ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) ∧ info.data = .data 152 29 [.data 151 110 [],.value x] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have allowed : Compile.unaryTyE .bswap ty = true := by simpa only [Compile.instE] using accepted
  have supported : eTy ty = true := by cases ty <;> simp [Compile.unaryTyE,Compile.tyE,eTy] at allowed ⊢
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  · cases ty <;> simp [Compile.unaryTyE,Compile.tyE,Clif.Ty.width] at allowed ⊢
  · have expected : instData f (.unary .bswap ty x) = .ok (.data 152 29 [.data 151 110 [],.value x]) := by
      cases ty <;> simp [Compile.unaryTyE,Compile.tyE] at allowed <;> rfl
    exact Except.ok.inj (raw.symm.trans expected)
end Data
/-- Original negation source data and actual first matching select its unique
in-scope root internally. No selected-rule certificate is a caller premise. -/
theorem stock_selected_neg_rule {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .ineg ty x))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = rule_lower_857 := by
  obtain ⟨_,data,_⟩ := neg_data inv source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  rw [stock_neg_opcode_inventory] at member
  have idEq := List.mem_singleton.mp member
  have candidate : rule_lower_857 ∈ program.rulesOf T.lower.id := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
  exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate idEq
private theorem type_match {ctx : Ctx} {r : Rule} {name : String} {target i w : Nat} {q : Pattern}
    (args : r.args = [.term 18 209 [.constPrim 14 name,q]])
    (primitive : (Backend.sem ctx).prim 14 name = some (.ty (.int target)))
    {info : IInfo} (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    {st : LState} {env env' : Isle.Interp.Env V}
    (matched : matchArgs program (Backend.sem ctx) st r.args [.inst i] env = .ok (some env')) : w = target := by
  rw [args] at matched
  obtain ⟨first,head,_⟩ := matchArgs_cons_inv matched
  obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl head
  rw [Backend.Proof.sem_extract] at extracted
  have expected := ext_inst_data_value ctx st source
  rw [type,Option.getD_some] at expected
  rw [expected] at extracted
  cases extracted
  obtain ⟨middle,typeMatch,_⟩ := matchArgs_cons_inv patterns
  have eq : ∀ a b,(Backend.sem ctx).eq a b = (a == b) := fun _ _ => rfl
  simp only [matchPat.eq_5,primitive,eq] at typeMatch
  split at typeMatch
  · rename_i same
    have types := beq_iff_eq.mp same
    exact CTy.int.inj (V.ty.inj types)
  · cases typeMatch
section Data
attribute [local semireducible] Isle.Aarch64.program
private theorem bitrev_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .bitrev ty x)) :
    IW ty.width ∧ info.data = .data 152 29 [.data 151 106 [],.value x] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by simpa [Compile.instE,Compile.unaryTyE,Compile.unaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  · cases ty <;> simp [eTy,Clif.Ty.width,IW] at supported ⊢
  · have expected : instData f (.unary .bitrev ty x) = .ok (.data 152 29 [.data 151 106 [],.value x]) := by
      simp only [instData,unaryOpcode,supported,ite_true]; rfl
    exact Except.ok.inj (raw.symm.trans expected)
end Data
/-- Original source opcode/type data and actual matching derive the selected
bswap rule internally. -/
theorem stock_selected_bswap_rule {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .bswap ty x))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = ScalarBit.bswapRule ty.width := by
  obtain ⟨width,data,type⟩ := bswap_data inv source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  rw [stock_bswap_opcode_inventory] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨fuel,fuelEq⟩ : ∃ fuel,selected.matchFuel = fuel+1 := ⟨selected.matchFuel-1,by omega⟩
  have matched := selected.matchedRun
  rw [fuelEq] at matched
  obtain ⟨bound,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs] at args
  rcases member with first | second | last
  · have candidate : rule_lower_2035 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen : selected.rule = rule_lower_2035 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate first
    rw [chosen] at args
    have actualWidth := type_match (target := 16) (name := "I16") rfl rfl source type args
    rw [chosen,actualWidth]
    rfl
  · have candidate : rule_lower_2038 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen : selected.rule = rule_lower_2038 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate second
    rw [chosen] at args
    have actualWidth := type_match (target := 32) (name := "I32") rfl rfl source type args
    rw [chosen,actualWidth]
    rfl
  · have candidate : rule_lower_2041 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen : selected.rule = rule_lower_2041 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate last
    rw [chosen] at args
    have actualWidth := type_match (target := 64) (name := "I64") rfl rfl source type args
    rw [chosen,actualWidth]
    rfl
/-- Original source opcode/type data and actual matching derive the selected
bitrev rule internally. -/
theorem stock_selected_bitrev_rule {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .bitrev ty x))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = ScalarBit.bitrevRule ty.width := by
  obtain ⟨width,data,type⟩ := bitrev_data inv source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  rw [stock_bitrev_opcode_inventory] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨fuel,fuelEq⟩ : ∃ fuel,selected.matchFuel = fuel+1 := ⟨selected.matchFuel-1,by omega⟩
  have matched := selected.matchedRun
  rw [fuelEq] at matched
  obtain ⟨bound,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs] at args
  rcases member with first | second | last
  · have candidate : rule_lower_1931 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen : selected.rule = rule_lower_1931 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate first
    rw [chosen] at args
    have actualWidth := type_match (target := 8) (name := "I8") rfl rfl source type args
    rw [chosen,actualWidth]
    rfl
  · have candidate : rule_lower_1937 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen : selected.rule = rule_lower_1937 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate second
    rw [chosen] at args
    have actualWidth := type_match (target := 16) (name := "I16") rfl rfl source type args
    rw [chosen,actualWidth]
    rfl
  · have candidate : rule_lower_1946 ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
    have chosen : selected.rule = rule_lower_1946 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate last
    obtain ⟨notByte,notHalf⟩ := ScalarBit.stock_bitrev_fallback_width source type data selected chosen
    simp only [ScalarBit.bitrevRule,notByte,notHalf,ite_false]
    exact chosen

open Backend.Stock.Proof.Neg in
/-- Original source transfer derives both operand getter and rule selection
internally; previous theorem variants remain available. -/
theorem stock_lower_neg_source_by_instruction {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.unary .ineg ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (u : BitVec ty.width) (d : Nat) (ρ' : Nat → CV),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧ step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .ineg u⟩ (ρ' d) ∧ cm' = cm ∧
      (∀ n,n < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ n → ρ' n = ρ n) ∧
      ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx
        fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have chosen := stock_selected_neg_rule (stock_lower_record_context run scope events).1 source clif receipt.selected
  have selectedId : step.rules.getLast? = some rule_lower_857.id := by
    rw [receipt.rules,receipt.selected.last_rule,chosen]
  exact stock_lower_neg_source_from_step run scope dominated events records block statement current source clif results
    statementResults mapped recorded emitted selectedId refines held sourceStep

open Backend.Stock.Proof.ScalarBit in
/-- Original source transfer derives both operand getter and rule selection
internally; previous theorem variants remain available. -/
theorem stock_lower_bitrev_source_by_instruction {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.unary .bitrev ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (u : BitVec ty.width) (d : Nat) (ρ' : Nat → CV),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧ step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bitrev u⟩ (ρ' d) ∧ cm' = cm ∧
      (∀ n,n < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ n → ρ' n = ρ n) ∧
      ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx
        fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have chosen := stock_selected_bitrev_rule (stock_lower_record_context run scope events).1 source clif receipt.selected
  have selectedId : step.rules.getLast? = some (bitrevRule ty.width).id := by
    rw [receipt.rules,receipt.selected.last_rule,chosen]
  exact stock_lower_bitrev_source_from_step run scope dominated events records block statement current source clif results
    statementResults mapped recorded emitted selectedId refines held sourceStep

open Backend.Stock.Proof.ScalarBit in
/-- Original source transfer derives both operand getter and rule selection
internally; previous theorem variants remain available. -/
theorem stock_lower_bswap_source_by_instruction {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.unary .bswap ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (u : BitVec ty.width) (d : Nat) (ρ' : Nat → CV),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧ step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bswap u⟩ (ρ' d) ∧ cm' = cm ∧
      (∀ n,n < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ n → ρ' n = ρ n) ∧
      ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx
        fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have chosen := stock_selected_bswap_rule (stock_lower_record_context run scope events).1 source clif receipt.selected
  have selectedId : step.rules.getLast? = some (bswapRule ty.width).id := by
    rw [receipt.rules,receipt.selected.last_rule,chosen]
  exact stock_lower_bswap_source_from_step run scope dominated events records block statement current source clif results
    statementResults mapped recorded emitted selectedId refines held sourceStep
end Backend.Stock.Proof

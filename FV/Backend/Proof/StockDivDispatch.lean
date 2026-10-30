import FV.Backend.Proof.IselCtlRuleIds
import FV.Backend.Proof.StockDivRootMatch
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
def typedRoots (op : Clif.DivOp) (w : Nat) : List Rule :=
  if op = .sdiv then
    if w = 64 then [rule_lower_1145,rule_lower_1163] else [rule_lower_1153,rule_lower_1167]
  else if w = 64 then [baseWideRule op] else [baseNarrowRule op]
private theorem type_pattern {ctx : Ctx} {r : Rule} {tp dp : Pattern}
    (args : r.args = [.term 18 209 [tp,dp]]) {i w : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    {st : LState} {env env' : Isle.Interp.Env V}
    (matched : matchArgs program (Backend.sem ctx) st r.args [.inst i] env = .ok (some env')) :
    ∃ initial final,matchPat program (Backend.sem ctx) st tp (.ty (.int w)) initial = .ok (some final) := by
  rw [args] at matched
  obtain ⟨first,head,_⟩ := matchArgs_cons_inv matched
  obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl head
  rw [Backend.Proof.sem_extract] at extracted
  have expected := ext_inst_data_value ctx st source
  rw [type,Option.getD_some] at expected
  rw [expected] at extracted
  cases extracted
  obtain ⟨middle,typeMatch,_⟩ := matchArgs_cons_inv patterns
  exact ⟨_,_,typeMatch⟩
private theorem wide_width {ctx : Ctx} {r : Rule} {dp : Pattern}
    (args : r.args = [.term 18 209 [.constPrim 14 "I64",dp]]) {i w : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    {st : LState} {env env' : Isle.Interp.Env V}
    (matched : matchArgs program (Backend.sem ctx) st r.args [.inst i] env = .ok (some env')) : w = 64 := by
  obtain ⟨initial,final,typeMatch⟩ := type_pattern args source type matched
  have prim : (Backend.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
  have eq : ∀ a b,(Backend.sem ctx).eq a b = (a == b) := fun _ _ => rfl
  simp only [matchPat.eq_5,prim,eq] at typeMatch
  split at typeMatch
  · rename_i same
    exact CTy.int.inj (V.ty.inj (beq_iff_eq.mp same))
  · cases typeMatch
private theorem narrow_width {ctx : Ctx} {r : Rule} {dp : Pattern}
    (args : r.args = [.term 18 209 [.term 14 111 [.bind 14 0 (.wildcard 14)],dp]])
    {i w : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w))
    {st : LState} {env env' : Isle.Interp.Env V}
    (matched : matchArgs program (Backend.sem ctx) st r.args [.inst i] env = .ok (some env')) : w ≤ 32 := by
  obtain ⟨initial,final,typeMatch⟩ := type_pattern args source type matched
  obtain ⟨fields,extracted,_⟩ := matchPat_extract_inv data_program.t111 term_111_kind rfl typeMatch
  rw [Backend.Proof.sem_extract,ext_fits_in_32_ty_fa] at extracted
  simp only [CTy.bits] at extracted
  by_cases small : w ≤ 32
  · exact small
  · simp only [small,ite_false] at extracted
    cases extracted
/-- Original opcode and actual type matching derive the complete typed
root alternatives, including both safe/general signed priorities. -/
theorem stock_selected_div_typed_roots {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (op : Clif.DivOp) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.div op ty x y))
    {st next : State} {out : V} {trace : List RuleId} (selected : LowerSelection ctx i st out next trace) :
    selected.rule ∈ typedRoots op ty.width := by
  obtain ⟨_,data,type⟩ := stock_div_source_data inv op source clif
  have member := stock_selected_div_roots inv op source clif selected
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨fuel,fuelEq⟩ : ∃ fuel,selected.matchFuel = fuel+1 := ⟨selected.matchFuel-1,by omega⟩
  have matched := selected.matchedRun
  rw [fuelEq] at matched
  obtain ⟨initial,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs] at args
  cases op
  · simp only [rootIds,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h0 | h1
    · have candidate : rule_lower_1116 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h0
      rw [chosen] at args
      have width := wide_width rfl source type args
      rw [chosen]
      rw [width]
      simp [typedRoots,baseWideRule]
    · have candidate : rule_lower_1119 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h1
      rw [chosen] at args
      have width := narrow_width rfl source type args
      rw [chosen]
      simp [typedRoots,baseNarrowRule,show ty.width ≠ 64 by omega]
  · simp only [rootIds,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h0 | h1 | h2 | h3
    · have candidate : rule_lower_1163 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h0
      rw [chosen] at args
      have width := wide_width rfl source type args
      rw [chosen]
      rw [width]
      simp [typedRoots,baseWideRule]
    · have candidate : rule_lower_1167 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h1
      rw [chosen] at args
      have width := narrow_width rfl source type args
      rw [chosen]
      simp [typedRoots,baseNarrowRule,show ty.width ≠ 64 by omega]
    · have candidate : rule_lower_1145 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h2
      rw [chosen] at args
      have width := wide_width rfl source type args
      rw [chosen]
      rw [width]
      simp [typedRoots,baseWideRule]
    · have candidate : rule_lower_1153 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h3
      rw [chosen] at args
      have width := narrow_width rfl source type args
      rw [chosen]
      simp [typedRoots,baseNarrowRule,show ty.width ≠ 64 by omega]
  · simp only [rootIds,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h0 | h1
    · have candidate : rule_lower_1190 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h0
      rw [chosen] at args
      have width := wide_width rfl source type args
      rw [chosen]
      rw [width]
      simp [typedRoots,baseWideRule]
    · have candidate : rule_lower_1197 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h1
      rw [chosen] at args
      have width := narrow_width rfl source type args
      rw [chosen]
      simp [typedRoots,baseNarrowRule,show ty.width ≠ 64 by omega]
  · simp only [rootIds,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h0 | h1
    · have candidate : rule_lower_1204 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h0
      rw [chosen] at args
      have width := wide_width rfl source type args
      rw [chosen]
      rw [width]
      simp [typedRoots,baseWideRule]
    · have candidate : rule_lower_1211 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h1
      rw [chosen] at args
      have width := narrow_width rfl source type args
      rw [chosen]
      simp [typedRoots,baseNarrowRule,show ty.width ≠ 64 by omega]
end Backend.Stock.Proof.ScalarDiv

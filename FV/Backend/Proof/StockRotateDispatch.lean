import FV.Backend.Proof.IselCtlRuleIds
import FV.Backend.Proof.StockRotateMatch
import FV.Backend.Proof.StockRootOpcodeMatch
namespace Backend.Stock.Proof.ScalarRotate
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
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
private theorem narrow_match_width {ctx : Ctx} {r : Rule} {i w : Nat} {info : IInfo}
    {q : Pattern} (shape : r.args = [.term 18 209 [.term 14 110 [.bind 14 0 (.wildcard 14)],q]])
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    {st : LState} {env env' : Isle.Interp.Env V}
    (matched : matchArgs program (Backend.sem ctx) st r.args [.inst i] env = .ok (some env')) : w ≤ 16 := by
  rw [shape] at matched
  obtain ⟨e1,root,_⟩ := matchArgs_cons_inv matched
  obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl root
  rw [Backend.Proof.sem_extract] at extracted
  have expected := ext_inst_data_value ctx st source
  rw [type,Option.getD_some] at expected
  rw [expected] at extracted
  cases extracted
  obtain ⟨e2,small,_⟩ := matchArgs_cons_inv patterns
  obtain ⟨fields,extracted,_⟩ := matchPat_extract_inv data_program.t110 term_110_kind rfl small
  rw [Backend.Proof.sem_extract,ext_fits_in_16] at extracted
  by_cases fits : w ≤ 16
  · exact fits
  · rw [if_neg fits] at extracted; cases extracted
private theorem left_inventory : sourceOpcodeIds 101 = [903,904,901,902,900,899] := by decide +kernel
private theorem right_inventory : sourceOpcodeIds 102 = [910,911,907,908,909,906] := by decide +kernel
/-- Original opcode/type and actual successful matching determine one of the12
scalar roots, without a caller-selected-rule certificate. -/
theorem stock_selected_rotate_rule {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (left : Bool) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.binary (rotateOp left) ty x y))
    {st next : State} {out : V} {trace : List RuleId} (selected : LowerSelection ctx i st out next trace) :
    ∃ immediate,selected.rule = rotateRule left immediate ty.width := by
  obtain ⟨width,data,type⟩ := stock_rotate_source_data inv left source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  have roots : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨fuel,fuelEq⟩ : ∃ fuel,selected.matchFuel = fuel+1 := ⟨selected.matchFuel-1,by omega⟩
  have matched := selected.matchedRun
  rw [fuelEq] at matched
  obtain ⟨bound,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs] at args
  cases left
  · simp only [rotateOpcode,Bool.false_eq_true,ite_false] at member
    rw [right_inventory] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h1 | h2 | h3 | h4 | h5 | h6
    · have candidate : rule_lower_1857 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen : selected.rule = rule_lower_1857 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h1
      rw [chosen] at args
      have actualWidth := type_match (target := 32) (name := "I32") rfl rfl source type args
      refine ⟨true,?_⟩
      rw [chosen,actualWidth]
      rfl
    · have candidate : rule_lower_1862 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen : selected.rule = rule_lower_1862 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h2
      rw [chosen] at args
      have actualWidth := type_match (target := 64) (name := "I64") rfl rfl source type args
      refine ⟨true,?_⟩
      rw [chosen,actualWidth]
      rfl
    · have candidate : rule_lower_1844 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen : selected.rule = rule_lower_1844 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h3
      rw [chosen] at args
      have actualWidth := type_match (target := 32) (name := "I32") rfl rfl source type args
      refine ⟨false,?_⟩
      rw [chosen,actualWidth]
      rfl
    · have candidate : rule_lower_1848 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen : selected.rule = rule_lower_1848 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h4
      rw [chosen] at args
      have actualWidth := type_match (target := 64) (name := "I64") rfl rfl source type args
      refine ⟨false,?_⟩
      rw [chosen,actualWidth]
      rfl
    · have candidate : rule_lower_1852 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen : selected.rule = rule_lower_1852 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h5
      rw [chosen] at args
      have small := narrow_match_width rfl source type args
      have actualWidth : ty.width = 8 ∨ ty.width = 16 := by rcases width with h | h | h | h <;> omega
      refine ⟨true,?_⟩
      simp only [rotateRule,actualWidth,ite_true,ite_false]
      exact chosen
    · have candidate : rule_lower_1840 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen : selected.rule = rule_lower_1840 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h6
      rw [chosen] at args
      have small := narrow_match_width rfl source type args
      have actualWidth : ty.width = 8 ∨ ty.width = 16 := by rcases width with h | h | h | h <;> omega
      refine ⟨false,?_⟩
      simp only [rotateRule,actualWidth,ite_true,ite_false]
      exact chosen
  · simp only [rotateOpcode,ite_true] at member
    rw [left_inventory] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h1 | h2 | h3 | h4 | h5 | h6
    · have candidate : rule_lower_1803 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen : selected.rule = rule_lower_1803 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h1
      rw [chosen] at args
      have actualWidth := type_match (target := 32) (name := "I32") rfl rfl source type args
      refine ⟨true,?_⟩
      rw [chosen,actualWidth]
      rfl
    · have candidate : rule_lower_1808 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen : selected.rule = rule_lower_1808 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h2
      rw [chosen] at args
      have actualWidth := type_match (target := 64) (name := "I64") rfl rfl source type args
      refine ⟨true,?_⟩
      rw [chosen,actualWidth]
      rfl
    · have candidate : rule_lower_1791 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen : selected.rule = rule_lower_1791 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h3
      rw [chosen] at args
      have actualWidth := type_match (target := 32) (name := "I32") rfl rfl source type args
      refine ⟨false,?_⟩
      rw [chosen,actualWidth]
      rfl
    · have candidate : rule_lower_1797 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen : selected.rule = rule_lower_1797 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h4
      rw [chosen] at args
      have actualWidth := type_match (target := 64) (name := "I64") rfl rfl source type args
      refine ⟨false,?_⟩
      rw [chosen,actualWidth]
      rfl
    · have candidate : rule_lower_1778 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen : selected.rule = rule_lower_1778 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h5
      rw [chosen] at args
      have small := narrow_match_width rfl source type args
      have actualWidth : ty.width = 8 ∨ ty.width = 16 := by rcases width with h | h | h | h <;> omega
      refine ⟨true,?_⟩
      simp only [rotateRule,actualWidth,ite_true,ite_false]
      exact chosen
    · have candidate : rule_lower_1772 ∈ program.rulesOf T.lower.id := by
        rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
      have chosen : selected.rule = rule_lower_1772 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate h6
      rw [chosen] at args
      have small := narrow_match_width rfl source type args
      have actualWidth : ty.width = 8 ∨ ty.width = 16 := by rcases width with h | h | h | h <;> omega
      refine ⟨false,?_⟩
      simp only [rotateRule,actualWidth,ite_true,ite_false]
      exact chosen
end Backend.Stock.Proof.ScalarRotate

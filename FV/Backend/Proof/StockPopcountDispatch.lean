import FV.Backend.Proof.StockSourceTypeMatch
import FV.Backend.Proof.StockPopcountScope
namespace Backend.Stock.Proof.Popcount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
attribute [local irreducible] Isle.Aarch64.program

def popcountRule (w : Nat) : Rule :=
  if w = 8 then rule_lower_2074 else if w = 16 then rule_lower_2080
  else if w = 32 then rule_lower_2086 else rule_lower_2092

/-- Original scope closure already excludes the i128 and vector roots. -/
theorem opcode_inventory : sourceOpcodeIds 111 = [937,938,939,940] := by decide +kernel

section Data
attribute [local semireducible] Isle.Aarch64.program
theorem source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .popcnt ty x)) :
    IW ty.width ∧ info.data = .data 152 29 [.data 151 111 [],.value x] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by simpa [Compile.instE,Compile.unaryTyE,Compile.unaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  · cases ty <;> simp [eTy,Clif.Ty.width,IW] at supported ⊢
  · have expected : instData f (.unary .popcnt ty x) = .ok (.data 152 29 [.data 151 111 [],.value x]) := by
      simp [instData,unaryOpcode,supported] <;> rfl
    exact Except.ok.inj (raw.symm.trans expected)
end Data

/-- Original source and successful matching determine the scalar count root.
The existing global scope closure discharges the unrelated type roots. -/
theorem selected_rule {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .popcnt ty x))
    {st next : State} {out : V} {trace : List RuleId} (selected : LowerSelection ctx i st out next trace) :
    selected.rule = popcountRule ty.width := by
  obtain ⟨width,data,type⟩ := source_data inv source clif
  have ids := stock_selected_source_opcode_ids inv source clif data selected
  rw [opcode_inventory] at ids
  have roots : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨fuel,fuelEq⟩ : ∃ fuel,selected.matchFuel = fuel+1 := ⟨selected.matchFuel-1,by omega⟩
  have matched := selected.matchedRun
  rw [fuelEq] at matched
  obtain ⟨bound,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs] at args
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ids
  rcases ids with one | two | three | four
  · have chosen : selected.rule = rule_lower_2074 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
      (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) one
    rw [chosen] at args
    have same := stock_match_source_type (wanted := .int 8) (name := "I8") rfl rfl source type args
    have typed : ty.width = 8 := CTy.int.inj same
    rw [chosen,typed]
    rfl
  · have chosen : selected.rule = rule_lower_2080 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
      (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) two
    rw [chosen] at args
    have same := stock_match_source_type (wanted := .int 16) (name := "I16") rfl rfl source type args
    have typed : ty.width = 16 := CTy.int.inj same
    rw [chosen,typed]
    rfl
  · have chosen : selected.rule = rule_lower_2086 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
      (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) three
    rw [chosen] at args
    have same := stock_match_source_type (wanted := .int 32) (name := "I32") rfl rfl source type args
    have typed : ty.width = 32 := CTy.int.inj same
    rw [chosen,typed]
    rfl
  · have chosen : selected.rule = rule_lower_2092 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
      (by rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel) four
    rw [chosen] at args
    have same := stock_match_source_type (wanted := .int 64) (name := "I64") rfl rfl source type args
    have typed : ty.width = 64 := CTy.int.inj same
    rw [chosen,typed]
    rfl
end Backend.Stock.Proof.Popcount

import FV.Backend.Proof.StockAcquireSelectedBlockPositions
import FV.Backend.Proof.IselMemAddr

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program

private theorem matchArgs_length {ctx : Ctx} {st : State} {patterns : List Pattern} {values : List V}
    {env env' : Isle.Interp.Env V}
    (run : matchArgs program (Stock.sem ctx) st patterns values env = .ok (some env')) :
    patterns.length = values.length := by
  induction patterns generalizing values env with
  | nil => cases values <;> simp only [matchArgs] at run ⊢ <;> cases run <;> rfl
  | cons pat patterns ih =>
    cases values with
    | nil => simp only [matchArgs] at run;cases run
    | cons value values =>
      obtain ⟨middle,head,tail⟩ := matchArgs_cons_inv run
      exact congrArg Nat.succ (ih tail)

private theorem decoded_shape {ctx : Ctx} {value : V} {ty tag : Nat} {fields : List V}
    (decoded : (Backend.sem ctx).unData ty value = some (tag,fields)) : value = .data ty tag fields := by
  cases value <;> try cases decoded
  rename_i actualType actualTag actualFields
  change (if actualType == ty then some (actualTag,actualFields) else none) = some (tag,fields) at decoded
  split at decoded
  · rename_i same
    have typeEq : actualType = ty := by simpa only [beq_iff_eq] using same
    subst actualType
    cases Option.some.inj decoded
    rfl
  · cases decoded

/-- Successful acquire matching derives the exact original consumer operand and opcode data. -/
theorem acquire_root_args_original_operand_data {ctx : Ctx} {st : State} {env : Isle.Interp.Env V}
    {ii originalValue : Nat}
    (args : matchArgs program (Stock.sem ctx) st rule_lower_1272.args [.inst ii]
      (Array.replicate rule_lower_1272.vars.length none) = .ok (some env))
    (held : env[3]? = some (some (.value originalValue))) :
    ∃ info,ctx.insts[ii]? = some info ∧
      info.data = .data 152 29 [.data 151 141 [],.value originalValue] := by
  obtain ⟨env1,head,tail⟩ := matchArgs_cons_inv args
  simp only [matchArgs,pure,Except.pure] at tail
  cases tail
  obtain ⟨values,extracted,fields⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl head
  change (match ctx.insts[ii]? with
    | some info => ExtResult.ok [V.ty (info.resTys.head?.getD .invalid),info.data]
    | none => ExtResult.unmodeled s!"inst {ii}") = ExtResult.ok values at extracted
  cases installed : ctx.insts[ii]? with
  | none => rw [installed] at extracted;cases extracted
  | some info =>
    rw [installed] at extracted
    cases extracted
    obtain ⟨envFit,fit,rest⟩ := matchArgs_cons_inv fields
    obtain ⟨envData,dataPat,empty⟩ := matchArgs_cons_inv rest
    simp only [matchArgs,pure,Except.pure] at empty
    cases empty
    obtain ⟨items,decoded,arguments⟩ := matchPat_enum_inv data_program.t2476 term_2476_kind dataPat
    change (Backend.sem ctx).unData 152 info.data = some (29,items) at decoded
    have arity : items.length = 2 := by
      have count := matchArgs_length arguments
      simpa only [List.length_cons,List.length_nil] using count.symm
    obtain ⟨opcode,value,itemsEq⟩ : ∃ opcode value,items = [opcode,value] :=
      ⟨items[0]'(by omega),items[1]'(by omega),List.eq_getElem_of_length_eq_two items arity⟩
    rw [itemsEq] at decoded arguments
    obtain ⟨envOpcode,opcodeRun,rest⟩ := matchArgs_cons_inv arguments
    obtain ⟨envOperand,operandRun,empty⟩ := matchArgs_cons_inv rest
    simp only [matchArgs,pure,Except.pure] at empty
    cases empty
    obtain ⟨opcodeFields,opcodeDecoded,opcodeArgs⟩ := matchPat_enum_inv data_program.t2425 term_2425_kind opcodeRun
    have opcodeEmpty : opcodeFields = [] := List.length_eq_zero_iff.mp (by
      have count := matchArgs_length opcodeArgs
      simpa only [List.length_nil] using count.symm)
    rw [opcodeEmpty] at opcodeDecoded
    change (Backend.sem ctx).unData 151 opcode = some (141,[]) at opcodeDecoded
    have opcodeEq := decoded_shape opcodeDecoded
    obtain ⟨inside,inner⟩ := matchPat_bind_inv operandRun
    have kept := stock_pattern_keeps (k := 3) (by decide) inner
    have boundValue := kept.trans (Array.getElem?_setIfInBounds_self_of_lt inside)
    have valueEq : value = .value originalValue := Option.some.inj (Option.some.inj (boundValue.symm.trans held))
    have data := decoded_shape decoded
    exact ⟨info,rfl,by simpa only [opcodeEq,valueEq] using data⟩

end Backend.Stock.Proof.Acquire810

import FV.Backend.Proof.StockAcquireSelectedSameBlock

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program

private theorem data_shape {ctx : Ctx} {value : V} {fields : List V}
    (decoded : (Backend.sem ctx).unData 152 value = some (29,fields)) : value = .data 152 29 fields := by
  cases value <;> try cases decoded
  rename_i actualType actualTag actualFields
  change (if actualType == 152 then some (actualTag,actualFields) else none) = some (29,fields) at decoded
  split at decoded
  · rename_i same
    have typeEq : actualType = 152 := by simpa only [beq_iff_eq] using same
    subst actualType
    cases Option.some.inj decoded
    rfl
  · cases decoded

/-- The actual acquire argument matcher requires an original unary data shape. -/
theorem acquire_root_args_unary_data {ctx : Ctx} {st : State} {env : Isle.Interp.Env V} {ii : Nat}
    (args : matchArgs program (Stock.sem ctx) st rule_lower_1272.args [.inst ii]
      (Array.replicate rule_lower_1272.vars.length none) = .ok (some env)) :
    ∃ info fields,ctx.insts[ii]? = some info ∧ info.data = .data 152 29 fields := by
  obtain ⟨env1,head,tail⟩ := matchArgs_cons_inv args
  obtain ⟨values,extracted,fields⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl head
  change Backend.externExtract ctx T.inst_data_value (.inst ii) st.base = .ok values at extracted
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
    obtain ⟨items,decoded,arguments⟩ := matchPat_enum_inv data_program.t2476 term_2476_kind dataPat
    change (Backend.sem ctx).unData 152 info.data = some (29,items) at decoded
    exact ⟨info,items,rfl,data_shape decoded⟩

/-- Original return and explicit-trap data cannot match an acquire unary consumer. -/
theorem ret_trap_data_not_unary {term : Clif.Terminator} {data : V} {fields : List V}
    (kind : retOrTrap term = true) (prepared : Backend.termData term = .ok data) :
    data ≠ .data 152 29 fields := by
  intro shape
  cases term <;> simp only [retOrTrap] at kind <;> try cases kind
  all_goals
    simp only [Backend.termData,pure,Except.pure] at prepared
    cases prepared
    have names := (mkVariant_eq_data shape).1
    rw [variantNames_Unary] at names
    simp at names

end Backend.Stock.Proof.Acquire810

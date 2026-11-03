import FV.Backend.Proof.StockAcquireDeferredLoadPattern

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program

private def extensionPattern (signed : Bool) : Pattern :=
  .term 18 209 [.term 14 113 [.wildcard 14],.term 152 2476
    [.term 151 (if signed then 2426 else 2425) [],.bind 15 4 (.term 15 1 [deferredLoadPattern])]]

private theorem extract_data_fields {ctx : Ctx} {state : State} {value : V} {fields : List V}
    (run : (Stock.sem ctx).extract T.inst_data_value value state = .ok fields) :
    ∃ ty data,fields = [.ty ty,data] := by
  cases value with
  | inst slot =>
    change (match ctx.insts[slot]? with
      | some info => ExtResult.ok [.ty (info.resTys.head?.getD .invalid),info.data]
      | none => ExtResult.unmodeled s!"inst {slot}") = ExtResult.ok fields at run
    cases found : ctx.insts[slot]? with
    | none => rw [found] at run; cases run
    | some info => rw [found] at run; cases run; exact ⟨_,_,rfl⟩
  | _ => cases run

private theorem extension_pattern_source {ctx : Ctx} {state : State} {value : V}
    {env bound : Isle.Interp.Env V} (signed : Bool)
    (matched : matchPat program (Stock.sem ctx) state (extensionPattern signed) value env = .ok (some bound)) :
    ∃ (original producer : Nat) (info : IInfo) (fields : List V),
      bound[4]? = some (some (.value original)) ∧ ctx.defInst? original = some producer ∧
      ctx.insts[producer]? = some info ∧ info.data = .data 152 16 fields := by
  obtain ⟨values,extracted,args⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl matched
  obtain ⟨ty,data,rfl⟩ := extract_data_fields extracted
  obtain ⟨middle,typeMatch,args⟩ := matchArgs_cons_inv args
  obtain ⟨next,unary,ending⟩ := matchArgs_cons_inv args
  simp only [matchArgs,pure,Except.pure] at ending
  cases ending
  obtain ⟨fields,decoded,args⟩ := matchPat_enum_inv data_program.t2476 term_2476_kind unary
  cases fields with
  | nil => cases args
  | cons opcode rest =>
    obtain ⟨first,opcodeMatch,args⟩ := matchArgs_cons_inv args
    cases rest with
    | nil => cases args
    | cons source rest =>
      obtain ⟨last,sourceMatch,ending⟩ := matchArgs_cons_inv args
      cases rest with
      | cons extra rest => cases ending
      | nil =>
        simp only [matchArgs,pure,Except.pure] at ending
        cases ending
        obtain ⟨original,producer,info,fields,shape,binding,defined,found,raw⟩ := deferred_load_bound_source sourceMatch
        exact ⟨original,producer,info,fields,binding,defined,found,raw⟩

/-- Both extension-load root patterns bind their actual original ordinary-load definition. -/
theorem deferred_load_root_args {ctx : Ctx} {state : State} {args : List V}
    {env bound : Isle.Interp.Env V} (signed : Bool)
    (matched : matchArgs program (Stock.sem ctx) state
      (if signed then rule_lower_1359 else rule_lower_1300).args args env = .ok (some bound)) :
    ∃ (original producer : Nat) (info : IInfo) (fields : List V),
      bound[4]? = some (some (.value original)) ∧ ctx.defInst? original = some producer ∧
      ctx.insts[producer]? = some info ∧ info.data = .data 152 16 fields := by
  have shape : (if signed then rule_lower_1359 else rule_lower_1300).args = [extensionPattern signed] := by
    cases signed <;> rfl
  rw [shape] at matched
  cases args with
  | nil => cases matched
  | cons value rest =>
    obtain ⟨middle,head,ending⟩ := matchArgs_cons_inv matched
    cases rest with
    | cons extra rest => cases ending
    | nil =>
      simp only [matchArgs,pure,Except.pure] at ending
      cases ending
      exact extension_pattern_source signed head

end Backend.Stock.Proof.Acquire810

import FV.Backend.Proof.IselCovFns

/-!
# Form coverage over float-capable contexts: the transfer functions of the extern helpers

`aextT`: `aext` with the value types widened to `mCTys` (`i8..i64`, `f32`, `f64`) — `value_type`
and `inst_data_value` describe a typed context's values, whose types `CtxInvT.valTyM` admits.
`actorC`: `actor` with the register-producing constructors class-aware — `put_in_reg`,
`put_extended_in_reg`, `load_constant_full` give `.reg 3` (an int or float vreg: `put_in_reg`
returns the value's own vreg, of its class, `Isel.lean`), `put_in_regs`/`put_in_regs_vec` give
`.flat 3 true`. `apre`/`aOracle` are unchanged.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Aarch64

/-- **Extern extractors** over float-capable contexts: `aext` with `eCTys` widened to `mCTys`. -/
def aextT (id : TermId) (a : AW) : List AW :=
  match tyPred id with
  | some q => match tysOf a with
    | some ts => [.ty (ts.filter q)]
    | none => [.top]
  | none =>
  if id == TId.value_type then [.ty mCTys]
  else if id == TId.inst_data_value then
    [.ty (.invalid :: mCTys), match a with
      | .xv .inst => .xv .data
      | _ => .c0]
  else if id == TId.def_inst then [.xv .inst]
  else if id == TId.maybe_uextend || id == TId.is_second_result || id == TId.first_result then
    [.xv .value]
  else if id == TId.value_array_2 then [.xv .value, .xv .value]
  else if id == TId.value_array_3 then [.xv .value, .xv .value, .xv .value]
  else if id == TId.value_slice_unwrap then [.xv .value, .c0]
  else if id == TId.multi_lane then
    match tysOf a with
    | some ts => if ts.any (·.laneCount > 1) then [.c0, .c0] else [.bot, .bot]
    | none => [.c0, .c0]
  else if id == TId.dynamic_lane then [.bot, .bot]
  else if id == TId.tls_model then [.data tyTlsModel VIdx.TlsModel.ElfGd []]
  else [.c0, .c0, .c0, .c0]

/-- **Extern constructors** over float-capable contexts: `actor` with the register-producing
constructors class-aware. -/
def actorC (id : TermId) (as : List AW) : AW :=
  match tyPred id, as with
  | some q, [a] => match tysOf a with
    | some ts => .ty (ts.filter q)
    | none => .c0
  | _, _ =>
  if id == TId.put_in_reg || id == TId.put_extended_in_reg || id == TId.load_constant_full then
    .reg 3
  else if id == TId.put_in_regs || id == TId.put_in_regs_vec then
    .flat 3 true
  else actorRest id as

end Backend.Proof.Cov

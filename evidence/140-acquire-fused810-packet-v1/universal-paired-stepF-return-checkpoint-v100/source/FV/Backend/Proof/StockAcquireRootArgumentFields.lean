import FV.Backend.Proof.StockAcquireDeferredPairValue

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program

/-- Actual original data and types determine the acquire argument environment. -/
theorem acquire_root_argument_fields {ctx : Ctx} {st : State} {root value producer pointer : Nat}
    {rootInfo info : IInfo} {targetTy sourceTy : CTy} {flags : Clif.MemFlags}
    (little : flags.endianness ≠ some .big)
    (rootInstalled : ctx.insts[root]? = some rootInfo)
    (rootData : rootInfo.data = .data 152 29 [.data 151 141 [],.value value])
    (rootType : rootInfo.resTys.head?.getD .invalid = targetTy) (fits : targetTy.bits ≤ 64)
    (valueType : ctx.valueType? value = some sourceTy) (defined : ctx.defInst? value = some producer)
    (installed : ctx.insts[producer]? = some info)
    (atomic : info.data = .data 152 17 [.data 151 158 [],.value pointer,.op (.memFlags flags)])
    {env : Isle.Interp.Env V}
    (matched : matchArgs program (Stock.sem ctx) st rule_lower_1272.args [V.inst root]
      (Array.replicate rule_lower_1272.vars.length none) = .ok (some env)) :
    env[1]? = some (some (V.ty sourceTy)) ∧ env[2]? = some (some (.op (.memFlags flags))) := by
  have rootExtract (state : State) : (Stock.sem ctx).extract T.inst_data_value (V.inst root) state =
      .ok [V.ty targetTy,rootInfo.data] := by
    change (match ctx.insts[root]? with
      | some found => ExtResult.ok [V.ty (found.resTys.head?.getD .invalid),found.data]
      | none => ExtResult.unmodeled s!"inst {root}") = _
    simp only [rootInstalled,rootType]
  have sourceExtract (state : State) : (Stock.sem ctx).extract T.inst_data_value (V.inst producer) state =
      .ok [V.ty (info.resTys.head?.getD .invalid),info.data] := by
    change (match ctx.insts[producer]? with
      | some found => ExtResult.ok [V.ty (found.resTys.head?.getD .invalid),found.data]
      | none => ExtResult.unmodeled s!"inst {producer}") = _
    rw [installed]
  have typeExtract (state : State) : (Stock.sem ctx).extract T.value_type (.value value) state = .ok [V.ty sourceTy] := by
    change (match ctx.valueType? value with
      | some ty => ExtResult.ok [V.ty ty]
      | none => ExtResult.unmodeled s!"value_type of unknown v{value}") = _
    rw [valueType]
  have defExtract (state : State) : (Stock.sem ctx).extract T.def_inst (.value value) state = .ok [V.inst producer] := by
    change (match ctx.defInst? value with | some i => ExtResult.ok [V.inst i] | none => ExtResult.fail) = _
    rw [defined]
  have fitExtract (state : State) : (Stock.sem ctx).extract T.fits_in_64 (V.ty targetTy) state = .ok [V.ty targetTy] := by
    change (if decide (targetTy.bits ≤ 64) then ExtResult.ok [V.ty targetTy] else ExtResult.fail) = _
    simp only [fits,decide_true,ite_true]
  have endianExtract (state : State) : (Stock.sem ctx).extract T.little_or_native_endian (.op (.memFlags flags)) state =
      .ok [.op (.memFlags flags)] := by
    change (if flags.endianness == some .big then ExtResult.fail else ExtResult.ok [V.op (.memFlags flags)]) = _
    have noBig : (flags.endianness == some .big) = false := by simpa only [beq_eq_false_iff_ne] using little
    rw [noBig]
    rfl
  have unData (ty : Nat) (value : V) : (Stock.sem ctx).unData ty value = (Backend.sem ctx).unData ty value := rfl
  have forward : matchArgs program (Stock.sem ctx) st rule_lower_1272.args [V.inst root]
      (Array.replicate rule_lower_1272.vars.length none) =
      .ok (some #[some (V.ty targetTy),some (V.ty sourceTy),some (.op (.memFlags flags)),some (.value value),none]) := by
    isel_eval [*,rule_lower_1272,rootExtract,sourceExtract,typeExtract,defExtract,fitExtract,endianExtract,unData,Backend.sem,
      data_program.t209,data_program.t113,data_program.t2476,data_program.t2425,data_program.t2,data_program.t1,
      data_program.t2464,data_program.t2442,data_program.t103,
      term_209_kind,term_113_kind,term_2476_kind,term_2425_kind,term_2_kind,term_1_kind,
      term_2464_kind,term_2442_kind,term_103_kind]
    rfl
  have same := Option.some.inj (Except.ok.inj (matched.symm.trans forward))
  rw [same]
  exact ⟨rfl,rfl⟩

end Backend.Stock.Proof.Acquire810

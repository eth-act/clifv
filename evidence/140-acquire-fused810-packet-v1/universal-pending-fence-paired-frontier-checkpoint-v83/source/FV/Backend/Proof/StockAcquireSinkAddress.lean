import FV.Backend.Proof.StockAcquireSinkPending

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program

/-- Actual atomic source data fixes the helper's address binding. -/
theorem sink_atomic_match_address {ctx : Ctx} {st matched : State}
    {before after : Array RuleId} {bound : Isle.Interp.Env V} {ii pointer n : Nat}
    {info : IInfo} {flags : Clif.MemFlags}
    (installed : ctx.insts[ii]? = some info)
    (atomic : info.data = .data 152 17 [.data 151 158 [],.value pointer,.op (.memFlags flags)])
    (run : (matchRule program (Stock.sem ctx) {} (n+2) rule_inst_3905 [.inst ii]).run
      (st,before) = .ok (some bound,matched,after)) :
    bound[0]? = some (some (.value pointer)) := by
  have extract (state : State) : (Stock.sem ctx).extract T.inst_data_value (.inst ii) state =
      .ok [.ty (info.resTys.head?.getD .invalid),info.data] := by
    change (match ctx.insts[ii]? with
      | some found => ExtResult.ok [V.ty (found.resTys.head?.getD .invalid),found.data]
      | none => ExtResult.unmodeled s!"inst {ii}") = _
    rw [installed]
  have unData (ty : Nat) (value : V) : (Stock.sem ctx).unData ty value =
      (Backend.sem ctx).unData ty value := rfl
  have forward : (matchRule program (Stock.sem ctx) {} (n+2) rule_inst_3905 [.inst ii]).run
      (st,before) = .ok (some #[some (.value pointer),some (.inst ii),none],st,before) := by
    isel_eval [*,rule_inst_3905,extract,unData,Backend.sem,
      data_program.t209,data_program.t2464,data_program.t2442,
      term_209_kind,term_2464_kind,term_2442_kind]
    rfl
  have equal := Except.ok.inj (run.symm.trans forward)
  have envEq := Option.some.inj (congrArg Prod.fst equal)
  rw [envEq]
  rfl

end Backend.Stock.Proof.Acquire810

import FV.Backend.Proof.StockCallStoreSource

namespace Backend.Stock.Proof.CallStoreResult
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A call trap comes from its actual callee, not from argument reads or signature checks. -/
theorem source_callee_trap {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame}
    {cm : Clif.Mem} {fn : Clif.FnRef} {args : List Nat} {code : Clif.TrapCode}
    (trapped : instOutcome env cp fr cm (.call fn args) = .trap code) :
    ∃ ext values g,fr.func.extern? fn = some ext ∧ fr.getMany args = .ok values ∧
      values.map (·.ty) = Clif.AbiParam.tys ext.sig.params ∧
      cp.func? ext.name = none ∧ env.extern ext.name = some g ∧ g values cm = .trapped code := by
  simp only [instOutcome] at trapped
  cases found : fr.func.extern? fn with
  | none => simp [found,Clif.Res.ofOption,bind,Clif.Res.bind] at trapped
  | some ext =>
    cases read : fr.getMany args with
    | trap c => exact False.elim (getMany_ne_trap read)
    | stuck message => simp [found,read,Clif.Res.ofOption,bind,Clif.Res.bind] at trapped
    | ok values =>
      by_cases types : values.map (·.ty) = Clif.AbiParam.tys ext.sig.params
      · simp only [found,read,Clif.Res.ofOption,bind,Clif.Res.bind,Clif.checkTys,types,
          beq_self_eq_true,Clif.Res.check_true,pure] at trapped
        cases internal : cp.func? ext.name with
        | some f => rw [internal] at trapped; cases trapped
        | none =>
          rw [internal] at trapped
          cases callee : env.extern ext.name with
          | none => rw [callee] at trapped; cases trapped
          | some g =>
            rw [callee] at trapped
            cases returned : g values cm with
            | returned outputs after =>
              rw [returned] at trapped
              split at trapped <;> cases trapped
            | trapped actual =>
              rw [returned] at trapped
              cases trapped
              exact ⟨ext,values,g,rfl,rfl,types,internal,callee,returned⟩
            | stuck message => rw [returned] at trapped; cases trapped
            | outOfFuel => rw [returned] at trapped; cases trapped
      · simp only [found,read,Clif.Res.ofOption,bind,Clif.Res.bind,Clif.checkTys] at trapped
        rw [show (values.map (·.ty) == Clif.AbiParam.tys ext.sig.params) = false from by simpa using types,
          Clif.Res.check_false] at trapped
        cases trapped

end Backend.Stock.Proof.CallStoreResult

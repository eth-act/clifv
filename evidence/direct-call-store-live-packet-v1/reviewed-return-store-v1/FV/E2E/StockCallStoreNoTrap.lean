import FV.Backend.Proof.StockCallStoreSource
import FV.E2E.Statement

namespace Backend.Stock.CallStore
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false

/-- Preserve the old explicit-trap condition without using it as source admission. -/
theorem no_trap_under_original_condition {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame}
    {cm : Clif.Mem} {source pointer : Nat} {flags : Clif.MemFlags}
    {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc} {result : Clif.AbiParam}
    (body : fr.body = [⟨[source],.call fn args⟩,⟨[],.store .store .i64 flags source pointer 8⟩])
    (term : fr.term = .ret [source]) (little : flags.endianness ≠ some .big)
    (lookup : fr.func.extern? fn = some ext) (external : cp.func? ext.name = none)
    (returns : ext.sig.returns = [result])
    (explicit : TrapsExplicit env cp ⟨fr,[],cm⟩) (fuel : Nat) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel ⟨fr,[],cm⟩ ≠ .trapped code := by
  intro trapped
  cases fuel with
  | zero => cases trapped
  | succ fuel =>
    have step : Clif.step env cp ⟨fr,[],cm⟩ =
        Clif.StepResult.ofRes (instOutcome env cp fr cm (.call fn args))
          (fun pair => Clif.continueWith ⟨fr,[],cm⟩ [⟨[],.store .store .i64 flags source pointer 8⟩]
            [source] pair.1 pair.2) := by
      simp only [Clif.step,body]
      apply stepCall_eq
      intro e found
      have same : e = ext := Option.some.inj (found.symm.trans lookup)
      subst e
      exact external
    rcases CallStoreResult.source_call_fault_or_continues body lookup external returns trapped with failed |
        ⟨after,value,called,typed,remaining⟩
    · have halted : Clif.step env cp ⟨fr,[],cm⟩ = .trapped code := by rw [step,failed]; rfl
      have impossible := explicit.stmt ⟨fr,[],cm⟩ code ⟨[source],.call fn args⟩
        [⟨[],.store .store .i64 flags source pointer 8⟩] (.refl _) halted body
      cases impossible
    · let next : Clif.State :=
        ⟨{fr with regs := fr.regs.set source value,body := [⟨[],.store .store .i64 flags source pointer 8⟩]},[],after⟩
      have advanced : Clif.step env cp ⟨fr,[],cm⟩ = .next next := by
        rw [step,called]
        simp only [Clif.StepResult.ofRes,Clif.continueWith,Clif.Regs.setMany,next]
      have failed := CallStoreResult.source_store_faults
        (fr := {fr with regs := fr.regs.set source value,body := [⟨[],.store .store .i64 flags source pointer 8⟩]})
        rfl term little remaining
      have halted : Clif.step env cp next = .trapped code := by
        rw [Clif.step_inst env cp next ⟨[],.store .store .i64 flags source pointer 8⟩ [] rfl
          (by intro fn args impossible; cases impossible)
          (by intro sig callee args impossible; cases impossible)]
        change Clif.StepResult.ofRes (Clif.evalInst _ _ _) _ = _
        rw [failed]
        rfl
      have reached : Reach env cp ⟨fr,[],cm⟩ next := .step advanced (.refl _)
      have impossible := explicit.stmt next code ⟨[],.store .store .i64 flags source pointer 8⟩ []
        reached halted rfl
      cases impossible

end Backend.Stock.CallStore

import FV.Backend.Proof.StockAcquireEntryNormal

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- A returned source run supplies the original successful read and exact widened byte. -/
theorem source_returned_read (env : Clif.Env) (program : Clif.Program)
    (pointer : BitVec 64) (memory : Clif.Mem) (fuel : Nat) {values : List Clif.Val} {final : Clif.Mem}
    (returned : Clif.runLoop env program fuel ⟨entry pointer,[],memory⟩ = .returned values final) :
    ∃ raw : BitVec 8,memory.load {} (Clif.effAddr ⟨.i64,pointer⟩ 0) 1 8 = .ok raw ∧
      values = [⟨.i64,raw.setWidth 64⟩] ∧ final = (memory.free []).leave := by
  cases fuel with
  | zero => cases returned
  | succ fuel =>
    cases fuel with
    | zero =>
      cases loaded : memory.load {} (Clif.effAddr ⟨.i64,pointer⟩ 0) 1 8 <;>
        simp [Clif.runLoop,Clif.step,Clif.evalInst,Clif.StepResult.ofRes,Clif.continueWith,
          Clif.Frame.get,Clif.Regs.setMany,Clif.Regs.set,Clif.Res.ofOption,Clif.Res.check,
          bind,Clif.Res.bind,Nat.mod_one,Clif.Ty.width,Clif.Ty.bytes,entry,function,loaded] at returned
    | succ fuel =>
      cases fuel with
      | zero =>
        cases loaded : memory.load {} (Clif.effAddr ⟨.i64,pointer⟩ 0) 1 8 <;>
          simp [Clif.runLoop,Clif.step,Clif.evalInst,Clif.StepResult.ofRes,Clif.continueWith,
            Clif.Frame.get,Clif.Regs.setMany,Clif.Regs.set,Clif.Res.ofOption,Clif.Res.check,
            bind,Clif.Res.bind,Nat.mod_one,Clif.Sem.uextend,Clif.Ty.width,Clif.Ty.bytes,entry,function,loaded] at returned
      | succ fuel =>
        rw [show fuel+1+1+1 = fuel+3 by omega,source_more_steps] at returned
        cases loaded : memory.load {} (Clif.effAddr ⟨.i64,pointer⟩ 0) 1 8 with
        | ok raw =>
          simp only [loaded,Clif.Outcome.returned.injEq] at returned
          exact ⟨raw,loaded,returned.1.symm,returned.2.symm⟩
        | trap code => simp only [loaded] at returned; cases returned
        | stuck message => simp only [loaded] at returned; cases returned

/-- The original entry contract derives the source read internally for every returned run. -/
theorem entry_returned_read {args : List Clif.Val} {state : Clif.State}
    (entered : ClifEntry function args state) (env : Clif.Env) (program : Clif.Program)
    (fuel : Nat) {values : List Clif.Val} {final : Clif.Mem}
    (returned : Clif.runLoop env program fuel state = .returned values final) :
    ∃ (pointer : BitVec 64) (raw : BitVec 8),args = [⟨.i64,pointer⟩] ∧
      state.mem.load {} (Clif.effAddr ⟨.i64,pointer⟩ 0) 1 8 = .ok raw ∧
      values = [⟨.i64,raw.setWidth 64⟩] ∧ final = (state.mem.free []).leave := by
  obtain ⟨pointer,arguments,frame,callers⟩ := original_entry_normal_form entered
  have same : (⟨entry pointer,[],state.mem⟩ : Clif.State) = state := by
    cases state
    simp_all
  obtain ⟨raw,read,values,memory⟩ := source_returned_read env program pointer state.mem fuel
    (by rwa [same])
  exact ⟨pointer,raw,arguments,read,values,memory⟩

end Backend.Stock.Proof.Acquire810

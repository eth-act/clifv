import FV.E2E.StockDivFixtures
import Lean
namespace E2E.StockDivNIWitness
open Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

/-- Complete executable source outcome for every original input value and
slot address, including coded traps rather than a no-trap side condition. -/
theorem source_runs (config : Configuration) (op : Clif.DivOp)
    (input : Nat → BitVec (valueType config).width) (slot : Nat) :
    Clif.runLoop Clif.Env.empty {funcs := []} 2
      ⟨frame config op input slot,[],Clif.Mem.empty⟩ =
      match Clif.Sem.div op (input 1) (input 8) with
      | .error code => .trapped code
      | .ok q => .returned [⟨valueType config,q⟩] Clif.Mem.empty := by
  let s : Clif.State := ⟨frame config op input slot,[],Clif.Mem.empty⟩
  have step : Clif.step Clif.Env.empty {funcs := []} s =
      Clif.StepResult.ofRes (Clif.evalInst s.frame s.mem (.div op (valueType config) 1 8))
        (fun (vs,cm) => Clif.continueWith s [] [100] vs cm) := by
    cases config <;> rfl
  have evaluated : Clif.evalInst s.frame s.mem (.div op (valueType config) 1 8) =
      match Clif.Sem.div op (input 1) (input 8) with
      | .error code => .trap code
      | .ok q => .ok ([⟨valueType config,q⟩],Clif.Mem.empty) := by
    cases config
    all_goals
      change (Clif.Res.ofExcept (Clif.Sem.div op (input 1) (input 8)) >>= fun q =>
        Clif.Res.ok ([Clif.Val.mk _ q],Clif.Mem.empty)) = _
      cases calculation : Clif.Sem.div op (input 1) (input 8) <;> rfl
  change Clif.runLoop Clif.Env.empty {funcs := []} (1+1) s = _
  rw [Clif.runLoop_succ,step,evaluated]
  cases division : Clif.Sem.div op (input 1) (input 8)
  all_goals cases config <;> rfl

/-- Zero is an accepted original input and reaches its actual coded trap. -/
theorem zero_traps (config : Configuration) (op : Clif.DivOp) (slot : Nat) :
    Clif.runLoop Clif.Env.empty {funcs := []} 2
      ⟨frame config op (fun _ => 0) slot,[],Clif.Mem.empty⟩ = .trapped .intDivz := by
  rw [source_runs]
  cases config <;> cases op <;> rfl

/-- Signed MIN / -1 remains a real overflow trap, with no excluded input. -/
theorem signed_minimum_overflow (config : Configuration) (slot : Nat) :
    Clif.runLoop Clif.Env.empty {funcs := []} 2
      ⟨frame config .sdiv (fun i => if i = 1 then BitVec.intMin _ else -1) slot,
        [],Clif.Mem.empty⟩ = .trapped .intOvf := by
  rw [source_runs]
  cases config <;> rfl

/-- The same MIN / -1 inputs return zero for signed remainder. -/
theorem signed_minimum_remainder (config : Configuration) (slot : Nat) :
    Clif.runLoop Clif.Env.empty {funcs := []} 2
      ⟨frame config .srem (fun i => if i = 1 then BitVec.intMin _ else -1) slot,
        [],Clif.Mem.empty⟩ = .returned [⟨valueType config,0⟩] Clif.Mem.empty := by
  rw [source_runs]
  cases config <;> rfl

end E2E.StockDivNIWitness

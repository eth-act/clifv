namespace E2E.StockMixedDivNIWitness
open Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Every previously tested scalar computation contributes to the dividend;
the divisor remains the original ninth stack argument. -/
def function (config : Configuration) (op : Clif.DivOp) : Clif.Function :=
  let old := StockHighMulNIWitness.function config
  let name := "stock_mixed_div_" ++ (match op with | .sdiv => "sdiv" | .udiv => "udiv" | .srem => "srem" | .urem => "urem")
  {old with
    name := name
    blocks := old.blocks.map fun b =>
      {b with body := b.body ++ [⟨[5000],.div op (valueType config) 4008 8⟩],term := .ret [5000]}}

abbrev arguments := StockDivNIWitness.arguments

def frame (config : Configuration) (op : Clif.DivOp)
    (input : Nat → BitVec (valueType config).width) (slot : Nat) : Clif.Frame := {
  func := function config op
  regs := (Clif.Regs.empty.setMany (List.range 9) (arguments config input)).getD Clif.Regs.empty
  slots := [(7,slot)]
  body := (function config op).blocks[0]!.body
  term := .ret [5000] }

theorem source_entry (config : Configuration) (op : Clif.DivOp)
    (input : Nat → BitVec (valueType config).width) (slot : Nat) :
    E2E.ClifEntry (function config op) (arguments config input)
      ⟨frame config op input slot,[],Clif.Mem.empty⟩ := by
  cases config <;> exact ⟨rfl,rfl,rfl,⟨_,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩

private def advance : Nat → Clif.State → Clif.State
  | 0,s => s
  | n+1,s => advance n (match Clif.step Clif.Env.empty {funcs := []} s with
      | .next t => t
      | _ => s)

private def beforeDiv (config : Configuration) (op : Clif.DivOp)
    (input : Nat → BitVec (valueType config).width) (slot : Nat) : Clif.State :=
  advance (StockHighMulNIWitness.function config).blocks[0]!.body.length
    ⟨frame config op input slot,[],Clif.Mem.empty⟩

/-- All original inputs and slots, with an actual trap or actual returned
quotient/remainder after the live scalar prefix. -/
theorem source_runs (config : Configuration) (op : Clif.DivOp)
    (input : Nat → BitVec (valueType config).width) (slot : Nat) :
    Clif.runLoop Clif.Env.empty {funcs := []}
      ((StockHighMulNIWitness.function config).blocks[0]!.body.length + 2)
      ⟨frame config op input slot,[],Clif.Mem.empty⟩ =
      match Clif.Sem.div op (StockHighMulNIWitness.resultValue config input) (input 8) with
      | .error code => .trapped code
      | .ok q => .returned [⟨valueType config,q⟩] Clif.Mem.empty := by
  have prefixRun : Clif.runLoop Clif.Env.empty {funcs := []}
      ((StockHighMulNIWitness.function config).blocks[0]!.body.length + 2)
      ⟨frame config op input slot,[],Clif.Mem.empty⟩ =
      Clif.runLoop Clif.Env.empty {funcs := []} 2 (beforeDiv config op input slot) := by
    cases config <;> rfl
  rw [prefixRun]
  let s := beforeDiv config op input slot
  have step : Clif.step Clif.Env.empty {funcs := []} s =
      Clif.StepResult.ofRes (Clif.evalInst s.frame s.mem (.div op (valueType config) 4008 8))
        (fun (vs,cm) => Clif.continueWith s [] [5000] vs cm) := by
    cases config <;> rfl
  have evaluated : Clif.evalInst s.frame s.mem (.div op (valueType config) 4008 8) =
      match Clif.Sem.div op (StockHighMulNIWitness.resultValue config input) (input 8) with
      | .error code => .trap code
      | .ok q => .ok ([⟨valueType config,q⟩],Clif.Mem.empty) := by
    cases config
    all_goals
      change (Clif.Res.ofExcept (Clif.Sem.div op _ (input 8)) >>= fun q =>
        Clif.Res.ok ([Clif.Val.mk _ q],Clif.Mem.empty)) = _
      first
        | cases h : Clif.Sem.div op (StockHighMulNIWitness.resultValue .systemVI64 input) (input 8) <;> rfl
        | cases h : Clif.Sem.div op (StockHighMulNIWitness.resultValue .systemVI32 input) (input 8) <;> rfl
  change Clif.runLoop Clif.Env.empty {funcs := []} (1+1) s = _
  rw [Clif.runLoop_succ,step,evaluated]
  cases calculation : Clif.Sem.div op (StockHighMulNIWitness.resultValue config input) (input 8)
  all_goals cases config <;> rfl
end E2E.StockMixedDivNIWitness
#print axioms E2E.StockMixedDivNIWitness.source_entry
#print axioms E2E.StockMixedDivNIWitness.source_runs

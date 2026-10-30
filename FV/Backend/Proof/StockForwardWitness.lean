import FV.Backend.Proof.MemRefines
import FV.Backend.Proof.StockForwardCheck
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem

namespace Backend.Stock.Proof.ForwardWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

/-- Four source blocks exceed the previous bounded production class. Empty
jump arguments carry an inherited scalar result across a separate middle block. -/
def function (trapping : Bool) : Clif.Function := {
  name := if trapping then "stock_forward_divide" else "stock_forward_rotate"
  sig := {params := [{ty := .i64},{ty := .i64}],returns := [{ty := .i64}]}
  blocks := [
    {id := 0,params := [(0,.i64),(1,.i64)],body := [⟨[],.nop⟩],term := .jump ⟨10,[]⟩},
    {id := 10,params := [],body := [⟨[],.nop⟩,⟨[2],if trapping then .div .udiv .i64 0 1 else .binary .rotl .i64 0 1⟩],term := .jump ⟨20,[]⟩},
    {id := 20,params := [],body := [⟨[],.nop⟩],term := .jump ⟨30,[]⟩},
    {id := 30,params := [],body := [⟨[],.nop⟩],term := .ret [2]}] }

-- witness: native_decide (fixed original-input source/class/scope/dominance/ABI checks only)
private theorem input_checks (trapping : Bool) : Stock.ForwardCfg.sourceOk (function trapping) = true := by
  cases trapping <;> native_decide
private theorem compiled (trapping : Bool) : (Stock.lower (function trapping)).isOk = true := by
  cases trapping <;> decide +kernel

/-- Actual kernel compilation and the executable source/artifact checks inhabit
the universal contract beyond three blocks. No emitted property is native. -/
theorem checked_driver_witness (trapping : Bool) : ∃ result,
    Stock.lower (function trapping) = .ok result ∧ (function trapping).blocks.length = 4 ∧
    Stock.ForwardCfg.eligible (function trapping) = true ∧ Stock.Scalar.Domain (function trapping) ∧
    Stock.ForwardCfg.check (function trapping) result.code = true := by
  have success := compiled trapping
  cases run : Stock.lower (function trapping) with
  | error message => rw [run] at success; cases success
  | ok result =>
    have domain := Stock.ForwardCfg.sourceOk_sound (input_checks trapping)
    have eligible : Stock.ForwardCfg.eligible (function trapping) = true := by cases trapping <;> decide +kernel
    exact ⟨result,rfl,rfl,eligible,domain,by simp [Stock.ForwardCfg.check,input_checks,run]⟩

private def initial (trapping : Bool) : Clif.Frame := {
  func := function trapping
  regs := (Clif.Regs.empty.set 0 ⟨.i64,7⟩).set 1 ⟨.i64,if trapping then 0 else 1⟩
  slots := []
  body := (function trapping).blocks[0]!.body
  term := (function trapping).blocks[0]!.term }

/-- ABI entry returns rotate(7,1)=14 through three real jumps, including direct
inheritance across a block that neither defines nor forwards the result. -/
theorem executable_four_block_return_witness (X : ExtSem) :
    ∃ result ρ0,Stock.lower (function false) = .ok result ∧ Stock.Scalar.Domain (function false) ∧
      Clif.enterFunc (function false) [⟨.i64,7⟩,⟨.i64,1⟩] Clif.Mem.empty = .ok (initial false,Clif.Mem.empty) ∧
      RunOkABI (function false) result.code (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True)
        (initial false).slots ⟨0,0,ρ0,Arm.write_base_gpr 1#5 1 (Arm.write_base_gpr 0#5 7 Arm.ArmState.default)⟩
        (.returned [⟨.i64,14⟩] Clif.Mem.empty) := by
  obtain ⟨result,run,blocks,eligible,domain,checked⟩ := checked_driver_witness false
  have entered : Clif.enterFunc (function false) [⟨.i64,7⟩,⟨.i64,1⟩] Clif.Mem.empty = .ok (initial false,Clif.Mem.empty) := rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 9 ⟨initial false,[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,14⟩] Clif.Mem.empty := rfl
  let initialWorld := Arm.write_base_gpr 1#5 1 (Arm.write_base_gpr 0#5 7 Arm.ArmState.default)
  have arguments : ArgsAtEntry (fun _ => False) (function false).sig [⟨.i64,7⟩,⟨.i64,1⟩] initialWorld := by
    intro loc value member
    change (loc,value) ∈ [(.reg (.x 0),⟨.i64,7⟩),(.reg (.x 1),⟨.i64,1⟩)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same <;> cases same
    all_goals
      simp only [VHolds,regVal,initialWorld,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
        Arm.read_store,Arm.write_store,rnum]
      rfl
  have memorySem : MemRefines (fun _ => False) 0 (fun _ => none) (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨ρ0,semantics⟩ := domain.returns run (SourceEntry.of_enterFunc entered) returned
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    memorySem stable trivial arguments
  exact ⟨result,ρ0,run,domain,entered,semantics⟩

/-- Actual ABI execution traps at the middle division before either later block
executes; the inherited final result cannot make the first-trap proof vacuous. -/
theorem executable_four_block_trap_witness (X : ExtSem) :
    ∃ result ρ0,Stock.lower (function true) = .ok result ∧ Stock.Scalar.Domain (function true) ∧
      Clif.enterFunc (function true) [⟨.i64,7⟩,⟨.i64,0⟩] Clif.Mem.empty = .ok (initial true,Clif.Mem.empty) ∧
      VTrapFrom result.code (csem (fun _ => False) ⟨0,0⟩ X)
        ⟨0,0,ρ0,Arm.write_base_gpr 1#5 0 (Arm.write_base_gpr 0#5 7 Arm.ArmState.default)⟩ .intDivz := by
  obtain ⟨result,run,blocks,eligible,domain,checked⟩ := checked_driver_witness true
  have entered : Clif.enterFunc (function true) [⟨.i64,7⟩,⟨.i64,0⟩] Clif.Mem.empty = .ok (initial true,Clif.Mem.empty) := rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 4 ⟨initial true,[],Clif.Mem.empty⟩ = .trapped .intDivz := rfl
  let initialWorld := Arm.write_base_gpr 1#5 0 (Arm.write_base_gpr 0#5 7 Arm.ArmState.default)
  have arguments : ArgsAtEntry (fun _ => False) (function true).sig [⟨.i64,7⟩,⟨.i64,0⟩] initialWorld := by
    intro loc value member
    change (loc,value) ∈ [(.reg (.x 0),⟨.i64,7⟩),(.reg (.x 1),⟨.i64,0⟩)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same <;> cases same
    all_goals
      simp only [VHolds,regVal,initialWorld,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
        Arm.read_store,Arm.write_store,rnum]
      rfl
  have memorySem : MemRefines (fun _ => False) 0 (fun _ => none) (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨ρ0,semantics⟩ := domain.traps run (SourceEntry.of_enterFunc entered) returned
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    memorySem stable trivial arguments
  exact ⟨result,ρ0,run,domain,entered,semantics⟩

end Backend.Stock.Proof.ForwardWitness

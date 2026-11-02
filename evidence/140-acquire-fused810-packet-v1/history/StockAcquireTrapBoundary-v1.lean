import FV.Backend.Proof.StockAcquireRecordWitness
import FV.Backend.Proof.StockAcquireEntry
import FV.E2E.MemTrapStatement

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- Reach the original acquire without executing its faulting access.
This additive observable leaves every old ordinary and atomic trap variant unchanged. -/
def VAcquireTrapFrom (vc : VCode) (sem : Backend.Proof.Sem)
    (initial : VState CV Arm.ArmState) (code : Clif.TrapCode)
    (property : BitVec 64 → Nat → Prop) : Prop :=
  ∃ b k regs world block ty d pointer flags,
    Star (VStep vc sem) (.run initial) (.run ⟨b,k,regs,world⟩) ∧
    vc.blocks[b]? = some block ∧
    block.insts[k]? = some (.loadAcquire ty (.vreg d .int) (.vreg pointer .int) flags) ∧
    AtomTy ty ∧ flags.trapCode = some code ∧ property (lo64 (regs pointer)) ty.bytes

/-- The actual complete Stock result reaches its real acquire after the original ABI move. -/
theorem lowered_args_prefix {result : Stock.Result} (lowered : Stock.lower function = .ok result)
    {isem : Backend.Proof.Sem} (driver : DriverSem isem) (regs : Nat → CV) (world : Arm.ArmState) :
    ∃ regs1 block,result.code.blocks[0]? = some block ∧ block.insts = completeCode ∧
      Star (VStep result.code isem) (.run ⟨0,0,regs,world⟩) (.run ⟨0,1,regs1,world⟩) ∧
      regs1 192 = regVal world (.x 0) := by
  obtain ⟨maps,⟨block,found,code⟩,records⟩ := actual_record_binding lowered
  let operands : Array Operand := #[⟨192,.int,.def,.late,.fixed (.x 0)⟩]
  let regs1 := vdefUpd operands [regVal world (.x 0)] regs
  have run : seqRun isem [.args [(.vreg 192 .int,.x 0)]] regs world = some (.fall regs1 world) :=
    seqRun_isem_one (by rfl) (driver.args [(.vreg 192 .int,.x 0)] world) rfl
  have segment : SegAt block 0 [.args [(.vreg 192 .int,.x 0)]] := by
    intro j bounded
    cases j with
    | zero => rw [code]; rfl
    | succ j => simp at bounded; omega
  have path := seqRun_fall_star (vc := result.code) (sem := isem) found segment (by rw [code]; decide) run
  refine ⟨regs1,block,found,code,?_,?_⟩
  · simpa only [List.length_cons,List.length_nil,Nat.zero_add] using path
  · simp [regs1,operands,vdefUpd,writeV,Operand.isDef,Operand.isEarly,Operand.isLate,upd]

/-- The original source memory fault reaches the actual deferred acquire boundary.
The existing MapFaults relation supplies the unmapped byte internally. -/
theorem lowered_byte_access_fault {result : Stock.Result} (lowered : Stock.lower function = .ok result)
    {isem : Backend.Proof.Sem} (driver : DriverSem isem)
    (env : Clif.Env) (program : Clif.Program) (pointer : BitVec 64) (memory : Clif.Mem)
    (fuel : Nat) (code : Clif.TrapCode)
    (trapped : Clif.runLoop env program fuel ⟨entry pointer,[],memory⟩ = .trapped code)
    (mp : ArmFault.MemMap) (faults : MapFaults mp env program ⟨entry pointer,[],memory⟩)
    (regs : Nat → CV) (world : Arm.ArmState)
    (argument : VHolds ⟨.i64,pointer⟩ (regVal world (.x 0))) :
    VAcquireTrapFrom result.code isem ⟨0,0,regs,world⟩ code
      (fun address bytes => ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none) := by
  obtain ⟨positive,readTrap⟩ := (source_first_trap env program pointer memory fuel code).mp trapped
  have flag := (Clif.Mem.load_trap readTrap).2
  have access := first_source_memory_trap env program pointer memory fuel code trapped
  obtain ⟨j,bounded,unmapped⟩ := faults _ code _ _ (.refl _) access
  obtain ⟨regs1,block,found,body,path,value192⟩ := lowered_args_prefix lowered driver regs world
  have address : lo64 (regs1 192) = BitVec.ofNat 64 (Clif.effAddr ⟨.i64,pointer⟩ 0) := by
    rw [value192]
    exact (lo64_of_holds argument rfl).trans (effAddr_zero ⟨.i64,pointer⟩).symm
  refine ⟨0,1,regs1,world,block,.int 8,195,192,{},path,found,?_,by simp [AtomTy],flag,?_⟩
  · rw [body]; rfl
  · refine ⟨j,bounded,?_⟩
    rw [address,← BitVec.ofNat_add]
    exact unmapped

end Backend.Stock.Proof.Acquire810

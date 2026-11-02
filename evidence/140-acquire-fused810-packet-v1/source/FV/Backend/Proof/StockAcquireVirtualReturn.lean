import FV.Backend.Proof.StockAcquireRecordWitness
import FV.Backend.Proof.StockAcquireEntry

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The actual complete Stock code returns the original widened byte.
The proof uses the retained record and final alias, with no execution certificate. -/
theorem lowered_byte_return {result : Stock.Result} (lowered : Stock.lower function = .ok result)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Backend.Proof.Sem} {MR : MemRelT}
    (refines : Refines F isem) (driver : DriverSem isem) (stable : MRStable F MR)
    (memorySem : MemRefines F sb syms isem) (memoryOk : MemRelOk F sb syms function MR)
    (pointer : BitVec 64) (memory : Clif.Mem) (raw : BitVec 8)
    (read : memory.load {} (Clif.effAddr ⟨.i64,pointer⟩ 0) 1 8 = .ok raw)
    (regs : Nat → CV) (world : Arm.ArmState) (related : MR [] memory world)
    (argument : VHolds ⟨.i64,pointer⟩ (regVal world (.x 0))) :
    ∃ final,VRetFrom result.code isem ⟨0,0,regs,world⟩ [(.vreg 195 .int,.x 0)]
      [ofX (raw.setWidth 64)] final ∧ MR [] memory final := by
  obtain ⟨maps,⟨block,found,code⟩,recordFacts⟩ := actual_record_binding lowered
  let argsOps : Array Operand := #[⟨192,.int,.def,.late,.fixed (.x 0)⟩]
  let regs1 := vdefUpd argsOps [regVal world (.x 0)] regs
  have argsRun : seqRun isem [.args [(.vreg 192 .int,.x 0)]] regs world = some (.fall regs1 world) :=
    seqRun_isem_one (by rfl) (driver.args [(.vreg 192 .int,.x 0)] world) rfl
  have value192 : regs1 192 = regVal world (.x 0) := by
    simp [regs1,argsOps,vdefUpd,writeV,Operand.isDef,Operand.isEarly,Operand.isLate,upd]
  have atomic : Clif.evalInst (entry pointer) memory (.atomicLoad .i8 {} 1) =
      .ok ([⟨.i8,raw⟩],memory) := by
    simp [Clif.evalInst,Clif.Frame.get,Clif.Res.ofOption,Clif.Res.check,bind,Clif.Res.bind,
      Nat.mod_one,Clif.Ty.width,Clif.Ty.bytes,entry,read]
  obtain ⟨loaded,regs2,world1,small,sameMemory,extended,bodyRun,value195,frame,memory1⟩ :=
    acquire_byte_pair_run stable memorySem memoryOk (by decide) (p := 1) (z := 0) (d := 195) (nr := 192)
      (by rfl) rfl (by rw [value192]; exact argument) atomic related
  have same : raw = loaded := by
    apply BitVec.eq_of_toNat_eq
    exact congrArg Clif.Val.toNat small
  subst loaded
  have prefixRun := seqRun_append_fall' isem argsRun bodyRun
  have segment : SegAt block 0 [.args [(.vreg 192 .int,.x 0)],acquireInstruction] := by
    intro j bounded
    cases j with
    | zero => simpa only [code,completeCode] using (show completeCode[0]? = some (.args [(.vreg 192 .int,.x 0)]) from rfl)
    | succ j =>
      cases j with
      | zero => simpa only [code,completeCode] using (show completeCode[1]? = some acquireInstruction from rfl)
      | succ j => simp at bounded; omega
  have path := seqRun_fall_star (vc := result.code) (sem := isem) found segment
    (by rw [code]; decide) prefixRun
  obtain ⟨final,returned,kept⟩ := refines (.rets [(.vreg 195 .int,.x 0)]) [ofX (raw.setWidth 64)]
    world1 [] world1 (ctl := .ret) rfl
  let retOps : Array Operand := #[⟨195,.int,.use,.early,.fixed (.x 0)⟩]
  refine ⟨final,⟨0,2,regs2,world1,block,retOps,[],?_,found,?_,rfl,?_,returned⟩,
    stable _ _ _ _ kept.toNF memory1⟩
  · simpa only [List.length_cons,List.length_nil,Nat.zero_add] using path
  · rw [code]; rfl
  · simp [vuses,retOps,Operand.isUse,value195]

end Backend.Stock.Proof.Acquire810

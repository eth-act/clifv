import FV.Backend.Proof.StockCallStoreResult
import FV.E2E.Statement

namespace Backend.Stock.CallStore
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false

/-- One kernel composes the real call, source-derived store, and unchanged ABI return. -/
theorem execute_tail
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {f : Clif.Function}
    (stable : MRStable F MR) (storeSem : Stock.Memory.StoreRefines F sb isem)
    (memoryOk : MemRelOk F sb syms f MR)
    (retSem : ∀ (us : List (Reg × Reg)) uses world,isem (.rets us) uses world = some ([],world,.ret))
    {vc : VCode} {block : VBlock} (placed : vc.blocks[0]? = some block)
    {name : String} {argument called pointer : Nat} (separate : pointer ≠ called)
    {flags : Clif.MemFlags} {prelude suffix : List MInst}
    (code : block.insts.toList = (prelude ++
      [.call ⟨.sym name,retPairs [(argument,.x 0)],callDefs [(.x 0,called)]⟩,
       .store .store64 (.vreg called .int) (.unsignedOffset (.vreg pointer .int) 8) flags,
       .rets (retPairs [(called,.x 0)])]) ++ suffix)
    {seed values : Nat → CV} {initial before after : Arm.ArmState} {output : CV}
    (preRun : seqRun isem prelude seed initial = some (.fall values before))
    (callRun : isem (.call ⟨.sym name,retPairs [(argument,.x 0)],callDefs [(.x 0,called)]⟩)
      ([(argument,Reg.x 0)].map (values ·.1)) before = some ([output],after,.next))
    {fr : Clif.Frame} {cm storedMem : Clif.Mem} {sourceValue sourcePointer : Nat}
    (memory : MR fr.slots cm after) (little : flags.endianness ≠ some .big)
    (held : ∀ value,fr.getAs sourceValue .i64 = .ok value → VHolds ⟨.i64,value⟩ output)
    (address : ∀ pv,fr.regs sourcePointer = some pv →
      amodeAddr sb (.unsignedOffset (.vreg pointer .int) 8) 8 [values pointer] after =
        some (BitVec.ofNat 64 (Clif.effAddr pv 8)))
    (source : Clif.evalInst fr cm (.store .store .i64 flags sourceValue sourcePointer 8) =
      .ok ([],storedMem)) :
    ∃ pv final,fr.regs sourcePointer = some pv ∧
      VReturns vc isem seed initial (retPairs [(called,.x 0)]) [output] final ∧
      SameWorld F final (Arm.write_mem_bytes 8 (BitVec.ofNat 64 (Clif.effAddr pv 8))
        ((lo64 output).setWidth 64) after) ∧ MR fr.slots storedMem final := by
  obtain ⟨pv,final,pointerRead,executed,world,memory',empty⟩ :=
    CallStoreResult.call_then_store_of_source stable storeSem memoryOk separate callRun memory
      little held address source
  let updated : Nat → CV := fun key => if key = called then output else values key
  have returned : seqRun isem [.rets (retPairs [(called,.x 0)])] updated final =
      some (.stop 0 (.rets (retPairs [(called,.x 0)]))
        (retOps [(called,.x 0)]).toArray updated final [] final .ret) := by
    simp [seqRun,operands_rets,retSem,retOps,Operand.isDef]
  have bodyRun := seqRun_append_fall_stop isem executed returned
  have complete := seqRun_append_fall_stop isem preRun bodyRun
  have segment : SegAt block 0 (prelude ++
      [.call ⟨.sym name,retPairs [(argument,.x 0)],callDefs [(.x 0,called)]⟩,
       .store .store64 (.vreg called .int) (.unsignedOffset (.vreg pointer .int) 8) flags,
       .rets (retPairs [(called,.x 0)])]) :=
    segAt_of_toList (L₁ := []) (by simpa only [List.nil_append] using code)
  obtain ⟨path,_,instruction,operands,ran,_,_⟩ := seqRun_stop_star placed segment complete
  refine ⟨pv,final,pointerRead,?_,world,memory'⟩
  refine ⟨0,_,updated,final,block,(retOps [(called,.x 0)]).toArray,[],path,placed,instruction,rfl,?_,retSem _ _ _⟩
  simp [vuses_retOps,updated]

end Backend.Stock.CallStore

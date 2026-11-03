import FV.Backend.Proof.StockLiveCallArithmetic
import FV.Backend.Proof.StockMemoryStoreContract

namespace Backend.Stock.Proof.CallStoreResult
open Backend Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The call/store continuation uses the returned value and the distinct original pointer.
The source store derives access validity from the actual post-call source memory. -/
theorem call_then_store_of_source
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {f : Clif.Function}
    (stable : MRStable F MR) (storeSem : Stock.Memory.StoreRefines F sb isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {name : String} {pairs : List (Nat × Reg)} {destination pointer : Nat}
    (separate : pointer ≠ destination) {values : Nat → CV} {output : CV}
    {before after : Arm.ArmState}
    (called : isem (.call ⟨.sym name,retPairs pairs,callDefs [(.x 0,destination)]⟩)
      (pairs.map (values ·.1)) before = some ([output],after,.next))
    {fr : Clif.Frame} {cm cm' : Clif.Mem} {sourceValue sourcePointer : Nat}
    {flags : Clif.MemFlags} {results : List Clif.Val}
    (memory : MR fr.slots cm after) (little : flags.endianness ≠ some .big)
    (held : ∀ value,fr.getAs sourceValue .i64 = .ok value → VHolds ⟨.i64,value⟩ output)
    (address : ∀ pv,fr.regs sourcePointer = some pv →
      amodeAddr sb (.unsignedOffset (.vreg pointer .int) 8) 8 [values pointer] after =
        some (BitVec.ofNat 64 (Clif.effAddr pv 8)))
    (source : Clif.evalInst fr cm (.store .store .i64 flags sourceValue sourcePointer 8) =
      .ok (results,cm')) :
    ∃ pv world,fr.regs sourcePointer = some pv ∧
      seqRun isem
        [.call ⟨.sym name,retPairs pairs,callDefs [(.x 0,destination)]⟩,
         .store .store64 (.vreg destination .int) (.unsignedOffset (.vreg pointer .int) 8) flags]
        values before = some (.fall (fun key => if key = destination then output else values key) world) ∧
      SameWorld F world (Arm.write_mem_bytes 8 (BitVec.ofNat 64 (Clif.effAddr pv 8))
        ((lo64 output).setWidth 64) after) ∧ MR fr.slots cm' world ∧ results = [] := by
  have callRun := seqRun_call_sym called (show [output].length = [(.x 0,destination)].length from rfl)
  have update := DirectCallResult.virtual_result pairs destination output values
  rw [vdefUpd_call] at update
  rw [update] at callRun
  let next : Nat → CV := fun key => if key = destination then output else values key
  obtain ⟨pv,world,pointerRead,stored,same,memory',empty⟩ :=
    Stock.Memory.store_source_seqRun_of_store stable storeSem memoryOk memory
      (ρ := next) (n := destination)
      (am := .unsignedOffset (.vreg pointer .int) 8)
      (by intro reg member; exact ⟨_,List.mem_singleton.mp member⟩)
      (show StoreOp.store64 ≠ .fpuStore128 from by decide) rfl (by decide) little
      (by intro value read; simpa only [next,ite_true] using held value read)
      (by intro pv found; simpa only [amUses,amVregs,AMode.regs,List.filterMap_cons,
          List.filterMap_nil,List.map_cons,List.map_nil,next,separate,↓reduceIte,StoreOp.bytes] using address pv found)
      source
  refine ⟨pv,world,pointerRead,seqRun_append_fall' isem callRun stored,?_,memory',empty⟩
  simpa only [next,ite_true,StoreOp.bytes] using same

/-- The source result binder leaves the original pointer unchanged after arbitrary callee effects. -/
theorem source_pointer {state next : Clif.State} {rest : List Clif.Stmt} {source pointer : Nat}
    {returned : Clif.Val} {after : Clif.Mem}
    (continued : Clif.continueWith state rest [source] [returned] after = .next next)
    (separate : pointer ≠ source) :
    next.frame.regs pointer = state.frame.regs pointer ∧ next.mem = after :=
  LiveCallArithmetic.source_live continued separate

end Backend.Stock.Proof.CallStoreResult

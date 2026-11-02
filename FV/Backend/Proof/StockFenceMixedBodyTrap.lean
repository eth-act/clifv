import FV.Backend.Proof.StockFenceMixedBodyRefines
import FV.Backend.Proof.StockMemoryLoadAccessTrap
import FV.Backend.Proof.StockMemoryStoreAccessTrap

namespace Backend.Stock.Proof.FenceFixture
open Backend.Proof Backend.Proof.Driver
open Backend.Stock.Memory Backend.Stock.Memory.IntegerRoots Backend.Stock.Memory.StoreRoots
open MemoryFaults
set_option autoImplicit false
set_option Elab.async false

private theorem iadd_notrap (fr : Clif.Frame) (cm : Clif.Mem) (x y : Nat) (code : Clif.TrapCode) :
    Clif.evalInst fr cm (.binary .iadd .i64 x y) ≠ .trap code := by
  intro failed
  simp only [Clif.evalInst,Clif.BinaryOp.isShift] at failed
  rcases Clif.res_bind_eq_trap failed with bad | ⟨a,left,failed⟩
  · exact PureBody.frame_getAs_notrap fr x .i64 code bad
  rcases Clif.res_bind_eq_trap failed with bad | ⟨b,right,failed⟩
  · exact PureBody.frame_getAs_notrap fr y .i64 code bad
  cases failed

/-- Every possible first trap in the unchanged mixed body uses its actual retained record. -/
theorem mixed_record_access_trap {result : Result} (run : Stock.lower function = .ok result)
    (scope : LowerScope function) (dominated : Dominated function)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit function event b term body)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {env : Clif.Env} {cp : Clif.Program} {MR : MemRelT} (initial : Clif.State)
    {sb : Nat} {code : Clif.TrapCode} (Q : Nat → Nat → Prop)
    (allFaults : ∀ state addr bytes,Reach env cp initial state →
      Clif.MemTrapAt env cp state code addr bytes → Q addr bytes) :
    ∀ record ∈ body.records,LocalAccessTrapRefines
      (LocalBody.IndexedSourceTrap env cp function event.ctx event.block)
      sb isem result.final.alias
      (ReachedGuardedRel function result event.ctx event.block MR env cp initial)
      (sourceAddrPred Q) record code := by
  have facts := mixed_actual_body_facts run events
  have lookup : function.blocks[0]? = some b := by simpa only [facts.1] using split.block
  have same : function.blocks[0]! = b := Option.some.inj lookup
  subst b
  intro record member
  obtain ⟨j,stm,statement,current⟩ := split.positions record member
  have bound : j < 7 := (List.getElem?_eq_some_iff.mp statement).1
  have index : record.inst = j := by simpa [blockStart,facts.1] using current
  have retained := split.retained record member
  obtain ⟨step,recorded,emitted⟩ := facts.2.2.2 record retained (by omega)
  obtain ⟨info,source,original,results⟩ := ArithmeticBody.body_source_info run events split statement current
  have inv := (stock_lower_record_context run scope events).1
  have casesJ : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases casesJ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have shape : stm = (function.blocks[0]!.body[0]!) := (Option.some.inj statement).symm
    subst stm
    obtain ⟨a,mapped⟩ := mixed_emitted_result_mapped run scope events retained source results recorded emitted
    have pointerType := inv.addr64 _ _ _ 7 source original rfl
    obtain ⟨nreg,pointer⟩ := inv.typedReg 7 _ pointerType
    exact stock_load_zero_access_trap .w64 run scope dominated events retained split.block statement current
      source original results mapped facts.2.2.1 pointer recorded emitted initial Q allFaults
  · have shape : stm = (function.blocks[0]!.body[1]!) := (Option.some.inj statement).symm
    subst stm
    intro point failed ρ world related
    obtain ⟨position,actual,inst,rest,present,clif,remaining,outcome⟩ := failed
    cases Option.some.inj (present.symm.trans source)
    cases Option.some.inj (clif.symm.trans original)
    change Clif.Res.ok ([],point.2.2) = Clif.Res.trap code at outcome
    cases outcome
  · have shape : stm = (function.blocks[0]!.body[2]!) := (Option.some.inj statement).symm
    subst stm
    intro point failed ρ world related
    obtain ⟨position,actual,inst,rest,present,clif,remaining,outcome⟩ := failed
    cases Option.some.inj (present.symm.trans source)
    cases Option.some.inj (clif.symm.trans original)
    exact False.elim (iadd_notrap point.2.1 point.2.2 63 31 code outcome)
  · have shape : stm = (function.blocks[0]!.body[3]!) := (Option.some.inj statement).symm
    subst stm
    have pointerType := inv.addr64 _ _ _ 7 source original rfl
    obtain ⟨pointerReg,pointer⟩ := inv.typedReg 7 _ pointerType
    obtain ⟨valueReg,value⟩ := inv.typedReg 100 _ facts.2.1
    exact stock_store_eight_i64_access_trap run scope dominated events retained split.block statement current
      source original facts.2.1 facts.2.2.1 pointer value recorded emitted initial Q allFaults
  · have shape : stm = (function.blocks[0]!.body[4]!) := (Option.some.inj statement).symm
    subst stm
    intro point failed ρ world related
    obtain ⟨position,actual,inst,rest,present,clif,remaining,outcome⟩ := failed
    cases Option.some.inj (present.symm.trans source)
    cases Option.some.inj (clif.symm.trans original)
    change Clif.Res.ok ([],point.2.2) = Clif.Res.trap code at outcome
    cases outcome
  · have shape : stm = (function.blocks[0]!.body[5]!) := (Option.some.inj statement).symm
    subst stm
    obtain ⟨a,mapped⟩ := mixed_emitted_result_mapped run scope events retained source results recorded emitted
    exact stock_udiv_access_first_trap run scope dominated events retained split.block statement current
      source original results mapped recorded emitted refines initial (sourceAddrPred Q)
  · have shape : stm = (function.blocks[0]!.body[6]!) := (Option.some.inj statement).symm
    subst stm
    obtain ⟨a,mapped⟩ := mixed_emitted_result_mapped run scope events retained source results recorded emitted
    have pointerType := inv.addr64 _ _ _ 7 source original rfl
    obtain ⟨nreg,pointer⟩ := inv.typedReg 7 _ pointerType
    exact stock_load_sixteen_access_trap .w64 run scope dominated events retained split.block statement current
      source original results mapped facts.2.2.1 pointer recorded emitted initial Q allFaults

end Backend.Stock.Proof.FenceFixture

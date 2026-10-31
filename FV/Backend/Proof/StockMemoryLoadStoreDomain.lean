import FV.Backend.Proof.StockMemoryLoadStoreReturnBody
import FV.Backend.Proof.StockMemoryReturnRefines
import FV.Backend.Proof.StockMemoryNotrap
import FV.Backend.Proof.StockMemoryContract

namespace Backend.Stock.Memory.LoadStore
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- A complete mixed load/store function inherits the original memory-capable contract.
The returned value comes from the load before the store updates source and machine memory. -/
theorem domain_of_load_store_return (width : IntegerRoots.Width) (kind : StoreRoots.Kind) (ty : Clif.Ty)
    {f : Clif.Function} (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {loadPointer storePointer value z : Nat} {loadFlags storeFlags : Clif.MemFlags} {valueTy : Clif.Ty}
    (shape : b.body = [⟨[z],.load .load width.sourceTy loadFlags loadPointer 0⟩,
      ⟨[],.store kind.sourceOp ty storeFlags value storePointer 0⟩]) (ret : b.term = .ret [z])
    (loadParameter : loadPointer ∈ b.params.map (·.1))
    (storeParameter : storePointer ∈ b.params.map (·.1)) (valueParameter : (value,valueTy) ∈ b.params)
    (storeWidth : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits)
    (loadNotrap : loadFlags.trapCode = none) (storeNotrap : storeFlags.trapCode = none) : Domain f := by
  have family : ∀ stm ∈ b.body,OrdinaryBody.OrdinaryInst stm.inst := by
    intro stm member
    have alternatives : stm = ⟨[z],.load .load width.sourceTy loadFlags loadPointer 0⟩ ∨
        stm = ⟨[],.store kind.sourceOp ty storeFlags value storePointer 0⟩ := by simpa [shape] using member
    rcases alternatives with rfl | rfl
    all_goals
      constructor
      · intro fn args impossible; cases impossible
      · intro sig callee args impossible; cases impossible
  have entryBlock : f.blocks[0]? = some b := by simp [blocks]
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      base syms memorySem MR stable memoryOk w memory arguments
    apply OrdinaryBody.actual_ordinary_entry_return_refines_frame run scope dominated abi blocks family ret
      entered returned refines driver memorySem stable ?_ memory arguments
    intro event events
    obtain ⟨b',term,body,split⟩ := stock_lower_body_scan_split run scope events
    have bound : event.block < 1 := by have h := lt_of_getElem? split.block; simpa [blocks] using h
    have zero : event.block = 0 := by omega
    have actualBlock : f.blocks[event.block]? = some b := by rw [zero]; exact entryBlock
    exact load_store_return_body width kind ty run scope dominated events actualBlock shape ret
      entryBlock loadParameter entryBlock storeParameter entryBlock valueParameter storeWidth
      stable memorySem memoryOk
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      base syms memorySem MR stable memoryOk w memory arguments
    obtain ⟨b',regs,entry,argTypes,paramTypes,set,frame⟩ := entered
    have sameBlock : b' = b := by
      have found : some b = some b' := by simpa only [Clif.Function.entry?,blocks,List.head?_cons] using entry
      exact Option.some.inj found.symm
    subst b'
    have sourceFamily : ∀ stm ∈ fr.body,OrdinaryBody.OrdinaryInst stm.inst ∧
        ∀ fr cm c,Clif.evalInst fr cm stm.inst ≠ .trap c := by
      intro stm member
      have present : stm ∈ b.body := by rw [frame] at member; exact member
      refine ⟨family stm present,?_⟩
      have alternatives : stm = ⟨[z],.load .load width.sourceTy loadFlags loadPointer 0⟩ ∨
          stm = ⟨[],.store kind.sourceOp ty storeFlags value storePointer 0⟩ := by simpa [shape] using present
      rcases alternatives with rfl | rfl
      · intro fr cm c
        exact Clif.evalInst_notrap rfl loadNotrap c
      · intro fr cm c
        exact Clif.evalInst_notrap rfl storeNotrap c
    exact False.elim ((OrdinaryBody.ordinary_source_notrap fuel ⟨fr,[],cm⟩ rfl sourceFamily
      (by rw [frame]; exact ret) code) trapped)

end Backend.Stock.Memory.LoadStore

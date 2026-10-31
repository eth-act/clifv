import FV.E2E.StockMemoryPairedEntryReturn
import FV.E2E.StockMemoryLoadStorePairedBody

namespace E2E.StockMemory.LoadStore
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Memory.IntegerRoots
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Source-only mixed load/store functions execute from instruction zero in
paired worlds. The original ABI/RelW and initialized-memory relations supply all
runtime premises; actual entry/body/retention/result-binding code is derived. -/
theorem load_store_return_paired_function_seeded (width : Width) (kind : Backend.Stock.Memory.StoreRoots.Kind) (ty : Clif.Ty) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    {loadPointer storePointer value z : Nat} {loadFlags storeFlags : Clif.MemFlags} {valueTy : Clif.Ty}
    (shape : b.body = [⟨[z],.load .load width.sourceTy loadFlags loadPointer 0⟩,
      ⟨[],.store kind.sourceOp ty storeFlags value storePointer 0⟩]) (ret : b.term = .ret [z])
    (loadParameter : loadPointer ∈ b.params.map (·.1))
    (storeParameter : storePointer ∈ b.params.map (·.1)) (valueParameter : (value,valueTy) ∈ b.params)
    (storeWidth : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    (registerOnly : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    (tls : XTls Γ.F X)
    {w w' : Arm.ArmState} (memory : MRP Γ f c D fr.slots cm (w,w'))
    (arguments : ArgsAtEntry Γ.F f.sig args w) (otherArguments : ArgsAtEntry Γ.F f.sig args w')
    (registers : ∀ pin v,(.reg pin,v) ∈ (locsOf f.sig).zip args → regVal w' pin = regVal w pin) :
    RunOkABI f result.code (pairSem (csem Γ.F fc X)) (MRP Γ f c D) fr.slots
      ⟨0,0,entrySeed result.ctx fr,(w,w')⟩ (.returned vals mem) := by
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
  apply actual_ordinary_paired_entry_return_refines_frame run scope dominated abi blocks family ret
    entered returned registerOnly slot symbols tls ?_ memory arguments otherArguments registers
  intro event events
  obtain ⟨b',term,body,split⟩ := stock_lower_body_scan_split run scope events
  have bound : event.block < 1 := by have h := lt_of_getElem? split.block; simpa [blocks] using h
  have zero : event.block = 0 := by omega
  have actualBlock : f.blocks[event.block]? = some b := by rw [zero]; exact entryBlock
  exact load_store_return_paired_body width kind ty run scope dominated events actualBlock shape ret
    entryBlock loadParameter entryBlock storeParameter entryBlock valueParameter storeWidth slot symbols tls

/-- Compatibility existential form of the canonical entry-seeded execution. -/
theorem load_store_return_paired_function (width : Width) (kind : Backend.Stock.Memory.StoreRoots.Kind) (ty : Clif.Ty) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    {loadPointer storePointer value z : Nat} {loadFlags storeFlags : Clif.MemFlags} {valueTy : Clif.Ty}
    (shape : b.body = [⟨[z],.load .load width.sourceTy loadFlags loadPointer 0⟩,
      ⟨[],.store kind.sourceOp ty storeFlags value storePointer 0⟩]) (ret : b.term = .ret [z])
    (loadParameter : loadPointer ∈ b.params.map (·.1))
    (storeParameter : storePointer ∈ b.params.map (·.1)) (valueParameter : (value,valueTy) ∈ b.params)
    (storeWidth : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    (registerOnly : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    (tls : XTls Γ.F X)
    {w w' : Arm.ArmState} (memory : MRP Γ f c D fr.slots cm (w,w'))
    (arguments : ArgsAtEntry Γ.F f.sig args w) (otherArguments : ArgsAtEntry Γ.F f.sig args w')
    (registers : ∀ pin v,(.reg pin,v) ∈ (locsOf f.sig).zip args → regVal w' pin = regVal w pin) :
    ∃ ρ, RunOkABI f result.code (pairSem (csem Γ.F fc X)) (MRP Γ f c D) fr.slots
      ⟨0,0,ρ,(w,w')⟩ (.returned vals mem) := by
  exact ⟨entrySeed result.ctx fr,load_store_return_paired_function_seeded width kind ty run scope dominated abi
    blocks shape ret loadParameter storeParameter valueParameter storeWidth entered returned registerOnly slot symbols tls memory arguments otherArguments registers⟩

end E2E.StockMemory.LoadStore

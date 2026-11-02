import FV.E2E.StockMemoryPairedEntryReturn
import FV.E2E.StockMemoryStorePairedBody

namespace E2E.StockMemory.StoreRoots
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Memory.StoreRoots
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Source-only singleton store/return functions execute from instruction zero in
paired worlds. The original ABI/RelW and initialized-memory relations supply all
runtime premises; actual entry/body/retention/result-binding code is derived. -/
theorem single_store_return_paired_function_seeded (kind : Kind) (ty : Clif.Ty) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    {value pointer : Nat} {flags : Clif.MemFlags} {valueTy : Clif.Ty}
    (singleton : b.body = [⟨[],.store kind.sourceOp ty flags value pointer 0⟩])
    (ret : b.term = .ret []) (parameter : pointer ∈ b.params.map (·.1))
    (valueParameter : (value,valueTy) ∈ b.params)
    (width : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits)
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
    have same : stm = ⟨[],.store kind.sourceOp ty flags value pointer 0⟩ := by simpa only [singleton,List.mem_singleton] using member
    subst stm
    constructor
    · intro fn args impossible; cases impossible
    · intro sig callee args impossible; cases impossible
  have formats : ∀ b' ∈ f.blocks, ∀ stm ∈ b'.body,CastComplete.MemoryFormat stm.inst := by
    intro b' member stm present
    have same : b' = b := by simpa [blocks] using member
    subst b'
    have same : stm = ⟨[],.store kind.sourceOp ty flags value pointer 0⟩ := by
      simpa [singleton] using present
    subst stm
    simp [CastComplete.MemoryFormat,instNames]
  have entryBlock : f.blocks[0]? = some b := by simp [blocks]
  apply actual_ordinary_paired_entry_return_refines_frame run scope dominated abi blocks family ret
    entered returned registerOnly slot symbols tls ?_ memory arguments otherArguments registers
  intro event events
  obtain ⟨b',term,body,split⟩ := stock_lower_body_scan_split run scope events
  have bound : event.block < 1 := by have h := lt_of_getElem? split.block; simpa [blocks] using h
  have zero : event.block = 0 := by omega
  have actualBlock : f.blocks[event.block]? = some b := by rw [zero]; exact entryBlock
  exact stock_single_store_return_paired_body kind ty run scope dominated formats events actualBlock
    singleton ret entryBlock parameter entryBlock valueParameter width
    slot symbols tls

/-- Compatibility existential form of the canonical entry-seeded execution. -/
theorem single_store_return_paired_function (kind : Kind) (ty : Clif.Ty) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    {value pointer : Nat} {flags : Clif.MemFlags} {valueTy : Clif.Ty}
    (singleton : b.body = [⟨[],.store kind.sourceOp ty flags value pointer 0⟩])
    (ret : b.term = .ret []) (parameter : pointer ∈ b.params.map (·.1))
    (valueParameter : (value,valueTy) ∈ b.params)
    (width : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits)
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
  exact ⟨entrySeed result.ctx fr,single_store_return_paired_function_seeded kind ty run scope dominated abi
    blocks singleton ret parameter valueParameter width entered returned registerOnly slot symbols tls memory arguments otherArguments registers⟩

end E2E.StockMemory.StoreRoots

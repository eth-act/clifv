import FV.E2E.StockMemoryTwoBlockPaired
import FV.Backend.Proof.StockMemoryCfgClass

namespace E2E.StockMemoryCfg
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The source-only CFG class supplies the complete paired ABI execution. -/
theorem paired_returns {f : Clif.Function} {result : Result}
    (family : Backend.Stock.MemoryCfg.TwoBlockClass f) (run : Stock.lower f = .ok result)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame} (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    (tls : XTls Γ.F X)
    {w w' : Arm.ArmState} (memory : MRP Γ f c D fr.slots cm (w,w'))
    (arguments : ArgsAtEntry Γ.F f.sig args w) (otherArguments : ArgsAtEntry Γ.F f.sig args w')
    (registers : ∀ pin v,(.reg pin,v) ∈ (locsOf f.sig).zip args → regVal w' pin = regVal w pin) :
    RunOkABI f result.code (pairSem (csem Γ.F fc X)) (MRP Γ f c D) fr.slots
      ⟨0,0,entrySeed result.ctx fr,(w,w')⟩ (.returned vals mem) := by
  obtain ⟨entry,target,x,z,flags,blocks,entryBody,targetBody,jump,ret,parameter,notrap⟩ := family.shape
  have nops : ∀ stm ∈ entry.body,stm.inst = .nop := by
    intro stm member
    have equal : stm = ⟨[],.nop⟩ := by simpa only [entryBody,List.mem_singleton] using member
    subst stm
    rfl
  have shape : ∀ j stm,target.body[j]? = some stm → j = 1 ∨ stm.inst = .nop := by
    intro j stm found
    cases j with
    | zero =>
      simp [targetBody] at found
      subst stm
      exact .inr rfl
    | succ j =>
      cases j with
      | zero => exact .inl rfl
      | succ j => simp [targetBody] at found
  exact StockMemory.stock_two_block_load_return_paired_function run family.scope family.dominated family.abi
    blocks nops jump (loadIndex := 1) (by rw [targetBody]; rfl) shape ret parameter entered family.registers
    slot symbols tls returned memory arguments otherArguments registers

end E2E.StockMemoryCfg

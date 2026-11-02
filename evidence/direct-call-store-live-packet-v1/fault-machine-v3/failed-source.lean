import FV.E2E.StockCallStoreFaultRun
import FV.E2E.StockCallStoreDomain
import FV.Backend.Proof.StockMemoryAccessMachineCheck
import FV.Backend.Proof.StockMemoryAccessStage
import FV.E2E.DeadCleanupRegLevelX
import FV.E2E.StockArithmeticStageContract

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof MemoryFaults Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- A callee trap is separate from a fault at the caller's subsequent store. -/
def CallStoreCalleeTrap (env : Clif.Env) (p : Clif.Program) (fr : Clif.Frame)
    (cm : Clif.Mem) (code : Clif.TrapCode) : Prop :=
  ∃ result fn args rest,fr.body = ⟨[result],.call fn args⟩ :: rest ∧
    instOutcome env p fr cm (.call fn args) = .trap code

/-- The checked machine reaches its first post-call store fault. Callee traps remain explicit. -/
theorem backend_store_fault_or_callee_stock_call_store
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (checked : Stock.CallStore.check f result.code = true) {cleanup : Bool}
    (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b,syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (shapes : ∀ (b : Nat) (block : VBlock) (j : Nat) (inst : MInst),vcp.blocks[b]? = some block → block.insts[j]? = some inst →
      ∀ sb uses world code address bytes,AccessAt sb inst uses world code address bytes → OrdinaryAccessShape inst)
    (mp : ArmFault.MemMap) (faults : MapFaults mp env p cs) {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env p fuel cs = .trapped code) :
    CallStoreCalleeTrap env p cs.frame cs.mem code ∨
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n,TrapAtF mp fb base code (runX (ArmStepX X H fa) n s) ∧
          ∀ j < n,actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
            (runX (ArmStepX X H fa) j s) := by
  obtain ⟨actual,lowered,equal,scope,dominated,abi,⟨layout⟩,_⟩ := Stock.CallStore.check_sound checked
  have sameResult : actual = result := Except.ok.inj (lowered.symm.trans hc.lower)
  subst actual
  have state : (⟨cs.frame,[],cs.mem⟩ : Clif.State) = cs := by
    have callers := hcs.callers
    cases cs
    cases callers
    rfl
  rcases layout.fault_ready (fc := ⟨fa.k,af.slotBase⟩) hc.lower scope dominated
      hsub hcs.stockSourceEntry (by rwa [state]) hslot hsym hrel hargs with callee | ready
  · apply Or.inl
    obtain ⟨blocks,parameters,body,term,rest⟩ := layout.source_fields
    obtain ⟨b,regs,entry,types,paramTypes,set,frame⟩ := hcs.stockSourceEntry
    have first : f.entry? = some layout.data.block := by simp only [Clif.Function.entry?,blocks,List.head?_cons]
    cases Option.some.inj (entry.symm.trans first)
    exact ⟨layout.data.called,layout.data.fn,[layout.data.argument],
      [⟨[],.store .store .i64 layout.data.flags layout.data.called layout.data.pointer 8⟩],
      (congrArg Clif.Frame.body frame).trans body,callee⟩
  · apply Or.inr
    obtain ⟨path⟩ := ready
    have access := path.execute hcs.sig hargs hrel hX mp (by rwa [state])
    rw [← hslot] at access
    have staged := accessTrap_stage hc.prepOk access
    have actual := accessTrap_gotV_value staged
    intro H G base ra s entry
    have machine := regLevel_access_fault_worldX_value hc.check hc.alloc hc.emit hc.layout
      (X := X) (H := H) (K := K) (G := G) (gv := GotV vcp)
      hcov entry.abi entry.stack entry.gfree (by rw [entry.hF]; exact entry.calls)
      (by rw [entry.hF]; exact entry.tries) (by rw [entry.hF]; exact entry.tls)
      (by rw [entry.hF]; exact entry.body) path.seed
      (fun b block j inst found located uses world code address bytes access =>
        shapes b block j inst found located af.slotBase uses world code address bytes access) mp
    rw [entry.hF] at machine
    exact machine code _ (fun _ _ held => sourceAddrPred_unmapped held) actual

end E2E

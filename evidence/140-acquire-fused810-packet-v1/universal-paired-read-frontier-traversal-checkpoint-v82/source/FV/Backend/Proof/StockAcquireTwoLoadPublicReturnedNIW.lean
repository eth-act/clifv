import FV.Backend.Proof.StockAcquireTwoLoadSeedReturned
import FV.Backend.Proof.StockMemoryAccessStage
import FV.E2E.StockArithmeticSemantics
import FV.E2E.DeadCleanupRegLevelW
import FV.E2E.LinkWorld

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Original public source returns reach the actual prepared machine return with every original W field.
The source free/leave memory and both complete final bindings remain exact. -/
-- witness: native_decide
theorem backend_correct_worldX_ni_stock_two_load_acquire_returnW {p : Clif.Program} {k : Nat} {result : Stock.Result} {vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {cleanup : Bool}
    (hc : CompiledStockArithmeticStage AcquireTwoLoadPrefix.function cleanup k result vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    (hsym : ∀ name address,syms name = some address → X.sym name 0 = BitVec.ofNat 64 address)
    (hslot : af.slotBase = slotOff)
    {world : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry AcquireTwoLoadPrefix.function args cs)
    (hrel : RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ AcquireTwoLoadPrefix.function c cs.frame.slots cs.mem world)
    (hargs : ArgsAtEntry F AcquireTwoLoadPrefix.function.sig args world)
    (fuel : Nat) {vals : List Clif.Val} {final : Clif.Mem}
    (returned : Clif.runLoop env p fuel cs = .returned vals final) :
    ∃ (us : List (Reg × Reg)) (outs : List CV) (reference : Arm.ArmState),
      ReturnABI AcquireTwoLoadPrefix.function us ∧ us.length = outs.length ∧ PrefixHold vals outs ∧ MemRel F syms final reference ∧
      result.code.RetsSite us ∧
      (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (initial : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra initial world →
        ∃ n,ActRet ra F G us outs reference initial (runX (ArmStepX X H fa) n initial) ∧
          PostTrace fa af base (ArmStepX X H fa) initial n ∧
          ∀ j < n,actGoodXW vcp rf af fa fb base initial X H K G (GotV vcp) (runX (ArmStepX X H fa) j initial)) ∧
      (XNI F syms (AcquireTwoLoadPrefix.function.externs.map (·.2)) (indSigs AcquireTwoLoadPrefix.function) c
        (CallLg env (AcquireTwoLoadPrefix.function.externs.map (·.2)) (indSigs AcquireTwoLoadPrefix.function)) X → XTls F X →
      ∀ (D : BitVec 64 → Prop) (otherWorld : Arm.ArmState),
        RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ AcquireTwoLoadPrefix.function c cs.frame.slots cs.mem otherWorld →
        SameWorld (fun a => F a ∨ D a) world otherWorld →
        (∀ pin v,(ArgLoc.reg pin,v) ∈ (locsOf AcquireTwoLoadPrefix.function.sig).zip args → regVal otherWorld pin = regVal world pin) →
        (∀ off v,(ArgLoc.stack off,v) ∈ (locsOf AcquireTwoLoadPrefix.function.sig).zip args → ∀ i < v.ty.bytes,
          otherWorld.mem (Arm.r (.GPR 29#5) world+BitVec.ofInt 64 (16+(off : Int))+BitVec.ofNat 64 i) =
            world.mem (Arm.r (.GPR 29#5) world+BitVec.ofInt 64 (16+(off : Int))+BitVec.ofNat 64 i)) →
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (initial : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra initial otherWorld →
          ∃ n,ActRet ra (fun a => F a ∨ D a) G us outs reference initial (runX (ArmStepX X H fa) n initial) ∧
            PostTrace fa af base (ArmStepX X H fa) initial n ∧
            ∀ j < n,actGoodXW vcp rf af fa fb base initial X H K G (GotV vcp) (runX (ArmStepX X H fa) j initial)) := by
  let Γ : Rel := ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩
  have source := AcquireTwoLoadPrefix.original_returned_seeded_runOkABI hc.lower hcs env p fuel returned
    (refines_valueSem F ⟨fa.k,af.slotBase⟩ X) (driverSem_valueSem F ⟨fa.k,af.slotBase⟩ X)
    (mrStable_relW Γ AcquireTwoLoadPrefix.function c) (memRefines_valueSem F ⟨fa.k,af.slotBase⟩ X hslot hsym)
    (memRelOk_relW Γ AcquireTwoLoadPrefix.function c) hrel hargs
  obtain ⟨us,outs,reference,cm0,reached,pins,arity,values,memory,freed⟩ := source
  have prepared := MemoryFaults.returns_stage hc.prepOk reached
  have site : result.code.RetsSite us := by
    obtain ⟨b,j,ρ,w,vb,ops,outputs,path,found,located,rest⟩ := reached
    exact ⟨b,vb,j,found,located⟩
  have finalMemory : MemRel F syms final reference := by
    rw [freed]
    exact memRel_leave (memRel_free memory.1.1 _)
  let regs := entrySeed result.ctx cs.frame
  have machineReturn : ∀ (bodyWorld : Arm.ArmState) (H : ArmHooks) (G : BitVec 64 → Prop)
      (base ra : BitVec 64) (initial : Arm.ArmState),
      ActEntry vcp rf af fa fb K F G X H base ra initial bodyWorld →
      ∀ rs os target,VReturns vcp (valueSemV (GotV vcp) F ⟨fa.k,af.slotBase⟩ X) regs bodyWorld rs os target →
        ∃ n,ActRet ra F G rs os target initial (runX (ArmStepX X H fa) n initial) ∧
          PostTrace fa af base (ArmStepX X H fa) initial n ∧
          ∀ j < n,actGoodXW vcp rf af fa fb base initial X H K G (GotV vcp) (runX (ArmStepX X H fa) j initial) := by
    intro bodyWorld H G base ra initial he rs os target reached
    have machine := regLevelCorrect_worldX_valueW hc.check hc.alloc hc.emit hc.layout
      (X := X) (H := H) (K := K) (G := G) (gv := GotV vcp)
      hcov he.abi he.stack he.gfree (by rw [he.hF];exact he.calls) (by rw [he.hF];exact he.tries)
      (by rw [he.hF];exact he.tls) (by rw [he.hF];exact he.body) regs
    rw [he.hF] at machine
    obtain ⟨n,⟨ret0,ret1,ret2,ret3,ret4,ret5,trace⟩,good⟩ := machine.1 rs os target reached
    exact ⟨n,⟨ret0,ret1,ret2,ret3,ret4,ret5⟩,trace,good⟩
  refine ⟨us,outs,reference,pins,arity,values,finalMemory,site,?_,?_⟩
  · intro H G base ra initial he
    exact machineReturn world H G base ra initial he us outs reference (vReturns_gotV_value prepared)
  · intro _hNI tls D otherWorld otherRel worlds registers _stack H G base ra initial he
    have otherArgs : ArgsAtEntry F AcquireTwoLoadPrefix.function.sig args otherWorld := by
      intro loc v member
      cases loc with
      | reg pin =>
        change VHolds v (regVal otherWorld pin)
        rw [registers pin v member]
        exact hargs (.reg pin) v member
      | stack off =>
        have location := (List.of_mem_zip member).1
        change ArgLoc.stack off ∈ [.reg (.x 0),.reg (.x 1)] at location
        simp at location
    have pairedMemory : MRP Γ AcquireTwoLoadPrefix.function c D cs.frame.slots cs.mem (world,otherWorld) :=
      ⟨hrel,otherRel,sameWorld_zof hrel.1.1 otherRel.1.1 worlds (fun _ h => h)⟩
    have paired := AcquireTwoLoadPrefix.original_returned_seeded_paired_runOkABI (fc := ⟨fa.k,af.slotBase⟩) hc.lower hcs env p fuel returned tls hslot hsym
      pairedMemory hargs otherArgs registers
    obtain ⟨pairUs,pairOuts,pairWorld,pairMemory,pairReached,_,_,_,pairRelated,_⟩ := paired
    obtain ⟨firstReached,otherReached⟩ := vRetFrom_pair pairReached
    obtain ⟨rfl,rfl,worldEq⟩ := vRetFrom_det firstReached reached
    have agreement : SameWorld (fun a => F a ∨ D a) pairWorld.2 reference := by
      rw [← worldEq]
      exact SameWorld.symm (SameWorld.mono (zof_sub pairMemory) pairRelated.2.2)
    have otherPrepared := MemoryFaults.returns_stage hc.prepOk otherReached
    obtain ⟨n,ret,trace,good⟩ := machineReturn otherWorld H G base ra initial he pairUs pairOuts pairWorld.2
      (vReturns_gotV_value otherPrepared)
    obtain ⟨r0,r1,r2,r3,r4,r5⟩ := ret
    refine ⟨n,⟨r0,r1,?_,?_,r4,r5⟩,trace,good⟩
    · intro a outside
      rw [r2 a (fun h => outside (Or.inl h))]
      exact agreement.2.1 a outside
    · intro field unmasked fp sp
      rw [r3 field unmasked fp sp]
      exact agreement.1 field unmasked


end E2E

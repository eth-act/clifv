import FV.E2E.StockAcquireTwoLoadReturnTraceStepF
import FV.Backend.Proof.StockAcquireTwoLoadPublicReturnedNIW

namespace E2E.LinkSys
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Original paired return premises give one shared output/reference tuple for both actual stepF executions. -/
-- witness: native_decide
theorem two_load_original_return_stepF_NIW (L : LinkSys) {κ : Nat → Clif.Function → Nat}
    {p : Clif.Program} {k M : Nat} {result : Stock.Result} {cleanup : Bool}
    (hc : CompiledStockArithmeticStage AcquireTwoLoadPrefix.function cleanup k result
      (L.A AcquireTwoLoadPrefix.function).vcp (L.A AcquireTwoLoadPrefix.function).rf
      (L.A AcquireTwoLoadPrefix.function).af (L.A AcquireTwoLoadPrefix.function).fa
      (L.A AcquireTwoLoadPrefix.function).fb)
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64}
    (covered : FormsCovered ⟨(L.A AcquireTwoLoadPrefix.function).fa.k,(L.A AcquireTwoLoadPrefix.function).af.slotBase⟩
      (L.A AcquireTwoLoadPrefix.function).vcp)
    (symbols : ∀ name address, syms name = some address → L.Xb.sym name 0 = BitVec.ofNat 64 address)
    (slot : (L.A AcquireTwoLoadPrefix.function).af.slotBase = slotOff)
    {world : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (sourceEntry : ClifEntry AcquireTwoLoadPrefix.function args cs)
    (related : RelW ⟨F,syms,slotOff,(RAFrame.compute (L.A AcquireTwoLoadPrefix.function).vcp
      (L.A AcquireTwoLoadPrefix.function).rf).intBase⟩ AcquireTwoLoadPrefix.function c cs.frame.slots cs.mem world)
    (arguments : ArgsAtEntry F AcquireTwoLoadPrefix.function.sig args world)
    (fuel : Nat) {vals : List Clif.Val} {final : Clif.Mem}
    (returned : Clif.runLoop env p fuel cs = .returned vals final)
    {mp : ArmFault.MemMap} {codeImage : BitVec 64 → Prop}
    (kept : ∀ a, (mp a).allows .W = false → L.Img a)
    (readable : ∀ a, codeImage a → (mp a).allows .R = true)
    (codeAddresses : ∀ a, CodeAddr (Arm.set_program Arm.ArmState.default
      ((L.A AcquireTwoLoadPrefix.function).fb.program (L.A AcquireTwoLoadPrefix.function).base)) a →
      codeImage a) :
    ∃ (us : List (Reg × Reg)) (outs : List CV) (reference : Arm.ArmState),
      ReturnABI AcquireTwoLoadPrefix.function us ∧ us.length = outs.length ∧ PrefixHold vals outs ∧
      MemRel F syms final reference ∧ result.code.RetsSite us ∧
      (∀ (G : BitVec 64 → Prop) (ra : BitVec 64) (initial : Arm.ArmState),
        L.MachEntry κ M AcquireTwoLoadPrefix.function F G ra initial world →
        ActEntry (L.A AcquireTwoLoadPrefix.function).vcp (L.A AcquireTwoLoadPrefix.function).rf
          (L.A AcquireTwoLoadPrefix.function).af (L.A AcquireTwoLoadPrefix.function).fa
          (L.A AcquireTwoLoadPrefix.function).fb (κ M AcquireTwoLoadPrefix.function) F G L.Xb (L.hooks M)
          (L.A AcquireTwoLoadPrefix.function).base ra initial world →
        ∃ n, ActRet ra F G us outs reference initial (ArmFault.runF mp n initial) ∧
          PostTrace (L.A AcquireTwoLoadPrefix.function).fa (L.A AcquireTwoLoadPrefix.function).af
            (L.A AcquireTwoLoadPrefix.function).base (ArmFault.stepF mp) initial n ∧
          L.RunGoodLBW n M AcquireTwoLoadPrefix.function initial) ∧
      (XNI F syms (AcquireTwoLoadPrefix.function.externs.map (·.2)) (indSigs AcquireTwoLoadPrefix.function) c
        (CallLg env (AcquireTwoLoadPrefix.function.externs.map (·.2)) (indSigs AcquireTwoLoadPrefix.function)) L.Xb →
      XTls F L.Xb → ∀ (D : BitVec 64 → Prop) (otherWorld : Arm.ArmState),
        RelW ⟨F,syms,slotOff,(RAFrame.compute (L.A AcquireTwoLoadPrefix.function).vcp
          (L.A AcquireTwoLoadPrefix.function).rf).intBase⟩ AcquireTwoLoadPrefix.function c cs.frame.slots cs.mem otherWorld →
        SameWorld (fun a => F a ∨ D a) world otherWorld →
        (∀ pin v, (ArgLoc.reg pin,v) ∈ (locsOf AcquireTwoLoadPrefix.function.sig).zip args →
          regVal otherWorld pin = regVal world pin) →
        (∀ off v, (ArgLoc.stack off,v) ∈ (locsOf AcquireTwoLoadPrefix.function.sig).zip args → ∀ i < v.ty.bytes,
          otherWorld.mem (Arm.r (.GPR 29#5) world + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 i) =
            world.mem (Arm.r (.GPR 29#5) world + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 i)) →
        ∀ (G : BitVec 64 → Prop) (ra : BitVec 64) (initial : Arm.ArmState),
          L.MachEntry κ M AcquireTwoLoadPrefix.function F G ra initial otherWorld →
          ActEntry (L.A AcquireTwoLoadPrefix.function).vcp (L.A AcquireTwoLoadPrefix.function).rf
            (L.A AcquireTwoLoadPrefix.function).af (L.A AcquireTwoLoadPrefix.function).fa
            (L.A AcquireTwoLoadPrefix.function).fb (κ M AcquireTwoLoadPrefix.function) F G L.Xb (L.hooks M)
            (L.A AcquireTwoLoadPrefix.function).base ra initial otherWorld →
          ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs reference initial (ArmFault.runF mp n initial) ∧
            PostTrace (L.A AcquireTwoLoadPrefix.function).fa (L.A AcquireTwoLoadPrefix.function).af
              (L.A AcquireTwoLoadPrefix.function).base (ArmFault.stepF mp) initial n ∧
            L.RunGoodLBW n M AcquireTwoLoadPrefix.function initial) := by
  obtain ⟨us,outs,reference,pins,arity,values,memory,site,ordinary,paired⟩ :=
    backend_correct_worldX_ni_stock_two_load_acquire_returnW (K := κ M AcquireTwoLoadPrefix.function)
      hc covered symbols slot sourceEntry related arguments fuel returned
  refine ⟨us,outs,reference,pins,arity,values,memory,site,?_,?_⟩
  · intro G ra initial machineEntry entry
    obtain ⟨n,ret,post,trace⟩ := ordinary (L.hooks M) G (L.A AcquireTwoLoadPrefix.function).base ra initial entry
    exact ⟨n,L.two_load_return_trace_stepF hc machineEntry ret post trace kept readable codeAddresses⟩
  · intro ni tls D otherWorld otherRel same registers stack G ra initial machineEntry entry
    obtain ⟨n,ret,post,trace⟩ := paired ni tls D otherWorld otherRel same registers stack
      (L.hooks M) G (L.A AcquireTwoLoadPrefix.function).base ra initial entry
    exact ⟨n,L.two_load_return_trace_stepF hc machineEntry ret post trace kept readable codeAddresses⟩

end E2E.LinkSys

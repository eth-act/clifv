import FV.E2E.StockCallStoreTrapRun
import FV.E2E.StockCallStoreTrapStage
import FV.E2E.StockCallStoreNoTry
import FV.E2E.WorldTrapStop
import FV.E2E.StockArithmeticStageContract

namespace Backend.Stock.CallStore
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- One world kernel transfers the actual raising call through either checked production stage. -/
theorem TrapReady.machine_stop {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {result : Stock.Result} {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {cleanup : Bool} (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb)
    (checked : check f result.code = true)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64} {fr : Clif.Frame} {cm : Clif.Mem}
    {w₀ : Arm.ArmState} {code : Clif.TrapCode}
    (source : TrapReady f result env p fr cm
      ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ ⟨fa.k,af.slotBase⟩ X w₀ code)
    (covered : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    {args : List Clif.Val} (types : args.map (·.ty) = f.sig.params.map (·.ty))
    (arguments : ArgsAtEntry F f.sig args w₀)
    (memory : RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c fr.slots cm w₀)
    (traps : XTrapsOk env (f.externs.map (·.2)) (indSigs f)
      (RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c) X)
    (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState)
    (entry : ActEntry vcp rf af fa fb K F G X H base ra s w₀) :
    ∃ n,CallTrapAt vcp F K G s fa base X (GotV vcp)
      (TrapCallSem env (f.externs.map (·.2)) (indSigs f)
        (RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c) X code)
      (runX (ArmStepX X H fa) n s) ∧
      ∀ j < n,actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
        (runX (ArmStepX X H fa) j s) ∧
      spv (runX (ArmStepX X H fa) n s) = spv s - BitVec.ofNat 64 (frameDrop af) ∧
      (runX (ArmStepX X H fa) n s).program = fb.program base := by
  obtain ⟨before,unwinds,related,world⟩ := source.execute types arguments memory traps
  have staged := unwinds_stage hc.prepOk unwinds
  have actual := vUnwinds_gotV_gen (gotPair_valueU _ _ _) staged
  have noTry := noTryCall_of_check checked
  have stagedNoTry : (Stock.Arithmetic.stage cleanup result.code).hasTryCall = false := by
    cases cleanup with
    | false => exact noTry
    | true => exact prune_noTryCall noTry
  have preparedNoTry := noTryCall_of_prepCheck hc.prepOk stagedNoTry
  have machine := regLevel_trapStop_world hc.check hc.alloc hc.emit hc.layout covered preparedNoTry
    (TrapCallSem env (f.externs.map (·.2)) (indSigs f)
      (RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c) X code) entry source.seed
  exact machine.2 0 before actual

/-- Preserve the original world theorem as a wrapper around the stopping kernel. -/
theorem TrapReady.machine {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {result : Stock.Result} {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {cleanup : Bool} (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb)
    (checked : check f result.code = true)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64} {fr : Clif.Frame} {cm : Clif.Mem}
    {w₀ : Arm.ArmState} {code : Clif.TrapCode}
    (source : TrapReady f result env p fr cm
      ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ ⟨fa.k,af.slotBase⟩ X w₀ code)
    (covered : FormsCovered ⟨fa.k,af.slotBase⟩ vcp)
    {args : List Clif.Val} (types : args.map (·.ty) = f.sig.params.map (·.ty))
    (arguments : ArgsAtEntry F f.sig args w₀)
    (memory : RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c fr.slots cm w₀)
    (traps : XTrapsOk env (f.externs.map (·.2)) (indSigs f)
      (RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c) X)
    (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState)
    (entry : ActEntry vcp rf af fa fb K F G X H base ra s w₀) :
    ∃ n,CallTrapAt vcp F K G s fa base X (GotV vcp)
      (TrapCallSem env (f.externs.map (·.2)) (indSigs f)
        (RelW ⟨F,syms,slotOff,(RAFrame.compute vcp rf).intBase⟩ f c) X code)
      (runX (ArmStepX X H fa) n s) ∧
      ∀ j < n,actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
        (runX (ArmStepX X H fa) j s) := by
  obtain ⟨n,trapped,good,stack,program⟩ := source.machine_stop hc checked covered types arguments memory traps
    H G base ra s entry
  exact ⟨n,trapped,good⟩

end Backend.Stock.CallStore

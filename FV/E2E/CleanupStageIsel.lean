import FV.E2E.SretReturn
import FV.Backend.Proof.CleanupStageFacts

/-!
# CLIF → VCode for the code after the skip of unused instructions (`skipStage`)

The production compiler runs, between the lowering `vc` (validated by `lowerCheck`) and the dead
cleanup, the skip of unused instructions `skipStage f vc` (`FV/Backend/CleanupStage.lean`). Its
simulation is the driver simulation of the kept code (`driver_correct_skip`,
`driver_correct_abi_skip`, `FV/Backend/Proof/LowerSimSkip.lean`), for the lowering obligations
`skipStage_spec` provides together with the deletion's hypotheses:

* `driver_correct_stage`, `driver_correct_abi_stage`: `driver_correct`/`driver_correct_abi` for
  a VCode `vcK` that is `vc` or `vc` without unused statements (`SkipHyp`);
* `iselSim_of_driver_stage`, `iselSimAbi_of_driver_stage`: `iselSim_of_driver`,
  `iselSimAbi_of_driver` for such `vcK`.
-/

namespace Backend.Proof.Driver
open Backend Backend.Proof

section
variable {f : Clif.Function} {vc vcK : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {sem : Sem}
  {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
  {drop : Nat → Nat → Bool}

/-- **The driver lemma with the ABI return values for `vc` or its kept code.** -/
theorem driver_correct_abi_stage (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    (hsk : vcK = vc ∨ SkipHyp f vc R bl drop vcK) (hds : DriverSem sem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hMR : MRStable F MR)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hP : RunPrem env p f cs) {Q : List Clif.Val → Prop}
    (hQ : ∀ s sv, Reach env p cs s → s.frame.getMany (sretRet f) = .ok sv → Q sv) (fuel : Nat) :
    RunOkAbi vcK sem MR slots Q ⟨0, 0, ρ₀, w₀⟩ (Clif.runLoop env p fuel cs) := by
  rcases hsk with rfl | hK
  · exact driver_correct_abi H hds hMem hMR hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr
      hargs hP hQ fuel
  · exact driver_correct_abi_skip H hK hds hMem hMR hB0 hcall hfunc hslots hbody hterm hregs hty
      hsig hmr hargs hP hQ fuel

/-- **The driver lemma for `vc` or its kept code.** -/
theorem driver_correct_stage (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    (hsk : vcK = vc ∨ SkipHyp f vc R bl drop vcK) (hds : DriverSem sem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hMR : MRStable F MR)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hP : RunPrem env p f cs) (fuel : Nat) :
    RunOk vcK sem MR slots ⟨0, 0, ρ₀, w₀⟩ (Clif.runLoop env p fuel cs) := by
  rcases hsk with rfl | hK
  · exact driver_correct H hds hMem hMR hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr
      hargs hP fuel
  · exact driver_correct_skip H hK hds hMem hMR hB0 hcall hfunc hslots hbody hterm hregs hty hsig
      hmr hargs hP fuel

end

end Backend.Proof.Driver

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver

/-- **CLIF → VCode for `vc` or its kept code** (`iselSim_of_driver`, through
`driver_correct_stage`). -/
theorem iselSim_of_driver_stage {f : Clif.Function} {vc vcK : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {drop : Nat → Nat → Bool} {sem : Sem} {Γ : Rel} {env : Clif.Env} {p : Clif.Program}
    (H : DriverHyp f vc ctx st0 R gn bl A sem (fun sl cm w => Γ.holds f sl cm w) env p)
    (hsk : vcK = vc ∨ SkipHyp f vc R bl drop vcK)
    (hds : DriverSem sem) {sb : Nat} (hMem : MemRefines Γ.F sb Γ.syms sem) :
    IselSim sem Γ env p f vcK := by
  intro args cs w₀ ρ₀ hce hrel hargs htr fuel
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := runPrem_of_entry hce htr
  have hrun := driver_correct_stage H hsk hds hMem (mrStable_holds Γ f) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs hP fuel
  refine ⟨fun vals cm h => ?_, fun c h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1 _)⟩
  · rw [h] at hrun
    exact hrun

/-- **CLIF → VCode with the ABI return values for `vc` or its kept code**
(`iselSimAbi_of_driver`, through `driver_correct_abi_stage`). -/
theorem iselSimAbi_of_driver_stage {f : Clif.Function} {vc vcK : VCode} {ctx : Ctx}
    {st0 : LState} {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow}
    {A : Nat → Nat → List Clif.ValueId} {drop : Nat → Nat → Bool}
    {sem : Sem} {Γ : Rel} {env : Clif.Env} {p : Clif.Program}
    (H : DriverHyp f vc ctx st0 R gn bl A sem (fun sl cm w => Γ.holds f sl cm w) env p)
    (hsk : vcK = vc ∨ SkipHyp f vc R bl drop vcK)
    (hds : DriverSem sem) {sb : Nat} (hMem : MemRefines Γ.F sb Γ.syms sem)
    (hS : sretStableB f = true) :
    IselSimAbi sem Γ env p f vcK := by
  intro args cs w₀ ρ₀ hce hrel hargs htr fuel
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := runPrem_of_entry hce htr
  have hrun := driver_correct_abi_stage H hsk hds hMem (mrStable_holds Γ f) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs hP
    (Q := (· = sretArg f args))
    (sret_reach H.ext H.tryExt H.noTail hP hS hB0 hce.callers hce.func hbody hterm hregs hty.symm)
    fuel
  refine ⟨fun vals cm h => ?_, fun c h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, sv, hret, h1, h2, hsv, h3, h4, h5⟩ := hrun
    subst hsv
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1 _)⟩
  · rw [h] at hrun
    exact hrun

end E2E

import FV.E2E.Main
import FV.Backend.Proof.LowerSimSkip

/-!
# CLIF → VCode for the code without unused statements (`skipDead`)

`iselSim_of_driver_skipDead` is `iselSim_of_driver` for `skipDead f vc`: from the lowering
validator's acceptance of `vc` (`skipDead_spec`) and the driver hypotheses for `vc`, the CLIF run
is realised by the VCode that Cranelift would select, without the statements whose results no
kept code reads (`FV/Backend/SkipDead.lean`).
-/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver

/-- **CLIF → VCode for `skipDead f vc`** (`iselSim_of_driver`, through `driver_correct_skipDead`). -/
theorem iselSim_of_driver_skipDead {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {sem : Sem} {Γ : Rel} {env : Clif.Env} {p : Clif.Program}
    (H : DriverHyp f vc ctx st0 R gn bl A sem (fun sl cm w => Γ.holds f sl cm w) env p)
    (hsk : skipDead f vc = vc ∨
      SkipHyp f vc R bl (skipAt f (skipDrops f R bl vc)) (skipDead f vc))
    (hds : DriverSem sem) {sb : Nat} (hMem : MemRefines Γ.F sb Γ.syms sem) :
    IselSim sem Γ env p f (skipDead f vc) := by
  intro args cs w₀ ρ₀ hce hrel hargs htr fuel
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := by
    have hf := hce.func
    exact ⟨htr.stmt, fun s c fn args et hr hs hb hT B hB => htr.tryCall s c fn args et hr hs hb hT B
        (hf ▸ hB),
      fun s c callee args et hr hs hb hT B hB =>
        htr.tryCallInd s c callee args et hr hs hb hT B (hf ▸ hB),
      fun s st rest sig callee args hr hb hi ⟨B, hB, hst⟩ =>
        htr.indirect s st rest sig callee args hr hb hi ⟨B, hf ▸ hB, hst⟩,
      fun s callee args et hr hb hT ⟨B, hB, e⟩ =>
        htr.tryIndirect s callee args et hr hb hT ⟨B, hf ▸ hB, e⟩⟩
  have hrun := driver_correct_skipDead H hsk hds hMem (mrStable_holds Γ f) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs hP fuel
  refine ⟨fun vals cm h => ?_, fun c h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1 _)⟩
  · rw [h] at hrun
    exact hrun

end E2E

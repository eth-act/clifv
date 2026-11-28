import FV.E2E.DeadCleanupWorld
import FV.E2E.LinkWorldR
import FV.E2E.DeadCleanupContractsR

/-!
# CLIF → VCode for the value semantics of the cleanup stage, register-guarded (#753, stage R2)

`DeadCleanupWorld`'s simulations at `regG P (valueSem …)` under the call families and contracts
with registers: `iselSim_relW_cleanup_ofR`, `iselSim_relW_cleanup_stageR`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

set_option autoImplicit false

section


/-- `iselSim_relW_cleanup` for `vcK`, the lowering `vc` or its kept code (`SkipHyp`), from the
lowering obligations of `vc` for the deletion's renaming and lowering record. -/
theorem iselSim_relW_cleanup_ofR {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcK vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    {ctx : Ctx} {st0 : LState} {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow}
    {A : Nat → Nat → List Clif.ValueId} {drop : Nat → Nat → Bool}
    (hshape : LowerShape f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term)
    (hsk : vcK = vc ∨ SkipHyp f vc R bl drop vcK)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    {P : BitVec 64 → Clif.Signature → Prop}
    (hPg : RegCompatGot P (f.externs.map (·.2)) (fun n => X.sym n 0))
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hPi : RegCompatInd P env (indSigs f) syms)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {args : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w, VReturns vcK (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) ρ₀ w₀ us outs w ∧
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTraps vcK (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) ρ₀ w₀ c') := by
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hRef : Refines F (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) := (refines_valueSem _ _ X).regG
  have hmem : MemRefines F slotOff syms (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) :=
    (memRefines_valueSem _ _ X hslot hsym).regG
  have hcalls := callsRefinePR_valueSem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hX hPg
  have hicalls := indCallsRefinePR_valueSem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hXI hsym
    (fun _ _ _ h => h.1.1.symbols) hPi
  have houtB := outgoing_le_intBaseCleanupA hc.toA
  have H : DriverHyp f vc ctx st0 R gn bl A (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) (RelW Γ f c) env p := {
    shape := hshape
    cert := hcert
    dsem := ((driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X).regG).toDriverSemG
    insts := instCallsR_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrectPR
      indRulesCorrectPR memRulesCorrectR_program hRef (mrStable_relW Γ f c) hcalls hicalls hmem
      (outArgsOk_relW Γ f c) (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (indStack_mono (indStack_of_check hc.lowerOk) houtB)
      (memRelOk_relW Γ f c)
    terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable hRef (mrStable_relW Γ f c)
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hc.lowerOk
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨_, tryCallsR_of_rules tryRulesCorrectPR tryUnmatchable hRef (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) hcalls, tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCallsR_of_rules tryIndRulesCorrectPR tryIndUnmatchable hRef (mrStable_relW Γ f c)
      hmem (outArgsOk_relW Γ f c) (indStack_mono (indStack_of_check hc.lowerOk) houtB) hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := by
      obtain ⟨ss, ps, he⟩ := cfg_of_prepare hc.prepare
      exact ⟨ss, ps, (cleanupStage_cfg f vc).symm.trans he⟩ }
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
  have hrun := driver_correct_stage H hsk ((driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X).regG) hmem
    (mrStable_relW Γ f c) hB0 hce.callers hce.func rfl hbody hterm
    hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs hP fuel
  refine ⟨fun vals cm h => ?_, fun c' h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1.1 _)⟩
  · rw [h] at hrun
    exact hrun

/-- **`iselSim_relW_cleanup` for the code after the skip of unused instructions**
(`skipStage f vc`, which the cleanup stage prunes and prepares). -/
theorem iselSim_relW_cleanup_stageR {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    {P : BitVec 64 → Clif.Signature → Prop}
    (hPg : RegCompatGot P (f.externs.map (·.2)) (fun n => X.sym n 0))
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hPi : RegCompatInd P env (indSigs f) syms)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {args : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w, VReturns (skipStage f vc) (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) ρ₀ w₀ us outs w ∧
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTraps (skipStage f vc) (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) ρ₀ w₀ c') := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hsk⟩ := skipStage_spec hc.lowerOk
  exact iselSim_relW_cleanup_ofR (hPg := hPg) (hPi := hPi) hsub hc hshape hcert hbr hsk hX hXI hsym hslot ρ₀ hce hrel hargs
    htr fuel

end

end E2E

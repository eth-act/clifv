import FV.E2E.MainT
import FV.E2E.CleanupStageIsel

/-!
# The typed CLIF → VCode layer for the code after the skip (`skipStage`)

The skip of unused instructions runs only on a function of subset E whose lowering `lowerCheck`
accepts (`skipStage`). For a function of the typed scope (validated by `lowerCheckT`):

* if the skip does not run, `skipStage f vc = vc` and the typed simulation of `vc`
  (`iselSimT_of_rules`) applies;
* if it runs, the function is of subset E (its returned values are integers) and `lowerCheck`
  accepts `vc`: the subset-E simulation of the kept code (`iselSim_of_driver_stage`, with the
  proven rule families) realises every CLIF return in the integer return registers, which are the
  typed ones (`retRegsOk_of_int`); the returned values' types come from the CLIF run
  (`iselSimT_of_iselSim`).

`iselSimT_stage` is `iselSimT_of_rules` for `skipStage f vc`.
-/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver

/-- **The driver hypotheses of a subset-E function** validated by `lowerCheck`, for the
relation `Γ.holds` and the proven rule families. -/
theorem driverHyp_holds {p : Clif.Program} {f : Clif.Function} {vc : VCode} {ctx : Ctx}
    {st0 : LState} {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow}
    {A : Nat → Nat → List Clif.ValueId}
    (hsub : InSubset p f) (hlc : lowerCheck f vc = true)
    (hshape : LowerShape f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) (hcfg : ∃ ss ps, vc.cfg = .ok (ss, ps))
    {sem : Sem} {Γ : Rel} {env : Clif.Env}
    (hRef : Refines Γ.F sem) (hds : DriverSem sem)
    (hcalls : CallsRefine Γ.F env (f.externs.map (·.2))
      (fun sl cm w => Γ.holds f sl cm w) sem)
    (hicalls : IndCallsRefine env (indSigs f) (fun sl cm w => Γ.holds f sl cm w) sem)
    (hmem : MemRefines Γ.F Γ.slotOff Γ.syms sem) (houtB : vc.outgoing ≤ Γ.out) :
    DriverHyp f vc ctx st0 R gn bl A sem (fun sl cm w => Γ.holds f sl cm w) env p := {
  shape := hshape
  cert := hcert
  dsem := hds.toDriverSemG
  insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
    indRulesCorrect memRulesCorrect_program hRef (mrStable_holds Γ f) hcalls hicalls hmem
    (outArgsOk_holds Γ f) (callsStack_mono (callsStack_of_check hlc) houtB)
    (memRelOk_holds Γ f)
  terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
    branchExcludedUnmatchable hRef (mrStable_holds Γ f)
  ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
  indSig := indSig_of_subset hsub
  subE := hsub.subsetE
  entryLocs := entryOk_of_check hlc
  brIdx := hbr
  noTail := noTail_of_subset hsub
  tries := ⟨Γ.out, tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef (mrStable_holds Γ f) hmem
    (outArgsOk_holds Γ f) hcalls, tryStack_mono (tryStack_of_check hlc) houtB⟩
  tryExt := hsub.tryExterns
  tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef (mrStable_holds Γ f)
    hicalls
  tryIndSig := tryIndSig_of_subset hsub
  cfg := hcfg }

theorem retRegsT_int_range : ∀ (n nx nv : Nat),
    retRegsT (List.replicate n .int) nx nv = (List.range n).map fun i => Reg.x (nx + i)
  | 0, _, _ => rfl
  | n + 1, nx, nv => by
    rw [List.replicate_succ, retRegsT, retRegsT_int_range n (nx + 1) nv, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    congr 1
    omega

/-- Integer values in the integer return registers `x0, x1, …` are in their typed return
registers. -/
theorem retRegsOk_of_int {vals : List Clif.Val} {us : List (Reg × Reg)}
    (hint : ∀ v ∈ vals, v.ty.isInt = true) (hlen : vals.length ≤ us.length)
    (hus : us.map (·.2) = (List.range us.length).map Reg.x) : RetRegsOk vals us := by
  refine ⟨List.replicate (us.length - vals.length) .int, ?_⟩
  have hv : vals.map (fun v => tyClass v.ty) = List.replicate vals.length .int := by
    apply List.eq_replicate_iff.mpr
    refine ⟨by simp, ?_⟩
    intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    have h := hint v hv
    revert h
    cases v.ty <;> simp [tyClass, Clif.Ty.isInt]
  rw [hv, List.replicate_append_replicate, Nat.add_sub_cancel' hlen, retRegsT_int_range, hus]
  simp

/-- **`IselSimT` from `IselSim`** for a function with integer returns: the run's realisation from
`IselSim`, the returned values' types from any `IselSimT` of the same function (a CLIF fact). -/
theorem iselSimT_of_iselSim {sem : Sem} {Γ : Rel} {env : Clif.Env} {p : Clif.Program}
    {f : Clif.Function} {vc vcK : VCode} (hE : IselSim sem Γ env p f vcK)
    (hT : IselSimT sem Γ env p f vc) (hint : f.sig.returns.all (·.ty.isInt) = true) :
    IselSimT sem Γ env p f vcK := by
  intro args cs w₀ ρ₀ hce hrel hargs htr fuel
  refine ⟨fun vals cm h => ?_, (hE args cs w₀ ρ₀ hce hrel hargs htr fuel).2⟩
  obtain ⟨us, outs, w, hv, hus, hlen, hph, hmr⟩ :=
    (hE args cs w₀ ρ₀ hce hrel hargs htr fuel).1 vals cm h
  obtain ⟨-, -, -, -, -, -, -, -, hty⟩ := (hT args cs w₀ ρ₀ hce hrel hargs htr fuel).1 vals cm h
  have hint' : ∀ v ∈ vals, v.ty.isInt = true := by
    intro v hv'
    have hm : v.ty ∈ vals.map (·.ty) := List.mem_map_of_mem hv'
    rw [hty] at hm
    obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
    rw [← he]
    exact List.all_eq_true.mp hint r hr
  exact ⟨us, outs, w, hv, retRegsOk_of_int hint' (by have := hph.1; omega) hus, hlen, hph, hmr,
    hty⟩

/-- **The typed CLIF → VCode layer for `skipStage f vc`** (`iselSimT_of_rules` for the code after
the skip of unused instructions). -/
theorem iselSimT_stage {p : Clif.Program} {f : Clif.Function} {vc : VCode}
    (hsub : InSubsetT p f) (hlow : lowerCheckT f vc = true)
    (hcfg : ∃ ss ps, vc.cfg = .ok (ss, ps))
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out : Nat} {env : Clif.Env}
    (hrules : LowerRulesCorrectTI Isle.Aarch64.program)
    (hrulesF : LowerRulesCorrectT Isle.Aarch64.program)
    (hrulesA : LowerRulesCorrectFT Isle.Aarch64.program)
    (hnE : NonEUnmatchableT Isle.Aarch64.program)
    (hcallRules : CallRulesCorrectT Isle.Aarch64.program)
    (hindRules : IndRulesCorrectT Isle.Aarch64.program)
    (hmemRules : MemRulesCorrectRTI Isle.Aarch64.program)
    (hmemF : MemRulesCorrectRT Isle.Aarch64.program)
    (htermRules : LowerTermRulesCorrectT Isle.Aarch64.program)
    (htermUn : TermUnmatchableT Isle.Aarch64.program)
    (hbranch : BranchRulesCorrectT Isle.Aarch64.program)
    (hbranchEx : BranchExcludedUnmatchableT Isle.Aarch64.program)
    (htryRules : TryRulesCorrectT Isle.Aarch64.program)
    (htryUn : TryUnmatchableT Isle.Aarch64.program)
    (htryIndRules : TryIndRulesCorrectT Isle.Aarch64.program)
    (htryIndUn : TryIndUnmatchableT Isle.Aarch64.program)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    (hFP : ∀ s, MemRefinesFP (fun _ => True) (F s) slotOff (sem s))
    (houtB : vc.outgoing ≤ out) :
    ∀ s, IselSimT (sem s) ⟨F s, syms, slotOff, out⟩ env p f (skipStage f vc) := by
  intro s
  have hT := iselSimT_of_rules hsub hlow hcfg hrules hrulesF hrulesA hnE hcallRules hindRules
    hmemRules hmemF htermRules htermUn hbranch hbranchEx htryRules htryUn htryIndRules htryIndUn
    hRef hds hcalls hicalls hmem hFP houtB s
  by_cases hE : (Compile.functionE f && lowerCheck f vc) = true
  · simp only [Bool.and_eq_true] at hE
    obtain ⟨hfE, hlc⟩ := hE
    have hsubE : InSubset p f :=
      ⟨hfE, hsub.externCalls, hsub.tryExterns, hsub.abiSigs, hsub.indSigs⟩
    obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hsk⟩ := skipStage_spec hlc
    exact iselSimT_of_iselSim
      (iselSim_of_driver_stage (Γ := ⟨F s, syms, slotOff, out⟩)
        (driverHyp_holds hsubE hlc hshape hcert hbr hcfg (hRef s) (hds s) (hcalls s) (hicalls s)
          (hmem s) houtB) hsk (hds s) (hmem s))
      hT (functionE_sig_int hfE).2
  · have he : skipStage f vc = vc := by
      unfold skipStage
      rw [if_neg hE]
    rw [he]
    exact hT

end E2E

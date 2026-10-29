import FV.E2E.FinalT
import FV.E2E.DeadCleanupFinal

/-!
# The typed dead-cleanup chain (S11e5 Stage C, slice 7)

The shipped route (`cargo fv --lean-link`) lowers, prunes dead pure producers
(`Backend.DeadCleanup.prune`) and prepares the pruned code; its semantics is the value semantics
`valueSem` (pure producers by their specification). For the typed movement scope:

* `CompiledCleanupT`/`CompiledCleanupAT` (`CompiledCleanup[A]` with `lowerCheckT`), integer
  `.toT`;
* `backend_correct_of_rules_cleanup_exT` (and `_ex_ofT` for integer returns: `ArmRefines`), from
  `iselSimT_of_rules` and `prune_correct`;
* at `valueSem`: `memRefinesFP_valueSem`, `backend_correct_m4_cleanup_exT`,
  `backend_correct_final_cleanup_exT`, `backend_correct_final_cleanupT` (`ArmRefinesT` under
  `TypedRules`), and the integer specialization `backend_correct_final_cleanup_ofT`
  (`backend_correct_final_cleanup`'s premises and conclusion through the typed chain).
-/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- `CompiledCleanup` with the typed lowering validator. -/
structure CompiledCleanupT (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc)
    (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheckT f vc = true
  prepare : prepare (Backend.DeadCleanup.prune vc) = .ok vcp
  prepOk : prepCheck (Backend.DeadCleanup.prune vc) vcp = true
  check : checkAlloc vcp rf = .ok ()
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

/-- `CompiledCleanupA` with the typed lowering validator. -/
structure CompiledCleanupAT (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc)
    (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheckT f vc = true
  prepare : prepare (Backend.DeadCleanup.prune vc) = .ok vcp
  prepOk : prepCheck (Backend.DeadCleanup.prune vc) vcp = true
  check : AllocChecked vcp rf
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

theorem CompiledCleanupT.toA {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupT f k vc vcp rf af fa fb) :
    CompiledCleanupAT f k vc vcp rf af fa fb :=
  ⟨hc.lower, hc.lowerOk, hc.prepare, hc.prepOk, allocChecked_of_checkAlloc hc.check, hc.alloc,
    hc.emit, hc.layout⟩

/-- **Integer specialization.** -/
theorem CompiledCleanup.toT {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanup f k vc vcp rf af fa fb) :
    CompiledCleanupT f k vc vcp rf af fa fb :=
  ⟨hc.lower, lowerCheckT_of_lowerCheck hc.lowerOk, hc.prepare, hc.prepOk, hc.check, hc.alloc,
    hc.emit, hc.layout⟩

theorem CompiledCleanupA.toT {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupA f k vc vcp rf af fa fb) :
    CompiledCleanupAT f k vc vcp rf af fa fb :=
  ⟨hc.lower, lowerCheckT_of_lowerCheck hc.lowerOk, hc.prepare, hc.prepOk, hc.check, hc.alloc,
    hc.emit, hc.layout⟩

theorem cfg_of_prepare_prune {vc vcp : VCode} (h : prepare (Backend.DeadCleanup.prune vc) = .ok vcp) :
    ∃ ss ps, vc.cfg = .ok (ss, ps) := by
  obtain ⟨ss, ps, he⟩ := cfg_of_prepare h
  exact ⟨ss, ps, (prune_cfg vc).symm.trans he⟩

/-- Pruning then preparing preserves returns and traps (`prune_correct`, `prepCheck`). -/
theorem prepareCorrect_prune {sem : Sem} {vc vcp : VCode} (hds : DriverSem sem)
    (hPure : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hCmp : CmpOverwrite sem)
    (h : prepCheck (Backend.DeadCleanup.prune vc) vcp = true) : PrepareCorrect sem vc vcp :=
  fun a w => by
    obtain ⟨hr, ht⟩ := prune_correct (vc := vc) hPure hCmp a w
    obtain ⟨pr, pt⟩ := prepareCorrect_of_check hds h a w
    exact ⟨fun _ _ _ h => pr _ _ _ (hr _ _ _ h), fun _ h => pt _ (ht _ h)⟩

/-- **The typed dead-cleanup `backend_correct`** from the typed rule families (`ArmRefinesT`). -/
theorem backend_correct_of_rules_cleanup_exT {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT p f) (hc : CompiledCleanupAT f k vc vcp rf af fa fb) (hT : TypedRules)
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    (hrulesF : LowerRulesCorrectT Isle.Aarch64.program)
    (hrulesA : LowerRulesCorrectFT Isle.Aarch64.program)
    (hmemF : MemRulesCorrectRT Isle.Aarch64.program)
    (hM6 : RegLevelCorrectEx sem F K astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    (hFP : ∀ s, MemRefinesFP (fun _ => True) (F s) slotOff (sem s))
    (hPure : ∀ s i us w outs w' ctl, pureForm i = true →
      sem s i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hCmp : ∀ s, CmpOverwrite (sem s))
    (houtB : vc.outgoing ≤ out)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesT fb base ra astep s (Clif.runLoop env p fuel cs) :=
  backend_correct_of_layers_exT
    (iselSimT_of_rules hsub hc.lowerOk (cfg_of_prepare_prune hc.prepare)
      lowerRulesCorrectTI_program hrulesF hrulesA nonEUnmatchableT_program hT.callsT hT.indT
      memRulesCorrectRTI_program hmemF hT.term hT.termUn hT.branch hT.branchEx hT.tryT
      hT.tryUn hT.tryIndT hT.tryIndUn hRef hds hcalls hicalls hmem hFP houtB)
    (fun s' => prepareCorrect_prune (hds s') (hPure s') (hCmp s') hc.prepOk)
    hM6 hent hres hbe
    (argsAtEntry_bodyT (lowerRFunc_frame hc.alloc) (entryRegsT_of_check hc.lowerOk) hbe hargs hargF hres)
    hcs hrel htr fuel

/-- **Integer returns**: the typed dead-cleanup chain gives `ArmRefines`. -/
theorem backend_correct_of_rules_cleanup_ex_ofT {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT p f) (hc : CompiledCleanupAT f k vc vcp rf af fa fb) (hT : TypedRules)
    (hint : f.sig.returns.all (·.ty.isInt) = true)
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    (hrulesF : LowerRulesCorrectT Isle.Aarch64.program)
    (hrulesA : LowerRulesCorrectFT Isle.Aarch64.program)
    (hmemF : MemRulesCorrectRT Isle.Aarch64.program)
    (hM6 : RegLevelCorrectEx sem F K astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    (hFP : ∀ s, MemRefinesFP (fun _ => True) (F s) slotOff (sem s))
    (hPure : ∀ s i us w outs w' ctl, pureForm i = true →
      sem s i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hCmp : ∀ s, CmpOverwrite (sem s))
    (houtB : vc.outgoing ≤ out)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs) :=
  backend_correct_of_layers_ex_ofT hint
    (iselSimT_of_rules hsub hc.lowerOk (cfg_of_prepare_prune hc.prepare)
      lowerRulesCorrectTI_program hrulesF hrulesA nonEUnmatchableT_program hT.callsT hT.indT
      memRulesCorrectRTI_program hmemF hT.term hT.termUn hT.branch hT.branchEx hT.tryT
      hT.tryUn hT.tryIndT hT.tryIndUn hRef hds hcalls hicalls hmem hFP houtB)
    (fun s' => prepareCorrect_prune (hds s') (hPure s') (hCmp s') hc.prepOk)
    hM6 hent hres hbe
    (argsAtEntry_bodyT (lowerRFunc_frame hc.alloc) (entryRegsT_of_check hc.lowerOk) hbe hargs hargF hres)
    hcs hrel htr fuel

/-- The float loads/stores of the value semantics are `csem`'s (they are not pure forms). -/
theorem memRefinesFP_valueSem (Rd F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) {sb : Nat}
    (hsb : ctx.slotBase = sb) : MemRefinesFP Rd F sb (valueSem F ctx X) := by
  obtain ⟨h1, h2⟩ := memRefinesFP_csem Rd F ctx X hsb
  refine ⟨fun sz d am fl us w a hsz ha hav hrd => ?_, fun sz d am fl v us w a hsz ha hav => ?_⟩
  · obtain ⟨w', e, hw⟩ := h1 sz d am fl us w a hsz ha hav hrd
    exact ⟨w', by simp only [valueSem, specForm, pureForm, cmpForm, Bool.false_or]; exact e, hw⟩
  · obtain ⟨w', e, hw⟩ := h2 sz d am fl v us w a hsz ha hav
    exact ⟨w', by simp only [valueSem, specForm, pureForm, cmpForm, Bool.false_or]; exact e, hw⟩

theorem hasTry_of_hasTryCallCleanupAT {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupAT f k vc vcp rf af fa fb)
    (h : vcp.hasTryCall = true) : ∃ B ∈ f.blocks, B.term.isTry = true :=
  Classical.byContradiction fun hn => by
    have hf : ∀ B ∈ f.blocks, B.term.isTry = false := fun B hB =>
      Bool.eq_false_iff.mpr fun ht => hn ⟨B, hB, ht⟩
    rw [noTryCall_of_prepCheck hc.prepOk (prune_noTryCall (noTryCallT_of_check hc.lowerOk hf))] at h
    cases h

theorem hasTls_of_vcodeCleanupAT {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupAT f k vc vcp rf af fa fb)
    (h : vcp.hasTls = true) : hasTls f = true := by
  cases hf : hasTls f
  · rw [noTls_of_prepCheck hc.prepOk (prune_noTls (noTlsT_of_check hc.lowerOk hf))] at h
    cases h
  · rfl

theorem outgoing_le_intBaseCleanupAT {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupAT f k vc vcp rf af fa fb) :
    vc.outgoing ≤ (RAFrame.compute vcp rf).intBase := by
  simp only [RAFrame.compute]
  rw [outgoing_of_prepCheck hc.prepOk, prune_outgoing]
  exact le_alignTo _ 16 (by decide)

set_option maxHeartbeats 1000000 in
/-- The stack-passed arguments avoid the addresses outside the world, from the allocation's
frame alone (`stackArgsAvoid_frameWA`'s argument). -/
theorem stackArgsAvoid_frameW_of_alloc {f : Clif.Function} {vcp : VCode} {rf : RFunc}
    {af : AFunc} {fb : FnBin} (halloc : lowerRFunc vcp rf = .ok af) {K : Nat}
    {s : Arm.ArmState} {base ra : BitVec 64} {args : List Clif.Val} (hres : StackAvail K af s)
    (_hent : AbiEntry fb base ra s) (hargs : ArgsIn f.sig args s) :
    StackArgsAvoid (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
      f.sig args s := by
  intro off v hm j hj hF
  have h := hargs _ _ hm
  simp only at h
  have hframe := lowerRFunc_frame halloc
  have hfs := (lowerRFunc_ok halloc).1.1
  have hD : frameDrop af = af.frameSize + 16 := by simp [frameDrop, hframe]
  have hsz : (RAFrame.compute vcp rf).size ≤ af.frameSize := by
    have e : (RAFrame.compute vcp rf).total =
        alignTo ((RAFrame.compute vcp rf).size + vcp.slotBytes) 16 +
          clobberBytes rf.saved := rfl
    rw [hfs, e]
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (le_alignTo16 _))
      (Nat.le_add_right _ _)
  have hsp := hres.1.1
  have hfit := h.fits
  have hx : (spv s + BitVec.ofNat 64 off + BitVec.ofNat 64 j -
      (spv s - BitVec.ofNat 64 (frameDrop af))).toNat = off + j + frameDrop af := by
    rw [hD]
    bv_omega
  rcases hF with (⟨-, h2⟩ | ⟨-, h2⟩ | hcode) | ⟨hlt, -⟩
  · rw [hx] at h2; omega
  · rw [hx] at h2; omega
  · have e : spv s + BitVec.ofNat 64 off + BitVec.ofNat 64 j = spv s + BitVec.ofNat 64 (off + j) := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
    rw [e] at hcode
    exact h.noCode j hj hcode
  · rw [(spBody_toNat hres).1] at hlt
    have : (spv s + BitVec.ofNat 64 off + BitVec.ofNat 64 j).toNat = (spv s).toNat + off + j := by
      bv_omega
    omega

/-- **The typed M4 assembly of the dead-cleanup route at `valueSem`.** -/
theorem backend_correct_m4_cleanup_exT {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT p f) (hc : CompiledCleanupAT f k vc vcp rf af fa fb) (hT : TypedRules)
    {F : Arm.ArmState → BitVec 64 → Prop} {ctx : Arm.ArmState → FnCtx}
    {X : Arm.ArmState → ExtSem}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    (hM6 : RegLevelCorrectEx (fun s => valueSem (F s) (ctx s) (X s)) F K astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (valueSem (F s) (ctx s) (X s)))
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    (hXI : ∀ s, XCallsIndOk env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    (hsym : ∀ s n b, syms n = some b → (X s).sym n 0 = BitVec.ofNat 64 b)
    (hmem : ∀ s, MemRefines (F s) slotOff syms (valueSem (F s) (ctx s) (X s)))
    (hslotB : ∀ s, (ctx s).slotBase = slotOff)
    (houtB : vc.outgoing ≤ out)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesT fb base ra astep s (Clif.runLoop env p fuel cs) :=
  backend_correct_of_rules_cleanup_exT hsub hc hT lowerRulesCorrectT_program
    lowerRulesCorrectFT_program memRulesCorrectRT_program hM6 hRef
    (fun s' => driverSem_valueSem (F s') (ctx s') (X s'))
    (fun s' => callsRefine_valueSem (hX s'))
    (fun s' => indCallsRefine_valueSem (hXI s') (hsym s') (fun _ _ _ h => h.1.symbols)) hmem
    (fun s' => memRefinesFP_valueSem _ (F s') (ctx s') (X s') (hslotB s'))
    (fun _ _ _ _ _ _ _ hp he => valueSem_pure hp he) (fun _ => valueSem_cmpOverwrite _ _ _) houtB
    hent hres hbe hargs hargF hcs hrel htr fuel

/-- **The typed final theorem of the dead-cleanup route** (`backend_correct_final_cleanup_ex`
for the typed scope; `ArmRefinesT` under `TypedRules`). -/
theorem backend_correct_final_cleanup_exT {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT p f) (hc : CompiledCleanupAT f k vc vcp rf af fa fb) (hT : TypedRules)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesT fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=
  backend_correct_m4_cleanup_exT (ctx := fun _ => ⟨fa.k, af.slotBase⟩) (X := fun _ => X) hsub hc hT
    (regLevelCorrect_backend_ex_value hc.check hc.alloc hc.emit hc.layout hcov hC
      (fun h => hCT (hasTry_of_hasTryCallCleanupAT hc h))
      (fun h => hTls (hasTls_of_vcodeCleanupAT hc h)))
    (fun _ => refines_valueSem _ _ X) hX hXI (fun _ => hsym)
    (fun _ => memRefines_valueSem _ _ X hslot hsym) (fun _ => hslot)
    (outgoing_le_intBaseCleanupAT hc)
    hent hres hbe hargs (stackArgsAvoid_frameW_of_alloc hc.alloc hres hent hargs) hcs hrel htr fuel

/-- **The typed final theorem of the dead-cleanup route** (`CompiledCleanupT`). -/
theorem backend_correct_final_cleanupT {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT p f) (hc : CompiledCleanupT f k vc vcp rf af fa fb) (hT : TypedRules)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesT fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=
  backend_correct_final_cleanup_exT hsub hc.toA hT hcov hC hCT hTls hX hXI hsym hslot hent hres
    hbe hargs hcs hrel htr fuel

/-- **Integer specialization of the typed dead-cleanup final theorem**:
`backend_correct_final_cleanup`'s premises and conclusion (`ArmRefines`) through the typed
chain. -/
theorem backend_correct_final_cleanup_ofT {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb) (hT : TypedRules)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  have hcA := hc.toT.toA
  exact backend_correct_of_rules_cleanup_ex_ofT hsub.toT hcA hT (functionE_sig_int hsub.subsetE).2
    lowerRulesCorrectT_program lowerRulesCorrectFT_program memRulesCorrectRT_program
    (regLevelCorrect_backend_ex_value hcA.check hcA.alloc hcA.emit hcA.layout hcov hC
      (fun h => hCT (hasTry_of_hasTryCallCleanupAT hcA h))
      (fun h => hTls (hasTls_of_vcodeCleanupAT hcA h)))
    (fun _ => refines_valueSem _ _ X)
    (fun _ => driverSem_valueSem _ _ X)
    (fun s' => callsRefine_valueSem (hX s'))
    (fun s' => indCallsRefine_valueSem (hXI s') hsym (fun _ _ _ h => h.1.symbols))
    (fun _ => memRefines_valueSem _ _ X hslot hsym)
    (fun _ => memRefinesFP_valueSem _ _ _ X hslot)
    (fun _ _ _ _ _ _ _ hp he => valueSem_pure hp he) (fun _ => valueSem_cmpOverwrite _ _ _)
    (outgoing_le_intBaseCleanupAT hcA)
    hent hres hbe hargs (stackArgsAvoid_frameW_of_alloc hcA.alloc hres hent hargs) hcs hrel htr fuel

end E2E

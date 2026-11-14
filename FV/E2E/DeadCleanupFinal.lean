import FV.E2E.Final
import FV.E2E.DeadCleanupPipeline
import FV.E2E.DeadCleanupContracts
import FV.E2E.DeadCleanupRegLevel

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

theorem backend_correct_m4_cleanup_exL {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupAL f k vc vcp rf af fa fb)
    {F : Arm.ArmState → BitVec 64 → Prop} {ctx : Arm.ArmState → FnCtx}
    {X : Arm.ArmState → ExtSem}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    -- M6 + M5
    (hM6 : RegLevelCorrectEx (fun s => valueSem (F s) (ctx s) (X s)) F K astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (valueSem (F s) (ctx s) (X s)))
    -- the external contract (callees of `f`, linker)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    -- the external contract of the indirect calls (their call-site signatures `indSigs f`;
    -- vacuous without indirect calls, `xCallsIndOk_nil`) and the linker's symbol addresses
    (hXI : ∀ s, XCallsIndOk env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    (hsym : ∀ s n b, syms n = some b → (X s).sym n 0 = BitVec.ofNat 64 b)
    (hmem : ∀ s, MemRefines (F s) slotOff syms (valueSem (F s) (ctx s) (X s)))
    -- the relation's outgoing stack-argument area holds every call's stack arguments
    (houtB : vc.outgoing ≤ out)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs) :=
  backend_correct_of_rules_cleanup_exL hsub hc
    lowerRulesCorrect_program excludedUnmatchable callRulesCorrect indRulesCorrect
    memRulesCorrect_program lowerTermRulesCorrect termUnmatchable branchRulesCorrect
    branchExcludedUnmatchable tryRulesCorrect tryUnmatchable tryIndRulesCorrect tryIndUnmatchable
    hM6 hRef (fun s' => driverSem_valueSem (F s') (ctx s') (X s'))
    (fun s' => callsRefine_valueSem (hX s'))
    (fun s' => indCallsRefine_valueSem (hXI s') (hsym s') (fun _ _ _ h => h.1.symbols)) hmem (fun _ _ _ _ _ _ _ hp he => valueSem_pure hp he) (fun _ => valueSem_cmpOverwrite _ _ _) houtB
    hent hres hbe hargs hargF hcs hrel htr fuel

theorem backend_correct_m4_cleanup_ex {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    {F : Arm.ArmState → BitVec 64 → Prop} {ctx : Arm.ArmState → FnCtx}
    {X : Arm.ArmState → ExtSem}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    -- M6 + M5
    (hM6 : RegLevelCorrectEx (fun s => valueSem (F s) (ctx s) (X s)) F K astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (valueSem (F s) (ctx s) (X s)))
    -- the external contract (callees of `f`, linker)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    -- the external contract of the indirect calls (their call-site signatures `indSigs f`;
    -- vacuous without indirect calls, `xCallsIndOk_nil`) and the linker's symbol addresses
    (hXI : ∀ s, XCallsIndOk env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    (hsym : ∀ s n b, syms n = some b → (X s).sym n 0 = BitVec.ofNat 64 b)
    (hmem : ∀ s, MemRefines (F s) slotOff syms (valueSem (F s) (ctx s) (X s)))
    -- the relation's outgoing stack-argument area holds every call's stack arguments
    (houtB : vc.outgoing ≤ out)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs) :=
  backend_correct_m4_cleanup_exL hsub hc.toL hM6 hRef hX hXI hsym hmem houtB hent hres hbe hargs hargF
    hcs hrel htr fuel

theorem hasTry_of_hasTryCallCleanupAL {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupAL f k vc vcp rf af fa fb)
    (h : vcp.hasTryCall = true) : ∃ B ∈ f.blocks, B.term.isTry = true :=
  Classical.byContradiction fun hn => by
    have hf : ∀ B ∈ f.blocks, B.term.isTry = false := fun B hB =>
      Bool.eq_false_iff.mpr fun ht => hn ⟨B, hB, ht⟩
    rw [noTryCall_of_prepCheck hc.prepOk
      (cleanupStage_noTryCall f (noTryCall_of_check hc.lowerOk hf))] at h
    cases h

theorem hasTry_of_hasTryCallCleanupA {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    (h : vcp.hasTryCall = true) : ∃ B ∈ f.blocks, B.term.isTry = true :=
  hasTry_of_hasTryCallCleanupAL hc.toL h

theorem hasTls_of_vcodeCleanupAL {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupAL f k vc vcp rf af fa fb)
    (h : vcp.hasTls = true) : hasTls f = true := by
  cases hf : hasTls f
  · rw [noTls_of_prepCheck hc.prepOk (cleanupStage_noTls f (noTls_of_check hc.lowerOk hf))] at h
    cases h
  · rfl

theorem hasTls_of_vcodeCleanupA {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    (h : vcp.hasTls = true) : hasTls f = true :=
  hasTls_of_vcodeCleanupAL hc.toL h

theorem outgoing_le_intBaseCleanupAL {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupAL f k vc vcp rf af fa fb) :
    vc.outgoing ≤ (RAFrame.compute vcp rf).intBase := by
  simp only [RAFrame.compute]
  rw [outgoing_of_prepCheck hc.prepOk, cleanupStage_outgoing]
  exact le_alignTo _ 16 (by decide)

theorem outgoing_le_intBaseCleanupA {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupA f k vc vcp rf af fa fb) :
    vc.outgoing ≤ (RAFrame.compute vcp rf).intBase :=
  outgoing_le_intBaseCleanupAL hc.toL

set_option maxHeartbeats 1000000 in
theorem stackArgsAvoid_frameWCleanupA {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupA f k vc vcp rf af fa fb) {K : Nat}
    {s : Arm.ArmState} {base ra : BitVec 64} {args : List Clif.Val} (hres : StackAvail K af s)
    (_hent : AbiEntry fb base ra s) (hargs : ArgsIn f.sig args s) :
    StackArgsAvoid (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
      f.sig args s := by
  intro off v hm j hj hF
  have h := hargs _ _ hm
  simp only at h
  have hframe := lowerRFunc_frame hc.alloc
  have hfs := (lowerRFunc_ok hc.alloc).1.1
  have hD : frameDrop af = af.frameSize + 16 := by simp [frameDrop, hframe]
  have hsz : (RAFrame.compute vcp rf).size ≤ af.frameSize := by
    have e : (RAFrame.compute vcp rf).total =
        alignTo ((RAFrame.compute vcp rf).size + vcp.slotBytes) 16 +
          clobberBytes rf.saved := rfl
    rw [(lowerRFunc_ok hc.alloc).1.1, e]
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

theorem stackArgsAvoid_frameWCleanupAL {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupAL f k vc vcp rf af fa fb) {K : Nat}
    {s : Arm.ArmState} {base ra : BitVec 64} {args : List Clif.Val} (hres : StackAvail K af s)
    (_hent : AbiEntry fb base ra s) (hargs : ArgsIn f.sig args s) :
    StackArgsAvoid (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
      f.sig args s := by
  cases hf : af.frame
  · intro off v hm
    obtain ⟨r, hr⟩ := regArgsB_spec (hc.leaf hf).2 _ (List.of_mem_zip hm).1
    cases hr
  · exact stackArgsAvoid_frameWCleanupA (hc.toA hf) hres _hent hargs

theorem backend_correct_final_cleanup_exL {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupAL f k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    -- the straight-line forms of the prepared VCode are covered (decided by `formsCoveredB`)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    -- the callee contract of the machine's call hook (AAPCS64)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    -- the callee contract of the call of a `try_call` (only for a function with one)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    -- the TLSDESC contract of the machine's `tls_value` hook (only for a function with one)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    -- the external contract (callees of `f`, linker)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    -- the external contract of the indirect calls of `f` (`call_indirect`, `try_call_indirect`:
    -- the externs at their link-time addresses, with the call sites' signatures; vacuous
    -- without indirect calls, `xCallsIndOk_nil`)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    -- memory forms (`memRefines_valueSem`): the external semantics' symbol addresses are the linked
    -- ones, and the relation's slot-region offset is the frame's slot base
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=
  backend_correct_m4_cleanup_exL (ctx := fun _ => ⟨fa.k, af.slotBase⟩) (X := fun _ => X) hsub hc
    (regLevelCorrect_backend_ex_value hc.check hc.alloc (fun hf => (hc.leaf hf).1) hc.emit hc.layout hcov hC
      (fun h => hCT (hasTry_of_hasTryCallCleanupAL hc h)) (fun h => hTls (hasTls_of_vcodeCleanupAL hc h)))
    (fun _ => refines_valueSem _ _ X) hX hXI (fun _ => hsym)
    (fun _ => memRefines_valueSem _ _ X hslot hsym) (outgoing_le_intBaseCleanupAL hc)
    hent hres hbe hargs (stackArgsAvoid_frameWCleanupAL hc hres hent hargs) hcs hrel htr fuel

theorem backend_correct_final_cleanup_ex {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    -- the straight-line forms of the prepared VCode are covered (decided by `formsCoveredB`)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    -- the callee contract of the machine's call hook (AAPCS64)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    -- the callee contract of the call of a `try_call` (only for a function with one)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    -- the TLSDESC contract of the machine's `tls_value` hook (only for a function with one)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    -- the external contract (callees of `f`, linker)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    -- the external contract of the indirect calls of `f` (`call_indirect`, `try_call_indirect`:
    -- the externs at their link-time addresses, with the call sites' signatures; vacuous
    -- without indirect calls, `xCallsIndOk_nil`)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    -- memory forms (`memRefines_valueSem`): the external semantics' symbol addresses are the linked
    -- ones, and the relation's slot-region offset is the frame's slot base
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=
  backend_correct_final_cleanup_exL hsub hc.toL hcov hC hCT hTls hX hXI hsym hslot
    hent hres hbe hargs hcs hrel htr fuel


theorem backend_correct_final_cleanup {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    -- the straight-line forms of the prepared VCode are covered (decided by `formsCoveredB`)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    -- the callee contract of the machine's call hook (AAPCS64)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    -- the callee contract of the call of a `try_call` (only for a function with one)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    -- the TLSDESC contract of the machine's `tls_value` hook (only for a function with one)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    -- the external contract (callees of `f`, linker)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    -- the external contract of the indirect calls of `f` (`call_indirect`, `try_call_indirect`:
    -- the externs at their link-time addresses, with the call sites' signatures; vacuous
    -- without indirect calls, `xCallsIndOk_nil`)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    -- memory forms (`memRefines_csem`): the external semantics' symbol addresses are the linked
    -- ones, and the relation's slot-region offset is the frame's slot base
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=

  backend_correct_final_cleanup_ex hsub hc.toA hcov hC hCT hTls hX hXI hsym hslot
    hent hres hbe hargs hcs hrel htr fuel

/-- **The backend theorem with frameless leaves (#1028)**: `backend_correct_final_cleanup` for an
allocated function that is `lowerRFunc`'s output or, under `preserve_frame_pointers=false`, that
output without its frame (`CompiledCleanupL`: `AllocAF`; without a frame the compiled code passes
`FnAsm.leafChk`, so it names neither `x29` nor `x30` but in `ret` and makes no call, and every
argument is in a register). The normal-return form: a function without calls is unwound through
by no exception. -/
theorem backend_correct_final_cleanup_leaf {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupL f k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    -- the straight-line forms of the prepared VCode are covered (decided by `formsCoveredB`)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    -- the callee contract of the machine's call hook (AAPCS64)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    -- the callee contract of the call of a `try_call` (only for a function with one)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    -- the TLSDESC contract of the machine's `tls_value` hook (only for a function with one)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    -- the external contract (callees of `f`, linker)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    -- the external contract of the indirect calls of `f` (`call_indirect`, `try_call_indirect`:
    -- the externs at their link-time addresses, with the call sites' signatures; vacuous
    -- without indirect calls, `xCallsIndOk_nil`)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    -- memory forms (`memRefines_csem`): the external semantics' symbol addresses are the linked
    -- ones, and the relation's slot-region offset is the frame's slot base
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=
  backend_correct_final_cleanup_exL hsub hc.toA hcov hC hCT hTls hX hXI hsym hslot
    hent hres hbe hargs hcs hrel htr fuel


end E2E

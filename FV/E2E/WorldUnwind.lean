import FV.E2E.WorldUnwindReg
import FV.E2E.WorldUnwindGot
import FV.E2E.DeadCleanupUnwind
import FV.E2E.DeadCleanupUnwindIsel
import FV.E2E.IselSimU
import FV.Backend.Proof.LowerSimUCheck
import FV.E2E.DeadCleanupWorld
import FV.E2E.CompiledEither

/-!
# The per-function world theorem with unwinding (S10f, #233)

`backend_correct_world_pipeline` (`FV/E2E/CompiledEither.lean`, what `FV/E2E/LinkArm.lean`
links) for the runs with unwinding (`Clif.runLoopX`) and the machine with unwinding
(`Unw.ArmStepU X H U T fa`), for both pipelines: the shipped dead-cleanup one (value semantics
with unwinding, `valueSemU`) and the legacy one (`csemU`).

* `ActEntryU`: `ActEntry` and the raising callees' contract `CalleeUnwOkG` (relative to `G`).
* `iselSimU_relW_cleanup`: CLIF → VCode with unwinding for the memory relation of an activation
  inside a linked program (`RelW`), by `driver_correctU`. An exceptional end of the CLIF run
  (`unwound e cm`) is a VCode run ending at a raising call (`VUnwinds`) with the exception object
  (`ExnRel`) and the world `w` after the unwinder restored that call, and `MemRel F syms cm w`:
  the CLIF memory after the frame's slots are freed and the frame is left (`cm = (cm0.free
  slots).leave`) is related to that world as the memory at the raising call (`cm0`) is
  (`memRel_free`, `memRel_leave`; the freed slots are in the frame, inside `F`).
* **`backend_correct_world_cleanupU`**, `backend_correct_worldU` (legacy, with
  `iselSimU_relW`), **`backend_correct_world_pipelineU`** (`CompiledEither`): for a returning
  CLIF run, one VCode outcome every activation (`ActEntryU`) realises (`ActRet`, `PostTrace`, the
  last step not leaving the frame by unwinding: the return is the epilogue's, not an `UnwExit`);
  for a trapping one, `TrapAt`; for an exceptional end, the exception object and the world after
  the unwinder restored the raising call, related to the CLIF memory, which every activation
  realises: `ActUnw` (an AAPCS64 return to the caller with the object in x0, the memory outside
  `F` that world's, `G` and the program kept), `PostTrace`, and the last step leaving the frame
  by unwinding (`UnwExit`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.UnwindTables Backend.DeadCleanup

/-- **What an Arm activation of the compiled function needs with unwinding**: `ActEntry` and the
raising callees' contract (relative to the kept addresses `G`). -/
structure ActEntryU (vcp : VCode) (rf : RFunc) (af : AFunc) (fa : FnAsm) (fb : FnBin) (K : Nat)
    (F G : BitVec 64 → Prop) (X : ExtSem) (H : ArmHooks) (XR : XRaise) (U : Unw.UnwHooks)
    (base ra : BitVec 64) (s w₀ : Arm.ArmState) : Prop
    extends ActEntry vcp rf af fa fb K F G X H base ra s w₀ where
  unw : CalleeUnwOkG F K G s (CallAt fa base) X XR U vcp.CallSite (GotV vcp)

/-- **CLIF → VCode with unwinding for an activation inside a linked program** (`RelW`; the
dead-cleanup pipeline's lowering, value semantics with unwinding). -/
theorem iselSimU_relW_cleanup {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {args : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ us outs w, VReturns vc (valueSemU F ⟨fa.k, af.slotBase⟩ X XR) ρ₀ w₀ us outs w ∧
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w) ∧
    (∀ c', Clif.runLoopX env p fuel cs.toX = .trapped c' →
      VTraps vc (valueSemU F ⟨fa.k, af.slotBase⟩ X XR) ρ₀ w₀ c') ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ obj w, VUnwinds vc (valueSemU F ⟨fa.k, af.slotBase⟩ X XR) XR ρ₀ w₀ obj w ∧
        ExnRel e obj ∧ MemRel F syms cm w) := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hUs⟩ := loweringU_of_check hlU
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  let sem := valueSemU F ⟨fa.k, af.slotBase⟩ X XR
  have hRef : Refines F sem := refines_valueSemU _ _ X XR
  have hmem : MemRefines F slotOff syms sem := memRefines_valueSemU _ _ X XR hslot hsym
  have hcalls := callsRefine_valueSemU (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hX hexcl
  have hicalls := indCallsRefine_valueSemU (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hXI hsym
    (fun _ _ _ h => h.1.1.symbols) hexcl
  have houtB := outgoing_le_intBaseCleanupA hc.toA
  have H : DriverHyp f vc ctx st0 R gn bl A sem (RelW Γ f c) env.toEnv p := {
    shape := hshape
    cert := hcert
    dsem := (driverSem_valueSemU F ⟨fa.k, af.slotBase⟩ X XR).toDriverSemG
    insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
      indRulesCorrect memRulesCorrect_program hRef (mrStable_relW Γ f c) hcalls hicalls hmem
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
    tries := ⟨_, tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) hcalls, tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef (mrStable_relW Γ f c)
      hmem (outArgsOk_relW Γ f c) (indStack_mono (indStack_of_check hc.lowerOk) houtB) hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := by
      obtain ⟨ss, ps, he⟩ := cfg_of_prepare hc.prepare
      exact ⟨ss, ps, (prune_cfg vc).symm.trans he⟩ }
  have HR : RaiseHyp f sem (RelW Γ f c) env F X XR slotOff syms (RAFrame.compute vcp rf).intBase :=
    ⟨raiseSem_valueSemU _ _ X XR, hRef, hmem, mrStable_relW Γ f c, outArgsOk_relW Γ f c,
      memRelOk_relW Γ f c, callsStack_mono (callsStack_of_check hc.lowerOk) houtB,
      tryStack_mono (tryStack_of_check hc.lowerOk) houtB,
      indStack_mono (indStack_of_check hc.lowerOk) houtB, hXR, hXRi, hsym,
      fun sl cm w h => (memRelOk_relW Γ f c).symbols sl cm w h⟩
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hrun := driver_correctU H hUs HR (driverSem_valueSemU F ⟨fa.k, af.slotBase⟩ X XR) hB0
    hce.callers hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs htr fuel
  refine ⟨fun vals cm h => ?_, fun c' h => ?_, fun e cm h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1.1 _)⟩
  · rw [h] at hrun
    exact hrun
  · rw [h] at hrun
    obtain ⟨obj, w, cm0, hu, hex, h4, h5⟩ := hrun
    exact ⟨obj, w, hu, hex, h5 ▸ memRel_leave (memRel_free h4.1.1 _)⟩

/-- **The per-function world theorem with unwinding** (`backend_correct_world_cleanup` with the
exceptional edge; the shipped dead-cleanup pipeline). -/
theorem backend_correct_world_cleanupU {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    -- the tables the unwinder reads (the emitted ones) and the decidable checks
    {T : Unw.FnTables} {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry))) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hpad : padsNonzeroB af fa = true)
    (hlast : lastCallsOk af fa = true) (hsaved : savedCheck vcp rf = true)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
            ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s)) ∧
    (∀ c', Clif.runLoopX env p fuel cs.toX = .trapped c' →
      ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
        (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (Unw.ArmStepU X H U T fa) n s)) ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ (obj : BitVec 64) (w : Arm.ArmState), ExnRel e obj ∧ MemRel F syms cm w ∧
        ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActUnw ra F G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
            UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s)) := by
  have hI := iselSimU_relW_cleanup hsub hc hlU hX hXI hXR hXRi hexcl hsym hslot (fun _ => 0) hcs
    hrel hargs htr fuel
  have hP := prepareCorrectU_cleanup (driverSem_valueSemU F ⟨fa.k, af.slotBase⟩ X XR)
    (fun _ _ _ _ _ _ hp he => valueSemU_pure hp he) (valueSemU_cmpOverwrite _ _ _ _) hc.prepOk XR
  have hM6 : ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
      (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ → _ :=
    fun H U G base ra s he => by
      have h := regLevelCorrect_worldUT hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
        (XR := XR) (U := U) (T := T) (K := K) (G := G) (gv := GotV vcp) he.abi he.stack he.gfree
        (gotSem_valueSemVU _ _ _ _ _)
        (realizes_valueU_world hcov (by rw [he.hF]; exact he.calls) (by rw [he.hF]; exact he.tries)
          (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.unw) hsites hlsda hpad hlast)
        (fun us uses w => by rw [valueSemVU_rets])
        (fun _ _ _ _ _ ht h => valueSemVU_halt_trap ht h) (by rw [he.hF]; exact he.unw)
        hsites hlsda hlast hrows hcie hfde hsaved (by rw [he.hF]; exact he.body) (fun _ => 0)
      rw [he.hF] at h
      exact h
  refine ⟨fun vals cm hrun => ?_, fun c' hrun H U G base ra s he => ?_,
    fun e cm hrun => ?_⟩
  · obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
    have hrs : vc.RetsSite us := by
      obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
      exact ⟨b, vb, k, hvb, hk⟩
    refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H U G base ra s he => ?_⟩
    exact (hM6 H U G base ra s he).1 us outs w
      (vReturns_gotV_gen (gotPair_valueU _ _ _) ((hP.1 _ _).1 _ _ _ hv))
  · exact (hM6 H U G base ra s he).2.1 c'
      (vTraps_gotV_gen (gotPair_valueU _ _ _) ((hP.1 _ _).2 c' (hI.2.1 c' hrun)))
  · obtain ⟨obj, w, hv, hex, hmemR⟩ := hI.2.2 e cm hrun
    exact ⟨obj, w, hex, hmemR, fun H U G base ra s he =>
      (hM6 H U G base ra s he).2.2 obj w
        (vUnwinds_gotV_gen (gotPair_valueU _ _ _) (hP.2 _ _ _ _ hv))⟩

/-- **The per-function world theorem with unwinding** (`backend_correct_world_cleanup` with the
exceptional edge; the shipped dead-cleanup pipeline). -/
theorem backend_correct_world_cleanupUG {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    -- the tables the unwinder reads (the emitted ones) and the decidable checks
    {T : Unw.FnTables} {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry))) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hpad : padsNonzeroB af fa = true)
    (hlast : lastCallsOk af fa = true) (hsaved : savedCheck vcp rf = true)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
            ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
            ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
              (runX (Unw.ArmStepU X H U T fa) i s)) ∧
    (∀ c', Clif.runLoopX env p fuel cs.toX = .trapped c' →
      ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
        (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (Unw.ArmStepU X H U T fa) n s) ∧
          (∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
            (runX (Unw.ArmStepU X H U T fa) i s)) ∧
          ∀ m, Arm.r .ERR (runX (Unw.ArmStepU X H U T fa) (n + m + 1) s) ≠ .None) ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ (obj : BitVec 64) (w : Arm.ArmState), ExnRel e obj ∧ MemRel F syms cm w ∧
        ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActUnw ra F G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
            UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
            ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
              (runX (Unw.ArmStepU X H U T fa) i s)) := by
  have hI := iselSimU_relW_cleanup hsub hc hlU hX hXI hXR hXRi hexcl hsym hslot (fun _ => 0) hcs
    hrel hargs htr fuel
  have hP := prepareCorrectU_cleanup (driverSem_valueSemU F ⟨fa.k, af.slotBase⟩ X XR)
    (fun _ _ _ _ _ _ hp he => valueSemU_pure hp he) (valueSemU_cmpOverwrite _ _ _ _) hc.prepOk XR
  have hM6 : ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
      (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ → _ :=
    fun H U G base ra s he => by
      have h := regLevelCorrect_worldUTG hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
        (XR := XR) (U := U) (T := T) (K := K) (G := G) (gv := GotV vcp) he.abi he.stack he.gfree
        (gotSem_valueSemVU _ _ _ _ _)
        (realizes_valueU_worldF hcov (by rw [he.hF]; exact he.calls) (by rw [he.hF]; exact he.tries)
          (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.unw) hsites hlsda hpad hlast)
        (fun us uses w => by rw [valueSemVU_rets])
        (fun _ _ _ _ _ ht h => valueSemVU_halt_trap ht h) (by rw [he.hF]; exact he.unw)
        hsites hlsda hlast hrows hcie hfde hsaved (by rw [he.hF]; exact he.body) (fun _ => 0)
      rw [he.hF] at h
      exact h
  refine ⟨fun vals cm hrun => ?_, fun c' hrun H U G base ra s he => ?_,
    fun e cm hrun => ?_⟩
  · obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
    have hrs : vc.RetsSite us := by
      obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
      exact ⟨b, vb, k, hvb, hk⟩
    refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H U G base ra s he => ?_⟩
    exact (hM6 H U G base ra s he).1 us outs w
      (vReturns_gotV_gen (gotPair_valueU _ _ _) ((hP.1 _ _).1 _ _ _ hv))
  · exact (hM6 H U G base ra s he).2.1 c'
      (vTraps_gotV_gen (gotPair_valueU _ _ _) ((hP.1 _ _).2 c' (hI.2.1 c' hrun)))
  · obtain ⟨obj, w, hv, hex, hmemR⟩ := hI.2.2 e cm hrun
    exact ⟨obj, w, hex, hmemR, fun H U G base ra s he =>
      (hM6 H U G base ra s he).2.2 obj w
        (vUnwinds_gotV_gen (gotPair_valueU _ _ _) (hP.2 _ _ _ _ hv))⟩

/-! ## The legacy pipeline (`csemU`) -/

/-- The callee contract for `csemU`, under the callees' exclusivity (a callee that returns
normally does not raise). -/
theorem callsRefine_csemU_of_excl {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    {env : Clif.Env} {exts : List Clif.ExtFunc} {MR : MemRelT} (hX : XCallsOk env exts MR X)
    (hex : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none) :
    CallsRefine F env exts MR (csemU F ctx X XR) := by
  obtain ⟨sym, h1, h2, h3⟩ := callsRefine_csem (F := F) (ctx := ctx) hX
  refine ⟨sym, fun rd n w => ?_, ?_, ?_⟩
  · obtain ⟨w', hs, hw⟩ := h1 rd n w
    exact ⟨w', csemU_of_csem hex hs, hw⟩
  · intro ext hext g sl cm w dest us ds uses args vals rvals cm' a b c d e f g'
    obtain ⟨outs, w', hs, rest⟩ := h2 ext hext g sl cm w dest us ds uses args vals rvals cm' a b c d e f g'
    exact ⟨outs, w', csemU_of_csem hex hs, rest⟩
  · intro ext hext g sl cm w dest us ds ti uses args vals rvals cm' a b c d e f g' h'
    obtain ⟨outs, w', hs, rest⟩ :=
      h3 ext hext g sl cm w dest us ds ti uses args vals rvals cm' a b c d e f g' h'
    exact ⟨outs, w', csemU_of_csem hex hs, rest⟩

/-- The indirect-call contract for `csemU`, under the callees' exclusivity. -/
theorem indCallsRefine_csemU_of_excl {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {XR : XRaise} {env : Clif.Env} {sigs : List Clif.Signature} {MR : MemRelT}
    {syms : String → Option Nat} (hX : XCallsIndOk env sigs MR X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMR : ∀ sl cm w, MR sl cm w → cm.symbols = syms)
    (hex : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none) :
    IndCallsRefine env sigs MR (csemU F ctx X XR) := by
  obtain ⟨h1, h2⟩ := indCallsRefine_csem (F := F) (ctx := ctx) hX hsym hMR
  refine ⟨?_, ?_⟩
  · intro sig hsig n g sl cm w a r us ds u args vals rvals cm' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
    obtain ⟨outs, w', hs, rest⟩ :=
      h1 sig hsig n g sl cm w a r us ds u args vals rvals cm' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
    exact ⟨outs, w', csemU_of_csem hex hs, rest⟩
  · intro sig hsig n g sl cm w a r us ds ti u args vals rvals cm' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    obtain ⟨outs, w', hs, rest⟩ := h2 sig hsig n g sl cm w a r us ds ti u args vals rvals cm' a1 a2
      a3 a4 a5 a6 a7 a8 a9 a10 a11
    exact ⟨outs, w', csemU_of_csem hex hs, rest⟩

/-- **CLIF → VCode with unwinding for an activation inside a linked program** (`RelW`; the
legacy pipeline, `csemU`). -/
theorem iselSimU_relW {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {args : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ us outs w, VReturns vc (csemU F ⟨fa.k, af.slotBase⟩ X XR) ρ₀ w₀ us outs w ∧
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w) ∧
    (∀ c', Clif.runLoopX env p fuel cs.toX = .trapped c' →
      VTraps vc (csemU F ⟨fa.k, af.slotBase⟩ X XR) ρ₀ w₀ c') ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ obj w, VUnwinds vc (csemU F ⟨fa.k, af.slotBase⟩ X XR) XR ρ₀ w₀ obj w ∧
        ExnRel e obj ∧ MemRel F syms cm w) := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hUs⟩ := loweringU_of_check hlU
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  let sem := csemU F ⟨fa.k, af.slotBase⟩ X XR
  have hRef : Refines F sem := refines_csemU _ _ X XR
  have hmem : MemRefines F slotOff syms sem := memRefines_csemU _ _ X XR hslot hsym
  have hcalls := callsRefine_csemU_of_excl (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hX hexcl
  have hicalls := indCallsRefine_csemU_of_excl (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hXI hsym
    (fun _ _ _ h => h.1.1.symbols) hexcl
  have houtB := outgoing_le_intBase hc
  have H : DriverHyp f vc ctx st0 R gn bl A sem (RelW Γ f c) env.toEnv p := {
    shape := hshape
    cert := hcert
    dsem := (driverSem_csemU F ⟨fa.k, af.slotBase⟩ X XR).toDriverSemG
    insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
      indRulesCorrect memRulesCorrect_program hRef (mrStable_relW Γ f c) hcalls hicalls hmem
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
    tries := ⟨_, tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) hcalls, tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef (mrStable_relW Γ f c)
      hmem (outArgsOk_relW Γ f c) (indStack_mono (indStack_of_check hc.lowerOk) houtB) hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := cfg_of_prepare hc.prepare }
  have HR : RaiseHyp f sem (RelW Γ f c) env F X XR slotOff syms (RAFrame.compute vcp rf).intBase :=
    ⟨raiseSem_csemU _ _ X XR, hRef, hmem, mrStable_relW Γ f c, outArgsOk_relW Γ f c,
      memRelOk_relW Γ f c, callsStack_mono (callsStack_of_check hc.lowerOk) houtB,
      tryStack_mono (tryStack_of_check hc.lowerOk) houtB,
      indStack_mono (indStack_of_check hc.lowerOk) houtB, hXR, hXRi, hsym,
      fun sl cm w h => (memRelOk_relW Γ f c).symbols sl cm w h⟩
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hrun := driver_correctU H hUs HR (driverSem_csemU F ⟨fa.k, af.slotBase⟩ X XR) hB0
    hce.callers hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs htr fuel
  refine ⟨fun vals cm h => ?_, fun c' h => ?_, fun e cm h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1.1 _)⟩
  · rw [h] at hrun
    exact hrun
  · rw [h] at hrun
    obtain ⟨obj, w, cm0, hu, hex, h4, h5⟩ := hrun
    exact ⟨obj, w, hu, hex, h5 ▸ memRel_leave (memRel_free h4.1.1 _)⟩

/-- **The per-function world theorem with unwinding for the legacy pipeline** (`csemU`). -/
theorem backend_correct_worldU {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {T : Unw.FnTables} {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry))) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hpad : padsNonzeroB af fa = true)
    (hlast : lastCallsOk af fa = true) (hsaved : savedCheck vcp rf = true)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
            ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s)) ∧
    (∀ c', Clif.runLoopX env p fuel cs.toX = .trapped c' →
      ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
        (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (Unw.ArmStepU X H U T fa) n s)) ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ (obj : BitVec 64) (w : Arm.ArmState), ExnRel e obj ∧ MemRel F syms cm w ∧
        ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActUnw ra F G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
            UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s)) := by
  have hI := iselSimU_relW hsub hc hlU hX hXI hXR hXRi hexcl hsym hslot (fun _ => 0) hcs
    hrel hargs htr fuel
  have hP := prepareCorrectU_of_check (driverSem_csemU F ⟨fa.k, af.slotBase⟩ X XR) hc.prepOk XR
  have hnc : ∀ {i : MInst}, trapCode? i ≠ none → ∀ info,
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) → False := fun ht _ h => by
    rcases h with rfl | ⟨_, rfl⟩ <;> simp [trapCode?] at ht
  have hM6 : ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
      (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ → _ :=
    fun H U G base ra s he => by
      have h := regLevelCorrect_worldUT hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
        (XR := XR) (U := U) (T := T) (K := K) (G := G) (gv := GotV vcp) he.abi he.stack he.gfree
        (gotSem_csemVU _ _ _ _ _)
        (realizes_csemU_world hcov (by rw [he.hF]; exact he.calls) (by rw [he.hF]; exact he.tries)
          (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.unw) hsites hlsda hpad hlast)
        (fun us uses w => by
          rw [csemVU_eq fun _ h => by rcases h with h | ⟨_, h⟩ <;> cases h]
          exact csemU_rets us uses w)
        (fun i uses w outs w' ht h => by
          rw [csemVU_eq fun info h => (hnc ht info h).elim] at h
          rwa [← csemU_trap ht])
        (by rw [he.hF]; exact he.unw)
        hsites hlsda hlast hrows hcie hfde hsaved (by rw [he.hF]; exact he.body) (fun _ => 0)
      rw [he.hF] at h
      exact h
  refine ⟨fun vals cm hrun => ?_, fun c' hrun H U G base ra s he => ?_,
    fun e cm hrun => ?_⟩
  · obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
    have hrs : vc.RetsSite us := by
      obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
      exact ⟨b, vb, k, hvb, hk⟩
    refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H U G base ra s he => ?_⟩
    exact (hM6 H U G base ra s he).1 us outs w
      (vReturns_gotV_gen (gotPair_csemU _ _ _) ((hP.1 _ _).1 _ _ _ hv))
  · exact (hM6 H U G base ra s he).2.1 c'
      (vTraps_gotV_gen (gotPair_csemU _ _ _) ((hP.1 _ _).2 c' (hI.2.1 c' hrun)))
  · obtain ⟨obj, w, hv, hex, hmemR⟩ := hI.2.2 e cm hrun
    exact ⟨obj, w, hex, hmemR, fun H U G base ra s he =>
      (hM6 H U G base ra s he).2.2 obj w
        (vUnwinds_gotV_gen (gotPair_csemU _ _ _) (hP.2 _ _ _ _ hv))⟩

/-- **The per-function world theorem with unwinding for the legacy pipeline** (`csemU`). -/
theorem backend_correct_worldUG {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {T : Unw.FnTables} {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry))) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hpad : padsNonzeroB af fa = true)
    (hlast : lastCallsOk af fa = true) (hsaved : savedCheck vcp rf = true)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
            ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
            ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
              (runX (Unw.ArmStepU X H U T fa) i s)) ∧
    (∀ c', Clif.runLoopX env p fuel cs.toX = .trapped c' →
      ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
        (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (Unw.ArmStepU X H U T fa) n s) ∧
          (∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
            (runX (Unw.ArmStepU X H U T fa) i s)) ∧
          ∀ m, Arm.r .ERR (runX (Unw.ArmStepU X H U T fa) (n + m + 1) s) ≠ .None) ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ (obj : BitVec 64) (w : Arm.ArmState), ExnRel e obj ∧ MemRel F syms cm w ∧
        ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActUnw ra F G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
            UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
            ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
              (runX (Unw.ArmStepU X H U T fa) i s)) := by
  have hI := iselSimU_relW hsub hc hlU hX hXI hXR hXRi hexcl hsym hslot (fun _ => 0) hcs
    hrel hargs htr fuel
  have hP := prepareCorrectU_of_check (driverSem_csemU F ⟨fa.k, af.slotBase⟩ X XR) hc.prepOk XR
  have hnc : ∀ {i : MInst}, trapCode? i ≠ none → ∀ info,
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) → False := fun ht _ h => by
    rcases h with rfl | ⟨_, rfl⟩ <;> simp [trapCode?] at ht
  have hM6 : ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
      (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ → _ :=
    fun H U G base ra s he => by
      have h := regLevelCorrect_worldUTG hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
        (XR := XR) (U := U) (T := T) (K := K) (G := G) (gv := GotV vcp) he.abi he.stack he.gfree
        (gotSem_csemVU _ _ _ _ _)
        (realizes_csemU_worldF hcov (by rw [he.hF]; exact he.calls) (by rw [he.hF]; exact he.tries)
          (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.unw) hsites hlsda hpad hlast)
        (fun us uses w => by
          rw [csemVU_eq fun _ h => by rcases h with h | ⟨_, h⟩ <;> cases h]
          exact csemU_rets us uses w)
        (fun i uses w outs w' ht h => by
          rw [csemVU_eq fun info h => (hnc ht info h).elim] at h
          rwa [← csemU_trap ht])
        (by rw [he.hF]; exact he.unw)
        hsites hlsda hlast hrows hcie hfde hsaved (by rw [he.hF]; exact he.body) (fun _ => 0)
      rw [he.hF] at h
      exact h
  refine ⟨fun vals cm hrun => ?_, fun c' hrun H U G base ra s he => ?_,
    fun e cm hrun => ?_⟩
  · obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
    have hrs : vc.RetsSite us := by
      obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
      exact ⟨b, vb, k, hvb, hk⟩
    refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H U G base ra s he => ?_⟩
    exact (hM6 H U G base ra s he).1 us outs w
      (vReturns_gotV_gen (gotPair_csemU _ _ _) ((hP.1 _ _).1 _ _ _ hv))
  · exact (hM6 H U G base ra s he).2.1 c'
      (vTraps_gotV_gen (gotPair_csemU _ _ _) ((hP.1 _ _).2 c' (hI.2.1 c' hrun)))
  · obtain ⟨obj, w, hv, hex, hmemR⟩ := hI.2.2 e cm hrun
    exact ⟨obj, w, hex, hmemR, fun H U G base ra s he =>
      (hM6 H U G base ra s he).2.2 obj w
        (vUnwinds_gotV_gen (gotPair_csemU _ _ _) (hP.2 _ _ _ _ hv))⟩

/-! ## Either pipeline -/

/-- **The per-function world theorem with unwinding for either pipeline** (`CompiledEither`: the
legacy one, `csemU`, or the dead-cleanup one, `valueSemU`; `backend_correct_world_pipeline`'s
counterpart). -/
theorem backend_correct_world_pipelineU {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledEither f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {T : Unw.FnTables} {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry))) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hpad : padsNonzeroB af fa = true)
    (hlast : lastCallsOk af fa = true) (hsaved : savedCheck vcp rf = true)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
            ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s)) ∧
    (∀ c', Clif.runLoopX env p fuel cs.toX = .trapped c' →
      ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
        (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (Unw.ArmStepU X H U T fa) n s)) ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ (obj : BitVec 64) (w : Arm.ArmState), ExnRel e obj ∧ MemRel F syms cm w ∧
        ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActUnw ra F G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
            UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s)) := by
  cases hc with
  | legacy hc =>
    exact backend_correct_worldU hsub hc hlU hcov hX hXI hXR hXRi hexcl hsym hslot
      hsites hlsda hrows hcie hfde hpad hlast hsaved hcs hrel hargs htr fuel
  | cleanup hc =>
    exact backend_correct_world_cleanupU hsub hc hlU hcov hX hXI hXR hXRi hexcl hsym
      hslot hsites hlsda hrows hcie hfde hpad hlast hsaved hcs hrel hargs htr fuel

/-- **The per-function world theorem with unwinding for either pipeline** (`CompiledEither`: the
legacy one, `csemU`, or the dead-cleanup one, `valueSemU`; `backend_correct_world_pipeline`'s
counterpart). -/
theorem backend_correct_world_pipelineUG {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledEither f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {T : Unw.FnTables} {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry))) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hpad : padsNonzeroB af fa = true)
    (hlast : lastCallsOk af fa = true) (hsaved : savedCheck vcp rf = true)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
            ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
            ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
              (runX (Unw.ArmStepU X H U T fa) i s)) ∧
    (∀ c', Clif.runLoopX env p fuel cs.toX = .trapped c' →
      ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
        (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (Unw.ArmStepU X H U T fa) n s) ∧
          (∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
            (runX (Unw.ArmStepU X H U T fa) i s)) ∧
          ∀ m, Arm.r .ERR (runX (Unw.ArmStepU X H U T fa) (n + m + 1) s) ≠ .None) ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ (obj : BitVec 64) (w : Arm.ArmState), ExnRel e obj ∧ MemRel F syms cm w ∧
        ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActUnw ra F G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
            UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
            ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
              (runX (Unw.ArmStepU X H U T fa) i s)) := by
  cases hc with
  | legacy hc =>
    exact backend_correct_worldUG hsub hc hlU hcov hX hXI hXR hXRi hexcl hsym hslot
      hsites hlsda hrows hcie hfde hpad hlast hsaved hcs hrel hargs htr fuel
  | cleanup hc =>
    exact backend_correct_world_cleanupUG hsub hc hlU hcov hX hXI hXR hXRi hexcl hsym
      hslot hsites hlsda hrows hcie hfde hpad hlast hsaved hcs hrel hargs htr fuel

end E2E

import FV.E2E.PairDriverTC
import FV.E2E.DeadCleanupTC
import FV.E2E.DeadCleanupT
import FV.E2E.DeadCleanupPair
import FV.E2E.DeadCleanupPairT
import FV.E2E.DeadCleanupGuardedFP
import FV.E2E.PoolRefinesFPV

/-! # The dead-cleanup world and non-interference, typed `try_call`s (S11e6, #419)

`DeadCleanupPairT.lean` for the scope with typed direct `try_call`s (`InSubsetTC`,
`CompiledCleanupTC`): the shipped route's value semantics `valueSem`; per-step contracts at
`valueSemGF` (the guarded value semantics with the float accesses), paired by
`lowerInstOk_pairF_value` and `lowerTryOkC_pairF_value` (`guardedStepF_value`); the typed driver
(`DriverHypTC`) from `driverHypTC_relW_of`.

* `iselSim_relW_cleanupTC`, `backend_correct_world_cleanupTC`;
* `instCalls_pair_valueTC`, `tryCalls_pair_valueTC`, `vcode_ni_valueTC`,
  `backend_correct_world_ni_valueTC`.

S11f (#35): the same for the scope with the proven float operations (`InSubsetTCF`,
`CompiledCleanupTCF`), suffix `TCF` (`instCalls_pair_valueTCF` from `lowerInstOkP_runTermTF`, no
`InstScopeT` premise); the `TC` theorems over `InSubsetTC` are their corollaries, statements
unchanged.

#1002 part 2: the validated shape is `LowerShapeTCS InstScope.tfl` (an `f64const` from the
literal pool among the instructions). `driverHypTCFS_relW_value` (`poolRefinesFP_valueSem`),
`instCalls_pair_valueTCFS` (`poolRefinesFP_valueSemGF`), `tryCalls_pair_valueTCS`,
`termCalls_pair_valueTS`, `tryIndCalls_pair_valueTS` (transported to `CtxTS S`) give
`iselSim_relW_cleanupTCF` and `vcode_ni_valueTCF` through `DriverHypTCS`, their statements
unchanged.
-/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64} {D : BitVec 64 → Prop}

/-- The pruned code's CFG is the lowered code's. -/
theorem cfg_of_cleanupTC (hc : CompiledCleanupTC f k vc vcp rf af fa fb) :
    ∃ ss ps, vc.cfg = .ok (ss, ps) := by
  obtain ⟨ss, ps, he⟩ := cfg_of_prepare hc.prepare
  exact ⟨ss, ps, (prune_cfg vc).symm.trans he⟩

/-- The pruned code's CFG is the lowered code's (`CompiledCleanupTCF`). -/
theorem cfg_of_cleanupTCF (hc : CompiledCleanupTCF f k vc vcp rf af fa fb) :
    ∃ ss ps, vc.cfg = .ok (ss, ps) := by
  obtain ⟨ss, ps, he⟩ := cfg_of_prepare hc.prepare
  exact ⟨ss, ps, (prune_cfg vc).symm.trans he⟩

/-- **The driver hypothesis at `valueSem` with the memory relation `RelW`, with the proven float
operations.** -/
theorem driverHypTCF_relW_value (hsub : InSubsetTCF p f)
    (hc : CompiledCleanupTCF f k vc vcp rf af fa fb) (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff) {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    (hshape : LowerShapeTC f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) :
    DriverHypTC f vc ctx st0 R gn bl A (valueSem F ⟨fa.k, af.slotBase⟩ X)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) env p :=
  driverHypTCF_relW_of hsub hT hc.lowerOk (cfg_of_cleanupTCF hc)
    (outgoing_le_intBaseCleanupATCF hc.toA) (refines_valueSem _ _ X)
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X) (callsRefine_valueSem hX)
    (indCallsRefine_valueSem hXI hsym (fun _ _ _ h => h.1.1.symbols))
    (memRefines_valueSem _ _ X hslot hsym) (memRefinesFP_valueSem (fun _ => True) F _ X hslot)
    hshape hcert hbr

/-- **The typed-`try_call` driver hypothesis at `valueSem` with the memory relation `RelW`.** -/
theorem driverHypTC_relW_value (hsub : InSubsetTC p f)
    (hc : CompiledCleanupTC f k vc vcp rf af fa fb) (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff) {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    (hshape : LowerShapeTC f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) :
    DriverHypTC f vc ctx st0 R gn bl A (valueSem F ⟨fa.k, af.slotBase⟩ X)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) env p :=
  driverHypTCF_relW_value hsub.toTCF hc.toTCF hT hX hXI hsym hslot hshape hcert hbr

/-- **The driver hypothesis at `valueSem` with the memory relation `RelW` over a scope inside
`InstScopeTFL`** (#1002 part 2: `driverHypTCF_relW_value` for `LowerShapeTCS S`;
`poolRefinesFP_valueSem`). -/
theorem driverHypTCFS_relW_value {S : InstScope} (hS : ∀ ctx, S.P ctx → InstScopeTFL ctx)
    (hsub : InSubsetTCF p f) (hc : CompiledCleanupTCF f k vc vcp rf af fa fb)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff) {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    (hshape : LowerShapeTCS S f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) :
    DriverHypTCS S f vc ctx st0 R gn bl A (valueSem F ⟨fa.k, af.slotBase⟩ X)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) env p :=
  driverHypTCFS_relW_of hS hsub hc.lowerOk (cfg_of_cleanupTCF hc)
    (outgoing_le_intBaseCleanupATCF hc.toA) (refines_valueSem _ _ X)
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X) (callsRefine_valueSem hX)
    (indCallsRefine_valueSem hXI hsym (fun _ _ _ h => h.1.1.symbols))
    (memRefines_valueSem _ _ X hslot hsym) (memRefinesFP_valueSem (fun _ => True) F _ X hslot)
    (poolRefinesFP_valueSem F _ X) hshape hcert hbr

/-- The prune-then-prepare step is correct for `valueSem`. -/
theorem prepareCorrect_cleanupTC (hc : CompiledCleanupTC f k vc vcp rf af fa fb) :
    PrepareCorrect (valueSem F ⟨fa.k, af.slotBase⟩ X) vc vcp := by
  intro a w
  obtain ⟨hr, ht⟩ := prune_correct (vc := vc)
    (fun _ _ _ _ _ _ hp he => valueSem_pure hp he) (valueSem_cmpOverwrite _ _ _) a w
  obtain ⟨pr, pt⟩ := prepareCorrect_of_check (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X)
    hc.prepOk a w
  exact ⟨fun _ _ _ he => pr _ _ _ (hr _ _ _ he), fun _ he => pt _ (ht _ he)⟩

/-- The prune-then-prepare step is correct for `valueSem` (`CompiledCleanupTCF`). -/
theorem prepareCorrect_cleanupTCF (hc : CompiledCleanupTCF f k vc vcp rf af fa fb) :
    PrepareCorrect (valueSem F ⟨fa.k, af.slotBase⟩ X) vc vcp := by
  intro a w
  obtain ⟨hr, ht⟩ := prune_correct (vc := vc)
    (fun _ _ _ _ _ _ hp he => valueSem_pure hp he) (valueSem_cmpOverwrite _ _ _) a w
  obtain ⟨pr, pt⟩ := prepareCorrect_of_check (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X)
    hc.prepOk a w
  exact ⟨fun _ _ _ he => pr _ _ _ (hr _ _ _ he), fun _ he => pt _ (ht _ he)⟩

/-- **CLIF → VCode with the proven float operations, for the dead-cleanup route**
(`iselSim_relW_cleanupTC` for `InSubsetTCF`/`CompiledCleanupTCF`). -/
theorem iselSim_relW_cleanupTCF (hsub : InSubsetTCF p f)
    (hc : CompiledCleanupTCF f k vc vcp rf af fa fb) (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {args : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w, VReturns vc (valueSem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us outs w ∧
        RetRegsOk vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧
        vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTraps vc (valueSem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c') := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringTCF_of_check hc.lowerOk
  have H := driverHypTCFS_relW_value (S := InstScope.tfl) (fun _ h => h) (c := c) hsub hc hX hXI
    hsym hslot hshape hcert hbr
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hrun := driver_correctTCS _ H (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X)
    (memRefines_valueSem _ _ X hslot hsym) (memRefinesFP_valueSem (fun _ => True) F _ X hslot)
    (mrStable_relW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig
    (ρ₀ := ρ₀) hrel hargs (runPrem_of_traps hce htr) fuel
  refine ⟨fun vals cm h => ?_, fun c' h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5, h6⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1.1 _), h6⟩
  · rw [h] at hrun
    exact hrun

/-- **CLIF → VCode, typed `try_call`s, for the dead-cleanup route** (`iselSim_relW_cleanup` for
the scope with typed `try_call`s). -/
theorem iselSim_relW_cleanupTC (hsub : InSubsetTC p f)
    (hc : CompiledCleanupTC f k vc vcp rf af fa fb) (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {args : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w, VReturns vc (valueSem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us outs w ∧
        RetRegsOk vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧
        vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTraps vc (valueSem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c') :=
  iselSim_relW_cleanupTCF hsub.toTCF hc.toTCF hT hX hXI hsym hslot ρ₀ hce hrel hargs htr fuel

/-- **The dead-cleanup per-function theorem with the final world, with the proven float
operations** (`backend_correct_world_cleanupTC` for `InSubsetTCF`/`CompiledCleanupTCF`). -/
theorem backend_correct_world_cleanupTCF (hsub : InSubsetTCF p f)
    (hc : CompiledCleanupTCF f k vc vcp rf af fa fb) (hT : TypedRules) {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals us ∧ vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) := by
  have hI := iselSim_relW_cleanupTCF hsub hc hT hX hXI hsym hslot (fun _ => 0) hcs hrel hargs htr
    fuel
  have hP := prepareCorrect_cleanupTCF (F := F) (X := X) hc (fun _ => 0) w₀
  have hM6 : ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntry vcp rf af fa fb K F G X H base ra s w₀ → _ := fun H G base ra s he => by
    have h := regLevelCorrect_world_value hc.check (AllocAF.of_lowerRFunc hc.alloc) (noLeaf_of_lowerRFunc hc.alloc) hc.emit hc.layout (X := X) (H := H)
      (K := K) (G := G) (gv := GotV vcp) hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
      (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body)
      (fun _ => 0)
    rw [he.hF] at h
    exact h
  refine ⟨fun vals cm hrun => ?_, fun c' hrun H G base ra s he => ?_⟩
  · obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR, htys⟩ := hI.1 vals cm hrun
    have hrs : vc.RetsSite us := by
      obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
      exact ⟨b, vb, k, hvb, hk⟩
    refine ⟨us, outs, w, hus, htys, hlen, hhold, hmemR, hrs, fun H G base ra s he => ?_⟩
    obtain ⟨n, h1, h2, h3, h4, h5, h6, h7⟩ :=
      (hM6 H G base ra s he).1 us outs w (vReturns_gotV_value (hP.1 _ _ _ hv))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩
  · exact (hM6 H G base ra s he).2 c' (vTraps_gotV_value (hP.2 c' (hI.2 c' hrun)))

/-- **The typed-`try_call` dead-cleanup per-function theorem with the final world**
(`backend_correct_world_cleanup` for the scope with typed `try_call`s). -/
theorem backend_correct_world_cleanupTC (hsub : InSubsetTC p f)
    (hc : CompiledCleanupTC f k vc vcp rf af fa fb) (hT : TypedRules) {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals us ∧ vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) :=
  backend_correct_world_cleanupTCF hsub.toTCF hc.toTCF hT hcov hX hXI hsym hslot hcs hrel hargs
    htr fuel

/-! ## Pairs of worlds -/

/-- **The typed statement calls on pairs of worlds, value semantics** (for the scope with typed
`try_call`s). -/
theorem instCalls_pair_valueTC (hc : CompiledCleanupTC f k vc vcp rf af fa fb)
    (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {ctx : Ctx} (hctx : CtxT f ctx) (hsc : InstScopeT ctx) (hst : StoresTyped ctx) :
    InstCallsT f ctx (pairSem (valueSem F ⟨fa.k, af.slotBase⟩ X))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p := by
  intro ii info inst st rss st' tr hmem hi hcl hsig hemp hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hstk := callsStack_mono (callsStackTC_of_check hc.lowerOk)
    (outgoing_le_intBaseCleanupATC hc.toA)
  have hIstk := indStack_mono (indStackTC_of_check hc.lowerOk)
    (outgoing_le_intBaseCleanupATC hc.toA)
  refine lowerInstOk_pairF_value hNI hTls (Γ := Γ) rfl hctx.inv.func hsig fun Rd Pc => ?_
  obtain ⟨B, hB, stm, hstm, hst'⟩ := hmem
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkP_runTermT lowerRulesCorrectTI_program
    lowerRulesCorrectT_program lowerRulesCorrectFT_program nonEUnmatchableT_program hT.calls
    hT.ind memRulesCorrectRTI_program memRulesCorrectRT_program refines_valueSemGF
    (mrStable_relW Γ f c)
    (callsRefineP_valueSemGF hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
    (indCallsRefineP_valueSemGF hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
    (memRefinesR_valueSemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym)
    (memRefinesFP_valueSemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot)
    hctx hsc (outArgsOk_relW Γ f c) (externsIn_self f) (memRelOk_relW Γ f c) hi hcl hsig hIstk
    (hst ii info inst hi hcl)
    (fun fn args e hc' he => hstk B hB stm hstm fn args e (hst' ▸ hc') he) hvb hrun
  cases hov
  rw [hemp, Array.empty_append] at hem
  rw [hem, List.toList_toArray]
  exact hok

/-- **The typed statement calls on pairs of worlds, value semantics, with the proven float
operations** (`instCalls_pair_valueTC` for `CompiledCleanupTCF`, over `CtxT` alone). -/
theorem instCalls_pair_valueTCF (hc : CompiledCleanupTCF f k vc vcp rf af fa fb)
    (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {ctx : Ctx} (hctx : CtxT f ctx) (hst : StoresTyped ctx) :
    InstCallsT f ctx (pairSem (valueSem F ⟨fa.k, af.slotBase⟩ X))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p := by
  intro ii info inst st rss st' tr hmem hi hcl hsig hemp hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hstk := callsStack_mono (callsStackTCF_of_check hc.lowerOk)
    (outgoing_le_intBaseCleanupATCF hc.toA)
  refine lowerInstOk_pairF_value hNI hTls (Γ := Γ) rfl hctx.inv.func hsig fun Rd Pc => ?_
  obtain ⟨B, hB, stm, hstm, hst'⟩ := hmem
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkP_runTermTF lowerRulesCorrectTI_program
    lowerRulesCorrectT_program lowerRulesCorrectFT_program lowerRulesCorrectCvtT_program
    lowerRulesCorrectFC_program nonEUnmatchableTF_program hT.calls
    hT.ind memRulesCorrectRTI_program memRulesCorrectRT_program refines_valueSemGF
    (mrStable_relW Γ f c)
    (callsRefineP_valueSemGF hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
    (indCallsRefineP_valueSemGF hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
    (memRefinesR_valueSemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym)
    (memRefinesFP_valueSemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot)
    hctx (outArgsOk_relW Γ f c) (externsIn_self f) (memRelOk_relW Γ f c) hi hcl hsig
    (indStack_mono (indStackTCF_of_check hc.lowerOk) (outgoing_le_intBaseCleanupATCF hc.toA))
    (hst ii info inst hi hcl)
    (fun fn args e hc' he => hstk B hB stm hstm fn args e (hst' ▸ hc') he) hvb hrun
  cases hov
  rw [hemp, Array.empty_append] at hem
  rw [hem, List.toList_toArray]
  exact hok

/-- **`instCalls_pair_valueTCF` with float calls** (S11g, #1015): over `CtxTW`, every `call` by
the float family (`lowerInstOkP_runTermTFW`, `callRulesCorrectTFP_program`), the other families
over `CtxTW` (`TypedRulesW`, `lowerRulesCorrectTIW_program`, `memRulesCorrectRTIW_program`). -/
theorem instCalls_pair_valueTCFW (hc : CompiledCleanupTCF f k vc vcp rf af fa fb)
    (hT : TypedRulesW)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {ctx : Ctx} (hctx : CtxTW f ctx) (hst : StoresTyped ctx) :
    InstCallsT f ctx (pairSem (valueSem F ⟨fa.k, af.slotBase⟩ X))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p := by
  intro ii info inst st rss st' tr hmem hi hcl hsig hemp hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hstk := callsStack_mono (callsStackTCF_of_check hc.lowerOk)
    (outgoing_le_intBaseCleanupATCF hc.toA)
  refine lowerInstOk_pairF_value hNI hTls (Γ := Γ) rfl hctx.inv.func hsig fun Rd Pc => ?_
  obtain ⟨B, hB, stm, hstm, hst'⟩ := hmem
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkP_runTermTFW lowerRulesCorrectTIW_program
    lowerRulesCorrectT_program lowerRulesCorrectFT_program lowerRulesCorrectCvtT_program
    lowerRulesCorrectFC_program nonEUnmatchableTFW_program callRulesCorrectTFP_program
    hT.ind memRulesCorrectRTIW_program memRulesCorrectRT_program refines_valueSemGF
    (mrStable_relW Γ f c)
    (callsRefineP_valueSemGF hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
    (indCallsRefineP_valueSemGF hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
    (memRefinesR_valueSemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym)
    (memRefinesFP_valueSemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot)
    hctx (outArgsOk_relW Γ f c) (externsIn_self f) (memRelOk_relW Γ f c) hi hcl hsig
    (indStack_mono (indStackTCF_of_check hc.lowerOk) (outgoing_le_intBaseCleanupATCF hc.toA))
    (hst ii info inst hi hcl)
    (fun fn args e hc' he => hstk B hB stm hstm fn args e (hst' ▸ hc') he) hvb hrun
  cases hov
  rw [hemp, Array.empty_append] at hem
  rw [hem, List.toList_toArray]
  exact hok

/-- **`instCalls_pair_valueTCFW` over a scope inside `InstScopeTFL`** (#1002 part 2: over
`CtxTS S`; `lowerInstOkP_runTermTFS`, the guarded value semantics' literal-pool load
`poolRefinesFP_valueSemGF`). -/
theorem instCalls_pair_valueTCFS {S : InstScope} (hS : ∀ ctx, S.P ctx → InstScopeTFL ctx)
    (hc : CompiledCleanupTCF f k vc vcp rf af fa fb) (hT : TypedRulesS S)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {ctx : Ctx} (hctx : CtxTS S f ctx) (hst : StoresTyped ctx) :
    InstCallsT f ctx (pairSem (valueSem F ⟨fa.k, af.slotBase⟩ X))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p := by
  intro ii info inst st rss st' tr hmem hi hcl hsig hemp hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hstk := callsStack_mono (callsStackTCF_of_check hc.lowerOk)
    (outgoing_le_intBaseCleanupATCF hc.toA)
  refine lowerInstOk_pairF_value hNI hTls (Γ := Γ) rfl hctx.inv.func hsig fun Rd Pc => ?_
  obtain ⟨B, hB, stm, hstm, hst'⟩ := hmem
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkP_runTermTFS hS (lowerRulesCorrectTIS_program S)
    lowerRulesCorrectT_program lowerRulesCorrectFT_program lowerRulesCorrectCvtT_program
    lowerRulesCorrectFC_program (nonEUnmatchableTFS_program hS) callRulesCorrectTFP_program
    hT.ind (memRulesCorrectRTIS_program S) memRulesCorrectRT_program refines_valueSemGF
    (mrStable_relW Γ f c)
    (callsRefineP_valueSemGF hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
    (indCallsRefineP_valueSemGF hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
    (memRefinesR_valueSemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym)
    (memRefinesFP_valueSemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot) poolRefinesFP_valueSemGF
    hctx (outArgsOk_relW Γ f c) (externsIn_self f) (memRelOk_relW Γ f c) hi hcl hsig
    (indStack_mono (indStackTCF_of_check hc.lowerOk) (outgoing_le_intBaseCleanupATCF hc.toA))
    (hst ii info inst hi hcl)
    (fun fn args e hc' he => hstk B hB stm hstm fn args e (hst' ▸ hc') he) hvb hrun
  cases hov
  rw [hemp, Array.empty_append] at hem
  rw [hem, List.toList_toArray]
  exact hok

/-- **The typed `try_call` calls on pairs of worlds, value semantics** (`TryCallsTC` of
`pairSem` at `valueSem`). -/
theorem tryCalls_pair_valueTC (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {ctx : Ctx} (hctx : CtxT f ctx) :
    TryCallsTC f ctx (pairSem (valueSem F ⟨fa.k, af.slotBase⟩ X))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p
      (RAFrame.compute vcp rf).intBase := by
  intro ti fn args et data sig items targets info trs lo st1 out st' tr hra hd he hph
    hinfo hregs hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hctx' := callCtxT_tryCtx hctx.inv hph data trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOfC sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  refine lowerTryOkC_pairF_value hNI hTls (Γ := Γ) rfl
    (fun fr cm hfr => callPin_stepPin (env := env) (cm := cm) (inst := .call fn args)
      (hfr.trans hctx'.func) (fun _ _ _ _ h => by cases h)) fun Rd Pc => ?_
  obtain ⟨ms, hem, hok⟩ := tryOkPC_runTerm (isem := valueSemGF F ⟨fa.k, af.slotBase⟩ X Rd Γ.syms
    (f.externs.map (·.2)) (indSigs f) c Pc) refines_valueSemGF (mrStable_relW Γ f c)
    (memRefinesR_valueSemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym)
    (memRefinesFP_valueSemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot) (outArgsOk_relW Γ f c)
    (callsRefineP_valueSemGF hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1)) hctx'
    (externsIn_self f) hra hd he hi hinfo hregs' hvb' (st := { st1 with emitted := #[] })
    (Nat.le_refl _) hrun
  have : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  rw [← this]
  exact hok

-- **`tryCalls_pair_valueTC` over `CtxTW`** (S11g; its proof reads only `CtxT.inv`).
ctxW_transport tryCalls_pair_valueTC => tryCalls_pair_valueTCW

-- **`termCalls_pair_valueT` and `tryIndCalls_pair_valueT` over `CtxTW`** (S11g; `TypedRulesW`).
ctxW_transport termCalls_pair_valueT => termCalls_pair_valueTW
ctxW_transport tryIndCalls_pair_valueT => tryIndCalls_pair_valueTW

-- **The same over `CtxTS S`** (#1002 part 2; `ScopeTransport.lean`).
scopeS_transport tryCalls_pair_valueTCW => tryCalls_pair_valueTCS
scopeS_transport termCalls_pair_valueTW => termCalls_pair_valueTS
scopeS_transport tryIndCalls_pair_valueTW => tryIndCalls_pair_valueTS

/-- **Non-interference of a dead-cleanup VCode run, with the proven float operations**
(`vcode_ni_value` for the scope with the proven float operations). -/
theorem vcode_ni_valueTCF (hsub : InSubsetTCF p f)
    (hc : CompiledCleanupTCF f k vc vcp rf af fa fb)
    (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {args : List Clif.Val} {cs : Clif.State} {w₀ w₀' : Arm.ArmState}
    (ρ₀ : Nat → CV) (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hrel' : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem
      w₀')
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    (hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r)
    (hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
      w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k))
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w w', VReturns vc (valueSem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us outs w ∧
        VReturns vc (valueSem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀' us outs w' ∧
        SameWorld (fun b => F b ∨ D b) w w' := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringTCF_of_check hc.lowerOk
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hS : ∀ ctx, InstScope.tfl.P ctx → InstScopeTFL ctx := fun _ h => h
  have H := driverHypTCFS_relW_value (S := InstScope.tfl) hS (c := c) hsub hc hX hXI hsym hslot
    hshape hcert hbr
  have hctxT : CtxTS InstScope.tfl f ctx := ⟨hshape.ctxInvT, hshape.scope⟩
  have hstT : StoresTyped ctx := storesTyped_of_buildCtx hsub.storeTyped hshape.hctx.choose_spec
  have hmem : MemRefines F slotOff syms (valueSem F ⟨fa.k, af.slotBase⟩ X) :=
    memRefines_valueSem _ _ X hslot hsym
  have houtB := outgoing_le_intBaseCleanupATCF hc.toA
  have hTS := typedRulesS_program InstScope.tfl
  have HP : DriverHypTCS InstScope.tfl f vc ctx st0 R gn bl A
      (pairSem (valueSem F ⟨fa.k, af.slotBase⟩ X)) (MRP Γ f c D) env p := {
    shape := hshape
    cert := hcert
    dsem := driverSemG_pair_value F ⟨fa.k, af.slotBase⟩ X
    insts := instCalls_pair_valueTCFS hS hc hTS hX hXI hsym hslot hNI hTls hctxT hstT
    terms := termCalls_pair_valueTS _ Γ rfl hTls ⟨fa.k, af.slotBase⟩ hTS hctxT
    ext := H.ext
    indSig := H.indSig
    subETC := H.subETC
    entryLocs := H.entryLocs
    brIdx := H.brIdx
    noTail := H.noTail
    tries := ⟨_, tryCalls_pair_valueTCS _ hTS hX hsym hslot hNI hTls hctxT,
      tryStack_mono (tryStackTCF_of_check hc.lowerOk) houtB⟩
    tryExt := H.tryExt
    tryInd := tryIndCalls_pair_valueTS _
      (indStack_mono (indStackTCF_of_check hc.lowerOk) houtB)
      hTS hXI hsym hNI hTls hctxT
    tryIndSig := H.tryIndSig
    cfg := H.cfg }
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP := runPrem_of_traps hce htr
  have h29 : Arm.r (.GPR 29#5) w₀' = Arm.r (.GPR 29#5) w₀ := (hsw.1 _ (by simp [Masked])).symm
  obtain ⟨kk, ρ₁, w₁, w₁', hs1, hm1, hsw1, hs2, hm2, hsw2⟩ := entry_step2TCS _ H
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X) hmem
    (memRefinesFP_valueSem (fun _ => True) F _ X hslot) (mrStable_relW Γ f c) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hrel' hargs hreg h29 hstk
  have hFD : ∀ a, F a → F a ∨ D a := fun a h => .inl h
  have hmP : MatchT f ctx R gn bl A (MRP Γ f c D) cs.frame.slots cs ⟨0, kk, ρ₁, (w₁, w₁')⟩ := by
    refine ⟨hm1.1, hm1.2.1, hm1.2.2.1, ⟨hm1.2.2.2.1, hm2.2.2.2.1, ?_⟩, hm1.2.2.2.2⟩
    have h01 : SameWorld (fun b => F b ∨ D b) w₁ w₁' :=
      SameWorld.trans (SameWorld.mono hFD hsw1)
        (SameWorld.trans hsw (SameWorld.symm (SameWorld.mono hFD hsw2)))
    exact sameWorld_zof hm1.2.2.2.1.1.1 hm2.2.2.2.1.1.1 h01 (fun b h => h)
  intro vals cm hrun
  have hR := sim_runTCS _ HP hP fuel cs ⟨0, kk, ρ₁, (w₁, w₁')⟩ (.refl _) hmP
  rw [hrun] at hR
  obtain ⟨us, outs, w, cm0, hret, -, -, -, hmr, -, -⟩ := hR
  obtain ⟨h1, h2⟩ := vRetFrom_pair hret
  exact ⟨us, outs, w.1, w.2, VRetFrom.prefix hs1 h1, VRetFrom.prefix hs2 h2,
    SameWorld.mono (zof_sub cm0) hmr.2.2⟩

/-- **Non-interference of a typed-`try_call` dead-cleanup VCode run** (`vcode_ni_value` for the
scope with typed `try_call`s, `vcode_ni_valueTCF`). -/
theorem vcode_ni_valueTC (hsub : InSubsetTC p f) (hc : CompiledCleanupTC f k vc vcp rf af fa fb)
    (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {args : List Clif.Val} {cs : Clif.State} {w₀ w₀' : Arm.ArmState}
    (ρ₀ : Nat → CV) (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hrel' : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem
      w₀')
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    (hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r)
    (hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
      w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k))
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w w', VReturns vc (valueSem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us outs w ∧
        VReturns vc (valueSem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀' us outs w' ∧
        SameWorld (fun b => F b ∨ D b) w w' :=
  vcode_ni_valueTCF hsub.toTCF hc.toTCF hT hX hXI hsym hslot hNI hTls ρ₀ hce hrel hrel' hargs hsw
    hreg hstk htr fuel

/-- **The dead-cleanup per-function theorem with the final world and non-interference, with the
proven float operations** (`backend_correct_world_ni_valueTC` for
`InSubsetTCF`/`CompiledCleanupTCF`). -/
theorem backend_correct_world_ni_valueTCF (hsub : InSubsetTCF p f)
    (hc : CompiledCleanupTCF f k vc vcp rf af fa fb) (hT : TypedRules) {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals us ∧ vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
          (CallLg env (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n) := by
  intro vals cm hrun
  have hPrep := prepareCorrect_cleanupTCF (F := F) (X := X) hc
  have hI := iselSim_relW_cleanupTCF hsub hc hT hX hXI hsym hslot (fun _ => 0) hcs hrel hargs htr
    fuel
  have hM6 : ∀ (w₀ : Arm.ArmState) (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
      (s : Arm.ArmState), ActEntry vcp rf af fa fb K F G X H base ra s w₀ → _ :=
    fun w₀ H G base ra s he => by
      have h := regLevelCorrect_world_value hc.check (AllocAF.of_lowerRFunc hc.alloc) (noLeaf_of_lowerRFunc hc.alloc) hc.emit hc.layout (X := X) (H := H)
        (K := K) (G := G) (gv := GotV vcp) hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
        (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body)
        (fun _ => 0)
      rw [he.hF] at h
      exact h
  obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR, htys⟩ := hI.1 vals cm hrun
  have hrs : vc.RetsSite us := by
    obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
    exact ⟨b, vb, k, hvb, hk⟩
  refine ⟨us, outs, w, hus, htys, hlen, hhold, hmemR, hrs, fun H G base ra s he => ?_,
    fun hNI hTls D w₀' hrel' hsw hreg hstk H G base ra s he => ?_⟩
  · have hP := hPrep (fun _ => 0) w₀
    obtain ⟨n, h1, h2, h3, h4, h5, h6, h7⟩ := (hM6 w₀ H G base ra s he).1 us outs w
      (vReturns_gotV_value (hP.1 _ _ _ hv))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩
  · obtain ⟨us', outs', w1, w2, hv1, hv2, hsw12⟩ := vcode_ni_valueTCF hsub hc hT hX hXI hsym hslot
      hNI hTls (fun _ => 0) hcs hrel hrel' hargs hsw hreg hstk htr fuel vals cm hrun
    obtain ⟨rfl, rfl, rfl⟩ := vRetFrom_det (vs := ⟨0, 0, fun _ => 0, w₀⟩) hv1 hv
    have hP := hPrep (fun _ => 0) w₀'
    obtain ⟨n, h1, h2, h3, h4, h5, h6, h7⟩ := (hM6 w₀' H G base ra s he).1 us' outs' w2
      (vReturns_gotV_value (hP.1 _ _ _ hv2))
    refine ⟨n, ⟨h1, h2, fun a ha => ?_, fun g hg h29 h31 => ?_, h5, h6⟩, h7⟩
    · rw [h3 a (fun hf => ha (.inl hf))]
      exact (hsw12.2.1 a ha).symm
    · rw [h4 g hg h29 h31]
      exact (hsw12.1 g hg).symm

/-- **The typed-`try_call` dead-cleanup per-function theorem with the final world and
non-interference** (`backend_correct_world_ni_value` for the scope with typed `try_call`s,
`backend_correct_world_ni_valueTCF`). -/
theorem backend_correct_world_ni_valueTC (hsub : InSubsetTC p f)
    (hc : CompiledCleanupTC f k vc vcp rf af fa fb) (hT : TypedRules) {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals us ∧ vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
          (CallLg env (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n) :=
  backend_correct_world_ni_valueTCF hsub.toTCF hc.toTCF hT hcov hX hXI hsym hslot hcs hrel hargs
    htr fuel

end

end E2E

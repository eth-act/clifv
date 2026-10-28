import FV.E2E.WorldUnwind
import FV.E2E.DeadCleanupTrapCall

/-!
# The per-function world theorem with callee traps (S9c, #376)

`backend_correct_final_cleanup_trapcall` (S9a) for an activation inside a linked program: the
memory relation `RelW` (the activation's slots at its `sp`), the kept addresses `G` and the GOT
pins `GotV vcp` of the machine-side activation (`ActEntry`), as `backend_correct_world_cleanup`
(what `FV/E2E/LinkArm.lean`'s induction applies per function) and its unwinding counterpart
`backend_correct_world_cleanupU` (`FV/E2E/WorldUnwind.lean`).

* `regLevel_trapCall_world`: the register level of the explicit and the callee traps for every
  initial vreg file (`checkAlloc`), with `G` and `GotV vcp`;
* **`backend_correct_world_cleanup_trapcall`**: for a run that traps with `c` under
  `TrapsExplicitC`, every activation (`ActEntry`) reaches a trap site of `f` with `c` or a
  callee-trap state (`CallTrapAt … (GotV vcp) (TrapCallSem …)`), every earlier state `GoodX`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **The register level of the explicit and the callee traps for an activation inside a
linked program** (`ActEntry`: kept addresses `G`, GOT pins `GotV vcp`), every initial vreg
file. -/
theorem regLevel_trapCall_world {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ())
    (halloc : lowerRFunc vcp rf = .ok af) (hemit : emitFunc k af = .ok fa)
    (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks} {K : Nat}
    {F G : BitVec 64 → Prop} (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hnt : vcp.hasTryCall = false) (XT : Option String → List CV → Arm.ArmState → Prop)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : ActEntry vcp rf af fa fb K F G X H base ra s w₀) (ρ₀ : Nat → CV) :
    (∀ c, VTraps vcp (valueSemVU (GotV vcp) F ⟨fa.k, af.slotBase⟩ X (xrT XT)) ρ₀ w₀ c →
      ∃ n, TrapAt fb base c (runX (ArmStepX X H fa) n s)) ∧
    (∀ obj w', VUnwinds vcp (valueSemVU (GotV vcp) F ⟨fa.k, af.slotBase⟩ X (xrT XT)) (xrT XT)
        ρ₀ w₀ obj w' →
      ∃ n, CallTrapAt vcp F K G s fa base X (GotV vcp) XT (runX (ArmStepX X H fa) n s) ∧
        ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp) (runX (ArmStepX X H fa) i s)) := by
  obtain ⟨cc, ins, hcA⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hcA.at
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let R : RL := ⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, GotV vcp⟩
  have hR : R.Wf := ⟨⟨cc, ins, a0, hat, entryOk_of_le hle⟩, halloc, hemit, hlayout, hlm,
    by show 4 * fb.words.size ≤ 2 ^ 64; have := he.abi.fits; omega, he.stack, ⟨body, hb⟩,
    he.abi.program, he.gfree⟩
  have hF : R.F = F := he.hF
  have hreal := realizes_value_all hR (by rw [hF]; exact he.calls)
    (fun h => by rw [show R.vc = vcp from rfl, hnt] at h; cases h)
    (by rw [hF]; exact he.tls) hcov
  have hRz := realizes_trapT (semU := valueSemVU R.gv R.F R.ctx R.X (xrT XT)) hreal
    (fun _ _ _ h => valueSemVU_noRaise h)
    (fun _ _ _ _ _ _ h hr => by rw [valueSemVU_call_raise h hr]) hnt
  have hbe' : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀ := by
    rw [hF]; exact he.body
  obtain ⟨_, h1, h2⟩ := regLevel_trapCall_core (XT := XT) hR he.abi hat
    (gotSem_valueSemVU _ _ _ _ _) hRz (fun _ _ _ _ _ ht h => valueSemVU_halt_trap ht h) hbe'
    (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  have e1 : valueSemVU R.gv R.F R.ctx R.X (xrT XT) =
      valueSemVU (GotV vcp) F ⟨fa.k, af.slotBase⟩ X (xrT XT) := by
    rw [hF]; rfl
  refine ⟨fun c htr => ?_, fun obj w' hu => ?_⟩
  · rw [← e1] at htr
    exact h1 c htr
  · rw [← e1] at hu
    obtain ⟨n, hct, ht⟩ := h2 obj w' hu
    refine ⟨n, ?_, fun i hi => (ht i hi).act⟩
    have hct' : CallTrapAt R.vc R.F R.K R.G R.s0 R.fa R.base R.X R.gv XT
        (runX R.step n R.s0) := hct
    rw [hF] at hct'
    exact hct'

/-- **The per-function world theorem with callee traps** (the shipped dead-cleanup pipeline;
`backend_correct_world_cleanup`'s trap half, widened): for a function without `try_call`
terminators in a program without functions, whose run traps with `c` under `TrapsExplicitC`,
every activation (`ActEntry`) reaches a trap site of `f` with `c`, or a callee-trap state
(`CallTrapAt` with the GOT pins `GotV vcp` and the trapping callees `TrapCallSem … c` of the
activation's memory relation `RelW`), every earlier state of the activation `GoodX`. -/
theorem backend_correct_world_cleanup_trapcall {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    (hp : p.funcs = []) (hft : ∀ B ∈ f.blocks, B.term.isTry = false)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXT : XTrapsOk env (f.externs.map (·.2)) (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicitC env p cs) {fuel : Nat} {tc : Clif.TrapCode}
    (hrun : Clif.runLoop env p fuel cs = .trapped tc) :
    ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
      ∃ n, TrapAt fb base tc (runX (ArmStepX X H fa) n s) ∨
        (CallTrapAt vcp F K G s fa base X (GotV vcp)
            (TrapCallSem env (f.externs.map (·.2)) (indSigs f)
              (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X tc)
            (runX (ArmStepX X H fa) n s) ∧
          ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
            (runX (ArmStepX X H fa) i s)) := by
  obtain ⟨htrX, hout⟩ := trapEnv_of_trapped env tc hp hft (noTail_of_subset hsub) hcs htr hrun
  let XT := TrapCallSem env (f.externs.map (·.2)) (indSigs f)
    (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X tc
  have hnt : vcp.hasTryCall = false :=
    noTryCall_of_prepCheck hc.prepOk (cleanupStage_noTryCall f (noTryCall_of_check hc.lowerOk hft))
  have hexcl : ∀ d uses w, X.call d uses w ≠ none → (xrT XT).raise d uses w = none :=
    fun _ _ _ hne => xrT_none fun h => hne h.1
  have hI := iselSimU_relW_cleanup_stage hsub hc hlU (xCallsOk_trapEnv (c := tc) hX)
    (xCallsIndOk_trapEnv (c := tc) hXI) (xRaiseOk_trapEnv hXT) (xRaiseIndOk_trapEnv hXT) hexcl
    hsym hslot (fun _ => 0) hcs hrel hargs htrX fuel
  have hP := prepareCorrectU_cleanup (vc := skipStage f vc)
    (driverSem_valueSemU F ⟨fa.k, af.slotBase⟩ X (xrT XT))
    (fun _ _ _ _ _ _ hp he => valueSemU_pure hp he) (valueSemU_cmpOverwrite _ _ _ _) hc.prepOk (xrT XT)
  intro H G base ra s he
  obtain ⟨hR1, hR2⟩ := regLevel_trapCall_world hc.check hc.alloc hc.emit hc.layout hcov hnt XT he
    (fun _ => 0)
  rcases hout with h | ⟨e, m, h⟩
  · obtain ⟨n, hn⟩ := hR1 tc
      (vTraps_gotV_gen (gotPair_valueU _ _ _) ((hP.1 _ _).2 tc (hI.2.1 tc h)))
    exact ⟨n, .inl hn⟩
  · obtain ⟨obj, w, hv, -, -⟩ := hI.2.2 e m h
    obtain ⟨n, hct, ht⟩ := hR2 obj w (vUnwinds_gotV_gen (gotPair_valueU _ _ _) (hP.2 _ _ _ _ hv))
    exact ⟨n, .inr ⟨hct, ht⟩⟩

end E2E

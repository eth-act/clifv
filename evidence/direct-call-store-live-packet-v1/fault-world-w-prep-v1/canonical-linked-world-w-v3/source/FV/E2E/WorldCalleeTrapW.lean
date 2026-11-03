import FV.E2E.RegLevelCalleeTrapW

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

theorem regLevel_calleeTrap_worldW {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ())
    (halloc : lowerRFunc vcp rf = .ok af) (hemit : emitFunc k af = .ok fa)
    (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks} {K : Nat}
    {F G : BitVec 64 → Prop} (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hnt : vcp.hasTryCall = false) (XT : Option String → List CV → Arm.ArmState → Prop)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : ActEntry vcp rf af fa fb K F G X H base ra s w₀) (ρ₀ : Nat → CV) :
    (∀ obj w', VUnwinds vcp (valueSemVU (GotV vcp) F ⟨fa.k, af.slotBase⟩ X (xrT XT)) (xrT XT)
        ρ₀ w₀ obj w' →
      ∃ n, CallTrapAt vcp F K G s fa base X (GotV vcp) XT (runX (ArmStepX X H fa) n s) ∧
        (∀ i < n, actGoodXW vcp rf af fa fb base s X H K G (GotV vcp)
          (runX (ArmStepX X H fa) i s)) ∧
        spv (runX (ArmStepX X H fa) n s) = spv s - BitVec.ofNat 64 (frameDrop af) ∧
        (runX (ArmStepX X H fa) n s).program = fb.program base) := by
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
  have hreal := realizes_value_allW hR (by rw [hF]; exact he.calls)
    (fun h => by rw [show R.vc = vcp from rfl, hnt] at h; cases h)
    (by rw [hF]; exact he.tls) hcov
  have hRz := realizes_trapT_trace (semU := valueSemVU R.gv R.F R.ctx R.X (xrT XT)) hreal
    (fun _ _ _ h => valueSemVU_noRaise h)
    (fun _ _ _ _ _ _ h hr => by rw [valueSemVU_call_raise h hr]) hnt
  have hbe' : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀ := by
    rw [hF]; exact he.body
  obtain ⟨_, h2⟩ := regLevel_calleeTrap_coreW (XT := XT) hR he.abi hat
    (gotSem_valueSemVU _ _ _ _ _) hRz hbe'
    (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  have e1 : valueSemVU R.gv R.F R.ctx R.X (xrT XT) =
      valueSemVU (GotV vcp) F ⟨fa.k, af.slotBase⟩ X (xrT XT) := by
    rw [hF]; rfl
  intro obj w' hu
  rw [← e1] at hu
  obtain ⟨n, hct, ht, hsp, hprog⟩ := h2 obj w' hu
  refine ⟨n, ?_, fun i hi => (ht i hi).act, hsp, hprog⟩
  have hct' : CallTrapAt R.vc R.F R.K R.G R.s0 R.fa R.base R.X R.gv XT
      (runX R.step n R.s0) := hct
  rw [hF] at hct'
  exact hct'


end E2E

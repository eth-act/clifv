import FV.E2E.CompiledAnyTSR
import FV.E2E.CompiledAnyTRG

/-!
# `CompiledAnyTSR` with the guarded per-state facts (#753, stage R2X')

`backend_correct_worldX_pipelineAnyTSR`, `backend_correct_world_niX_pipelineAnyTSR`
with the per-state facts `actGoodXR P` (the guarded call premise at a call line) under
`RegLevelRG` (suffix `G`).
-/
namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

set_option autoImplicit false

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

end

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64}

/-- **The typed per-state world theorem for either typed artifact or the Stock artifact of an
integer function, at the register-guarded semantics** (`backend_correct_worldX_pipelineAnyTS`
for `CompiledAnyTSR` and `ActEntryR P`, given M6 for the register-guarded semantics). -/
theorem backend_correct_worldX_pipelineAnyTSRG (hM6 : RegLevelRG) (hsub : InSubsetTCF p f)
    (hc : CompiledAnyTSR p f k vc vcp rf af fa fb)
    (hT : TypedRules) {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    {P : BitVec 64 → Clif.Signature → Prop}
    (hPg : RegCompatGot P (f.externs.map (·.2)) (fun n => X.sym n 0))
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hPi : RegCompatInd P env (indSigs f) syms)
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
          ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodXR P vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s) ∧
          (∀ i < n, actGoodXR P vcp rf af fa fb base s X H K G (GotV vcp)
            (runX (ArmStepX X H fa) i s)) ∧
          ∀ m, Arm.r .ERR (runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) := by
  rcases hc with hc | ⟨hsubS, hns, hc | ⟨hc, hnc⟩⟩
  · exact backend_correct_worldX_pipelineAnyTFRG hM6 (hPg := hPg) (hPi := hPi) hsub hc hT hcov hX hXI
      hsym hslot hcs hrel hargs htr fuel
  · obtain ⟨hret, htrap⟩ := backend_correct_worldX_productionRG hM6 (K := K) (hPg := hPg) (hPi := hPi)
      hsubS hc hcov hX hXI hsym hslot hcs hrel hargs htr fuel
    refine ⟨fun vals cm hrun => ?_, htrap⟩
    obtain ⟨us, outs, w, hus, hlen, hhold, hmem, hrs, hall⟩ := hret vals cm hrun
    exact ⟨us, outs, w,
      retRegsOk_of_retPins hus (returned_int_stock hsubS hns hcs htr hrun) (by have := hhold.1; omega),
      returned_tys_stock hsubS hns hcs htr hrun, hlen, hhold, hmem, hrs, hall⟩
  · obtain ⟨hret, htrap⟩ := backend_correct_worldX_semantic (K := K) hsubS hc.toSemantic hcov hX
      hXI hsym hslot hcs hrel hargs htr fuel
    refine ⟨fun vals cm hrun => ?_,
      fun c' hrun H G base ra s he =>
        let ⟨n, h1, h2, h3⟩ := htrap c' hrun H G base ra s (he.toActEntry hnc)
        ⟨n, h1, fun i hi => actGoodXR.of_noCallSites (h2 i hi) hnc, h3⟩⟩
    obtain ⟨us, outs, w, hus, hlen, hhold, hmem, hrs, hall⟩ := hret vals cm hrun
    exact ⟨us, outs, w,
      retRegsOk_of_retPins hus (returned_int_stock hsubS hns hcs htr hrun) (by have := hhold.1; omega),
      returned_tys_stock hsubS hns hcs htr hrun, hlen, hhold, hmem, hrs,
      fun H G base ra s he =>
        let ⟨n, h1, h2, h3⟩ := hall H G base ra s (he.toActEntry hnc)
        ⟨n, h1, h2, fun i hi => actGoodXR.of_noCallSites (h3 i hi) hnc⟩⟩

/-- **The typed per-state world theorem with non-interference for either typed artifact or the
Stock artifact of an integer function, at the register-guarded semantics**
(`backend_correct_world_niX_pipelineAnyTS` for `CompiledAnyTSR` and `ActEntryR P`). -/
theorem backend_correct_world_niX_pipelineAnyTSRG (hM6 : RegLevelRG) (hsub : InSubsetTCF p f)
    (hc : CompiledAnyTSR p f k vc vcp rf af fa fb)
    (hT : TypedRules) {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    {P : BitVec 64 → Clif.Signature → Prop}
    (hPg : RegCompatGot P (f.externs.map (·.2)) (fun n => X.sym n 0))
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hPi : RegCompatInd P env (indSigs f) syms)
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
          ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodXR P vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
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
            ActEntryR P vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodXR P vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  rcases hc with hc | ⟨hsubS, hns, hc | ⟨hc, hnc⟩⟩
  · exact backend_correct_world_niX_pipelineAnyTFRG hM6 (hPg := hPg) (hPi := hPi) hsub hc hT hcov hX
      hXI hsym hslot hcs hrel hargs htr fuel
  · intro vals cm hrun
    obtain ⟨us, outs, w, hus, hlen, hhold, hmem, hrs, hall, hni⟩ :=
      backend_correct_world_niX_productionRG hM6 (K := K) (hPg := hPg) (hPi := hPi) hsubS hc hcov hX
        hXI hsym hslot hcs hrel hargs htr fuel vals cm hrun
    exact ⟨us, outs, w,
      retRegsOk_of_retPins hus (returned_int_stock hsubS hns hcs htr hrun) (by have := hhold.1; omega),
      returned_tys_stock hsubS hns hcs htr hrun, hlen, hhold, hmem, hrs, hall, hni⟩
  · intro vals cm hrun
    obtain ⟨us, outs, w, hus, hlen, hhold, hmem, hrs, hall, hni⟩ :=
      backend_correct_world_niX_semantic (K := K) hsubS hc hcov hX hXI hsym hslot hcs hrel hargs
        htr fuel vals cm hrun
    exact ⟨us, outs, w,
      retRegsOk_of_retPins hus (returned_int_stock hsubS hns hcs htr hrun) (by have := hhold.1; omega),
      returned_tys_stock hsubS hns hcs htr hrun, hlen, hhold, hmem, hrs,
      fun H G base ra s he =>
        let ⟨n, h1, h2, h3⟩ := hall H G base ra s (he.toActEntry hnc)
        ⟨n, h1, h2, fun i hi => actGoodXR.of_noCallSites (h3 i hi) hnc⟩,
      fun hNI hTls D w₀' hrel' hsw hreg hstk H G base ra s he =>
        let ⟨n, h1, h2, h3⟩ := hni hNI hTls D w₀' hrel' hsw hreg hstk H G base ra s (he.toActEntry hnc)
        ⟨n, h1, h2, fun i hi => actGoodXR.of_noCallSites (h3 i hi) hnc⟩⟩

end

end E2E

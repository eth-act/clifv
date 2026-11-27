import FV.E2E.CompiledAnyTS
import FV.E2E.CompiledAnyTR
import FV.E2E.CompiledProductionR

/-!
# Either typed artifact, or the Stock artifact of an integer function, at the register-guarded
semantics (#753, stage R2)

The four world theorems of the typed link layer (`backend_correct_world{,_ni,X,_niX}_pipelineAnyTS`)
for activations with the register-guarded callee contracts (`ActEntryR P`: a `.reg` call enters a
function `P` places at its target only with that function's argument and return registers), under
the contracts with registers (`RegCompatGot`, `RegCompatInd`) and M6 for the register-guarded
semantics (`RegLevelR`, stage R3), as premises:
`backend_correct_world_pipelineAnyTSR`, `backend_correct_world_ni_pipelineAnyTSR`,
`backend_correct_worldX_pipelineAnyTSR`, `backend_correct_world_niX_pipelineAnyTSR`.

Their artifact contract `CompiledAnyTSR` is `CompiledAnyTS` with the Stock artifact narrowed to
`CompiledSemanticNIR`: the retained production artifact (`CompiledProduction`, the artifact of
every function `SemanticNI.check` accepts through `lowerCheck`, the case of every function with a
call site), or a Stock-category artifact (`CompiledSemanticNI`) whose prepared code has no call
sites (`NoCallSites`; the Stock classifiers of `SemanticNI.check` admit no call), where
`ActEntryR P` is `ActEntry` (`ActEntryR.toActEntry`) and the existing Stock world theorems apply.
`CompiledAnyTSR.toTS`: every such artifact is a `CompiledAnyTS` one.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

set_option autoImplicit false

/-- **The Stock route's artifact for the register-guarded world theorems** (#753): the retained
production artifact (`CompiledProduction`, `CompiledSemanticNI.compatible`), or a Stock-category
artifact (`CompiledSemanticNI`) whose prepared code has no call sites. -/
def CompiledSemanticNIR (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc) (af : AFunc)
    (fa : FnAsm) (fb : FnBin) : Prop :=
  CompiledProduction f k vc vcp rf af fa fb ∨
    (CompiledSemanticNI f k vc vcp rf af fa fb ∧ NoCallSites vcp)

/-- **The Stock artifact of an integer function for the register-guarded world theorems**
(`CompiledStockT` with `CompiledSemanticNIR`). -/
def CompiledStockTR (p : Clif.Program) (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc)
    (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop :=
  InSubset p f ∧ f.sig.params.any (·.purpose == .sret) = false ∧
    CompiledSemanticNIR f k vc vcp rf af fa fb

/-- **The artifact contract of the register-guarded world theorems** (`CompiledAnyTS` with
`CompiledStockTR`). -/
def CompiledAnyTSR (p : Clif.Program) (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc)
    (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop :=
  CompiledAnyT p f k vc vcp rf af fa fb ∨ CompiledStockTR p f k vc vcp rf af fa fb

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

theorem CompiledSemanticNIR.toNI (h : CompiledSemanticNIR f k vc vcp rf af fa fb) :
    CompiledSemanticNI f k vc vcp rf af fa fb := by
  rcases h with h | ⟨h, -⟩
  · exact .compatible h
  · exact h

/-- Every `CompiledAnyTSR` artifact is a `CompiledAnyTS` one (its projections). -/
theorem CompiledAnyTSR.toTS (h : CompiledAnyTSR p f k vc vcp rf af fa fb) :
    CompiledAnyTS p f k vc vcp rf af fa fb := by
  rcases h with h | ⟨h1, h2, h3⟩
  · exact .inl h
  · exact .inr ⟨h1, h2, h3.toNI⟩

end

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64}

/-- **The typed per-state world theorem for either typed artifact or the Stock artifact of an
integer function, at the register-guarded semantics** (`backend_correct_worldX_pipelineAnyTS`
for `CompiledAnyTSR` and `ActEntryR P`, given M6 for the register-guarded semantics). -/
theorem backend_correct_worldX_pipelineAnyTSR (hM6 : RegLevelR) (hsub : InSubsetTCF p f)
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
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s) ∧
          (∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
            (runX (ArmStepX X H fa) i s)) ∧
          ∀ m, Arm.r .ERR (runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) := by
  rcases hc with hc | ⟨hsubS, hns, hc | ⟨hc, hnc⟩⟩
  · exact backend_correct_worldX_pipelineAnyTFR hM6 (hPg := hPg) (hPi := hPi) hsub hc hT hcov hX hXI
      hsym hslot hcs hrel hargs htr fuel
  · obtain ⟨hret, htrap⟩ := backend_correct_worldX_productionR hM6 (K := K) (hPg := hPg) (hPi := hPi)
      hsubS hc hcov hX hXI hsym hslot hcs hrel hargs htr fuel
    refine ⟨fun vals cm hrun => ?_, htrap⟩
    obtain ⟨us, outs, w, hus, hlen, hhold, hmem, hrs, hall⟩ := hret vals cm hrun
    exact ⟨us, outs, w,
      retRegsOk_of_retPins hus (returned_int_stock hsubS hns hcs htr hrun) (by have := hhold.1; omega),
      returned_tys_stock hsubS hns hcs htr hrun, hlen, hhold, hmem, hrs, hall⟩
  · obtain ⟨hret, htrap⟩ := backend_correct_worldX_semantic (K := K) hsubS hc.toSemantic hcov hX
      hXI hsym hslot hcs hrel hargs htr fuel
    refine ⟨fun vals cm hrun => ?_,
      fun c' hrun H G base ra s he => htrap c' hrun H G base ra s (he.toActEntry hnc)⟩
    obtain ⟨us, outs, w, hus, hlen, hhold, hmem, hrs, hall⟩ := hret vals cm hrun
    exact ⟨us, outs, w,
      retRegsOk_of_retPins hus (returned_int_stock hsubS hns hcs htr hrun) (by have := hhold.1; omega),
      returned_tys_stock hsubS hns hcs htr hrun, hlen, hhold, hmem, hrs,
      fun H G base ra s he => hall H G base ra s (he.toActEntry hnc)⟩

/-- **The typed per-state world theorem with non-interference for either typed artifact or the
Stock artifact of an integer function, at the register-guarded semantics**
(`backend_correct_world_niX_pipelineAnyTS` for `CompiledAnyTSR` and `ActEntryR P`). -/
theorem backend_correct_world_niX_pipelineAnyTSR (hM6 : RegLevelR) (hsub : InSubsetTCF p f)
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
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
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
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  rcases hc with hc | ⟨hsubS, hns, hc | ⟨hc, hnc⟩⟩
  · exact backend_correct_world_niX_pipelineAnyTFR hM6 (hPg := hPg) (hPi := hPi) hsub hc hT hcov hX
      hXI hsym hslot hcs hrel hargs htr fuel
  · intro vals cm hrun
    obtain ⟨us, outs, w, hus, hlen, hhold, hmem, hrs, hall, hni⟩ :=
      backend_correct_world_niX_productionR hM6 (K := K) (hPg := hPg) (hPi := hPi) hsubS hc hcov hX
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
      fun H G base ra s he => hall H G base ra s (he.toActEntry hnc),
      fun hNI hTls D w₀' hrel' hsw hreg hstk H G base ra s he =>
        hni hNI hTls D w₀' hrel' hsw hreg hstk H G base ra s (he.toActEntry hnc)⟩

/-- **The typed world theorem for either typed artifact or the Stock artifact of an integer
function, at the register-guarded semantics** (`backend_correct_world_pipelineAnyTS` for
`CompiledAnyTSR` and `ActEntryR P`; `backend_correct_worldX_pipelineAnyTSR` without the
per-state facts). -/
theorem backend_correct_world_pipelineAnyTSR (hM6 : RegLevelR) (hsub : InSubsetTCF p f)
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
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) := by
  obtain ⟨hret, htrap⟩ := backend_correct_worldX_pipelineAnyTSR hM6 (hPg := hPg) (hPi := hPi) hsub hc
    hT hcov hX hXI hsym hslot hcs hrel hargs htr fuel
  refine ⟨fun vals cm hrun => ?_, fun c' hrun H G base ra s he => ?_⟩
  · obtain ⟨us, outs, w, h1, h2, h3, h4, h5, h6, hall⟩ := hret vals cm hrun
    exact ⟨us, outs, w, h1, h2, h3, h4, h5, h6, fun H G base ra s he =>
      let ⟨n, ha, hp, _⟩ := hall H G base ra s he
      ⟨n, ha, hp⟩⟩
  · obtain ⟨n, ht, _⟩ := htrap c' hrun H G base ra s he
    exact ⟨n, ht⟩

/-- **The typed world theorem with non-interference for either typed artifact or the Stock
artifact of an integer function, at the register-guarded semantics**
(`backend_correct_world_ni_pipelineAnyTS` for `CompiledAnyTSR` and `ActEntryR P`;
`backend_correct_world_niX_pipelineAnyTSR` without the per-state facts). -/
theorem backend_correct_world_ni_pipelineAnyTSR (hM6 : RegLevelR) (hsub : InSubsetTCF p f)
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
            ActEntryR P vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n) := by
  intro vals cm hrun
  obtain ⟨us, outs, w, h1, h2, h3, h4, h5, h6, hall, hni⟩ :=
    backend_correct_world_niX_pipelineAnyTSR hM6 (hPg := hPg) (hPi := hPi) hsub hc hT hcov hX hXI
      hsym hslot hcs hrel hargs htr fuel vals cm hrun
  exact ⟨us, outs, w, h1, h2, h3, h4, h5, h6,
    fun H G base ra s he =>
      let ⟨n, ha, hp, _⟩ := hall H G base ra s he
      ⟨n, ha, hp⟩,
    fun hNI hTls D w₀' hrel' hsw hreg hstk H G base ra s he =>
      let ⟨n, ha, hp, _⟩ := hni hNI hTls D w₀' hrel' hsw hreg hstk H G base ra s he
      ⟨n, ha, hp⟩⟩

end

end E2E

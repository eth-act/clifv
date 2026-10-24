import FV.E2E.CompiledEitherT
import FV.E2E.CompiledEitherTC
import FV.E2E.FinalT
import FV.E2E.DeadCleanupT
import FV.E2E.DeadCleanupTC
import FV.Backend.Proof.DriverCheckTyC

/-!
# Either typed artifact, typed `try_call`s (S11e6, #419)

`CompiledEitherT` widened to also admit the scope with typed direct `try_call`s:
`CompiledAnyT p f …` is either the typed movement scope's artifact (`InSubsetT` with
`CompiledEitherT`) or the typed-`try_call` artifact (`CompiledEitherTC`). The projections keep
the consumers' `hc.alloc`-style access, and the four pipeline dispatch theorems dispatch on the
disjunction to the existing `…_pipelineT` (left, with `InSubsetT.toTC`) and the `…_pipelineTC`
theorems; their conclusions are literally the typed ones.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **The artifact contract of either typed scope**: the typed movement scope (`InSubsetT` with
`CompiledEitherT`) or the scope with typed `try_call`s (`CompiledEitherTC`). -/
def CompiledAnyT (p : Clif.Program) (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc)
    (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop :=
  (InSubsetT p f ∧ CompiledEitherT f k vc vcp rf af fa fb) ∨
    CompiledEitherTC f k vc vcp rf af fa fb

namespace CompiledAnyT
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

theorem lower (h : CompiledAnyT p f k vc vcp rf af fa fb) : lowerFunction f = .ok vc := by
  rcases h with ⟨-, h⟩ | h
  · exact h.lower
  · exact h.lower

theorem check (h : CompiledAnyT p f k vc vcp rf af fa fb) : checkAlloc vcp rf = .ok () := by
  rcases h with ⟨-, h⟩ | h
  · exact h.check
  · exact h.check

theorem alloc (h : CompiledAnyT p f k vc vcp rf af fa fb) : lowerRFunc vcp rf = .ok af := by
  rcases h with ⟨-, h⟩ | h
  · exact h.alloc
  · exact h.alloc

theorem emit (h : CompiledAnyT p f k vc vcp rf af fa fb) : emitFunc k af = .ok fa := by
  rcases h with ⟨-, h⟩ | h
  · exact h.emit
  · exact h.emit

theorem layout (h : CompiledAnyT p f k vc vcp rf af fa fb) : fa.layout = .ok fb := by
  rcases h with ⟨-, h⟩ | h
  · exact h.layout
  · exact h.layout

end CompiledAnyT

/-- `hasTls_of_vcodeCleanupAT` for `CompiledCleanupATC` (the typed-`try_call` cleanup
artifact). -/
theorem hasTls_of_vcodeCleanupATC {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupATC f k vc vcp rf af fa fb)
    (h : vcp.hasTls = true) : hasTls f = true := by
  cases hf : hasTls f
  · rw [noTls_of_prepCheck hc.prepOk (prune_noTls (noTlsTC_of_check hc.lowerOk hf))] at h
    cases h
  · rfl

/-- `hasTls_of_vcode_pipeline` for `CompiledAnyT`. -/
theorem hasTls_of_vcode_pipelineAnyT {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hc : CompiledAnyT p f k vc vcp rf af fa fb) (ht : vcp.hasTls = true) :
    hasTls f = true := by
  rcases hc with ⟨-, hc⟩ | hc
  · cases hc with
    | legacy hc => exact hasTls_of_vcodeAT hc.toA ht
    | cleanup hc => exact hasTls_of_vcodeCleanupAT hc.toA ht
  · cases hc with
    | legacy hc => exact hasTls_of_vcodeATC hc.toA ht
    | cleanup hc => exact hasTls_of_vcodeCleanupATC hc.toA ht

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64}

/-- **The typed world theorem for either artifact and either scope**
(`backend_correct_world_pipelineT`'s conclusion, literally). -/
theorem backend_correct_world_pipelineAnyT (hsub : InSubsetTC p f)
    (hc : CompiledAnyT p f k vc vcp rf af fa fb)
    (hT : TypedRules) {K : Nat}
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
  rcases hc with ⟨hsubT, hc⟩ | hc
  · exact backend_correct_world_pipelineT hsubT hc hT hcov hX hXI hsym hslot hcs hrel hargs htr
      fuel
  · exact backend_correct_world_pipelineTC hsub hc hT hcov hX hXI hsym hslot hcs hrel hargs htr
      fuel

/-- **The typed world theorem with non-interference for either artifact and either scope**
(`backend_correct_world_ni_pipelineT`'s conclusion, literally). -/
theorem backend_correct_world_ni_pipelineAnyT (hsub : InSubsetTC p f)
    (hc : CompiledAnyT p f k vc vcp rf af fa fb)
    (hT : TypedRules) {K : Nat}
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
  rcases hc with ⟨hsubT, hc⟩ | hc
  · exact backend_correct_world_ni_pipelineT hsubT hc hT hcov hX hXI hsym hslot hcs hrel hargs
      htr fuel
  · exact backend_correct_world_ni_pipelineTC hsub hc hT hcov hX hXI hsym hslot hcs hrel hargs
      htr fuel

/-- **The typed per-state world theorem for either artifact and either scope**
(`backend_correct_worldX_pipelineT`'s conclusion, literally). -/
theorem backend_correct_worldX_pipelineAnyT (hsub : InSubsetTC p f)
    (hc : CompiledAnyT p f k vc vcp rf af fa fb)
    (hT : TypedRules) {K : Nat}
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
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s) ∧
          (∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
            (runX (ArmStepX X H fa) i s)) ∧
          ∀ m, Arm.r .ERR (runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) := by
  rcases hc with ⟨hsubT, hc⟩ | hc
  · exact backend_correct_worldX_pipelineT hsubT hc hT hcov hX hXI hsym hslot hcs hrel hargs htr
      fuel
  · exact backend_correct_worldX_pipelineTC hsub hc hT hcov hX hXI hsym hslot hcs hrel hargs htr
      fuel

/-- **The typed per-state world theorem with non-interference for either artifact and either
scope** (`backend_correct_world_niX_pipelineT`'s conclusion, literally). -/
theorem backend_correct_world_niX_pipelineAnyT (hsub : InSubsetTC p f)
    (hc : CompiledAnyT p f k vc vcp rf af fa fb)
    (hT : TypedRules) {K : Nat}
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
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  rcases hc with ⟨hsubT, hc⟩ | hc
  · exact backend_correct_world_niX_pipelineT hsubT hc hT hcov hX hXI hsym hslot hcs hrel hargs
      htr fuel
  · exact backend_correct_world_niX_pipelineTC hsub hc hT hcov hX hXI hsym hslot hcs hrel hargs
      htr fuel

end

end E2E

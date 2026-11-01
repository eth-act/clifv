import FV.E2E.CompiledSemanticABI

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The checker branch determines the physical return convention. -/
inductive ReturnPinMode where
  | ordinary
  | stockABI
  deriving DecidableEq

namespace ReturnPinMode

/-- Retain ordinary x0 order or the actual Stock ABI return pins. -/
def Valid (mode : ReturnPinMode) (f : Clif.Function) (us : List (Reg × Reg)) : Prop :=
  match mode with
  | .ordinary => us.map (·.2) = (List.range us.length).map Reg.x
  | .stockABI => ReturnABI f us

/-- Compute the mode from the existing checker order. No caller certificate is required. -/
def checked (f : Clif.Function) (vc : VCode) : ReturnPinMode :=
  if SemanticNI.check f vc then .ordinary else .stockABI

/-- Select physical registers from the derived mode and original function signature. -/
def pins (mode : ReturnPinMode) (f : Clif.Function) (count : Nat) : List Reg :=
  match mode with
  | .ordinary => (List.range count).map Reg.x
  | .stockABI => (returnPins f count).getD []

/-- The selected registers agree with every return proved by the mode contract. -/
theorem pins_of_valid {mode : ReturnPinMode} {f : Clif.Function} {us : List (Reg × Reg)}
    (valid : mode.Valid f us) : mode.pins f us.length = us.map (·.2) := by
  cases mode with
  | ordinary => exact valid.symm
  | stockABI =>
    change (returnPins f us.length).getD [] = us.map (·.2)
    rw [show returnPins f us.length = some (us.map (·.2)) from valid]
    rfl

end ReturnPinMode

/-- Retain the checker branch with the existing actual pipeline artifact. -/
inductive CompiledSemanticReturnPins (f : Clif.Function) (k : Nat) (vc vcp : VCode)
    (rf : RFunc) (af : AFunc) (fa : FnAsm) (fb : FnBin) : ReturnPinMode → Prop where
  | compatible : CompiledSemanticNI f k vc vcp rf af fa fb →
      CompiledSemanticReturnPins f k vc vcp rf af fa fb .ordinary
  | memorySretCopy {cleanup : Bool} {result : Stock.Result} :
      Stock.Memory.SretCopy.CfgClass f → result.code = vc → Stock.MemoryStoreCfg.effectsOnly vc = true →
      CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb →
      CompiledSemanticReturnPins f k vc vcp rf af fa fb .stockABI

namespace CompiledSemanticReturnPins
variable {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} {mode : ReturnPinMode}

/-- The original ABI artifact remains available with all its guarantees. -/
theorem erase (hc : CompiledSemanticReturnPins f k vc vcp rf af fa fb mode) :
    CompiledSemanticABI f k vc vcp rf af fa fb := by
  cases hc with
  | compatible h => exact .compatible h
  | memorySretCopy family equal effects h => exact .memorySretCopy family equal effects h

/-- The actual checker and pipeline derive the mode internally. -/
theorem of_checks {cleanup : Bool} (lower : SemanticABI.check f vc = true)
    (prepared : Backend.prepare (Stock.Arithmetic.stage cleanup vc) = .ok vcp)
    (prepOk : prepCheck (Stock.Arithmetic.stage cleanup vc) vcp = true)
    (check : Backend.checkAlloc vcp rf = .ok ()) (alloc : lowerRFunc vcp rf = .ok af)
    (emit : emitFunc k af = .ok fa) (layout : fa.layout = .ok fb) :
    CompiledSemanticReturnPins f k vc vcp rf af fa fb (ReturnPinMode.checked f vc) := by
  by_cases old : SemanticNI.check f vc = true
  · simp only [ReturnPinMode.checked,old,↓reduceIte]
    exact .compatible (CompiledSemanticNI.of_checks old prepared prepOk check alloc emit layout)
  · have rejected : SemanticNI.check f vc = false := Bool.eq_false_iff.mpr old
    have memory : Stock.MemorySretCopy.check f vc = true := by
      simpa only [SemanticABI.check,rejected,Bool.false_or] using lower
    simp only [ReturnPinMode.checked,rejected,Bool.false_eq_true,↓reduceIte]
    obtain ⟨result,family,run,equal,effects⟩ := Stock.MemorySretCopy.check_sound memory
    exact .memorySretCopy family equal effects
      ⟨run,by rwa [equal],by rwa [equal],check,alloc,emit,layout⟩

end CompiledSemanticReturnPins

theorem backend_correct_world_niX_semantic_return_pins {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {mode : ReturnPinMode}
    (hsub : InSubset p f) (hc : CompiledSemanticReturnPins f k vc vcp rf af fa fb mode)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
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
        ReturnPinMode.Valid mode f us ∧ us.length = outs.length ∧
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
  cases hc with
  | compatible old =>
    intro vals cm returned
    obtain ⟨us,outs,w,pins,arity,values,memory,site,run,paired⟩ :=
      backend_correct_world_niX_semantic hsub old hcov hX hXI hsym hslot hcs hrel hargs htr fuel vals cm returned
    exact ⟨us,outs,w,pins,arity,values,memory,site,run,paired⟩
  | memorySretCopy family equal effects h =>
    subst vc
    classical
    by_cases tls : XTls F X
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,run,paired⟩ :=
        backend_correct_world_niX_stock_sret_copy_memory family effects h hcov hsym hslot tls hcs hrel hargs
          fuel vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,run,fun _ _ => paired⟩
    · intro vals cm returned
      obtain ⟨us,outs,w,pins,arity,values,memory,site,run⟩ :=
        (backend_correct_worldX_stock_memory_abi family.domainABI h hcov hsym hslot hcs hrel hargs fuel).1 vals cm returned
      exact ⟨us,outs,w,pins,arity,values,memory,site,run,fun _ positive => False.elim (tls positive)⟩


end E2E

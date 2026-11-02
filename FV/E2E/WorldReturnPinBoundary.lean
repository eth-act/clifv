import FV.E2E.CompiledProgramReturnPins
import FV.E2E.SemanticABIBoundary

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false


namespace CompiledProgramReturnPins
variable {L : LinkSys} {g : Clif.Function} {modes : Clif.Function → ReturnPinMode}

theorem entryRegs (hc : CompiledProgramReturnPins L g modes) :
    ∀ loc ∈ locsOf g.sig,∀ r,loc = .reg r → ∃ n,r = .x n ∧ n ≤ 8 :=
  hc.artifact.erase.entryRegs

end CompiledProgramReturnPins

/-- The new compilation field retains the existing TLS provenance boundary. -/
theorem hasTls_of_vcode_return_pins {L : LinkSys} {f : Clif.Function} {modes : Clif.Function → ReturnPinMode}
    (hc : CompiledProgramReturnPins L f modes) (tls : (L.A f).vcp.hasTls = true) : hasTls f = true :=
  hasTls_of_vcode_semantic_abi hc.artifact.erase tls

/-- The original stack-argument boundary follows from the same actual allocation. -/
theorem stackArgsAvoid_frameW_return_pins {L : LinkSys} {f : Clif.Function} {modes : Clif.Function → ReturnPinMode}
    (hc : CompiledProgramReturnPins L f modes) {K : Nat} {s : Arm.ArmState} {base ra : BitVec 64}
    {args : List Clif.Val} (room : StackAvail K (L.A f).af s)
    (entry : AbiEntry (L.A f).fb base ra s) (arguments : ArgsIn f.sig args s) :
    StackArgsAvoid (frameW K (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af s) f.sig args s :=
  stackArgsAvoid_frameW_semantic_abi hc.artifact.erase room entry arguments

theorem backend_correct_world_return_pins {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {mode : ReturnPinMode}
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
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ReturnPinMode.Valid mode f us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) := by
  cases hc with
  | compatible old =>
    exact backend_correct_world_semantic hsub old hcov hX hXI hsym hslot hcs hrel hargs htr fuel
  | memorySretCopy family equal effects stage =>
    subst vc
    have both := backend_correct_worldX_stock_memory_abi (p := p) (env := env) (K := K) family.domainABI stage hcov hsym hslot hcs hrel hargs fuel
    refine ⟨fun vals cm returned => ?_,fun code trapped H G base ra s entry => ?_⟩
    · obtain ⟨us,outs,w,pins,arity,values,memory,site,run⟩ := both.1 vals cm returned
      refine ⟨us,outs,w,pins,arity,values,memory,site,?_⟩
      intro H G base ra s entry
      obtain ⟨n,ret,trace,_⟩ := run H G base ra s entry
      exact ⟨n,ret,trace⟩
    · obtain ⟨n,trap,_⟩ := both.2 code trapped H G base ra s entry
      exact ⟨n,trap⟩
  | voidCall source equal h =>
    subst vc
    exact backend_correct_worldX_stock_void_call hsub source h hcov hX hXI hsym hslot hcs hrel hargs htr fuel

theorem backend_correct_world_ni_return_pins {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {mode : ReturnPinMode}
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
  intro vals cm returned
  obtain ⟨us,outs,w,pins,arity,values,memory,site,run,paired⟩ :=
    backend_correct_world_niX_semantic_return_pins (K := K) hsub hc hcov hX hXI hsym hslot hcs hrel hargs htr fuel vals cm returned
  refine ⟨us,outs,w,pins,arity,values,memory,site,?_,?_⟩
  · intro H G base ra s entry
    obtain ⟨n,ret,trace,_⟩ := run H G base ra s entry
    exact ⟨n,ret,trace⟩
  · intro hNI hTls D w' rel worlds regs stack H G base ra s entry
    obtain ⟨n,ret,trace,_⟩ := paired hNI hTls D w' rel worlds regs stack H G base ra s entry
    exact ⟨n,ret,trace⟩


/-- A supported signature with an implicit sret result has no explicit source returns. -/
theorem no_explicit_returns_of_sret {f : Clif.Function} (abi : sigAbiOk f.sig = true)
    (sret : (sigRets f.sig).any (·.purpose == .sret) = true) : f.sig.returns = [] := by
  simp only [sigAbiOk,Bool.and_eq_true] at abi
  have normal := abi.1.1.2
  apply Classical.byContradiction
  intro nonempty
  have nonemptyBool : f.sig.returns.isEmpty = false := by
    cases found : f.sig.returns with
    | nil => exact False.elim (nonempty found)
    | cons p ps => rfl
  have same : sigRets f.sig = f.sig.returns := by
    unfold sigRets
    cases found : f.sig.params.find? (·.purpose == .sret) <;> simp only [nonemptyBool,Bool.false_eq_true,↓reduceIte]
  rw [same] at sret
  obtain ⟨parameter,member,purpose⟩ := List.any_eq_true.mp sret
  have ordinary := beq_iff_eq.mp (List.all_eq_true.mp normal parameter member)
  simp [ordinary] at purpose

/-- Physical ABI pins retain every explicit source-result guarantee of ArmRefines. -/
theorem armRefines_of_actRet_return_pins {fb : FnBin} {base ra : BitVec 64}
    {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {F G : BitVec 64 → Prop}
    {syms : String → Option Nat} {f : Clif.Function} {mode : ReturnPinMode}
    {vals : List Clif.Val} {cm : Clif.Mem} {us : List (Reg × Reg)} {outs : List CV}
    {w : Arm.ArmState} (pins : mode.Valid f us) (abi : sigAbiOk f.sig = true)
    (types : vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns)
    (arity : us.length = outs.length) (values : PrefixHold vals outs) (memory : MemRel F syms cm w)
    {n : Nat} (returned : ActRet ra F G us outs w s (runX astep n s)) :
    ArmRefines fb base ra astep s (.returned vals cm) := by
  cases mode with
  | ordinary => exact armRefines_of_actRet pins arity values memory returned
  | stockABI =>
    by_cases ordinary : (sigRets f.sig).any (·.purpose == .sret) = false
    · exact armRefines_of_actRet (ReturnABI.ordinary pins ordinary) arity values memory returned
    · have sret : (sigRets f.sig).any (·.purpose == .sret) = true := by
        cases found : (sigRets f.sig).any (·.purpose == .sret) with
        | false => exact False.elim (ordinary found)
        | true => rfl
      have none := no_explicit_returns_of_sret abi sret
      have length := congrArg List.length types
      simp only [Clif.AbiParam.tys,none,List.map_nil,List.length_map,List.length_nil] at length
      have empty : vals = [] := by
        cases vals with
        | nil => rfl
        | cons v vs => simp only [List.length_cons] at length; omega
      subst vals
      refine ⟨n,returned.ret,?_,memAgree_of memory returned.mem⟩
      intro j v found
      simp at found

end E2E

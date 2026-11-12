import FV.E2E.LinkScopeDefsT
import FV.E2E.FinalDirectT

/-! # Soundness of the typed input conditions (S11e5 Stage C, slice 7)

`fnScopeTB g` (`LinkScopeDefsT.lean`) gives every per-function premise of the typed theorems
that is about `g` alone:

* `lowerScopeT_of` (`lowerScopeTB` decides `LowerScopeT`; integer: `lowerScopeTB_of_lowerScopeB`),
  `lowersTB_spec`, `fnScopeT_parts`;
* `inSubsetT_of_fnScopeT`: `InSubsetT` of the per-function programs (`P.bare`);
* `allocChecked_of_fnScopeT`: the allocation the backend lowers (`allocResult`, whatever the
  untrusted allocator answered) is `AllocChecked`; `compiledAT_of_fnScopeT`,
  `compiledT_of_fnScopeT`: the typed artifact contracts from the pipeline's results;
* `backend_correct_finalT_scope`: the typed final theorem of a function in the typed input
  scope (`backend_correct_finalT_alloc` with the decided premises discharged by `fnScopeTB`);
* `inScopePT_parts`: `InScopePT` is the program conditions and `fnScopeTB` of every function.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill

/-- **`lowerScopeTB` decides `LowerScopeT`.** -/
theorem lowerScopeT_of {f : Clif.Function} (h : lowerScopeTB f = true) : LowerScopeT f := by
  simp only [lowerScopeTB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hE, hne⟩, hent⟩, hctx⟩, htry⟩, hcall⟩, htc⟩, hind⟩ := h
  refine ⟨hE, hne, hent, fun ctx ranges st0 hb => ?_, fun B hB et het sig hsig i hi => ?_,
    ⟨fun B hB st hst fn args e hi he => ?_, fun B hB fn args et e ht he => ?_⟩, hind⟩
  · rw [hb] at hctx
    simp only [Bool.and_eq_true, List.all_eq_true] at hctx
    refine ⟨hctx.1, fun ii info inst x hi hc hm => ?_⟩
    have := hctx.2 info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
    simp only [hc, hm, decide_eq_true_eq] at this
    exact this
  · have := htry B hB
    rcases het with ⟨fn, args, ht⟩ | ⟨c, args, ht⟩ <;>
    · simp only [ht, hsig, List.all_eq_true] at this
      have := this _ hi
      simpa using this
  · have := hcall B hB st hst
    simp only [hi, he] at this
    exact this
  · have := htc B hB
    simp only [ht, he] at this
    exact this

/-- **Integer specialization**: `lowerScopeB` implies `lowerScopeTB`. -/
theorem lowerScopeTB_of_lowerScopeB {f : Clif.Function} (h : lowerScopeB f = true) :
    lowerScopeTB f = true := by
  unfold lowerScopeB at h
  unfold lowerScopeTB
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨hE, hne⟩, hent⟩, hctx⟩, htry⟩, hcall⟩, htc⟩, hind⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨Compile.functionET_of_functionE hE, hne⟩, hent⟩, hctx⟩, htry⟩, hcall⟩, htc⟩, hind⟩

theorem lowersTB_spec {f : Clif.Function} (h : lowersTB f = true) :
    extendsWidenB f = true ∧ ∃ vc vcp, lowerFunction f = .ok vc ∧ ctlSpillB vc = true ∧
      prepare vc = .ok vcp ∧ spillSizeOkB vcp = true ∧ formsCoveredB default vcp = true ∧
      killFreeB vcp = true := by
  unfold lowersTB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hw, h⟩ := h
  refine ⟨hw, ?_⟩
  split at h
  · rename_i vc hl
    rw [Bool.and_eq_true] at h
    obtain ⟨hc, h⟩ := h
    split at h
    · rename_i vcp hp
      simp only [Bool.and_eq_true] at h
      exact ⟨vc, vcp, hl, hc, hp, h.1.1, h.1.2, h.2⟩
    · cases h
  · cases h

theorem fnScopeT_parts {g : Clif.Function} (h : fnScopeTB g = true) :
    Compile.functionET g = true ∧ Compile.storeTypedB g = true ∧
    Compile.tryArgClassOk g = true ∧
    (sigAbiOk g.sig = true ∧ ∀ e ∈ g.externs, sigAbiOk e.2.sig = true) ∧ indSigsOk g = true ∧
    (regLocs g.sig).Nodup ∧ (∀ r ∈ regLocs g.sig, r.isArgReg = true) ∧
    (∀ p ∈ g.sig.params, p.ty.width ≤ 64) ∧ linkFreeB g = true ∧ dominatedB g = true ∧
    lowerScopeTB g = true ∧ arityOkB g = true ∧ resClassOkB g = true ∧ lowersTB g = true ∧
    entryParamsB g = true := by
  simp only [fnScopeTB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h4', h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, ⟨h4, h4'⟩, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

/-- **The typed subset of the per-function programs** from `fnScopeTB`. -/
theorem inSubsetT_of_fnScopeT {g : Clif.Function} (h : fnScopeTB g = true) (p : Clif.Program) :
    InSubsetT p.bare g := by
  obtain ⟨hE, hst, -, habi, hind, -⟩ := fnScopeT_parts h
  refine ⟨hE, ?_, ?_, habi, ?_, hst⟩
  · intro b _ st _ fn args _ e he
    exact Clif.Program.bare_func? _ _
  · intro b _ fn args et _ e he
    exact Clif.Program.bare_func? _ _
  · intro sig hs
    have := List.all_eq_true.mp hind sig hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2

/-- **The allocation the backend lowers is `AllocChecked`** for a function in the typed input
scope, whatever the untrusted allocator answered (slice 6's `allocChecked_allocResultT`, its
run-time premises decided by `fnScopeTB`). -/
theorem allocChecked_of_fnScopeT {g : Clif.Function} (h : fnScopeTB g = true) {vc vcp : VCode}
    (hl : lowerFunction g = .ok vc) (hp : prepare vc = .ok vcp) (ra : Except String RFunc) :
    AllocChecked vcp (allocResult vcp ra) := by
  obtain ⟨-, -, htc, -, -, -, -, -, -, hd, hs, har, hrc, hlo, -⟩ := fnScopeT_parts h
  obtain ⟨-, vc', vcp', hl', hctl, hp', -, hform, hk⟩ := lowersTB_spec hlo
  rw [hl] at hl'
  cases hl'
  rw [hp] at hp'
  cases hp'
  exact allocChecked_allocResultT (dominated_of hd) (lowerScopeT_of hs) (arityOk_of har) htc
    (resClassOk_of_resClassOkB hrc) hl hp (ctlSpill_of_ctlSpillB hctl)
    ((formsCoveredB_iff _ _).mp hform) hk ra

/-- **The typed artifact contract (`AllocChecked` form) of a function in the typed input
scope**, from the pipeline's results (no validator premise). -/
theorem compiledAT_of_fnScopeT {g : Clif.Function} (h : fnScopeTB g = true) {k : Nat}
    {vc vcp : VCode} {ra : Except String RFunc} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} (hl : lowerFunction g = .ok vc) (hp : prepare vc = .ok vcp)
    (hrf : rf = allocResult vcp ra) (ha : lowerRFunc vcp rf = .ok af)
    (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb) :
    E2E.CompiledAT g k vc vcp rf af fa fb := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hd, hs, -⟩ := fnScopeT_parts h
  exact E2E.CompiledAT.of_lowerT (dominated_of hd) (lowerScopeT_of hs) hl hp
    (hrf ▸ allocChecked_of_fnScopeT h hl hp ra) ha he hla

/-- **The typed artifact contract (`checkAlloc` form) of a function in the typed input scope**,
when `checkAlloc` accepts the allocation (the world theorems' `CompiledT`). -/
theorem compiledT_of_fnScopeT {g : Clif.Function} (h : fnScopeTB g = true) {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hl : lowerFunction g = .ok vc) (hp : prepare vc = .ok vcp)
    (hch : checkAlloc vcp rf = .ok ()) (ha : lowerRFunc vcp rf = .ok af)
    (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb) :
    E2E.CompiledT g k vc vcp rf af fa fb := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hd, hs, -⟩ := fnScopeT_parts h
  exact E2E.CompiledT.of_lowerT (dominated_of hd) (lowerScopeT_of hs) hl hp hch ha he hla

/-- **The typed final theorem of a function in the typed input scope**: for `fnScopeTB g`, the
backend's pipeline results (`lowerFunction`, `prepare`, the allocation `allocResult vcp ra` of
any allocator answer `ra`, `lowerRFunc`, emission, layout) and the run/link contracts, the Arm
run refines the CLIF run of the per-function program `p.bare`, each returned value in the ABI
return register of its class (`ArmRefinesT`), under the typed control families `TypedRules`. -/
theorem backend_correct_finalT_scope {p : Clif.Program} {g : Clif.Function}
    (h : fnScopeTB g = true) (hT : E2E.TypedRules) {k : Nat} {vc vcp : VCode}
    {ra : Except String RFunc} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hl : lowerFunction g = .ok vc) (hp : prepare vc = .ok vcp)
    (hrf : rf = allocResult vcp ra) (ha : lowerRFunc vcp rf = .ok af)
    (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb)
    (hcov : formsCoveredB ⟨fa.k, af.slotBase⟩ vcp = true)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ g.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls g = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (g.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs g) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ g sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra' : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra' s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn g.sig args s) (hcs : ClifEntry g args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ g cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p.bare cs) (fuel : Nat) :
    E2E.ArmRefinesT fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p.bare fuel cs) :=
  E2E.backend_correct_final_exT (inSubsetT_of_fnScopeT h p)
    (compiledAT_of_fnScopeT h hl hp hrf ha he hla) hT ((formsCoveredB_iff _ _).mp hcov) hC hCT
    hTls hX hXI hsym hslot hent hres hbe hargs hcs hrel htr fuel

/-- `InScopePT`: the program conditions and `fnScopeTB` of every function. -/
theorem inScopePT_parts {I : LinkInput} (h : InScopePT I = true) :
    progScopeB I.prog (fun n => I.syms.lookup n) = true ∧ ∀ g ∈ I.prog.funcs, fnScopeTB g = true := by
  simp only [InScopePT, Bool.and_eq_true, List.all_eq_true] at h
  exact h

end E2E.LinkCheck

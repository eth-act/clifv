import FV.E2E.Compose
import FV.Backend.Proof.DriverCheckSound
import FV.Backend.Proof.PrepareSound
import FV.Backend.Proof.IselMemArm
import FV.E2E.RegLevelEmit

/-!
# M7: `backend_correct`

The end-to-end theorem from the layer hypotheses: M4's rule theorems (`LowerRulesCorrect`,
`ExcludedUnmatchable`, and the terminator calls `TermCalls`, themselves proven from M4's
terminator rule statements in `backend_correct_of_rules`), M6+M5's register-level theorem
(`RegLevelCorrect`) and the semantics facts `Refines`/`DriverSem` of the shared VCode semantics.
M7's own obligations are discharged by the validators the pipeline runs (`Compiled.lowerOk`,
`Compiled.prepOk`): `loweringObligations_of_check`, `prepareCorrect_of_check`. The CLIF → VCode
driver simulation (`driver_correct`) and the composition (`backend_correct_of_layers`) are
proven.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

theorem memRel_free {F : BitVec 64 → Prop} {syms} {cm : Clif.Mem} {w : Arm.ArmState}
    (h : MemRel F syms cm w) (bases : List Nat) : MemRel F syms (cm.free bases) w := by
  have hv : ∀ a n, (cm.free bases).valid a n = true → cm.valid a n = true := by
    intro a n hv
    simp only [Clif.Mem.valid, Clif.Mem.free, List.any_eq_true, List.mem_filter] at hv ⊢
    obtain ⟨x, ⟨hx, -⟩, hc⟩ := hv
    exact ⟨x, hx, hc⟩
  exact ⟨fun a b ha hb => h.bytes a b (hv a 1 ha) hb, fun a n ha => h.valid a n (hv a n ha),
    h.symbols⟩

/-- The CLIF ↔ VCode relation only looks at memory outside `F` and at `sp`: M4's `MRStable`. -/
theorem mrStable_holds (Γ : Rel) (f : Clif.Function) :
    MRStable Γ.F (fun sl cm w => Γ.holds f sl cm w) := by
  intro sl cm w w' hsw ⟨hm, hs, ho⟩
  have hsp : spv w' = spv w := by
    simp only [spv]
    exact hsw.1 (.GPR 31#5) (by simp [Masked]) (fun fl h => by cases h)
  refine ⟨⟨fun a b ha hb => ?_, hm.valid, hm.symbols⟩, ?_, ?_⟩
  · have hF := (hm.valid a 1 ha).2 0 (by omega)
    simp only [Nat.add_zero] at hF
    rw [← hm.bytes a b ha hb]
    simp only [Arm.read_mem, Arm.read_store]
    rw [hsw.2.1 _ hF]
  · simpa [Rel.slotReg, hsp] using hs
  · simpa only [OutRel, hsp] using ho

/-- The CLIF ↔ VCode relation satisfies what M4's memory rules need (`MemRelOk`, contract change
#7): bytes/allocations/symbols from `MemRel`, slots from `SlotRel`, and a store of `n` bytes to a
live allocation on both sides keeps `MemRel` (same allocations; the written bytes agree, the
others are untouched on both sides) and `SlotRel` (`sp` unchanged). -/
theorem memRelOk_holds (Γ : Rel) (f : Clif.Function) :
    MemRelOk Γ.F Γ.slotOff Γ.syms f (fun sl cm w => Γ.holds f sl cm w) where
  bytes := fun _ _ _ a b h ha hb => h.1.bytes a b ha hb
  valid := fun _ _ _ a n h ha => h.1.valid a n ha
  symbols := fun _ _ _ h => h.1.symbols
  slots := fun _ _ w id b h hl => by
    obtain ⟨off, ho, hb⟩ := h.2.1 id b hl
    exact ⟨off, ho, by rw [hb]; rfl⟩
  store := fun sl cm w a n y h hv => by
    obtain ⟨hm, hs, ho⟩ := h
    have hA := (hm.valid a n hv).1
    have hsp' : spv (Arm.write_mem_bytes n (BitVec.ofNat 64 a) y w) = spv w := by
      simp only [spv, Arm.r_of_write_mem_bytes]
    refine ⟨⟨fun a' b ha' hb => ?_, fun a' k hk => hm.valid a' k hk, hm.symbols⟩, ?_, ?_⟩
    · rw [writeBits_valid] at ha'
      have ha64 := (hm.valid a' 1 ha').1
      rw [read_mem_write_mem_bytes y w hA (by omega)]
      rw [writeBits_bytes] at hb
      split
      · rename_i hin
        rw [if_pos hin] at hb
        cases hb
        apply BitVec.eq_of_getLsbD_eq
        intro k hk
        simp [hk]
      · rename_i hin
        rw [if_neg hin] at hb
        exact hm.bytes a' b ha' hb
    · simpa [Rel.slotReg, hsp'] using hs
    · refine ⟨ho.1, by rw [hsp']; exact ho.2.1, fun a' k hv' => ?_⟩
      rw [hsp']
      exact ho.2.2 a' k (by rwa [writeBits_valid] at hv')

/-- The relation keeps the outgoing stack-argument area free (`OutRel`): writes there keep it
(M4's `OutArgsOk`, agent/stack-tls-proof). -/
theorem outArgsOk_holds (Γ : Rel) (f : Clif.Function) :
    OutArgsOk Γ.F Γ.out (fun sl cm w => Γ.holds f sl cm w) := by
  intro sl cm w ⟨hm, hs, ho⟩
  refine ⟨ho.1, ho.2.1, fun k n y hkn => ?_⟩
  have hsp' : spv (Arm.write_mem_bytes n (spOf w + BitVec.ofNat 64 k) y w) = spv w := by
    simp only [spv, Arm.r_of_write_mem_bytes]
  have hne : ∀ a, (∃ n', cm.valid a n' = true ∧ 0 < n') → ∀ j < n,
      BitVec.ofNat 64 a ≠ spOf w + BitVec.ofNat 64 k + BitVec.ofNat 64 j := by
    intro a ⟨n', hv, hn'⟩ j hj e
    rw [BitVec.add_assoc, show BitVec.ofNat 64 k + BitVec.ofNat 64 j = BitVec.ofNat 64 (k + j) by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]] at e
    exact ho.2.2 a n' hv 0 hn' (k + j) (by omega) (by simpa using (show BitVec.ofNat 64 a = spv w + BitVec.ofNat 64 (k + j) from e))
  refine ⟨⟨fun a b ha hb => ?_, hm.valid, hm.symbols⟩, ?_, ?_⟩
  · rw [← hm.bytes a b ha hb]
    simp only [Arm.read_mem, Arm.read_store]
    rw [writeBytes_mem_ne _ _ _ _ _ (hne a ⟨1, ha, by omega⟩)]
  · simpa [Rel.slotReg, hsp'] using hs
  · simpa only [OutRel, hsp'] using ho

theorem noTail_of_subset {p : Clif.Program} {f : Clif.Function} (h : InSubset p f) :
    ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args := by
  intro B hB fn args ht
  have := h.subsetE
  simp only [Compile.functionE, Bool.and_eq_true, List.all_eq_true] at this
  have := (this.2 B hB).2
  rw [ht] at this
  simp [Compile.termE] at this

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp at h
  | (k, v) :: l, a, b, h => by
    by_cases hk : a = k
    · subst hk; simp at h; subst h; simp
    · simp only [List.lookup, show (a == k) = false from by simpa using hk] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

theorem cfg_of_prepare {vc vcp : VCode} (h : prepare vc = .ok vcp) :
    ∃ ss ps, vc.cfg = .ok (ss, ps) := by
  unfold prepare at h
  cases hc : vc.cfg with
  | ok r => exact ⟨r.1, r.2, rfl⟩
  | error e => rw [hc] at h; cases h

/-- The call-site signature of an indirect call of an in-subset function is one of its
indirect-call signatures, with register arguments. -/
theorem indSig_of_subset {p : Clif.Program} {f : Clif.Function} (h : InSubset p f) :
    ∀ B ∈ f.blocks, ∀ st ∈ B.body, IndSigOk f (indSigs f) st.inst := by
  intro B hB st hst sig callee args s hi hs
  have hmem : s ∈ indSigs f := by
    unfold indSigs
    refine List.mem_flatMap.mpr ⟨B, hB, List.mem_append_left _ (List.mem_filterMap.mpr ⟨st, hst, ?_⟩)⟩
    rw [hi]; exact hs
  exact ⟨hmem, (h.indSigs s hmem).1⟩

/-- The same for a `try_call_indirect` (its exception table's signature). -/
theorem tryIndSig_of_subset {p : Clif.Program} {f : Clif.Function} (h : InSubset p f) :
    ∀ B ∈ f.blocks, ∀ c args et s, B.term = .tryCallIndirect c args et →
      f.sigDecls.lookup et.sig = some s → s ∈ indSigs f ∧ s.params.length ≤ 8 := by
  intro B hB c args et s ht hs
  have hmem : s ∈ indSigs f := by
    unfold indSigs
    refine List.mem_flatMap.mpr ⟨B, hB, List.mem_append_right _ ?_⟩
    rw [ht]; simp [hs]
  exact ⟨hmem, (h.indSigs s hmem).1⟩

/-- **CLIF → VCode** from the driver simulation (the entry loads read memory through `sem`'s
load forms, `MemRefines`). -/
theorem iselSim_of_driver {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {sem : Sem} {Γ : Rel} {env : Clif.Env} {p : Clif.Program}
    (H : DriverHyp f vc ctx st0 R gn bl A sem (fun sl cm w => Γ.holds f sl cm w) env p)
    {sb : Nat} (hMem : MemRefines Γ.F sb Γ.syms sem) :
    IselSim sem Γ env p f vc := by
  intro args cs w₀ ρ₀ hce hrel hargs htr fuel
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := by
    have hf := hce.func
    exact ⟨htr.stmt, fun s c fn args et hr hs hb hT B hB => htr.tryCall s c fn args et hr hs hb hT B
        (hf ▸ hB),
      fun s c callee args et hr hs hb hT B hB =>
        htr.tryCallInd s c callee args et hr hs hb hT B (hf ▸ hB),
      fun s st rest sig callee args hr hb hi ⟨B, hB, hst⟩ =>
        htr.indirect s st rest sig callee args hr hb hi ⟨B, hf ▸ hB, hst⟩,
      fun s callee args et hr hb hT ⟨B, hB, e⟩ =>
        htr.tryIndirect s callee args et hr hb hT ⟨B, hf ▸ hB, e⟩⟩
  have hrun := driver_correct H hMem (mrStable_holds Γ f) hB0 hce.callers hce.func rfl hbody hterm
    hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs hP fuel
  refine ⟨fun vals cm h => ?_, fun c h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_free h4.1 _⟩
  · rw [h] at hrun
    exact hrun

/-- **M7's lowering obligations** from the lowering validator. -/
theorem loweringObligations_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheck f vc = true) :
    LoweringObligations f vc :=
  lowering_of_check h

/-- **`prepare` preserves returns and traps**, from the `prepare` validator. -/
theorem prepareCorrect_of_check {sem : Sem} {vc vcp : VCode} (hds : DriverSem sem)
    (h : prepCheck vc vcp = true) : PrepareCorrect sem vc vcp :=
  fun ρ₀ w₀ => prep_sound hds h ρ₀ w₀

/-- The stack-passed arguments' bytes avoid the frame addresses `F` (agent/stack-tls-proof; for
the backend's frame `frameF` this follows from `ArgsIn` and `StackAvail`, `stackArgsAvoid_frameF`). -/
def StackArgsAvoid (F : BitVec 64 → Prop) (sig : Clif.Signature) (args : List Clif.Val)
    (s : Arm.ArmState) : Prop :=
  ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf sig).zip args →
    Avoids F v.ty.bytes (spv s + BitVec.ofNat 64 off)

theorem fp_off_eq (a : BitVec 64) (off : Nat) :
    a - 16#64 + BitVec.ofInt 64 (16 + (off : Int)) = a + BitVec.ofNat 64 off := by
  have h : BitVec.ofInt 64 (16 + (off : Int)) = 16#64 + BitVec.ofNat 64 off := by
    apply BitVec.eq_of_toNat_eq
    rw [show (16 + (off : Int)) = ((16 + off : Nat) : Int) by push_cast; rfl, BitVec.ofInt_natCast]
    simp [BitVec.toNat_add]
  rw [h, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The arguments of the ABI entry state `s` are where the entry code reads them in the
body-entry world `w₀`: the register-passed ones in x0–x8 (kept by the prologue), the
stack-passed ones at `fp + 16 + off` (the prologue's fp is `sp - 16`; memory is unchanged). -/
theorem argsAtEntry_body {f : Clif.Function} {args : List Clif.Val} {af : AFunc}
    {s w₀ : Arm.ArmState} {F : BitVec 64 → Prop} (hframe : af.frame = true)
    (hregs : ∀ l ∈ locsOf f.sig, ∀ r, l = .reg r → ∃ n, r = .x n ∧ n ≤ 8)
    (hbe : BodyEntry af s w₀) (h : ArgsIn f.sig args s) (hav : StackArgsAvoid F f.sig args s) :
    ArgsAtEntry F f.sig args w₀ := by
  intro loc v hm
  have hl : loc ∈ locsOf f.sig := (List.of_mem_zip hm).1
  have h1 := h loc v hm
  have hfp : Arm.r (.GPR 29#5) w₀ = spv s - 16#64 := by
    have := hbe.fp; simp only [hframe, ↓reduceIte] at this; exact this
  cases loc with
  | reg r =>
    obtain ⟨n, rfl, hn⟩ := hregs _ hl r rfl
    simp only at h1 ⊢
    rw [regVal_x, show xreg n w₀ = xreg n s from hbe.args n (by omega)]
    exact h1
  | stack off =>
    simp only at h1 ⊢
    rw [hfp, fp_off_eq]
    refine ⟨hav off v hm, ?_⟩
    rw [show Arm.read_mem_bytes v.ty.bytes (spv s + BitVec.ofNat 64 off) w₀ =
        Arm.read_mem_bytes v.ty.bytes (spv s + BitVec.ofNat 64 off) s from
      read_mem_bytes_congr _ _ (fun k _ => by rw [hbe.mem])]
    exact h1.bytes

theorem callsStack_mono {f : Clif.Function} {a b : Nat} (h : CallsStack f a) (hab : a ≤ b) :
    CallsStack f b := fun B hB st hst fn args e hi he =>
  ⟨Nat.le_trans (h B hB st hst fn args e hi he).1 hab, (h B hB st hst fn args e hi he).2⟩

theorem tryStack_mono {f : Clif.Function} {a b : Nat} (h : TryStack f a) (hab : a ≤ b) :
    TryStack f b := fun B hB fn args et hi e he =>
  ⟨Nat.le_trans (h B hB fn args et hi e he).1 hab, (h B hB fn args et hi e he).2⟩

/-- **`backend_correct` (M7).** For an in-subset CLIF function `f` of `p`, compiled by the
Lean backend (`Compiled`, including M7's validators) and loaded at `base`, an Arm execution
from an ABI entry state `s` with enough stack, whose CLIF counterpart `cs` has its stack slots at
the body frame's slot region (relative to the body-entry world `w₀`) and its memory related to the
Arm memory, refines the CLIF run: returns with the same values (low bits) and memory, traps at a
trap site with the same code (explicit traps; a `try_call`: its normal return). Hypotheses: M4
(`hrules`, `hex`, `hterms`, `htries`), M6+M5 (`hM6`), the shared VCode semantics of each
activation (`hRef`, `hds`). -/
theorem backend_correct {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    -- M4
    (hrules : LowerRulesCorrect Isle.Aarch64.program)
    (hex : ExcludedUnmatchable Isle.Aarch64.program)
    (hcallRules : CallRulesCorrect Isle.Aarch64.program)
    (hindRules : IndRulesCorrect Isle.Aarch64.program)
    (hmemRules : MemRulesCorrect Isle.Aarch64.program)
    (hterms : ∀ s, TermCalls (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w))
    (htries : ∀ s, TryCalls f (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w)
      env p out)
    (htryInds : ∀ s, TryIndCalls (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w)
      env p (indSigs f))
    -- M6 + M5
    (hM6 : RegLevelCorrect sem F astep vcp af fb)
    -- the shared VCode semantics (M6's `csem`)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    -- the callee contract (M6, from `CalleeSound`)
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    -- the indirect-call contract (M6, from `XCallsIndOk`)
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    -- the memory forms (M6: loads/stores/`loadAddr`/GOT loads of `csem` with slot base `slotOff`
    -- and the link-time symbol addresses `syms`)
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    -- the outgoing stack-argument area of the relation holds every call's stack arguments
    (houtB : vc.outgoing ≤ out)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs) := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligations_of_check hc.lowerOk
  refine backend_correct_of_layers (fun s' => iselSim_of_driver (ctx := ctx) (st0 := st0) (R := R)
    (gn := gn) (bl := bl) (A := A) ?_ (hmem s')) (fun s' => prepareCorrect_of_check (hds s') hc.prepOk)
    hM6 hent hres hbe
    (argsAtEntry_body (lowerRFunc_frame hc.alloc) (entryRegs_of_check hc.lowerOk) hbe hargs hargF)
    hcs hrel htr fuel
  exact {
    shape := hshape
    cert := hcert
    dsem := hds s'
    insts := instCalls_of_rules hrules hex hcallRules hindRules hmemRules (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hcalls s') (hicalls s') (hmem s')
      (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f)
      (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (memRelOk_holds ⟨F s', syms, slotOff, out⟩ f)
    terms := hterms s'
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hc.lowerOk
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨out, htries s', tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := htryInds s'
    tryIndSig := tryIndSig_of_subset hsub
    cfg := cfg_of_prepare hc.prepare }

/-- **`backend_correct` from M4's rule statements only**: the terminator calls (`TermCalls`)
from M4's terminator rules (`termCalls_of_rules`), the `try_call` calls (`TryCalls`) from M4's
`try_call` rules (`tryCalls_of_rules`). -/
theorem backend_correct_of_rules {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    -- M4
    (hrules : LowerRulesCorrect Isle.Aarch64.program)
    (hex : ExcludedUnmatchable Isle.Aarch64.program)
    (hcallRules : CallRulesCorrect Isle.Aarch64.program)
    (hindRules : IndRulesCorrect Isle.Aarch64.program)
    (hmemRules : MemRulesCorrect Isle.Aarch64.program)
    (htermRules : LowerTermRulesCorrect Isle.Aarch64.program)
    (htermUn : TermUnmatchable Isle.Aarch64.program)
    (hbranch : BranchRulesCorrect Isle.Aarch64.program)
    (hbranchEx : BranchExcludedUnmatchable Isle.Aarch64.program)
    (htryRules : TryRulesCorrect Isle.Aarch64.program)
    (htryUn : TryUnmatchable Isle.Aarch64.program)
    (htryIndRules : TryIndRulesCorrect Isle.Aarch64.program)
    (htryIndUn : TryIndUnmatchable Isle.Aarch64.program)
    -- M6 + M5
    (hM6 : RegLevelCorrect sem F astep vcp af fb)
    -- the shared VCode semantics (M6's `csem`)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    -- the callee contract (M6, from `CalleeSound`)
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    -- the indirect-call contract (M6, from `XCallsIndOk`)
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    -- the memory forms (M6: loads/stores/`loadAddr`/GOT loads of `csem` with slot base `slotOff`
    -- and the link-time symbol addresses `syms`)
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    -- the outgoing stack-argument area of the relation holds every call's stack arguments
    (houtB : vc.outgoing ≤ out)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs) :=
  backend_correct hsub hc hrules hex hcallRules hindRules hmemRules
    (fun s' => termCalls_of_rules htermRules htermUn hbranch hbranchEx (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f))
    (fun s' => tryCalls_of_rules htryRules htryUn (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hmem s')
      (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f) (hcalls s'))
    (fun s' => tryIndCalls_of_rules htryIndRules htryIndUn (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hicalls s'))
    hM6 hRef hds hcalls hicalls hmem houtB hent hres hbe hargs hargF hcs hrel htr fuel

end E2E

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

theorem slots_fold_ids (ss : List (Clif.SlotId × Clif.StackSlot)) :
    ∀ (acc : List (Clif.SlotId × Nat)) (m : Clif.Mem),
      (ss.foldl (fun (acc : List (Clif.SlotId × Nat) × Clif.Mem) (s : Clif.SlotId × Clif.StackSlot) =>
        let (base, m) := acc.2.alloc s.2.size (s.2.align.getD 1)
        (acc.1 ++ [(s.1, base)], m)) (acc, m)).1.map (·.1) = acc.map (·.1) ++ ss.map (·.1) := by
  induction ss with
  | nil => intro acc m; simp
  | cons s ss ih =>
    intro acc m
    simp only [List.foldl_cons]
    rw [ih]
    simp

/-- `Clif.run`'s own initial state (bump-allocated slots) is a `ClifEntry`: the theorem's CLIF
entry states differ from `Clif.initState` only in the (unspecified) slot addresses and the
initial memory. -/
theorem clifEntry_initState {p : Clif.Program} {f : Clif.Function} {args : List Clif.Val}
    {mem : Clif.Mem} {s : Clif.State} (hf : p.func? f.name = some f)
    (h : Clif.initState p f.name args mem = .ok s) : ClifEntry f args s := by
  simp only [Clif.initState, hf, Clif.Res.ofOption_some, Clif.Res.ok_bind] at h
  cases he : Clif.enterFunc f args mem with
  | ok r =>
    rw [he] at h
    obtain ⟨fr, mem'⟩ := r
    simp only [Clif.Res.ok_bind, Clif.Res.pure_eq, Clif.Res.ok.injEq] at h
    subst h
    unfold Clif.enterFunc at he
    rcases checkTys_cases s!"arguments of %{f.name}" args (Clif.AbiParam.tys f.sig.params) with
      ⟨hc1, hty1⟩ | ⟨m, hc1⟩
    · rw [hc1] at he
      simp only [Clif.Res.ok_bind] at he
      cases hen : f.entry? with
      | none => rw [hen] at he; cases he
      | some b =>
        rw [hen] at he
        simp only [Clif.Res.ofOption_some, Clif.Res.ok_bind] at he
        rcases checkTys_cases s!"entry block of %{f.name}" args (b.params.map (·.2)) with
          ⟨hc2, hty2⟩ | ⟨m, hc2⟩
        · rw [hc2] at he
          simp only [Clif.Res.ok_bind] at he
          cases hs : Clif.Regs.empty.setMany (b.params.map (·.1)) args with
          | none => rw [hs] at he; cases he
          | some regs =>
            rw [hs] at he
            simp only [Clif.Res.ofOption_some, Clif.Res.ok_bind, Clif.Res.pure_eq,
              Clif.Res.ok.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            refine ⟨rfl, rfl, by simpa [Clif.AbiParam.tys] using hty1,
              ⟨b, hen, rfl, rfl, hty2.symm, hs⟩, ?_⟩
            have := slots_fold_ids f.slots [] mem
            simpa using this
        · rw [hc2] at he; cases he
    · rw [hc1] at he; cases he
  | trap => rw [he] at h; cases h
  | stuck => rw [he] at h; cases h

end E2E

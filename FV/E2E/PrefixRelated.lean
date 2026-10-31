import FV.E2E.DeadCleanupPrefix
import FV.E2E.ExtSemGuardR
import FV.E2E.BackendWorldPRB

/-!
# The machine's earlier calls are the CLIF run's (SEM1 #537, item (d), docs/plans/uninit.md §5.9)

The induction step of the slot-byte statement needs, for each call `j < N` of the activation, that
the machine's call-`j` state passes arguments and a world related to the CLIF invocation of count
`j` (so that the callee statement one level down applies to both and the oracle counters agree).
The pipeline relates them only inside the simulation; this file reads the relation off it with a
call semantics answering only related calls:

* `ExtSemI.relOnly XI Q`: call `n` of `XI` where `Q n d uses w`, undefined elsewhere;
  `relOnly_call_some`, `relOnly_call_of`;
* `csemV_of_call_sub`, `CalleeOkGP.ofCallSub`, `CalleeTryOkGP.ofCallSub` (the machine contracts are
  antitone in the call results), `ActEntryPRN.relOnly`;
* `RelatedN`: the call `(d, uses, w)` is related to the CLIF invocation of count `n` (its
  contract `CallPostN` is not vacuous); `xCalls_relOnly` (stage 1 for `XI.relOnly (RelatedN …)`
  from stage 1 for `XI`);
* **`prefix_related_cleanupPRI`**, **`prefix_relatedPRI`**: `backend_prefix*PRI` whose last
  conjunct also states that the machine's call `j < N` is `RelatedN … j`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

open Classical in
/-- **The calls of `XI` where `Q` holds**, undefined elsewhere. -/
noncomputable def _root_.Backend.Proof.ExtSemI.relOnly (XI : ExtSemI)
    (Q : Nat → Option String → List CV → Arm.ArmState → Prop) : ExtSemI :=
  { XI with call := fun n d uses w => if Q n d uses w then XI.call n d uses w else none }

theorem relOnly_call_some {XI : ExtSemI} {Q : Nat → Option String → List CV → Arm.ArmState → Prop}
    {n : Nat} {d : Option String} {uses : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState}
    (h : ((XI.relOnly Q).at n).call d uses w = some r) :
    Q n d uses w ∧ (XI.at n).call d uses w = some r := by
  simp only [ExtSemI.at, ExtSemI.relOnly] at h ⊢
  by_cases hq : Q n d uses w
  · simp only [hq, ↓reduceIte] at h; exact ⟨hq, h⟩
  · simp only [hq, ↓reduceIte] at h; cases h

theorem relOnly_call_of {XI : ExtSemI} {Q : Nat → Option String → List CV → Arm.ArmState → Prop}
    {n : Nat} {d : Option String} {uses : List CV} {w : Arm.ArmState} (hq : Q n d uses w) :
    ((XI.relOnly Q).at n).call d uses w = (XI.at n).call d uses w := by
  simp [ExtSemI.at, ExtSemI.relOnly, hq]

/-- **Fewer call results, fewer instruction results.** -/
theorem csemV_of_call_sub {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {X : ExtSem} (c : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState))
    (hc : ∀ d u w r, c d u w = some r → X.call d u w = some r) {i : MInst} {uses : List CV}
    {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : csemV gv F ctx { X with call := c } i uses w = some r) : csemV gv F ctx X i uses w = some r := by
  cases hi : i.isCallI
  · rw [← csemV_call_congr gv F ctx X c hi]; exact h
  · obtain ⟨info, hci⟩ := callLike_of_isCallI hi
    rcases hci with rfl | ⟨ti, rfl⟩
    · simp only [csemV] at h ⊢
      split at h
      · rename_i hg1
        have hg2 : gotGuard gv X info uses := hg1
        simp only [csem, Option.map_eq_some_iff] at h
        simp only [hg2, ↓reduceIte, csem, Option.map_eq_some_iff]
        obtain ⟨r', hr', e⟩ := h
        exact ⟨r', hc _ _ _ _ hr', e⟩
      · cases h
    · simp only [csemV] at h ⊢
      split at h
      · rename_i hg1
        have hg2 : gotGuard gv X info uses := hg1
        simp only [csem, Option.map_eq_some_iff, Option.filter_eq_some_iff] at h
        simp only [hg2, ↓reduceIte, csem, Option.map_eq_some_iff, Option.filter_eq_some_iff]
        obtain ⟨r', ⟨hr', hf⟩, e⟩ := h
        exact ⟨r', ⟨hc _ _ _ _ hr', hf⟩, e⟩
      · cases h

theorem _root_.Backend.Proof.CalleeOkGP.ofCallSub {P : Arm.ArmState → Prop} {F : BitVec 64 → Prop}
    {K : Nat} {G : BitVec 64 → Prop} {s0 : Arm.ArmState} {Pc : BitVec 64 → MInst → Prop}
    {X : ExtSem} {H : ArmHooks} {S : CallInfo → Prop} {gv : Nat → String → Prop}
    (h : CalleeOkGP P F K G s0 Pc X H S gv)
    (c : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState))
    (hc : ∀ d u w r, c d u w = some r → X.call d u w = some r) :
    CalleeOkGP P F K G s0 Pc { X with call := c } H S gv :=
  ⟨fun ctx info hS s hP hK hF hG cc wh ops regs i' w outs w' hops hst hasg hpi hsw hal herr hsem =>
    h.os ctx info hS s hP hK hF hG cc wh ops regs i' w outs w' hops hst hasg hpi hsw hal herr
      (csemV_of_call_sub c hc hsem),
    h.pc, fun d uses w outs w' hx herr => h.ext d uses w outs w' (hc _ _ _ _ hx) herr⟩

theorem _root_.Backend.Proof.CalleeTryOkGP.ofCallSub {P : Arm.ArmState → Prop}
    {F : BitVec 64 → Prop} {K : Nat} {G : BitVec 64 → Prop} {s0 : Arm.ArmState}
    {Pc : BitVec 64 → MInst → Prop} {X : ExtSem} {H : ArmHooks} {S : CallInfo → TryInfo → Prop}
    {gv : Nat → String → Prop} (h : CalleeTryOkGP P F K G s0 Pc X H S gv)
    (c : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState))
    (hc : ∀ d u w r, c d u w = some r → X.call d u w = some r) :
    CalleeTryOkGP P F K G s0 Pc { X with call := c } H S gv :=
  fun ctx info ti hS cc wh ops regs i' s w outs w' s' hP hK hF hG hops hst hasg hpi hsw hal herr
    hsem hex => h ctx info ti hS cc wh ops regs i' s w outs w' s' hP hK hF hG hops hst hasg hpi hsw
      hal herr (csemV_of_call_sub c hc hsem) hex

/-- **The machine entry for `XI` is one for `XI.relOnly Q`** (fewer call results). -/
theorem ActEntryPRN.relOnly {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {K : Nat} {F G : BitVec 64 → Prop} {XI : ExtSemI} {H : ArmHooks} {base ra : BitVec 64}
    {Kp : Nat} {c : BitVec 64} {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState}
    {s w₀ : Arm.ArmState} {N : Nat} (h : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp c P R s w₀ N)
    (Q : Nat → Option String → List CV → Arm.ArmState → Prop) :
    ActEntryPRN vcp rf af fa fb K F G (XI.relOnly Q) H base ra Kp c P R s w₀ N :=
  ⟨h.abi, h.stack, h.gfree, h.hF, h.proph, h.regp,
    fun n hn => (h.calls n hn).ofCallSub _ fun _ _ _ _ hx => (relOnly_call_some hx).2,
    fun ht n hn => (h.tries ht n hn).ofCallSub _ fun _ _ _ _ hx => (relOnly_call_some hx).2,
    h.pc, fun ht n => ⟨(h.tls ht n).pc, (h.tls ht n).seq, (h.tls ht n).flags⟩, h.body⟩

/-- **The call `(d, uses, w)` is related to the CLIF invocation of count `n`**: its contract is
not vacuous. -/
def RelatedN (env : Clif.Env) (p : Clif.Program) (cs : Clif.State) (exts : List Clif.ExtFunc)
    (sigs : List Clif.Signature) (MR : MemRelT) (sym : String → Int → BitVec 64) (n : Nat)
    (d : Option String) (uses : List CV) (w : Arm.ArmState) : Prop :=
  ¬ ∀ r, CallPostN env p cs exts sigs MR sym n d uses w r

/-- **Stage 1 for `XI.relOnly (RelatedN …)` from stage 1 for `XI`**: the contracts ask only at
related calls. -/
theorem xCalls_relOnly {env : Clif.Env} {p : Clif.Program} {cs : Clif.State}
    {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {MR : MemRelT} {XI : ExtSemI}
    (hnrc : NoRetCall env p cs) {s : Clif.State} {n : Nat} (hs : ReachN env p cs s n)
    (hX : XCallsOk (env.only (Clif.Invoked env p s)) exts MR (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) sigs MR (XI.at n)) :
    XCallsOk (env.only (Clif.Invoked env p s)) exts MR
        ((XI.relOnly (RelatedN env p cs exts sigs MR XI.sym)).at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) sigs MR
        ((XI.relOnly (RelatedN env p cs exts sigs MR XI.sym)).at n) := by
  have hAA := invoked_sub_invokedN hnrc hs
  refine ⟨fun ext hext g sl cm w d uses args vals rvals cm' hg hd ha hmr hret hlen => ?_,
    fun sig hsig nm g sl cm w u args vals rvals cm' hg hsg hlo hargs hmr hret hlen hty => ?_⟩
  · have hq : RelatedN env p cs exts sigs MR XI.sym n d uses w := fun hv =>
      callPost_not_vacuous (sl := sl) hext hg hd ha hmr hret hlen fun r =>
        callPost_only_mono hAA (hv r)
    rw [relOnly_call_of hq]
    exact hX.1 ext hext g sl cm w d uses args vals rvals cm' hg hd ha hmr hret hlen
  · have hq : RelatedN env p cs exts sigs MR XI.sym n none (u :: args) w := fun hv =>
      callPost_not_vacuous_ind (sl := sl) hsig hg hsg hlo hargs hmr hret hlen hty fun r =>
        callPost_only_mono hAA (hv r)
    rw [relOnly_call_of hq]
    exact hX.2 sig hsig nm g sl cm w u args vals rvals cm' hg hsg hlo hargs hmr hret hlen hty

/-- **The machine's earlier calls are the CLIF run's, cleanup path**: `backend_prefix_cleanupPRI`
with, at the machine's call `j < N`, the VCode call `(callDest info, uses, w)` related to the
CLIF invocation of count `j` (`RelatedN`). -/
theorem prefix_related_cleanupPRI {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hnrc : NoRetCall env p cs)
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) {N : Nat} {H : ArmHooks} {G : BitVec 64 → Prop}
    {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64} {P : Nat → BitVec 64 → BitVec 8}
    {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State} (hr : ReachN env p cs t N) (hcn : callNum t = 1) :
    ∀ j < N, ∃ u i info uses w r, OnCall (ArmStepX (XI.at 0) H fa) fa base s j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧ CallSiteAt F K G s fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧
      (XI.at j).call (callDest info) uses w = some r ∧
      RelatedN env p cs (f.externs.map (·.2)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym j (callDest info) uses w := by
  intro j hj
  obtain ⟨u, i, info, uses, w, r, hon, hsp, hsite, hci, hx⟩ :=
    backend_prefix_cleanupPRI (XI := XI.relOnly (RelatedN env p cs (f.externs.map (·.2)) (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym))
      hsub hc hone htc hcov (fun s n hs => xCalls_relOnly hnrc hs (hX s n hs)) hsym hslot hcs hrel
      hargs htr (he.relOnly _) hr hcn j hj
  obtain ⟨hq, hx'⟩ := relOnly_call_some hx
  exact ⟨u, i, info, uses, w, r, hon, hsp, hsite, hci, hx', hq⟩

/-- **The machine's earlier calls are the CLIF run's, `Compiled` path.** -/
theorem prefix_relatedPRI {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hnrc : NoRetCall env p cs)
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) {N : Nat} {H : ArmHooks} {G : BitVec 64 → Prop}
    {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64} {P : Nat → BitVec 64 → BitVec 8}
    {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State} (hr : ReachN env p cs t N) (hcn : callNum t = 1) :
    ∀ j < N, ∃ u i info uses w r, OnCall (ArmStepX (XI.at 0) H fa) fa base s j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧ CallSiteAt F K G s fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧
      (XI.at j).call (callDest info) uses w = some r ∧
      RelatedN env p cs (f.externs.map (·.2)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym j (callDest info) uses w := by
  intro j hj
  obtain ⟨u, i, info, uses, w, r, hon, hsp, hsite, hci, hx⟩ :=
    backend_prefixPRI (XI := XI.relOnly (RelatedN env p cs (f.externs.map (·.2)) (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) XI.sym))
      hsub hc hone htc hcov (fun s n hs => xCalls_relOnly hnrc hs (hX s n hs)) hsym hslot hcs hrel
      hargs htr (he.relOnly _) hr hcn j hj
  obtain ⟨hq, hx'⟩ := relOnly_call_some hx
  exact ⟨u, i, info, uses, w, r, hon, hsp, hsite, hci, hx', hq⟩

end E2E

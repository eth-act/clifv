import FV.Backend.Proof.DriverCheckTyC
import FV.Backend.Proof.DriverCheckCF

/-!
# The typed lowering validator with the proven float operations (S11f, #35)

Soundness of `lowerCheckTCF` (`DriverCheckCF.lean`: `lowerCheckTC` whose supported-instruction
check is `instScopeOkF`, `Compile.instETF`): `lowerShapeTC_of_okF`, `loweringTCF_of_check` (the
shape `LowerShapeTC`, whose scope is `InstScopeTF`) and the tail facts
(`noTryCallTCF_of_check`, `noTlsTCF_of_check`, `callsStackTCF_of_check`, `tryStackTCF_of_check`,
`entryOkTCF_of_check`, `entryRegsTCF_of_check`). It accepts what `lowerCheckTC` accepts
(`lowerCheckTCF_of_lowerCheckTC`). `lowerCheckTC` and its theorems are unchanged.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- `shapeOkT`'s acceptance is `shapeOkTF`'s. -/
theorem shapeOkTF_of_shapeOkT {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {gn : Nat → Nat} {bl : List BLow} (h : shapeOkT f vc ctx st0 gn bl = true) :
    shapeOkTF f vc ctx st0 gn bl = true := by
  unfold shapeOkT at h
  unfold shapeOkTF
  cases hI : instScopeOk ctx
  · simp [hI] at h
  · have hF := instScopeOkF_complete (instScopeOk_sound hI).toTF
    simp only [hI] at h
    simp only [hF]
    exact h

/-- **`lowerCheckTC`'s acceptance is `lowerCheckTCF`'s.** -/
theorem lowerCheckTCF_of_lowerCheckTC {f : Clif.Function} {vc : VCode}
    (h : lowerCheckTC f vc = true) : lowerCheckTCF f vc = true := by
  unfold lowerCheckTC at h
  unfold lowerCheckTCF
  split at h
  · cases h
  · rename_i ctx ranges st0 hb
    simp only [hb]
    split at h
    · cases h
    · rename_i bl hl
      simp only [hl]
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨⟨shapeOkTF_of_shapeOkT h.1.1.1.1, h.1.1.1.2⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩

/-- **Soundness of the typed shape check with the float operations.** -/
theorem lowerShapeTC_of_okF {f : Clif.Function} {vc : VCode} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st0 : LState} {bl : List BLow} {gn : Nat → Nat}
    (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hl : lowBlocksC f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl)
    (hgn : ∀ n, st0.nextVreg ≤ n → gn n = n) (hs : shapeOkTF f vc ctx st0 gn bl = true) :
    LowerShapeTC f vc ctx st0 (renOf gn) gn bl := by
  obtain ⟨-, hlb⟩ := lowBlocksC_spec hl
  simp only [shapeOkTF, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hctx, hsc⟩, hvb⟩, hpar⟩, hlen⟩, hsize⟩, hlab⟩, hblk⟩, hfresh⟩ := hs
  have hblk' : ∀ bi B L, f.blocks[bi]? = some B → bl[bi]? = some L →
      blockOkT f vc ctx st0 (renOf gn) gn bl bi B L = true := by
    intro bi B L hB hL
    have := all_range hblk (lt_of_getElem? hB)
    simpa [hB, hL] using this
  refine ⟨⟨ranges, hb⟩, ctxOkT_sound hctx, instScopeOkF_sound hsc, renOf_vrenaming gn, hgn, ?_,
    hlen, hsize, ?_, ?_, hfresh, ?_, ?_⟩
  · intro B hB p hp
    have := List.all_eq_true.mp (List.all_eq_true.mp hpar B hB) p hp
    simpa using this
  · intro x r hx
    have : x < ctx.valReg.size := lt_valReg hx
    omega
  · intro l vb hvb
    have := all_range hlab (Array.getElem?_eq_some_iff.mp hvb).1
    simpa [hvb] using this
  · intro bi B L hB hL
    have h := hblk' bi B L hB hL
    unfold blockOkT at h
    split at h
    · cases h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have h' := h.2
      split at h'
      · rename_i info hinfo
        simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, Option.isNone_iff_eq_none] at h'
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
        rw [hinfo]
        cases info
        simp_all
      · cases h'
  · intro bi B L hB hL
    obtain ⟨hsl, hsj, htemp0, nl0, nl', hterm⟩ := hlb bi B L hB hL
    obtain ⟨hnt, hty⟩ := lowTermC_spec hterm
    have h := hblk' bi B L hB hL
    unfold blockOkT at h
    split at h
    · cases h
    · rename_i vb hvb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hst⟩, htemp⟩, hle⟩, hcode⟩, htne⟩, hpars⟩, hbargs⟩, hsucc⟩, -⟩ := h
      refine ⟨vb, hvb, hsl, ?_, by simpa using htemp, hle, fun hnt' => ?_, fun et ht => ?_,
        hcode, by simpa using htne, hpars, hbargs, succOkT_sound hsucc⟩
      rotate_left
      · obtain ⟨h1, h2, out, tr, h3⟩ := hnt hnt'
        exact ⟨h1, h2, out, tr, h3⟩
      · obtain ⟨T, h1, h2, h3, -, h5, h6, out, tr, h7⟩ := hty et ht
        exact ⟨T, h1, h2, h3, h5, h6, out, tr, h7⟩
      intro j stm sl hj hslj
      have := all_range hst (lt_of_getElem? hj)
      rw [hj, hslj] at this
      obtain ⟨h1, h2, h3, h4⟩ := stmtOk_sound this
      exact ⟨h1, h2, h3, hsj j sl hslj, h4⟩

/-- **Soundness of the validator with the float operations**: `lowerCheckTCF f vc = true` gives
the typed structure of the VCode (`LowerShapeTC`, scope `InstScopeTF`), an SSA availability
certificate and the `br_table` index typing. -/
theorem loweringTCF_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckTCF f vc = true) :
    ∃ ctx st0 R gn bl A, LowerShapeTC f vc ctx st0 R gn bl ∧ Cert f ctx st0 gn bl A ∧
      ∀ B ∈ f.blocks, BrIdxTyped ctx B.term := by
  unfold lowerCheckTCF at h
  split at h
  · cases h
  · rename_i ctx ranges st0 hb
    split at h
    · cases h
    · rename_i bl hl
      simp only [Bool.and_eq_true] at h
      have hS := lowerShapeTC_of_okF (gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))) hb hl
        (fun n hn => gnAt_temp hn) h.1.1.1.1
      exact ⟨ctx, st0, _, _, bl, _, hS, cert_of_ok hS.len h.1.1.1.2, brIdx_of_ok h.1.1.2⟩

/-- The tail of `lowerCheckTCF` (its conjuncts after the shape and certificate). -/
theorem lowerCheckTCF_tail {f : Clif.Function} {vc : VCode} (h : lowerCheckTCF f vc = true) :
    ((f.blocks.any (·.term.isTry) || !vc.hasTryCall) && (hasTls f || !vc.hasTls)) = true ∧
      callsStackOkB f vc.outgoing = true ∧ entryOkBT f = true := by
  unfold lowerCheckTCF at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Bool.and_eq_true] at h
      exact ⟨by simp only [Bool.and_eq_true]; exact h.1.2, h.2.1, h.2.2⟩

/-- A function without `try_call` lowers to VCode without `tryCall` (`lowerCheckTCF`). -/
theorem noTryCallTCF_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckTCF f vc = true)
    (hf : ∀ B ∈ f.blocks, B.term.isTry = false) : vc.hasTryCall = false := by
  have h1 := (lowerCheckTCF_tail h).1
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1.1 with h2 | h2
  · obtain ⟨B, hB, hB'⟩ := List.any_eq_true.mp h2
    rw [hf B hB] at hB'; cases hB'
  · exact h2

/-- A function without `tls_value` lowers to VCode without `ElfTlsGetAddr` (`lowerCheckTCF`). -/
theorem noTlsTCF_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckTCF f vc = true)
    (hf : hasTls f = false) : vc.hasTls = false := by
  have h1 := (lowerCheckTCF_tail h).1
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1.2 with h2 | h2
  · rw [hf] at h2; cases h2
  · exact h2

/-- The calls of `f` fit the VCode's outgoing area (`lowerCheckTCF`). -/
theorem callsStackTCF_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckTCF f vc = true) :
    CallsStack f vc.outgoing := by
  have h2 := (lowerCheckTCF_tail h).2.1
  simp only [callsStackOkB, Bool.and_eq_true] at h2
  intro B hB st hst fn args e hi he
  have := List.all_eq_true.mp (List.all_eq_true.mp h2.1.1 B hB) st hst
  rw [hi] at this
  simp only [he, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- The callees of the `try_call`s of `f` fit the VCode's outgoing area (`lowerCheckTCF`). -/
theorem tryStackTCF_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckTCF f vc = true) :
    TryStack f vc.outgoing := by
  have h2 := (lowerCheckTCF_tail h).2.1
  simp only [callsStackOkB, Bool.and_eq_true] at h2
  intro B hB fn args et hi e he
  have := List.all_eq_true.mp h2.1.2 B hB
  rw [hi] at this
  simp only [he, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- The call-site signatures of the indirect calls of `f` fit the VCode's outgoing area
(`lowerCheckTCF`, S5). -/
theorem indStackTCF_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckTCF f vc = true) :
    IndStack (indSigs f) vc.outgoing := by
  have h2 := (lowerCheckTCF_tail h).2.1
  simp only [callsStackOkB, Bool.and_eq_true] at h2
  intro s hs
  have := List.all_eq_true.mp h2.2 s hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- The entry's parameter locations and byte sizes compute (`lowerCheckTCF`'s `entryOkBT`). -/
theorem entryOkTCF_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckTCF f vc = true) :
    (locsOf f.sig).length = f.sig.params.length ∧ ∃ bytes, sigParamBytes f.sig = .ok bytes := by
  have h2 := (lowerCheckTCF_tail h).2.2
  simp only [entryOkBT, Bool.and_eq_true, beq_iff_eq] at h2
  refine ⟨h2.1.1, ?_⟩
  have h3 := h2.2
  split at h3
  · exact ⟨_, ‹_›⟩
  · cases h3

/-- The register-passed parameters of the entry are in x0..x8 or v0..v7 (`lowerCheckTCF`). -/
theorem entryRegsTCF_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckTCF f vc = true) :
    ∀ l ∈ locsOf f.sig, ∀ r, l = .reg r → (∃ n, r = .x n ∧ n ≤ 8) ∨ (∃ n, r = .v n ∧ n ≤ 7) := by
  have h2 := (lowerCheckTCF_tail h).2.2
  simp only [entryOkBT, Bool.and_eq_true, beq_iff_eq] at h2
  intro l hl r hr
  have := List.all_eq_true.mp h2.1.2 l hl
  subst hr
  cases r with
  | x n => exact .inl ⟨n, rfl, by simpa using this⟩
  | v n => exact .inr ⟨n, rfl, by simpa using this⟩
  | _ => cases this

end Backend.Proof.Driver

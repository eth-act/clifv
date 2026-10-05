import FV.Backend.Proof.LowerSpec
import FV.Backend.Proof.PrepareComplete
import FV.Backend.Proof.IselTermFacts
import FV.Backend.Proof.LowerLoopPrep

/-!
# Completeness of `lowerCheck`: `lowerFunction`'s loop

`lowerFunction_run`: `lowerFunction`'s imperative per-block loop (statement loop, terminator,
`try_call` edge blocks, label counter, alias recording and resolution) computes exactly what the
recursive `lowBlocks` records, and its VCode is `vcBlocksOf f bl` (V1d). From it:
`prepDomain_of_lower` (V2: the VCode is in `PrepDomain`, so `prepCheck` accepts `prepare`'s
output) and `ctxOk_complete`.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Prep

variable {f : Clif.Function} {vc : VCode}

/-- What `buildCtx` builds. -/
theorem ctxFacts_of {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hb : buildCtx f = .ok (ctx, ranges, st0)) : CtxFacts f ctx st0 :=
  (ctxSpec_of hb).facts

/-- The recorded lowering has one entry per block, starting at the block's first instruction. -/
theorem lowBlocks_start {call : StmtCall} {tcall : TermCallF} {ycall : TryCallF} {st : LState}
    {nl : Nat} {bl : List BLow} (hl : lowBlocks f call tcall ycall 0 f.blocks st nl = some bl) :
    bl.length = f.blocks.length ∧ ∀ bi L, bl[bi]? = some L → L.start = blockStart f bi := by
  obtain ⟨h1, h2⟩ := lowBlocks_start_gen f.blocks 0 st nl bl hl
  exact ⟨h1, fun bi L h => by rw [h2 bi L h, Nat.zero_add, blockStart_eq]⟩

/-- **The loop simulation (V1d).** -/
theorem lowerFunction_run (h : lowerFunction f = .ok vc) :
    ∃ ctx ranges st0 bl, buildCtx f = .ok (ctx, ranges, st0) ∧
      lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
        some bl ∧
      vc.blocks = vcBlocksOf f bl ∧ vc.outgoing = outOf st0 bl ∧ LoopFacts f ctx bl := by
  obtain ⟨ctx, ranges, st0, pb, d, bl, hb, hpb, hI, rfl⟩ := loop_run h
  have hlow := hI.low
  rw [List.take_of_length_le (Nat.le_refl _)] at hlow
  have hmem : ∀ B ∈ f.blocks, ∃ bi, bi < f.blocks.length ∧ f.blocks[bi]? = some B := by
    intro B hB
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hB
    exact ⟨i, hi, by rw [List.getElem?_eq_getElem hi, e]⟩
  refine ⟨ctx, ranges, st0, bl, hb, by rw [lowBlocks_eq, hlow]; rfl, ?_, ?_, ?_⟩
  · apply Array.ext'
    simp [finishVC, vcBlocksOf, hI.blocks, hI.edges, hI.alias]
    rfl
  · simp only [finishVC, outOf]
    exact lowB_out f _ _ _ _ _ _ _ _ _ _ hlow
  · refine ⟨fun bi B L hB hL j stm sl hs hsl => hI.pf.results bi B L hB hL j stm sl hs hsl,
      fun B hB => ?_, fun bi B L et hB hL het => ?_, fun bi B L T _ hL hT => hI.pf.tryLast bi L T hL hT,
      fun hne => hI.pf.entry (List.length_pos_iff.mpr hne), ⟨pb, hpb⟩, fun B hB => ?_⟩
    · obtain ⟨bi, hbi, hB'⟩ := hmem B hB
      exact hI.pf.args bi B hbi hB'
    · obtain ⟨T, hT, hd⟩ := hI.pf.tryArgs bi B L et hB hL het
      refine ⟨T, hT, fun k td hk => ?_⟩
      obtain ⟨h1, h2⟩ := hd k td hk
      refine ⟨h1, fun a ha => ?_⟩
      have hkl : k < et.handlers.length + 1 := by
        have := (List.getElem?_eq_some_iff.mp hk).1
        simpa [Clif.ExnTable.dests] using this
      have := h2 a ha
      cases a with
      | val v => exact this
      | ret i => exact ⟨by simp only [ArgOk] at this; omega, this.2⟩
      | exn i => exact this
    · obtain ⟨bi, hbi, hB'⟩ := hmem B hB
      exact hI.pf.sret bi B hbi hB'

/-- **V2**: `lowerFunction`'s VCode is in `PrepDomain`. -/
theorem prepDomain_of_lower (hs : LowerScope f) (h : lowerFunction f = .ok vc) (_hne : f.blocks ≠ []) :
    Prep.PrepDomain vc :=
  prepDomain_of hs h

/-- `buildCtx`'s context passes `ctxOk` on in-scope input. -/
theorem ctxOk_complete (hs : LowerScope f) {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hb : buildCtx f = .ok (ctx, ranges, st0)) : ctxOk f ctx = true :=
  ctxOk_of hs hb

end Backend.Proof.Driver

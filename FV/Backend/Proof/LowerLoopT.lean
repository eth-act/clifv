import FV.Backend.Proof.LowerLoopSimT

/-!
# The typed loop simulation (S11e5 Stage C, slice 3)

`lowerFunction_runT`: for a function whose externs have integer signatures (`Compile.sigE`; the
recorded lowering `lowBlocks` lowers a `try_call` only on integer signatures, `lowerFunction`
also on `f32`/`f64` ones, S11e6), `lowerFunction`'s VCode is `vcBlocksOfT f ctx bl`, the
typed raw blocks (`rawBlockT`) and edge blocks (`edgeBlocksT`) of the recorded lowering, renamed
by the alias resolution, with the typed loop facts `LoopFactsT` (branch and `try_call` arguments
in their values' class vregs `vregOf ctx`).

Integer specialization: on an integer context (`CtxE`) the typed model is the integer one
(`rawBlockT_int`, `edgeBlocksT_int`, `vcBlocksOfT_int`, `LoopFactsT.toInt`), so the integer
`lowerFunction_run` follows from the typed one (`lowerFunction_run_of_runT`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Prep

/-- The blocks of `lowerFunction f`'s VCode, from the recorded lowering `bl` (typed). -/
def vcBlocksOfT (f : Clif.Function) (ctx : Ctx) (bl : List BLow) : Array VBlock :=
  let a := aliasArr (aliasOf f bl)
  let R := lowerFunction.resolve a (a.size + 1)
  ((((f.blocks.zip bl).zipIdx.map fun (p : (Clif.Block × BLow) × Nat) => rawBlockT f ctx bl p.2 p.1.1) ++
      (f.blocks.zip bl).flatMap fun (p : Clif.Block × BLow) => edgeBlocksT f ctx p.1 p.2).map
    (fixBlock R)).toArray

/-- What `lowerFunction` checks on the way that `lowBlocks` does not record (typed). -/
structure LoopFactsT (f : Clif.Function) (ctx : Ctx) (bl : List BLow) : Prop where
  results : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
    ∀ (j : Nat) (stm : Clif.Stmt) (sl : SLow), B.body[j]? = some stm → L.sl[j]? = some sl →
    (sl.rss.length = stm.results.length ∨ stm.results = []) ∧
    ∀ (r : Nat) (rs : List Reg), (r, rs) ∈ stm.results.zip sl.rss → ∃ x, rs = [x]
  args : ∀ B ∈ f.blocks, ∀ bc ∈ dests B.term, ∃ tb, f.block? bc.block = some tb ∧
    (bc.args ≠ [] → tb.params.length = bc.args.length) ∧
    ∀ a ∈ bc.args, ctx.valueReg? a = some (vregOf ctx a)
  tryArgs : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (et : Clif.ExnTable), f.blocks[bi]? = some B →
    bl[bi]? = some L → IsTryWith B.term et →
    ∃ T : TryLow, L.tl = some T ∧ ∀ (k : Nat) (td : Clif.TryDest), et.dests[k]? = some td →
      (∃ tb, f.block? td.block = some tb ∧ tb.params.length = td.args.length) ∧
      ∀ a ∈ td.args, match a with
        | .val v => ctx.valueReg? v = some (vregOf ctx v)
        | .ret i => k = et.handlers.length ∧ i < T.regs.1.length
        | .exn i => k ≠ et.handlers.length ∧ i < T.regs.2.length
  tryLast : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (T : TryLow), f.blocks[bi]? = some B →
    bl[bi]? = some L → L.tl = some T → ∃ c, L.tst'.emitted.back? = some (.call c)
  entry : f.blocks ≠ [] → ∃ locs n, sigArgLocs f.sig = .ok (locs, n)
  paramBytes : ∃ bytes, sigParamBytes f.sig = .ok bytes
  sret : ∀ B ∈ f.blocks, ∀ vs, B.term = .ret vs → sretRet f = [] → sigRets f.sig = f.sig.returns

variable {f : Clif.Function} {vc : VCode}

/-- **The typed loop simulation (V1d)**, for a function whose externs have integer signatures:
`lowerFunction`'s imperative loop computes what `lowBlocks` records, and its VCode is
`vcBlocksOfT f ctx bl`. -/
theorem lowerFunction_runT (hx : f.externs.all (Compile.sigE ·.2.sig) = true)
    (h : lowerFunction f = .ok vc) :
    ∃ ctx ranges st0 bl, buildCtx f = .ok (ctx, ranges, st0) ∧
      lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
        some bl ∧
      vc.blocks = vcBlocksOfT f ctx bl ∧ vc.outgoing = outOf st0 bl ∧ LoopFactsT f ctx bl := by
  obtain ⟨ctx, ranges, st0, pb, d, bl, hb, hpb, hI, rfl⟩ := loop_runT hx h
  have hlow := hI.low
  rw [List.take_of_length_le (Nat.le_refl _)] at hlow
  have hmem : ∀ B ∈ f.blocks, ∃ bi, bi < f.blocks.length ∧ f.blocks[bi]? = some B := by
    intro B hB
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hB
    exact ⟨i, hi, by rw [List.getElem?_eq_getElem hi, e]⟩
  refine ⟨ctx, ranges, st0, bl, hb, by rw [lowBlocks_eq, hlow]; rfl, ?_, ?_, ?_⟩
  · apply Array.ext'
    simp [finishVC, vcBlocksOfT, hI.blocks, hI.edges, hI.alias]
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
      | ret i => exact ⟨by simp only [ArgOkT] at this; omega, this.2⟩
      | exn i => exact this
    · obtain ⟨bi, hbi, hB'⟩ := hmem B hB
      exact hI.pf.sret bi B hbi hB'

/-! ## Integer specialization -/

theorem vrenaming_id : VRenaming id id := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

section
variable {ctx : Ctx} (hE : CtxE ctx)
include hE

theorem tryEdgeArgT_int (rets pays : List Reg) : tryEdgeArgT ctx rets pays = tryEdgeArg rets pays := by
  funext a; cases a <;> simp [tryEdgeArgT, tryEdgeArg, vregOf_int hE]

theorem rawBlockT_int (f : Clif.Function) (bl : List BLow) (bi : Nat) (B : Clif.Block) :
    rawBlockT f ctx bl bi B = rawBlock f bl bi B := by
  have hs : segT f ctx id bl bi = seg f id bl bi := funext (segT_int hE f id bl bi)
  simp only [rawBlockT, rawBlock, preT_int hE f vrenaming_id, hs, vregOf_int hE] <;> rfl

theorem edgeBlocksT_int (f : Clif.Function) (B : Clif.Block) (L : BLow) :
    edgeBlocksT f ctx B L = edgeBlocks f B L := by
  simp only [edgeBlocksT, edgeBlocks, tryEdgeArgT_int hE, vregOf_int hE] <;> rfl

theorem vcBlocksOfT_int (f : Clif.Function) (bl : List BLow) :
    vcBlocksOfT f ctx bl = vcBlocksOf f bl := by
  have hr : (fun (p : (Clif.Block × BLow) × Nat) => rawBlockT f ctx bl p.2 p.1.1) =
      fun p => rawBlock f bl p.2 p.1.1 := funext fun p => rawBlockT_int hE f bl p.2 p.1.1
  have he : (fun (p : Clif.Block × BLow) => edgeBlocksT f ctx p.1 p.2) =
      fun p => edgeBlocks f p.1 p.2 := funext fun p => edgeBlocksT_int hE f p.1 p.2
  simp only [vcBlocksOfT, vcBlocksOf, hr, he]

theorem LoopFactsT.toInt {f : Clif.Function} {bl : List BLow} (h : LoopFactsT f ctx bl) :
    LoopFacts f ctx bl := by
  refine ⟨h.results, fun B hB bc hbc => ?_, fun bi B L et hB hL het => ?_, h.tryLast, h.entry,
    h.paramBytes, h.sret⟩
  · obtain ⟨tb, h1, h2, h3⟩ := h.args B hB bc hbc
    exact ⟨tb, h1, h2, fun a ha => by rw [h3 a ha, vregOf_int hE]⟩
  · obtain ⟨T, hT, hd⟩ := h.tryArgs bi B L et hB hL het
    refine ⟨T, hT, fun k td hk => ?_⟩
    obtain ⟨h1, h2⟩ := hd k td hk
    refine ⟨h1, fun a ha => ?_⟩
    have := h2 a ha
    cases a with
    | val v => simp only at this ⊢; rw [this, vregOf_int hE]
    | ret i => exact this
    | exn i => exact this

end

/-- **Integer specialization**: the integer loop simulation `lowerFunction_run` (subset E) is the
typed one on an integer context. -/
theorem lowerFunction_run_of_runT (hE : Compile.functionE f = true) (h : lowerFunction f = .ok vc) :
    ∃ ctx ranges st0 bl, buildCtx f = .ok (ctx, ranges, st0) ∧
      lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
        some bl ∧
      vc.blocks = vcBlocksOf f bl ∧ vc.outgoing = outOf st0 bl ∧ LoopFacts f ctx bl := by
  have hx : f.externs.all (Compile.sigE ·.2.sig) = true := by
    simp only [Compile.functionE, Bool.and_eq_true] at hE; exact hE.1.2
  obtain ⟨ctx, ranges, st0, bl, hb, hl, hvb, hout, hlf⟩ := lowerFunction_runT hx h
  have hc : CtxE ctx := (ctxSpec_of hb).ctxE hE
  exact ⟨ctx, ranges, st0, bl, hb, hl, by rw [hvb, vcBlocksOfT_int hc], hout, hlf.toInt hc⟩

end Backend.Proof.Driver

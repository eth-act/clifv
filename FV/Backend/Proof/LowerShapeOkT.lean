import FV.Backend.Proof.LowerLoopT
import FV.Backend.Proof.LowerShapeOk
import FV.Backend.Proof.IselTermFactsTy
import FV.Backend.Proof.LowerLoopCtxTF

/-!
# Completeness of the typed shape check (S11e5 Stage C, slice 3)

`shapeOkT_complete`: on SSA input of the typed scope (`LowerScopeT`) with well-founded aliases,
`shapeOkT` accepts `lowerFunction`'s VCode, so the typed validator's shape `LowerShapeT` holds for
it (`lowerShapeT_of_lower`). The proof is `shapeOk_complete` over the typed loop simulation
(`lowerFunction_runT`) with one input fact stated separately: the terminator rules emit code
(`TermEmitsT`, or `TermEmitsTI` on terminators whose integer operands are in integer
positions). On integer contexts that is `term_emits` (`termEmitsT_of_ctxInv`); on float-capable
contexts it is `term_emitsTy` (`termEmitsTI_of_ctxInvT`), so `shapeOkT_completeT` and
`lowerShapeT_of_lowerT` need no premise beyond the typed scope.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

variable {f : Clif.Function} {vc : VCode}

/-- The terminator rules of context `ctx` emit code (`term_emits`'s conclusion). -/
def TermEmitsT (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ {ti : Nat}, ti < ctx.insts.size → ctx.insts[ti]? = some (⟨.op .unit, [], [], none⟩ : IInfo) →
    ∀ {t : Clif.Terminator}, t.isTry = false → ∀ {data : V}, termData (abiTerm f t) = .ok data →
    ∀ {targets : List Label}, TargetsLen t targets → ∀ {s : LState}, ValsBelow ctx s →
    BrIdxTyped ctx t → ∀ {out : V} {s' : LState} {tr : List Isle.RuleId},
    termCallF ctx ti data t targets s = .ok (some out, s', tr) → s.emitted.size < s'.emitted.size

/-- On an integer context the terminator rules emit code (`term_emits`). -/
theorem termEmitsT_of_ctxInv {ctx : Ctx} (h : CtxInv f ctx) : TermEmitsT f ctx :=
  fun hti hph _ ht _ hd _ htg _ hvb hbt _ _ _ hr => term_emits h hti hph ht hd htg hvb hbt hr

/-- `TermEmitsT` on terminators whose integer operands are in integer positions
(`TermIntPos`: on a typed-scope function, every terminator's, `termIntPos_of`). -/
def TermEmitsTI (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ {ti : Nat}, ti < ctx.insts.size → ctx.insts[ti]? = some (⟨.op .unit, [], [], none⟩ : IInfo) →
    ∀ {t : Clif.Terminator}, t.isTry = false → ∀ {data : V}, termData (abiTerm f t) = .ok data →
    ∀ {targets : List Label}, TargetsLen t targets → ∀ {s : LState}, ValsBelow ctx s →
    BrIdxTyped ctx t → TermIntPos ctx t → ∀ {out : V} {s' : LState} {tr : List Isle.RuleId},
    termCallF ctx ti data t targets s = .ok (some out, s', tr) → s.emitted.size < s'.emitted.size

theorem TermEmitsT.toI {ctx : Ctx} (h : TermEmitsT f ctx) : TermEmitsTI f ctx :=
  fun hti hph _ ht _ hd _ htg _ hvb hbt _ _ _ _ hr => h hti hph ht hd htg hvb hbt hr

/-- **On a float-capable context the terminator rules emit code** (`term_emitsTy`). -/
theorem termEmitsTI_of_ctxInvT {ctx : Ctx} (h : CtxInvT f ctx) : TermEmitsTI f ctx :=
  fun _ hph _ ht _ hd _ htg _ hvb hbt hip _ _ _ hr => term_emitsTy h hph ht hd htg hvb hbt hip hr

/-- The integer operands of a typed-scope function's terminators are in integer positions of
`buildCtx`'s context (`Compile.opsTypedT`). -/
theorem termIntPos_of (hs : LowerScopeT f) {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hb : buildCtx f = .ok (ctx, ranges, st0)) {B : Clif.Block}
    (hB : B ∈ f.blocks) : TermIntPos ctx B.term := by
  intro x hx t ht
  refine (ctxSpec_of hb).eCTys_of_not_floatDef ht fun hfd => ?_
  have hT := hs.subsetT
  simp only [Compile.functionET, Compile.opsTypedT, Bool.and_eq_true, List.all_eq_true] at hT
  have := (hT.1.2 B hB).2 x hx
  simp [hfd] at this

/-- The integer operands of a float-scope function's terminators are in integer positions of
`buildCtx`'s context (`Compile.opsTypedTF`). -/
theorem termIntPos_ofF (hs : LowerScopeTF f) {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hb : buildCtx f = .ok (ctx, ranges, st0)) {B : Clif.Block}
    (hB : B ∈ f.blocks) : TermIntPos ctx B.term := by
  intro x hx t ht
  refine (ctxSpec_of hb).eCTys_of_not_floatDef ht fun hfd => ?_
  have hO := (functionETF_parts hs.subsetTF).2.2.2.1
  simp only [Compile.opsTypedTF, Bool.and_eq_true, List.all_eq_true] at hO
  have := (hO B hB).2 x hx
  simp [hfd] at this

/-! ## Renaming the typed recorded code -/

theorem preT_map (ctx : Ctx) {R : Reg → Reg} {gn : Nat → Nat} (hR : VRenaming R gn) (bi : Nat) :
    (preT f ctx id bi).map (MInst.mapRegs R) = preT f ctx R bi := by
  unfold preT
  split
  · simp only [List.map_cons, MInst.mapRegs, entryRegsT, entryLoadsT, List.map_filterMap]
    congr 2
    · congr 1
      funext q
      unfold entryRegOfT
      split <;> rfl
    · congr 1
      funext q
      unfold entryLoadOfT
      split
      · simp only [Option.map_some]
        cases hc : valClassOf ctx q.1.1.1 <;>
          simp [vregOf, stackArgLoad, hc, hR.vreg, Reg.homeCls, MInst.mapRegs, AMode.mapRegs]
      · rfl
  · rfl

theorem segT_map (ctx : Ctx) (R : Reg → Reg) (bl : List BLow) (bi j : Nat) :
    (segT f ctx id bl bi j).map (MInst.mapRegs R) = segT f ctx R bl bi j := by
  unfold segT
  split
  · split
    · exact shape_map_mapRegs_id R _
    · rfl
  · rfl

/-- The renamed instructions of a typed raw block are the `R`-renamed typed code. -/
theorem rawBlockT_insts (ctx : Ctx) {R : Reg → Reg} {gn : Nat → Nat} (hR : VRenaming R gn)
    (bl : List BLow) (bi : Nat) (B : Clif.Block) :
    ((rawBlockT f ctx bl bi B).insts.map (MInst.mapRegs R)).toList =
      preT f ctx R bi ++ ((List.range B.body.length).map (segT f ctx R bl bi)).flatten ++
        tseg R bl bi := by
  simp only [rawBlockT, Array.toList_map, List.map_append, preT_map ctx hR, tseg_map,
    List.map_flatten, List.map_map, Function.comp_def, segT_map]

/-! ## Edge blocks -/

/-- The edge block of a branch successor (typed). -/
def edgeOfBcT (f : Clif.Function) (ctx : Ctx) (p : Clif.BlockCall × Label) : Option VBlock :=
  if p.1.args.isEmpty then none else (blockIdx? f p.1.block).map fun tl =>
    { label := p.2, insts := #[.jump tl], branchArgs := (p.1.args.map fun a => vregOf ctx a).toArray }

/-- The edge block of a `try_call` successor (typed). -/
def edgeOfTryT (f : Clif.Function) (ctx : Ctx) (T : TryLow) (p : Clif.TryDest × Label) :
    Option VBlock :=
  (blockIdx? f p.1.block).map fun tl =>
    { label := p.2, insts := #[.jump tl],
      branchArgs := (p.1.args.map (tryEdgeArgT ctx T.regs.1 T.regs.2)).toArray }

theorem shape_edgeBlocksT_try {ctx : Ctx} {B : Clif.Block} {L : BLow} {et : Clif.ExnTable}
    {T : TryLow} (ht : IsTryWith B.term et) (hT : L.tl = some T) :
    edgeBlocksT f ctx B L = (et.dests.zip L.targets).filterMap (edgeOfTryT f ctx T) := by
  unfold edgeBlocksT
  rcases ht with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h, hT] <;> rfl

theorem shape_edgeBlocksT_other {ctx : Ctx} {B : Clif.Block} {L : BLow}
    (ht : B.term.isTry = false) (hj : ∀ bc, B.term ≠ .jump bc) :
    edgeBlocksT f ctx B L = ((dests B.term).zip L.targets).filterMap (edgeOfBcT f ctx) := by
  unfold edgeBlocksT
  cases h : B.term with
  | jump bc => exact absurd h (hj bc)
  | tryCall => rw [h] at ht; cases ht
  | tryCallIndirect => rw [h] at ht; cases ht
  | _ => rfl

theorem filterMap_labels {α : Type} {g g' : α → Option VBlock}
    (h : ∀ x, (g x).map (·.label) = (g' x).map (·.label)) :
    ∀ l : List α, (l.filterMap g).map (·.label) = (l.filterMap g').map (·.label)
  | [] => rfl
  | x :: l => by
    have hx := h x
    simp only [List.filterMap_cons]
    cases hg : g x <;> cases hg' : g' x <;> rw [hg, hg'] at hx <;> simp at hx ⊢
    · exact filterMap_labels h l
    · exact ⟨hx, filterMap_labels h l⟩

/-- The typed edge blocks carry the integer ones' labels. -/
theorem edgeBlocksT_labels (ctx : Ctx) (B : Clif.Block) (L : BLow) :
    (edgeBlocksT f ctx B L).map (·.label) = (edgeBlocks f B L).map (·.label) := by
  have htry : ∀ (et : Clif.ExnTable) (T : TryLow),
      ((et.dests.zip L.targets).filterMap (edgeOfTryT f ctx T)).map (·.label) =
        ((et.dests.zip L.targets).filterMap (edgeOfTry f T)).map (·.label) := by
    intro et T
    apply filterMap_labels
    intro x
    simp only [edgeOfTryT, edgeOfTry]
    rcases blockIdx? f x.1.block <;> rfl
  have hbr : ∀ t : Clif.Terminator,
      (((dests t).zip L.targets).filterMap (edgeOfBcT f ctx)).map (·.label) =
        (((dests t).zip L.targets).filterMap (edgeOfBc f)).map (·.label) := by
    intro t
    apply filterMap_labels
    intro x
    simp only [edgeOfBcT, edgeOfBc]
    split
    · rfl
    · rcases blockIdx? f x.1.block <;> rfl
  rcases try_or B.term with ht | ⟨et, ht⟩
  · by_cases hj : ∃ bc, B.term = .jump bc
    · obtain ⟨bc, hj⟩ := hj
      rw [shape_edgeBlocks_jump hj]
      unfold edgeBlocksT; rw [hj]
    · have hj' : ∀ bc, B.term ≠ .jump bc := fun bc e => hj ⟨bc, e⟩
      rw [shape_edgeBlocksT_other ht hj', shape_edgeBlocks_other ht hj', hbr]
  · cases hT : L.tl with
    | some T =>
      rw [shape_edgeBlocksT_try ht hT, shape_edgeBlocks_try ht hT, htry]
    | none =>
      unfold edgeBlocksT edgeBlocks
      rcases ht with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h, hT] <;> rfl

theorem edgesT_labels (ctx : Ctx) (ps : List (Clif.Block × BLow)) :
    (ps.flatMap fun p => edgeBlocksT f ctx p.1 p.2).map (·.label) =
      (ps.flatMap fun p => edgeBlocks f p.1 p.2).map (·.label) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.flatMap_cons, List.map_append, edgeBlocksT_labels, ih]

/-! ## The shape -/

/-- **The shape part of `lowerCheckT`** (typed scope, SSA, well-founded aliases, terminator
rules that emit code on terminators with integer-position operands). -/
theorem shapeOkT_completeI (h : lowerFunction f = .ok vc) (hs : LowerScopeT f)
    (hssa : (valueDefs f).Nodup) {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    {bl : List BLow} (hb : buildCtx f = .ok (ctx, ranges, st0)) (hte : TermEmitsTI f ctx)
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl)
    (hu : ((aliasOf f bl).map (·.1)).Nodup) (hwf : AliasWF (aliasOf f bl)) :
    shapeOkT f vc ctx st0 (gnAt (gnTable st0.nextVreg (aliasOf f bl))) bl = true := by
  -- the run
  obtain ⟨ctx', ranges', st0', bl', hb', hl', hvc, -, hlf⟩ := lowerFunction_runT hs.externsE h
  rw [hb] at hb'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
  obtain ⟨rfl, rfl, rfl⟩ := hb'
  rw [hl, Option.some.injEq] at hl'
  subst hl'
  have hcf := ctxFacts_of hb
  obtain ⟨hlen, hlb⟩ := lowBlocks_spec hl
  obtain ⟨-, hstart⟩ := lowBlocks_start hl
  have hctxok := ctxOkT_of hs hb
  have hscope := instScopeOk_complete ((ctxSpec_of hb).instScopeT hs.subsetT)
  -- the alias resolution
  have hk : ∀ p ∈ aliasOf f bl, p.1 < st0.nextVreg := by
    intro p hp
    obtain ⟨B, hB, stm, hstm, hr⟩ := aliasOf_key hp
    exact (hcf.vals p.1 (List.mem_flatMap.mpr ⟨B, hB, List.mem_append_right _
      (List.mem_flatMap.mpr ⟨stm, hstm, hr⟩)⟩)).1
  have hR := resolve_eq hu hk hwf
  have hstep := gn_step hu hk hwf
  have hpath := gn_path hu hk hwf
  generalize gnAt (gnTable st0.nextVreg (aliasOf f bl)) = gn at hR hstep hpath ⊢
  have hRen := renOf_vrenaming gn
  -- the states and labels along the lowering
  have hmono : ∀ {c : Ctx} {term : String} {args : List V} {s : LState} {o : Option V}
      {s' : LState} {tr : List Isle.RuleId}, runTerm c term args s = .ok (o, s', tr) →
      s.nextVreg ≤ s'.nextVreg := fun h => (runTerm_mono h).1
  obtain ⟨⟨k, hek⟩, hth⟩ := lowBlocks_thread (fun _ _ _ _ _ h => hmono h)
    (fun _ _ _ _ _ _ _ _ h => hmono h) (fun _ _ _ _ _ _ _ _ h => hmono h) hl
  rw [← edgesT_labels ctx] at hek
  -- the VCode
  obtain ⟨raws, hraws⟩ : ∃ r : List VBlock,
      r = (f.blocks.zip bl).zipIdx.map fun p => rawBlockT f ctx bl p.2 p.1.1 := ⟨_, rfl⟩
  obtain ⟨edges, hedges⟩ : ∃ e : List VBlock,
      e = (f.blocks.zip bl).flatMap fun p => edgeBlocksT f ctx p.1 p.2 := ⟨_, rfl⟩
  rw [← hedges] at hek
  have hvc' : vc.blocks = ((raws ++ edges).map (fixBlock (renOf gn))).toArray := by
    rw [hvc, ← hR, hraws, hedges]; rfl
  have hraws_len : raws.length = f.blocks.length := by simp [hraws, hlen]
  have hedges_len : edges.length = k := by
    have := congrArg List.length hek
    simpa using this
  have hraw : ∀ bi B L, f.blocks[bi]? = some B → bl[bi]? = some L →
      raws[bi]? = some (rawBlockT f ctx bl bi B) := by
    intro bi B L hB hL
    have hz : (f.blocks.zip bl)[bi]? = some (B, L) := List.getElem?_zip_eq_some.mpr ⟨hB, hL⟩
    simp only [hraws, List.getElem?_map, List.getElem?_zipIdx, hz, Option.map_some, Nat.zero_add]
  have hlab : ∀ i (hi : i < (raws ++ edges).length), (raws ++ edges)[i].label = i := by
    intro i hi
    by_cases h1 : i < raws.length
    · rw [List.getElem_append_left h1]
      simp [hraws, rawBlockT]
    · obtain ⟨j, rfl⟩ : ∃ j, i = raws.length + j := ⟨i - raws.length, by omega⟩
      have hl2 : (raws ++ edges).length = raws.length + edges.length := List.length_append
      have hj : j < edges.length := by omega
      have hjk : j < k := by omega
      rw [List.getElem_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      have h2 : (edges.map (·.label))[j]? = some (f.blocks.length + j) := by
        rw [hek, List.getElem?_range'] <;> simp [hjk]
      rw [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some,
        Option.some.injEq] at h2
      rw [h2, hraws_len]
  have hblk : ∀ bi B L, f.blocks[bi]? = some B → bl[bi]? = some L →
      vc.blocks[bi]? = some (fixBlock (renOf gn) (rawBlockT f ctx bl bi B)) := by
    intro bi B L hB hL
    have hbi : bi < raws.length := by rw [hraws_len]; exact lt_of_getElem? hB
    rw [hvc', List.getElem?_toArray, List.getElem?_map, List.getElem?_append_left hbi,
      hraw bi B L hB hL, Option.map_some]
  have hedge : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
      ∀ eb ∈ edgeBlocksT f ctx B L, ∀ l : Nat, eb.label = l →
        vc.blocks[l]? = some (fixBlock (renOf gn) eb) := by
    intro bi B L hB hL eb heb l hl
    have hm : eb ∈ raws ++ edges := by
      refine List.mem_append_right _ ?_
      rw [hedges]
      exact List.mem_flatMap.mpr ⟨(B, L),
        List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hB, hL⟩), heb⟩
    rw [hvc', List.getElem?_toArray, List.getElem?_map, ← hl, get_label hlab hm, Option.map_some]
  -- one block
  have hblock : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
      blockOkT f vc ctx st0 (renOf gn) gn bl bi B L = true := by
    intro bi B L hB hL
    obtain ⟨hsl, -, htst, nl0, nl', hlt⟩ := hlb bi B L hB hL
    have hLs := hstart bi L hL
    have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
    obtain ⟨hslth, htstth⟩ := hth L (List.mem_of_getElem? hL)
    have hph := hcf.term bi B hB
    rw [← hLs] at hph
    -- the terminator segment is not empty
    have hne : tseg (renOf gn) bl bi ≠ [] := by
      simp only [tseg, hL, ne_eq, List.map_eq_nil_iff]
      rcases try_or B.term with ht | ⟨et, ht⟩
      · obtain ⟨htl, hd, out, tr, hrun⟩ := (lowTerm_spec hlt).1 ht
        rw [htl]
        simp only [fixTry]
        have htg : TargetsLen B.term L.targets := by
          intro x d tbl hbt
          have := lowTerm_targets ht hlt
          rw [hbt] at this
          have h1 := (edgeTargets_spec (f := f) (bcs := dests (.brTable x d tbl)) this).1
          simpa [dests] using h1
        have hvb : ValsBelow ctx L.tst := by
          intro x r hx
          have : x < ctx.valReg.size := by
            simp only [Ctx.valueReg?] at hx
            cases h : ctx.valReg[x]? with
            | none => rw [h] at hx; cases hx
            | some _ => exact (Array.getElem?_eq_some_iff.mp h).1
          obtain ⟨h1, h2, -⟩ := hcf.size
          omega
        have hbt := brIdx_of_ok (hs.ctxFacts ctx ranges st0 hb).1 B hBmem
        have hti : L.start + B.body.length < ctx.insts.size :=
          (Array.getElem?_eq_some_iff.mp hph).1
        have hlt' := hte hti hph ht hd htg hvb hbt (termIntPos_of hs hb hBmem) hrun
        intro hnil
        have := Array.length_toList (xs := L.tst'.emitted)
        rw [hnil] at this
        simp only [List.length_nil] at this
        omega
      · obtain ⟨T, hT, -⟩ := (lowTerm_spec hlt).2 et ht
        obtain ⟨c, hc⟩ := hlf.tryLast bi B L T hB hL hT
        rw [hT]
        simp only [fixTry]
        apply tryFix_ne_nil
        intro hnil
        rw [← Array.getLast?_toList, hnil] at hc
        cases hc
    -- the successors
    have hsucc : succOkT f vc ctx (renOf gn) B L = true := by
      have he := hedge bi B L hB hL
      rcases try_or B.term with ht | ⟨et, ht⟩
      · have htg := lowTerm_targets ht hlt
        by_cases hj : ∃ bc, B.term = .jump bc
        · obtain ⟨bc, hj⟩ := hj
          unfold succOkT
          rw [hj] at htg ⊢
          simp only [targetsOf, Option.map_eq_some_iff, Prod.mk.injEq] at htg
          obtain ⟨tl, htl, h1, -⟩ := htg
          simp [htl, h1]
        · have hj' : ∀ bc, B.term ≠ .jump bc := fun bc e => hj ⟨bc, e⟩
          rw [shape_targetsOf_other hj'] at htg
          obtain ⟨h1, -, h3, -⟩ := edgeTargets_spec htg
          have hed := shape_edgeBlocksT_other (L := L) (f := f) (ctx := ctx) ht hj'
          unfold succOkT
          cases hterm : B.term with
          | jump bc => exact absurd hterm (hj' bc)
          | tryCall => rw [hterm] at ht; cases ht
          | tryCallIndirect => rw [hterm] at ht; cases ht
          | _ =>
            rw [hterm] at h1 h3 hed
            refine (Bool.and_eq_true _ _).mpr ⟨decide_eq_true h1, List.all_eq_true.mpr fun p hp => ?_⟩
            obtain ⟨tl, htl, hemp⟩ := h3 p hp
            obtain ⟨bc, tlab⟩ := p
            simp only at htl hemp ⊢
            rw [htl]
            simp only
            split
            · exact decide_eq_true (hemp ‹_›)
            · rename_i hne'
              have hm : ({ label := tlab, insts := #[MInst.jump tl]
                           branchArgs := (bc.args.map fun a => vregOf ctx a).toArray } : VBlock) ∈
                  edgeBlocksT f ctx B L := by
                rw [hed]
                exact List.mem_filterMap.mpr ⟨(bc, tlab), hp, by simp [edgeOfBcT, htl, hne']⟩
              rw [he _ hm tlab rfl]
              simp [fixBlock, MInst.mapRegs]
      · have ht' := ht
        obtain ⟨T, hT, -, hexn, htt, -⟩ := (lowTerm_spec hlt).2 et ht
        obtain ⟨htg, -, hall⟩ := tryTargets_spec htt
        obtain ⟨T', hT', hargs⟩ := hlf.tryArgs bi B L et hB hL ht
        rw [hT, Option.some.injEq] at hT'
        subst hT'
        have hsig := exnTableOpnd_sig hexn
        obtain ⟨tl, htl⟩ := Option.isSome_iff_exists.mp
          (hall et.normal (by simp [Clif.ExnTable.dests]))
        have hlast : L.targets.getLast? = some (nl0 + et.handlers.length) := by
          rw [htg]
          simp [Clif.ExnTable.dests, List.range'_concat]
        have hmemz : (et.normal, nl0 + et.handlers.length) ∈ et.dests.zip L.targets := by
          rw [htg]
          simp only [Clif.ExnTable.dests, List.length_append, List.length_singleton,
            List.range'_concat, Nat.one_mul]
          rw [List.zip_append (by simp)]
          simp
        have hm : ({ label := nl0 + et.handlers.length, insts := #[MInst.jump tl]
                     branchArgs := (et.normal.args.map (tryEdgeArgT ctx T.regs.1 T.regs.2)).toArray } :
              VBlock) ∈ edgeBlocksT f ctx B L := by
          rw [shape_edgeBlocksT_try ht hT]
          exact List.mem_filterMap.mpr ⟨_, hmemz, by simp [edgeOfTryT, htl]⟩
        have hvbl := he _ hm _ rfl
        have hnorm := hargs et.handlers.length et.normal (by simp [Clif.ExnTable.dests])
        have hnoexn : ∀ i, Clif.TryArg.exn i ∉ et.normal.args := fun i hi => by
          have := hnorm.2 _ hi
          simp at this
        unfold succOkT
        rcases ht with ⟨fn, args, hterm⟩ | ⟨c, args, hterm⟩ <;> rw [hterm] <;>
        · simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨by rw [htg]; simp [Clif.ExnTable.dests], ?_⟩
          rw [htl, hlast, hT]
          simp only
          rw [hvbl]
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨⟨by simp [fixBlock, MInst.mapRegs], rfl⟩, ?_⟩, ?_⟩
          · simp only [fixBlock, List.map_toArray, List.map_map]
            congr 1
            refine List.map_congr_left fun a ha => ?_
            cases a with
            | val v => rfl
            | ret i => rfl
            | exn i => exact absurd ha (hnoexn i)
          · refine List.all_eq_true.mpr fun a ha => ?_
            cases a with
            | val v => rfl
            | ret i => exact decide_eq_true (hs.tryRet B hBmem et ht' T.sig hsig i ha)
            | exn i => exact absurd ha (hnoexn i)
    unfold blockOkT
    rw [hblk bi B L hB hL]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨hsl, ?_⟩, ?_⟩, htstth⟩, ?_⟩, ?_⟩, rfl⟩, ?_⟩, hsucc⟩, ?_⟩
    · -- the statements
      refine List.all_eq_true.mpr fun j hj => ?_
      have hj' := List.mem_range.mp hj
      obtain ⟨stm, hstm⟩ : ∃ stm, B.body[j]? = some stm := ⟨_, List.getElem?_eq_getElem hj'⟩
      obtain ⟨sl, hsl'⟩ : ∃ sl, L.sl[j]? = some sl := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      simp only [hstm, hsl']
      obtain ⟨info, hinfo, hic, hir⟩ := hcf.stmt bi B j stm hB hstm
      rw [← hLs] at hinfo
      have hslm := hslth sl (List.mem_of_getElem? hsl')
      unfold stmtOk
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨?_, ?_⟩, hslm.2⟩, ?_⟩
      · rw [hinfo]; simp [hic, hir]
      · rw [hslm.1]; rfl
      · refine List.all_eq_true.mpr fun p hm => ?_
        obtain ⟨r, rs⟩ := p
        rcases rs with _ | ⟨x, _ | ⟨y, ys⟩⟩
        · rfl
        · cases x with
          | vreg out c => exact decide_eq_true (hstep _ (aliasOf_mem hB hL hstm hsl' hm))
          | _ => rfl
        · cases x <;> rfl
    · rw [htst]; rfl
    · exact rawBlockT_insts ctx hRen bl bi B
    · cases h : tseg (renOf gn) bl bi with
      | nil => exact absurd h hne
      | cons => rfl
    · simp only [fixBlock, rawBlockT]
      generalize B.term = t
      cases t <;> simp
    · rw [hph]; rfl
  -- the function
  simp only [shapeOkT, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hctxok, hscope⟩, ?_⟩, ?_⟩, hlen⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨h1, h2, -⟩ := hcf.size
    omega
  · refine List.all_eq_true.mpr fun B hB => List.all_eq_true.mpr fun p hp => decide_eq_true ?_
    have hnk : ∀ y, AliasPath (aliasOf f bl) p.1 y → y = p.1 := by
      intro y hy
      cases hy with
      | refl => rfl
      | step hm _ =>
        exfalso
        obtain ⟨B', hB', stm, hstm, hr⟩ := aliasOf_key hm
        exact param_not_result hssa hB hB' (List.mem_map_of_mem hp)
          (List.mem_flatMap.mpr ⟨stm, hstm, hr⟩)
    exact hnk _ (hpath p.1).1
  · rw [hvc']
    simp [hraws_len]
  · refine List.all_eq_true.mpr fun l _ => ?_
    split
    · rename_i vb hvb
      rw [hvc', List.getElem?_toArray, List.getElem?_map] at hvb
      obtain ⟨eb, heb, rfl⟩ := Option.map_eq_some_iff.mp hvb
      obtain ⟨hl, rfl⟩ := List.getElem?_eq_some_iff.mp heb
      exact decide_eq_true (hlab l hl)
    · rfl
  · refine List.all_eq_true.mpr fun bi hbi => ?_
    have hbi' := List.mem_range.mp hbi
    obtain ⟨B, hB⟩ : ∃ B, f.blocks[bi]? = some B := ⟨_, List.getElem?_eq_getElem hbi'⟩
    obtain ⟨L, hL⟩ : ∃ L, bl[bi]? = some L := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    simp only [hB, hL]
    exact hblock bi B L hB hL
  · rw [buildCtx_fresh hb]
    exact Nat.le_refl _

/-- **The shape part of `lowerCheckT`** (typed scope, SSA, well-founded aliases, terminator
rules that emit code). -/
theorem shapeOkT_complete (h : lowerFunction f = .ok vc) (hs : LowerScopeT f)
    (hssa : (valueDefs f).Nodup) {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    {bl : List BLow} (hb : buildCtx f = .ok (ctx, ranges, st0)) (hte : TermEmitsT f ctx)
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl)
    (hu : ((aliasOf f bl).map (·.1)).Nodup) (hwf : AliasWF (aliasOf f bl)) :
    shapeOkT f vc ctx st0 (gnAt (gnTable st0.nextVreg (aliasOf f bl))) bl = true :=
  shapeOkT_completeI h hs hssa hb hte.toI hl hu hwf

/-- **The shape part of `lowerCheckT` on the typed scope** (SSA, well-founded aliases; no
premise on the terminator rules: `termEmitsTI_of_ctxInvT`). -/
theorem shapeOkT_completeT (h : lowerFunction f = .ok vc) (hs : LowerScopeT f)
    (hssa : (valueDefs f).Nodup) {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    {bl : List BLow} (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl)
    (hu : ((aliasOf f bl).map (·.1)).Nodup) (hwf : AliasWF (aliasOf f bl)) :
    shapeOkT f vc ctx st0 (gnAt (gnTable st0.nextVreg (aliasOf f bl))) bl = true :=
  shapeOkT_completeI h hs hssa hb (termEmitsTI_of_ctxInvT (ctxInvT_of hs hb)) hl hu hwf

/-- **The typed shape of `lowerFunction`'s VCode**: on SSA typed-scope input with well-founded
aliases whose terminator rules emit code, `lowerFunction f = .ok vc` gives `LowerShapeT`. -/
theorem lowerShapeT_of_lower (h : lowerFunction f = .ok vc) (hs : LowerScopeT f)
    (hssa : (valueDefs f).Nodup) {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    {bl : List BLow} (hb : buildCtx f = .ok (ctx, ranges, st0)) (hte : TermEmitsT f ctx)
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl)
    (hu : ((aliasOf f bl).map (·.1)).Nodup) (hwf : AliasWF (aliasOf f bl)) :
    LowerShapeT f vc ctx st0 (renOf (gnAt (gnTable st0.nextVreg (aliasOf f bl))))
      (gnAt (gnTable st0.nextVreg (aliasOf f bl))) bl :=
  lowerShapeT_of_ok hb hl (fun _ hn => gnAt_temp hn)
    (shapeOkT_complete h hs hssa hb hte hl hu hwf)

/-- **The typed shape of `lowerFunction`'s VCode on the typed scope**: on SSA typed-scope input
with well-founded aliases, `lowerFunction f = .ok vc` gives `LowerShapeT` (floats included; no
premise on the terminator rules). -/
theorem lowerShapeT_of_lowerT (h : lowerFunction f = .ok vc) (hs : LowerScopeT f)
    (hssa : (valueDefs f).Nodup) {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    {bl : List BLow} (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl)
    (hu : ((aliasOf f bl).map (·.1)).Nodup) (hwf : AliasWF (aliasOf f bl)) :
    LowerShapeT f vc ctx st0 (renOf (gnAt (gnTable st0.nextVreg (aliasOf f bl))))
      (gnAt (gnTable st0.nextVreg (aliasOf f bl))) bl :=
  lowerShapeT_of_ok hb hl (fun _ hn => gnAt_temp hn)
    (shapeOkT_completeT h hs hssa hb hl hu hwf)

/-- **Integer specialization**: on the integer scope the terminator premise holds
(`term_emits`), so the typed shape check accepts every in-scope lowering `shapeOk` accepts. -/
theorem shapeOkT_complete_int (h : lowerFunction f = .ok vc) (hs : LowerScope f)
    (hssa : (valueDefs f).Nodup) {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    {bl : List BLow} (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl)
    (hu : ((aliasOf f bl).map (·.1)).Nodup) (hwf : AliasWF (aliasOf f bl)) :
    shapeOkT f vc ctx st0 (gnAt (gnTable st0.nextVreg (aliasOf f bl))) bl = true :=
  shapeOkT_complete h hs.toT hssa hb (termEmitsT_of_ctxInv (ctxOk_sound (ctxOk_complete hs hb)))
    hl hu hwf

end Backend.Proof.Driver

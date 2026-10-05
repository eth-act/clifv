import FV.Backend.Proof.SpillEdgesPrep
import FV.Backend.Proof.SpillEdgesIsel
import FV.Backend.Proof.SpillArity
import FV.Backend.Proof.LowerLoop
import FV.Backend.Proof.LowerComplete
import FV.Backend.Proof.LowerShapeOkFacts

/-!
# The CFG facts of `lowerFunction`'s VCode (V4)

`lowOk_of`: on `Dominated`, `LowerScope`, `ArityOk` input, `lowerFunction`'s VCode meets `LowOk`.
Its blocks (`vcBlocksOf`): block `bi < n` is CLIF block `bi`'s code, ending in its terminator's
lowering (a `jump`, a branch to the recorded labels, an instruction without successors for
`return`/`trap`, the `tryCall`); the blocks from `n` on are edge blocks `jump tl` with the branch
arguments of one successor, labelled consecutively from `n` (so disjoint across blocks).
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Driver

/-- What the lowering run records about `vc`. -/
structure Low (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (bl : List BLow)
    (RR : Reg → Reg) : Prop where
  hb : ∃ ranges, buildCtx f = .ok (ctx, ranges, st0)
  low : ∃ stE nlE, lowB f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
    some (bl, stE, nlE)
  blocks : vc.blocks.toList = (((f.blocks.zip bl).zipIdx.map fun p => rawBlock f bl p.2 p.1.1) ++
    (f.blocks.zip bl).flatMap fun p => edgeBlocks f p.1 p.2).map (fixBlock RR)
  ren : ∃ gn, VRenaming RR gn
  lf : LoopFacts f ctx bl
  len : bl.length = f.blocks.length

theorem low_of {f : Clif.Function} {vc : VCode} (h : lowerFunction f = .ok vc) :
    ∃ ctx st0 bl RR, Low f vc ctx st0 bl RR := by
  obtain ⟨ctx, ranges, st0, bl, hb, hl, hvb, -, hlf⟩ := lowerFunction_run h
  rw [lowBlocks_eq] at hl
  cases hr : lowB f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length with
  | none => rw [hr] at hl; cases hl
  | some r =>
    rw [hr] at hl
    obtain ⟨bl', stE, nlE⟩ := r
    cases hl
    simp only at hvb hlf
    have hbl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
        some bl' := by rw [lowBlocks_eq, hr]; rfl
    refine ⟨ctx, st0, bl', lowerFunction.resolve (aliasArr (aliasOf f bl')) ((aliasArr (aliasOf f bl')).size + 1), ⟨⟨ranges, hb⟩, ⟨stE, nlE, hr⟩, by rw [hvb]; simp [vcBlocksOf], resolve_vrenaming _ _,
      hlf, (lowBlocks_spec hbl).1⟩⟩

theorem nodup_flat_lab {α : Type} (g : α → List VBlock) : ∀ (l : List α),
    ((l.flatMap g).map (·.label)).Nodup → ∀ (i i' : Nat) (a a' : α), i < i' → l[i]? = some a →
    l[i']? = some a' → ∀ e ∈ g a, ∀ e' ∈ g a', e.label ≠ e'.label
  | [], _, _, _, _, _, _, ha, _, _, _, _, _ => by simp at ha
  | c :: l, hn, i, i', a, a', hii, ha, ha', e, he, e', he' => by
    rw [List.flatMap_cons, List.map_append, List.nodup_append] at hn
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
      subst ha
      obtain ⟨i', rfl⟩ : ∃ j, i' = j + 1 := ⟨i' - 1, by omega⟩
      simp only [List.getElem?_cons_succ] at ha'
      exact hn.2.2 _ (List.mem_map_of_mem he) _
        (List.mem_map_of_mem (List.mem_flatMap.mpr ⟨a', List.mem_of_getElem? ha', he'⟩))
    | succ i =>
      obtain ⟨i', rfl⟩ : ∃ j, i' = j + 1 := ⟨i' - 1, by omega⟩
      exact nodup_flat_lab g l hn.2.1 i i' a a' (by omega) (by simpa using ha) (by simpa using ha')
        e he e' he'

theorem tl_aux : ∀ (items : List (Option Nat)) (ls : List Label), ls.length = items.length + 1 →
    (items.zip ls).map Prod.snd ++ [ls.getLastD 0] = ls
  | [], [l], _ => rfl
  | [], [], h => by simp at h
  | [], _ :: _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: items, l :: ls, h => by
    have := tl_aux items ls (by simpa using h)
    cases ls with
    | nil => simp at h
    | cons l' ls => simpa [List.getLastD] using this

/-- A `try_call`'s successors are the labels `tryInfoOf` was given. -/
theorem tryInfo_targets {sig : Clif.Signature} {items : List (Option Nat)} {ls : List Label}
    {info : TryInfo} (h : tryInfoOf sig items ls = some info) (c : CallInfo) :
    (MInst.tryCall c info).targets = ls := by
  unfold tryInfoOf at h
  split at h
  · cases h
  rename_i hl
  cases h
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hl
  simp only [MInst.targets, List.map_map]
  rw [show List.map _ (items.zip ls) = List.map Prod.snd (items.zip ls) from
    List.map_congr_left (fun p _ => by rcases p with ⟨_ | n, l⟩ <;> rfl)]
  exact tl_aux items ls hl

theorem tryCall_targets_ne (c : CallInfo) (ti : TryInfo) : (MInst.tryCall c ti).targets ≠ [] := by
  simp [MInst.targets]

/-- The last instruction of CLIF block `x`'s code is that of its terminator's segment. -/
theorem raw_back_of {f : Clif.Function} {bl : List BLow} {RR : Reg → Reg} {x : Nat} {B : Clif.Block}
    {L : BLow} (hL : bl[x]? = some L) {i : MInst}
    (hi : (fixTry L.tl L.tst'.emitted.toList).getLast? = some i) :
    (fixBlock RR (rawBlock f bl x B)).insts.back? = some (i.mapRegs RR) := by
  simp only [fixBlock, rawBlock, tseg, hL, map_mapRegs_id]
  rw [Array.back?_map, List.back?_toArray, List.getLast?_append, hi]
  rfl

theorem succIds_of {t : Clif.Terminator} (ht : t.isTry = false) : succIds t = (dests t).map (·.block) := by
  cases t <;> first | rfl | (simp [Clif.Terminator.isTry] at ht)

theorem succIds_try {t : Clif.Terminator} {et : Clif.ExnTable} (h : IsTryWith t et) :
    succIds t = et.dests.map (·.block) := by
  rcases h with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

theorem nodup_flatMap_mem {α β : Type} (g : α → List β) : ∀ {l : List α}, (l.flatMap g).Nodup →
    ∀ {x : α}, x ∈ l → (g x).Nodup
  | [], _, _, hx => by simp at hx
  | a :: l, hn, x, hx => by
    rw [List.flatMap_cons, List.nodup_append] at hn
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hn.1
    · exact nodup_flatMap_mem g hn.2.1 hx

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {bl : List BLow} {RR : Reg → Reg}
  (H : Low f vc ctx st0 bl RR)
include H

theorem Low.hbl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
    some bl := by
  obtain ⟨stE, nlE, hr⟩ := H.low
  rw [lowBlocks_eq, hr]; rfl

theorem Low.labs : ((f.blocks.zip bl).flatMap fun p => edgeBlocks f p.1 p.2).map (·.label) =
    List.range' f.blocks.length (((f.blocks.zip bl).flatMap fun p => edgeBlocks f p.1 p.2).length) := by
  obtain ⟨stE, nlE, hr⟩ := H.low
  obtain ⟨h1, -⟩ := lowB_labels _ _ _ _ _ _ _ hr
  have := congrArg List.length h1
  simp only [List.length_map, List.length_range'] at this
  rw [h1, this]

theorem Low.rawLen : ((f.blocks.zip bl).zipIdx.map fun p => rawBlock f bl p.2 p.1.1).length =
    f.blocks.length := by
  simp [H.len]

/-- The blocks of `vc`: CLIF block `x`'s code or an edge block labelled `x`. -/
theorem Low.cases {x : Nat} {vb : VBlock} (hx : vc.blocks[x]? = some vb) :
    (∃ B L, x < f.blocks.length ∧ f.blocks[x]? = some B ∧ bl[x]? = some L ∧
      vb = fixBlock RR (rawBlock f bl x B)) ∨
    (∃ (bi : Nat) (B : Clif.Block) (L : BLow) (e : VBlock), f.blocks[bi]? = some B ∧ bl[bi]? = some L ∧ e ∈ edgeBlocks f B L ∧ e.label = x ∧
      f.blocks.length ≤ x ∧ vb = fixBlock RR e) := by
  rw [← Array.getElem?_toList, H.blocks, List.getElem?_map] at hx
  by_cases hxn : x < f.blocks.length
  · left
    rw [List.getElem?_append_left (by rw [H.rawLen]; exact hxn), List.getElem?_map,
      List.getElem?_zipIdx] at hx
    obtain ⟨B, hB⟩ : ∃ B, f.blocks[x]? = some B := ⟨_, List.getElem?_eq_getElem hxn⟩
    obtain ⟨L, hL⟩ : ∃ L, bl[x]? = some L := ⟨_, List.getElem?_eq_getElem (by rw [H.len]; exact hxn)⟩
    rw [(List.getElem?_zip_eq_some (z := (B, L))).mpr ⟨hB, hL⟩] at hx
    simp only [Option.map_some, Option.some.injEq, Nat.zero_add] at hx
    exact ⟨B, L, hxn, hB, hL, hx.symm⟩
  · right
    rw [List.getElem?_append_right (by rw [H.rawLen]; omega), H.rawLen] at hx
    cases he : ((f.blocks.zip bl).flatMap fun p => edgeBlocks f p.1 p.2)[x - f.blocks.length]? with
    | none => rw [he] at hx; cases hx
    | some e =>
      rw [he] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      have hl := congrArg (·[x - f.blocks.length]?) H.labs
      simp only [List.getElem?_map, he, Option.map_some] at hl
      rw [List.getElem?_range' (by
        have := (List.getElem?_eq_some_iff.mp he).1; omega)] at hl
      simp only [Option.some.injEq] at hl
      obtain ⟨p, hp, hep⟩ := List.mem_flatMap.mp (List.mem_of_getElem? he)
      obtain ⟨bi, hbi, hpe⟩ := List.getElem_of_mem hp
      have hz : (f.blocks.zip bl)[bi]? = some p := by rw [List.getElem?_eq_getElem hbi, hpe]
      obtain ⟨hB, hL⟩ := List.getElem?_zip_eq_some.mp hz
      exact ⟨bi, p.1, p.2, e, hB, hL, hep, by lomega, by lomega, hx.symm⟩

theorem Low.raw_at {x : Nat} {B : Clif.Block} (hB : f.blocks[x]? = some B) :
    vc.blocks[x]? = some (fixBlock RR (rawBlock f bl x B)) := by
  have hxn : x < f.blocks.length := (List.getElem?_eq_some_iff.mp hB).1
  obtain ⟨L, hL⟩ : ∃ L, bl[x]? = some L := ⟨_, List.getElem?_eq_getElem (by rw [H.len]; exact hxn)⟩
  rw [← Array.getElem?_toList, H.blocks, List.getElem?_map,
    List.getElem?_append_left (by rw [H.rawLen]; exact hxn), List.getElem?_map, List.getElem?_zipIdx,
    (List.getElem?_zip_eq_some (z := (B, L))).mpr ⟨hB, hL⟩]
  simp

theorem Low.edge_at {bi : Nat} {B : Clif.Block} {L : BLow} (hB : f.blocks[bi]? = some B)
    (hL : bl[bi]? = some L) {e : VBlock} (he : e ∈ edgeBlocks f B L) :
    f.blocks.length ≤ e.label ∧ vc.blocks[e.label]? = some (fixBlock RR e) := by
  have hm : e ∈ (f.blocks.zip bl).flatMap fun p => edgeBlocks f p.1 p.2 :=
    List.mem_flatMap.mpr ⟨(B, L), List.mem_of_getElem? ((List.getElem?_zip_eq_some (z := (B, L))).mpr ⟨hB, hL⟩), he⟩
  obtain ⟨i, hi, hei⟩ := List.getElem_of_mem hm
  have hl := congrArg (·[i]?) H.labs
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, hei, Option.map_some] at hl
  rw [List.getElem?_range' hi] at hl
  simp only [Option.some.injEq, Nat.one_mul] at hl
  refine ⟨by lomega, ?_⟩
  rw [hl, ← Array.getElem?_toList, H.blocks, List.getElem?_map,
    List.getElem?_append_right (by rw [H.rawLen]; omega), H.rawLen, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem hi, hei]
  rfl

/-- Edge blocks of different CLIF blocks have different labels. -/
theorem Low.edge_disj {bi bi' : Nat} {B B' : Clif.Block} {L L' : BLow} (hB : f.blocks[bi]? = some B)
    (hL : bl[bi]? = some L) (hB' : f.blocks[bi']? = some B') (hL' : bl[bi']? = some L')
    {e e' : VBlock} (he : e ∈ edgeBlocks f B L) (he' : e' ∈ edgeBlocks f B' L')
    (hl : e.label = e'.label) : bi = bi' := by
  have hn : (((f.blocks.zip bl).flatMap fun p => edgeBlocks f p.1 p.2).map (·.label)).Nodup := by
    rw [H.labs]; exact List.nodup_range'
  have hz := (List.getElem?_zip_eq_some (z := (B, L))).mpr ⟨hB, hL⟩
  have hz' := (List.getElem?_zip_eq_some (z := (B', L'))).mpr ⟨hB', hL'⟩
  rcases Nat.lt_trichotomy bi bi' with h | h | h
  · exact absurd hl (nodup_flat_lab (fun p => edgeBlocks f p.1 p.2) _ hn bi bi' _ _ h hz hz' e he e' he')
  · exact h
  · exact absurd hl.symm (nodup_flat_lab (fun p => edgeBlocks f p.1 p.2) _ hn bi' bi _ _ h hz' hz e' he' e he)

/-- **The terminator of CLIF block `x`'s code**: a `jump` for a `jump`, a branch to the recorded
labels otherwise (none for `return`/`trap`), the `tryCall` for a `try_call`. -/
theorem Low.raw_back (hs : LowerScope f) (hbt : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) {x : Nat}
    {B : Clif.Block} {L : BLow} (hB : f.blocks[x]? = some B) (hL : bl[x]? = some L) :
    ∃ t, (fixBlock RR (rawBlock f bl x B)).insts.back? = some t ∧
      (∀ bc, B.term = .jump bc → ∃ tl, t = .jump tl ∧ L.targets = [tl]) ∧
      (B.term.isTry = false → t.targets = L.targets ∧ ∀ c ti, t ≠ .tryCall c ti) ∧
      (∀ et, IsTryWith B.term et → ∃ c ti, t = .tryCall c ti ∧ t.targets = L.targets) := by
  obtain ⟨ranges, hb⟩ := H.hb
  have sp := ctxSpec_of hb
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  obtain ⟨-, -, hem, nl0, nl1, hlt⟩ := (lowBlocks_spec H.hbl).2 x B L hB hL
  have hst : L.start = blockStart f x := (lowBlocks_start H.hbl).2 x L hL
  have hph := sp.facts.term x B hB
  rw [← hst] at hph
  rcases try_or B.term with ht | ⟨et, het⟩
  · obtain ⟨htl, hd, out, tr, hrun⟩ := (lowTerm_spec hlt).1 ht
    have htg := lowTerm_targets ht hlt
    obtain ⟨hctx', hi'⟩ := termCtx_facts hctx hph L.data
    have hval : ValsBelow ctx L.tst := by
      intro y r hy
      have h1 : y < ctx.valReg.size := by
        simp only [Ctx.valueReg?] at hy
        cases hh : ctx.valReg[y]? with
        | none => rw [hh] at hy; cases hy
        | some _ => exact (Array.getElem?_eq_some_iff.mp hh).1
      have h2 := sp.facts.size
      obtain ⟨stE, nlE, hr⟩ := H.low
      have h3 := lowB_mono _ _ _ _ _ _ _ hr x L hL
      omega
    have hvb' : ValsBelow (termCtx ctx (L.start + B.body.length) L.data) L.tst := hval
    have hfix : fixTry L.tl L.tst'.emitted.toList = L.tst'.emitted.toList := by rw [htl]; rfl
    -- the emitted code ends in `i`
    have last : ∀ (ms : List MInst) (i : MInst), L.tst'.emitted = L.tst.emitted ++ (ms ++ [i]).toArray →
        (fixBlock RR (rawBlock f bl x B)).insts.back? = some (i.mapRegs RR) := by
      intro ms i he
      apply raw_back_of hL
      rw [hfix, he, hem]
      simp
    have nojump : ∀ bc, B.term ≠ .jump bc → ∀ et, ¬ IsTryWith B.term et := fun _ _ et h => by
      rw [isTry_of h] at ht; cases ht
    unfold termCallF termCall at hrun
    cases hT : B.term with
    | jump bc =>
      rw [hT] at hrun hd htg
      obtain ⟨l, he, hlt'⟩ := jumpShape_runTerm hctx' hd hi' hrun
      refine ⟨_, last _ _ he, fun bc' _ => ⟨l, rfl, hlt'⟩, fun _ => ⟨by rw [hlt']; rfl,
        fun c ti h => by cases h⟩, fun et h => ?_⟩
      rcases h with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
    | ret xs =>
      rw [hT] at hrun hd htg
      obtain ⟨ms, i, he, hit⟩ := termShapeT_runTerm (t := .ret (xs ++ sretRet f)) hctx' rfl hd hi' hvb' hrun
      have hL0 : L.targets = [] := by
        simp only [targetsOf, dests, edgeTargets, Option.some.injEq, Prod.mk.injEq] at htg
        exact htg.1.symm
      refine ⟨_, last _ _ he, (fun _ h => nomatch h), fun _ => ⟨by rw [targets_mapRegs, hit, hL0],
        fun c ti h => tryCall_targets_ne c ti (by rw [← h, targets_mapRegs, hit])⟩, fun et h => ?_⟩
      rcases h with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
    | trap c =>
      rw [hT] at hrun hd htg
      obtain ⟨ms, i, he, hit⟩ := termShapeT_runTerm (t := .trap c) hctx' rfl hd hi' hvb' hrun
      have hL0 : L.targets = [] := by
        simp only [targetsOf, dests, edgeTargets, Option.some.injEq, Prod.mk.injEq] at htg
        exact htg.1.symm
      refine ⟨_, last _ _ he, (fun _ h => nomatch h), fun _ => ⟨by rw [targets_mapRegs, hit, hL0],
        fun c ti h => tryCall_targets_ne c ti (by rw [← h, targets_mapRegs, hit])⟩, fun et h => ?_⟩
      rcases h with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
    | brif cnd tb eb =>
      rw [hT] at hrun hd htg
      have hbt' : BrIdxTyped (termCtx ctx (L.start + B.body.length) L.data) (.brif cnd tb eb) := by
        intro _ _ _ h; cases h
      obtain ⟨ms, i, he, hit⟩ := branchShape_runTerm hctx' rfl hd hi' hbt' (fun _ _ _ h => by cases h)
        hvb' hrun
      have hno := emitted_of_run hrun hem i (by rw [he, hem]; simp)
      refine ⟨_, last _ _ he, (fun _ h => nomatch h), fun _ => ⟨by rw [targets_mapRegs, hit],
        notTry_mapRegs RR i hno⟩, fun et h => ?_⟩
      rcases h with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
    | brTable y d tbl =>
      rw [hT] at hrun hd htg
      have hbt' : BrIdxTyped (termCtx ctx (L.start + B.body.length) L.data) (.brTable y d tbl) := by
        have := hbt B (List.mem_of_getElem? hB); rw [hT] at this; exact this
      have htl' : TargetsLen (.brTable y d tbl) L.targets := by
        intro _ _ _ h
        cases h
        have := (edgeTargets_spec (by simpa [targetsOf] using htg)).1
        simpa [dests] using this
      obtain ⟨ms, i, he, hit⟩ := branchShape_runTerm hctx' rfl hd hi' hbt' htl' hvb' hrun
      have hno := emitted_of_run hrun hem i (by rw [he, hem]; simp)
      refine ⟨_, last _ _ he, (fun _ h => nomatch h), fun _ => ⟨by rw [targets_mapRegs, hit],
        notTry_mapRegs RR i hno⟩, fun et h => ?_⟩
      rcases h with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
    | returnCall fn args =>
      rw [hT] at hd
      simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
    | tryCall => rw [hT] at ht; cases ht
    | tryCallIndirect => rw [hT] at ht; cases ht
  · obtain ⟨T, hT, -, -, -, -, hinfo, -⟩ := (lowTerm_spec hlt).2 et het
    obtain ⟨c, hc⟩ := H.lf.tryLast x B L T hB hL hT
    rw [← back_toList] at hc
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hc
    have hfix : (fixTry L.tl L.tst'.emitted.toList).getLast? = some (.tryCall c T.info) := by
      rw [hT]
      show (tryFix T.info L.tst'.emitted.toList).getLast? = _
      rw [hys, tryFix_append]
      simp
    refine ⟨_, raw_back_of hL hfix, fun bc h => ?_, fun h => absurd (isTry_of het) (by rw [h]; simp),
      fun et' _ => ⟨_, T.info, rfl, by rw [targets_mapRegs]; exact tryInfo_targets hinfo c⟩⟩
    rcases het with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> rw [h'] at h <;> cases h

/-- **The targets of CLIF block `x`'s terminator**: a block (without arguments, or of a
`jump`), or an edge block of `x`; a `try_call`'s: its edge blocks, distinct. -/
theorem Low.raw_tgt {x : Nat} {B : Clif.Block} {L : BLow} (hB : f.blocks[x]? = some B)
    (hL : bl[x]? = some L) :
    (B.term.isTry = false → ∀ l ∈ L.targets,
      (∃ bc ∈ dests B.term, blockIdx? f bc.block = some l ∧ (bc.args = [] ∨ B.term = .jump bc)) ∨
      (∃ e ∈ edgeBlocks f B L, e.label = l)) ∧
    (∀ et, IsTryWith B.term et → L.targets.Nodup ∧ ∀ l ∈ L.targets, ∃ e ∈ edgeBlocks f B L, e.label = l) := by
  obtain ⟨-, -, -, nl0, nl1, hlt⟩ := (lowBlocks_spec H.hbl).2 x B L hB hL
  constructor
  · intro ht l hl
    have htg := lowTerm_targets ht hlt
    by_cases hj : ∃ bc, B.term = .jump bc
    · obtain ⟨bc, hj⟩ := hj
      rw [hj] at htg
      simp only [targetsOf, Option.map_eq_some_iff, Prod.mk.injEq] at htg
      obtain ⟨tl, htl, h1, -⟩ := htg
      rw [← h1] at hl
      simp only [List.mem_singleton] at hl
      subst hl
      exact .inl ⟨bc, by rw [hj]; simp [dests], htl, .inr hj⟩
    · have hj' : ∀ bc, B.term ≠ .jump bc := fun bc e => hj ⟨bc, e⟩
      rw [shape_targetsOf_other hj'] at htg
      obtain ⟨hlen, -, hp, -⟩ := edgeTargets_spec htg
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
      have hk' : k < (dests B.term).length := by omega
      have hpz : ((dests B.term)[k], L.targets[k]) ∈ (dests B.term).zip L.targets :=
        List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr
          ⟨List.getElem?_eq_getElem hk', List.getElem?_eq_getElem hk⟩)
      obtain ⟨tl, htl, hargs⟩ := hp _ hpz
      by_cases ha : ((dests B.term)[k]).args = []
      · have e := hargs ha
        simp only at e
        exact .inl ⟨_, List.getElem_mem hk', by rw [e]; exact htl, .inl ha⟩
      · right
        refine ⟨⟨L.targets[k], #[.jump tl], #[],
          (((dests B.term)[k]).args.map (fun a => Reg.vreg a .int)).toArray⟩, ?_, rfl⟩
        rw [shape_edgeBlocks_other ht hj']
        exact List.mem_filterMap.mpr ⟨_, hpz, by simp [edgeOfBc, ha, htl]⟩
  · intro et het
    obtain ⟨T, hT, -, -, htt, -⟩ := (lowTerm_spec hlt).2 et het
    obtain ⟨hts, -, hall⟩ := tryTargets_spec htt
    refine ⟨by rw [hts]; exact List.nodup_range', fun l hl => ?_⟩
    have hlabs := edgeOfTry_labels (f := f) (T := T) (ds := et.dests) (ls := L.targets)
      (by rw [hts]; simp) hall
    rw [← shape_edgeBlocks_try het hT] at hlabs
    rw [← hlabs] at hl
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hl
    exact ⟨e, he, rfl⟩

/-- **An edge block** jumps to a non-entry block whose parameters its arguments (integer vregs)
match. -/
theorem Low.edge_facts (hs : LowerScope f) {bi : Nat} {B : Clif.Block} {L : BLow}
    (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L) {e : VBlock} (he : e ∈ edgeBlocks f B L) :
    ∃ tl TB, e.insts = #[.jump tl] ∧ e.params = #[] ∧ f.blocks[tl]? = some TB ∧ tl ≠ 0 ∧
      TB.params.length = e.branchArgs.size ∧ ∀ a ∈ e.branchArgs.toList, ∃ v, a = .vreg v .int := by
  have hBm : B ∈ f.blocks := List.mem_of_getElem? hB
  obtain ⟨-, -, -, nl0, nl1, hlt⟩ := (lowBlocks_spec H.hbl).2 bi B L hB hL
  rcases try_or B.term with ht | ⟨et, het⟩
  · by_cases hj : ∃ bc, B.term = .jump bc
    · obtain ⟨bc, hj⟩ := hj
      rw [shape_edgeBlocks_jump hj] at he
      simp at he
    · have hj' : ∀ bc, B.term ≠ .jump bc := fun bc e => hj ⟨bc, e⟩
      rw [shape_edgeBlocks_other ht hj'] at he
      obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.mp he
      simp only [edgeOfBc] at hpe
      split at hpe
      · cases hpe
      rename_i ha
      obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.mp hpe
      have hbc : p.1 ∈ dests B.term := (List.of_mem_zip hp).1
      obtain ⟨TB, hTB, hTBi⟩ := block?_of_idx htl
      obtain ⟨tb, htb, hlen, -⟩ := H.lf.args B hBm p.1 hbc
      obtain rfl : tb = TB := Option.some.inj (htb.symm.trans hTB)
      refine ⟨tl, tb, rfl, rfl, hTBi, fun h0 => ?_, by simp [hlen (by simpa using ha)], ?_⟩
      · subst h0
        exact hs.noEntryPred B hBm p.1.block (by rw [succIds_of ht]; exact List.mem_map_of_mem hbc) htl
      · intro a hm
        simp only [List.toList_toArray, List.mem_map] at hm
        obtain ⟨v, -, rfl⟩ := hm
        exact ⟨v, rfl⟩
  · obtain ⟨T, hT, -, hexn, -, hregs, -, -⟩ := (lowTerm_spec hlt).2 et het
    rw [shape_edgeBlocks_try het hT] at he
    obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.mp he
    simp only [edgeOfTry] at hpe
    obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.mp hpe
    obtain ⟨k, hk, hpk⟩ := List.getElem_of_mem hp
    have hdk : et.dests[k]? = some p.1 := by
      have := (List.getElem?_zip_eq_some.mp (by rw [List.getElem?_eq_getElem hk, hpk])).1
      exact this
    obtain ⟨T', hT', hargs⟩ := H.lf.tryArgs bi B L et hB hL het
    rw [hT] at hT'
    cases hT'
    obtain ⟨⟨tb, htb, hlen⟩, hai⟩ := hargs k p.1 hdk
    obtain ⟨TB, hTB, hTBi⟩ := block?_of_idx htl
    obtain rfl : tb = TB := Option.some.inj (htb.symm.trans hTB)
    obtain ⟨-, hregs', -⟩ := tryRegsOf_spec (exnTableOpnd_cc hexn) hregs
    refine ⟨tl, tb, rfl, rfl, hTBi, fun h0 => ?_, by simp [hlen], ?_⟩
    · subst h0
      exact hs.noEntryPred B hBm p.1.block
        (by rw [succIds_try het]; exact List.mem_map_of_mem (List.mem_of_getElem? hdk)) htl
    · intro a hm
      simp only [List.toList_toArray, List.mem_map] at hm
      obtain ⟨ta, hta, rfl⟩ := hm
      have hok := hai ta hta
      rw [hregs']
      cases ta with
      | val v => exact ⟨v, rfl⟩
      | ret i =>
        simp only at hok
        rw [hregs'] at hok
        simp only [List.length_map, List.length_range] at hok
        exact ⟨L.tst.nextVreg + i, by simp [tryEdgeArg, hok.2]⟩
      | exn i =>
        simp only at hok
        rw [hregs'] at hok
        simp only [List.length_cons, List.length_nil] at hok
        have : i = 0 ∨ i = 1 := by omega
        rcases this with rfl | rfl
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩

end

/-- `lowerFunction`'s VCode meets `LowOk` on `Dominated`, `LowerScope`, `ArityOk` input. -/
theorem lowOk_of {f : Clif.Function} {vc : VCode} (hd : Dominated f) (hs : LowerScope f)
    (ha : ArityOk f) (h : lowerFunction f = .ok vc) : LowOk vc := by
  obtain ⟨ctx, st0, bl, RR, H⟩ := low_of h
  obtain ⟨gn, hRR⟩ := H.ren
  have hbt : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term := by
    obtain ⟨ctx', st0', R', gn', bl', A', hshape, -, hbt'⟩ := lowering_of_check (lowerCheck_complete hd hs h)
    obtain ⟨ranges', hb'⟩ := hshape.hctx
    obtain ⟨ranges, hb⟩ := H.hb
    rw [hb] at hb'
    cases hb'
    exact hbt'
  have hn : 0 < f.blocks.length := List.length_pos_iff.mpr hs.nonempty
  obtain ⟨B0, hB0⟩ : ∃ B0, f.blocks[0]? = some B0 := ⟨_, List.getElem?_eq_getElem hn⟩
  -- the block at a CLIF block's index
  have tgtBlk : ∀ (tl : Nat) (TB : Clif.Block), f.blocks[tl]? = some TB → tl ≠ 0 →
      ∃ tb, vc.blocks[tl]? = some tb ∧ tb.params = (TB.params.map fun p => Reg.vreg p.1 .int).toArray ∧
        (tb.params.toList.map Reg.homeNum).Nodup := by
    intro tl TB hTB h0
    refine ⟨_, H.raw_at hTB, by simp [fixBlock, rawBlock, h0], ?_⟩
    simp only [fixBlock, rawBlock, h0, ite_false, List.toList_toArray, List.map_map]
    have hnd := nodup_flatMap_mem _ hd.ssa (List.mem_of_getElem? hTB)
    exact (List.nodup_append.mp hnd).1
  have backE : ∀ (e : VBlock) (tl : Label), e.insts = #[.jump tl] →
      (fixBlock RR e).insts.back? = some (.jump tl) := by
    intro e tl he; simp [fixBlock, he]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- nonempty
    have := H.raw_at hB0
    exact (Array.getElem?_eq_some_iff.mp this).1
  · -- labels
    intro l vb hvb
    rcases H.cases hvb with ⟨B, L, -, -, -, rfl⟩ | ⟨bi, B, L, e, -, -, -, hl, -, rfl⟩
    · rfl
    · exact hl
  · -- entry
    intro vb hvb
    rw [H.raw_at hB0] at hvb
    cases hvb
    rfl
  · -- no branch to the entry
    intro b vb t hvb hback h0
    rcases H.cases hvb with ⟨B, L, -, hB, hL, rfl⟩ | ⟨bi, B, L, e, hB, hL, he, -, -, rfl⟩
    · obtain ⟨t', hb', -, hnt, htry⟩ := H.raw_back hs hbt hB hL
      rw [hb'] at hback
      cases hback
      have hBm := List.mem_of_getElem? hB
      rcases try_or B.term with ht | ⟨et, het⟩
      · rw [(hnt ht).1] at h0
        rcases (H.raw_tgt hB hL).1 ht 0 h0 with ⟨bc, hbc, hidx, -⟩ | ⟨e, he, hl⟩
        · exact hs.noEntryPred B hBm bc.block (by rw [succIds_of ht]; exact List.mem_map_of_mem hbc) hidx
        · have := (H.edge_at hB hL he).1; rw [hl] at this; omega
      · obtain ⟨c, ti, -, htg⟩ := htry et het
        rw [htg] at h0
        obtain ⟨e, he, hl⟩ := ((H.raw_tgt hB hL).2 et het).2 0 h0
        have := (H.edge_at hB hL he).1; rw [hl] at this; omega
    · obtain ⟨tl, TB, hins, -, -, htl0, -⟩ := H.edge_facts hs hB hL he
      rw [backE e tl hins] at hback
      cases hback
      simp [MInst.targets] at h0
      exact htl0 h0.symm
  · -- branch arguments
    intro b vb hvb hba
    rcases H.cases hvb with ⟨B, L, -, hB, hL, rfl⟩ | ⟨bi, B, L, e, hB, hL, he, -, -, rfl⟩
    · have hBm := List.mem_of_getElem? hB
      obtain ⟨t', hb', hjump, -, -⟩ := H.raw_back hs hbt hB hL
      obtain ⟨bc, hj⟩ : ∃ bc, B.term = .jump bc := by
        refine Classical.byContradiction fun hj => hba ?_
        simp only [fixBlock, rawBlock]
        split
        · rename_i bc hbc; exact absurd ⟨bc, hbc⟩ hj
        · simp
      obtain ⟨tl, rfl, hLt⟩ := hjump bc hj
      have ht : B.term.isTry = false := by rw [hj]; rfl
      obtain ⟨bc', hbc', hidx, -⟩ | ⟨e, he, -⟩ := (H.raw_tgt hB hL).1 ht tl (by rw [hLt]; simp)
      · rw [hj] at hbc'
        simp only [dests, List.mem_singleton] at hbc'
        subst hbc'
        obtain ⟨TB, hTB, hTBi⟩ := block?_of_idx hidx
        have htl0 : tl ≠ 0 := fun h0 => hs.noEntryPred B hBm bc'.block
          (by rw [hj]; simp [succIds, dests]) (h0 ▸ hidx)
        obtain ⟨tb, htb, hpar, hnd⟩ := tgtBlk tl TB hTBi htl0
        obtain ⟨tb', htb', hlen, -⟩ := H.lf.args B hBm bc' (by rw [hj]; simp [dests])
        obtain rfl : tb' = TB := Option.some.inj (htb'.symm.trans hTB)
        have hba' : (fixBlock RR (rawBlock f bl b B)).branchArgs =
            ((bc'.args.map fun a => Reg.vreg a .int).toArray).map RR := by
          simp only [fixBlock, rawBlock, hj]
        have hne : bc'.args ≠ [] := by
          intro h0; rw [hba', h0] at hba; exact hba (by simp)
        refine ⟨tl, tb, hb', htb, by rw [hpar, hba']; simp [hlen hne], fun k a p hak hpk => ?_, hnd⟩
        rw [hba'] at hak
        rw [hpar] at hpk
        simp only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_map] at hak hpk
        obtain ⟨a0, -, rfl⟩ := Option.map_eq_some_iff.mp (by simpa using hak)
        obtain ⟨p0, -, rfl⟩ := Option.map_eq_some_iff.mp hpk
        exact ⟨_, _, .int, hRR.vreg _ _, rfl⟩
      · rw [shape_edgeBlocks_jump hj] at he; simp at he
    · obtain ⟨tl, TB, hins, -, hTB, htl0, hlen, hargs⟩ := H.edge_facts hs hB hL he
      obtain ⟨tb, htb, hpar, hnd⟩ := tgtBlk tl TB hTB htl0
      refine ⟨tl, tb, backE e tl hins, htb, by rw [hpar]; simp [fixBlock, hlen], fun k a p hak hpk => ?_, hnd⟩
      simp only [fixBlock, Array.getElem?_map] at hak
      obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.mp hak
      obtain ⟨v, rfl⟩ := hargs a0 (Array.mem_toList_iff.mpr (Array.mem_of_getElem? ha0))
      rw [hpar] at hpk
      simp only [List.getElem?_toArray, List.getElem?_map] at hpk
      obtain ⟨p0, -, rfl⟩ := Option.map_eq_some_iff.mp hpk
      exact ⟨_, _, .int, hRR.vreg _ _, rfl⟩
  · -- no branch arguments
    intro b vb t l tb hvb hba hback hl htb
    -- an edge block target
    have viaE : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (e : VBlock), f.blocks[bi]? = some B →
        bl[bi]? = some L → e ∈ edgeBlocks f B L → e.label = l → tb.params = #[] := by
      intro bi B L e hB hL he hel
      obtain ⟨-, hat⟩ := H.edge_at hB hL he
      rw [hel, htb] at hat
      cases hat
      obtain ⟨-, -, -, hpar, -⟩ := H.edge_facts hs hB hL he
      exact hpar
    -- a CLIF block target without parameters
    have viaB : ∀ (TB : Clif.Block), f.blocks[l]? = some TB → TB.params = [] → tb.params = #[] := by
      intro TB hTB hp
      rw [H.raw_at hTB] at htb
      cases htb
      simp [fixBlock, rawBlock, hp]
    rcases H.cases hvb with ⟨B, L, -, hB, hL, rfl⟩ | ⟨bi, B, L, e, hB, hL, he, -, -, rfl⟩
    · have hBm := List.mem_of_getElem? hB
      obtain ⟨t', hb', -, hnt, htry⟩ := H.raw_back hs hbt hB hL
      rw [hb'] at hback
      cases hback
      rcases try_or B.term with ht | ⟨et, het⟩
      · rw [(hnt ht).1] at hl
        rcases (H.raw_tgt hB hL).1 ht l hl with ⟨bc, hbc, hidx, hcase⟩ | ⟨e, he, hel⟩
        · have hnil : bc.args = [] := by
            rcases hcase with h0 | hj
            · exact h0
            · have : (fixBlock RR (rawBlock f bl b B)).branchArgs =
                  ((bc.args.map fun a => Reg.vreg a .int).toArray).map RR := by
                simp only [fixBlock, rawBlock, hj]
              rw [this] at hba
              simpa using hba
          obtain ⟨TB, hTB, hTBi⟩ := block?_of_idx hidx
          have := ha B hBm bc hbc TB hTB
          rw [hnil] at this
          exact viaB TB hTBi (List.eq_nil_of_length_eq_zero this)
        · exact viaE _ _ _ e hB hL he hel
      · obtain ⟨c, ti, -, htg⟩ := htry et het
        rw [htg] at hl
        obtain ⟨e, he, hel⟩ := ((H.raw_tgt hB hL).2 et het).2 l hl
        exact viaE _ _ _ e hB hL he hel
    · obtain ⟨tl, TB, hins, -, hTB, -, hlen, -⟩ := H.edge_facts hs hB hL he
      rw [backE e tl hins] at hback
      cases hback
      simp [MInst.targets] at hl
      subst hl
      have : e.branchArgs.size = 0 := by
        have := congrArg Array.size hba; simpa [fixBlock] using this
      exact viaB TB hTB (List.eq_nil_of_length_eq_zero (by omega))
  · -- a `try_call`'s block has no branch arguments
    intro b vb info ti hvb hback
    rcases H.cases hvb with ⟨B, L, -, hB, hL, rfl⟩ | ⟨bi, B, L, e, hB, hL, he, -, -, rfl⟩
    · obtain ⟨t', hb', -, hnt, -⟩ := H.raw_back hs hbt hB hL
      rw [hb'] at hback
      cases hback
      rcases try_or B.term with ht | ⟨et, het⟩
      · exact absurd rfl ((hnt ht).2 info ti)
      · simp only [fixBlock, rawBlock]
        split
        · rename_i bc hbc; rcases het with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] at hbc <;> cases hbc
        · simp
    · obtain ⟨tl, TB, hins, -⟩ := H.edge_facts hs hB hL he
      rw [backE e tl hins] at hback
      cases hback
  · -- a `try_call`'s successor is its own
    intro b vb info ti j l hvb hback hj b' vb' t' j' hvb' hback' hj'
    rcases H.cases hvb with ⟨B, L, -, hB, hL, rfl⟩ | ⟨bi, B, L, e, hB, hL, he, -, -, rfl⟩
    · obtain ⟨t0, hb0, -, hnt, htry⟩ := H.raw_back hs hbt hB hL
      rw [hb0] at hback
      cases hback
      rcases try_or B.term with ht | ⟨et, het⟩
      · exact absurd rfl ((hnt ht).2 info ti)
      obtain ⟨c, ti', -, htg⟩ := htry et het
      have hlm : l ∈ L.targets := by rw [← htg]; exact List.mem_of_getElem? hj
      obtain ⟨hnodup, hall⟩ := (H.raw_tgt hB hL).2 et het
      obtain ⟨e, he, hel⟩ := hall l hlm
      have hge := (H.edge_at hB hL he).1
      rw [hel] at hge
      rcases H.cases hvb' with ⟨B', L', -, hB', hL', rfl⟩ | ⟨bi', B', L', e', hB', hL', he', -, -, rfl⟩
      · obtain ⟨t1, hb1, -, hnt', htry'⟩ := H.raw_back hs hbt hB' hL'
        rw [hb1] at hback'
        cases hback'
        have hlm' : ∀ hl' : l ∈ L'.targets, ∃ e' ∈ edgeBlocks f B' L', e'.label = l := by
          intro hl'
          rcases try_or B'.term with ht' | ⟨et', het'⟩
          · rcases (H.raw_tgt hB' hL').1 ht' l hl' with ⟨bc, -, hidx, -⟩ | h
            · obtain ⟨TB, -, hTBi⟩ := block?_of_idx hidx
              have := (List.getElem?_eq_some_iff.mp hTBi).1
              omega
            · exact h
          · exact ((H.raw_tgt hB' hL').2 et' het').2 l hl'
        rcases try_or B'.term with ht' | ⟨et', het'⟩
        · rw [(hnt' ht').1] at hj'
          obtain ⟨e', he', hel'⟩ := hlm' (List.mem_of_getElem? hj')
          have := H.edge_disj hB hL hB' hL' he he' (by rw [hel, hel'])
          subst this
          rw [hB] at hB'
          cases hB'
          rw [isTry_of het] at ht'
          cases ht'
        · obtain ⟨c', ti'', -, htg'⟩ := htry' et' het'
          rw [htg'] at hj'
          obtain ⟨e', he', hel'⟩ := hlm' (List.mem_of_getElem? hj')
          have := H.edge_disj hB hL hB' hL' he he' (by rw [hel, hel'])
          subst this
          rw [hL] at hL'
          cases hL'
          refine ⟨rfl, ?_⟩
          rw [htg] at hj
          exact nodup_idx hnodup hj' hj
      · obtain ⟨tl, TB, hins, -, hTB, -⟩ := H.edge_facts hs hB' hL' he'
        rw [backE e' tl hins] at hback'
        cases hback'
        have hj0 : j' = 0 := by
          have := (List.getElem?_eq_some_iff.mp hj').1; simp [MInst.targets] at this; omega
        subst hj0
        simp [MInst.targets] at hj'
        subst hj'
        have := (List.getElem?_eq_some_iff.mp hTB).1
        omega
    · obtain ⟨tl, TB, hins, -⟩ := H.edge_facts hs hB hL he
      rw [backE e tl hins] at hback
      cases hback

end Backend.Proof.Spill

import FV.Backend.Proof.SpillEdgesLow
import FV.Backend.Proof.LowerShapeOkT

/-!
# The CFG facts of `lowerFunction`'s VCode, typed (S11e5 Stage C, slice 3)

`LowT`: `Low` over the typed loop simulation (typed raw blocks `rawBlockT`, typed edge blocks
`edgeBlocksT`, typed loop facts `LoopFactsT`). `lowT_of` needs no premise on `f`
(`low_of` takes `Compile.functionE`). The label, block-position and target facts carry over
(`LowT.labs`, `cases`, `raw_at`, `edge_at`, `edge_disj`, `raw_tgt`); an edge block's arguments
are vregs of any class (`LowT.edge_facts`, where `Low.edge_facts` says `.int`). On integer
contexts `LowT` is `Low` (`Low.toT`, `LowT.toLow`).
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Driver

/-- What the lowering run records about `vc`, typed. -/
structure LowT (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (bl : List BLow)
    (RR : Reg → Reg) : Prop where
  hb : ∃ ranges, buildCtx f = .ok (ctx, ranges, st0)
  low : ∃ stE nlE, lowB f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
    some (bl, stE, nlE)
  blocks : vc.blocks.toList = (((f.blocks.zip bl).zipIdx.map fun p => rawBlockT f ctx bl p.2 p.1.1) ++
    (f.blocks.zip bl).flatMap fun p => edgeBlocksT f ctx p.1 p.2).map (fixBlock RR)
  ren : ∃ gn, VRenaming RR gn
  lf : LoopFactsT f ctx bl
  len : bl.length = f.blocks.length

/-- **The typed lowering run**, on every input. -/
theorem lowT_of {f : Clif.Function} {vc : VCode} (h : lowerFunction f = .ok vc) :
    ∃ ctx st0 bl RR, LowT f vc ctx st0 bl RR := by
  obtain ⟨ctx, ranges, st0, bl, hb, hl, hvb, -, hlf⟩ := lowerFunction_runT h
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
    refine ⟨ctx, st0, bl', lowerFunction.resolve (aliasArr (aliasOf f bl'))
      ((aliasArr (aliasOf f bl')).size + 1), ⟨⟨ranges, hb⟩, ⟨stE, nlE, hr⟩,
      by rw [hvb]; simp [vcBlocksOfT], resolve_vrenaming _ _, hlf, (lowBlocks_spec hbl).1⟩⟩

/-! ## Integer specialization -/

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {bl : List BLow}
  {RR : Reg → Reg} (hE : CtxE ctx)
include hE

theorem blocksT_int :
    (((f.blocks.zip bl).zipIdx.map fun p => rawBlockT f ctx bl p.2 p.1.1) ++
      (f.blocks.zip bl).flatMap fun p => edgeBlocksT f ctx p.1 p.2) =
    (((f.blocks.zip bl).zipIdx.map fun p => rawBlock f bl p.2 p.1.1) ++
      (f.blocks.zip bl).flatMap fun p => edgeBlocks f p.1 p.2) := by
  have hr : (fun (p : (Clif.Block × BLow) × Nat) => rawBlockT f ctx bl p.2 p.1.1) =
      fun p => rawBlock f bl p.2 p.1.1 := funext fun p => rawBlockT_int hE f bl p.2 p.1.1
  have he : (fun (p : Clif.Block × BLow) => edgeBlocksT f ctx p.1 p.2) =
      fun p => edgeBlocks f p.1 p.2 := funext fun p => edgeBlocksT_int hE f p.1 p.2
  rw [hr, he]

theorem LoopFacts.toT (h : LoopFacts f ctx bl) : LoopFactsT f ctx bl := by
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

/-- An integer run is a typed one (on an integer context). -/
theorem Low.toT (H : Low f vc ctx st0 bl RR) : LowT f vc ctx st0 bl RR :=
  ⟨H.hb, H.low, by rw [H.blocks, blocksT_int hE], H.ren, LoopFacts.toT hE H.lf, H.len⟩

/-- A typed run on an integer context is the integer one. -/
theorem LowT.toLow (H : LowT f vc ctx st0 bl RR) : Low f vc ctx st0 bl RR :=
  ⟨H.hb, H.low, by rw [H.blocks, blocksT_int hE], H.ren, LoopFactsT.toInt hE H.lf, H.len⟩

end

/-! ## The CFG facts -/

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {bl : List BLow} {RR : Reg → Reg}
  (H : LowT f vc ctx st0 bl RR)
include H

theorem LowT.hbl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
    some bl := by
  obtain ⟨stE, nlE, hr⟩ := H.low
  rw [lowBlocks_eq, hr]; rfl

theorem LowT.labs : ((f.blocks.zip bl).flatMap fun p => edgeBlocksT f ctx p.1 p.2).map (·.label) =
    List.range' f.blocks.length (((f.blocks.zip bl).flatMap fun p => edgeBlocksT f ctx p.1 p.2).length) := by
  obtain ⟨stE, nlE, hr⟩ := H.low
  obtain ⟨h1, -⟩ := lowB_labels _ _ _ _ _ _ _ hr
  rw [← edgesT_labels ctx] at h1
  have := congrArg List.length h1
  simp only [List.length_map, List.length_range'] at this
  rw [h1, this]

theorem LowT.rawLen : ((f.blocks.zip bl).zipIdx.map fun p => rawBlockT f ctx bl p.2 p.1.1).length =
    f.blocks.length := by
  simp [H.len]

/-- The blocks of `vc`: CLIF block `x`'s typed code or a typed edge block labelled `x`. -/
theorem LowT.cases {x : Nat} {vb : VBlock} (hx : vc.blocks[x]? = some vb) :
    (∃ B L, x < f.blocks.length ∧ f.blocks[x]? = some B ∧ bl[x]? = some L ∧
      vb = fixBlock RR (rawBlockT f ctx bl x B)) ∨
    (∃ (bi : Nat) (B : Clif.Block) (L : BLow) (e : VBlock), f.blocks[bi]? = some B ∧ bl[bi]? = some L ∧
      e ∈ edgeBlocksT f ctx B L ∧ e.label = x ∧ f.blocks.length ≤ x ∧ vb = fixBlock RR e) := by
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
    cases he : ((f.blocks.zip bl).flatMap fun p => edgeBlocksT f ctx p.1 p.2)[x - f.blocks.length]? with
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

theorem LowT.raw_at {x : Nat} {B : Clif.Block} (hB : f.blocks[x]? = some B) :
    vc.blocks[x]? = some (fixBlock RR (rawBlockT f ctx bl x B)) := by
  have hxn : x < f.blocks.length := (List.getElem?_eq_some_iff.mp hB).1
  obtain ⟨L, hL⟩ : ∃ L, bl[x]? = some L := ⟨_, List.getElem?_eq_getElem (by rw [H.len]; exact hxn)⟩
  rw [← Array.getElem?_toList, H.blocks, List.getElem?_map,
    List.getElem?_append_left (by rw [H.rawLen]; exact hxn), List.getElem?_map, List.getElem?_zipIdx,
    (List.getElem?_zip_eq_some (z := (B, L))).mpr ⟨hB, hL⟩]
  simp

theorem LowT.edge_at {bi : Nat} {B : Clif.Block} {L : BLow} (hB : f.blocks[bi]? = some B)
    (hL : bl[bi]? = some L) {e : VBlock} (he : e ∈ edgeBlocksT f ctx B L) :
    f.blocks.length ≤ e.label ∧ vc.blocks[e.label]? = some (fixBlock RR e) := by
  have hm : e ∈ (f.blocks.zip bl).flatMap fun p => edgeBlocksT f ctx p.1 p.2 :=
    List.mem_flatMap.mpr ⟨(B, L), List.mem_of_getElem?
      ((List.getElem?_zip_eq_some (z := (B, L))).mpr ⟨hB, hL⟩), he⟩
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

/-- Typed edge blocks of different CLIF blocks have different labels. -/
theorem LowT.edge_disj {bi bi' : Nat} {B B' : Clif.Block} {L L' : BLow} (hB : f.blocks[bi]? = some B)
    (hL : bl[bi]? = some L) (hB' : f.blocks[bi']? = some B') (hL' : bl[bi']? = some L')
    {e e' : VBlock} (he : e ∈ edgeBlocksT f ctx B L) (he' : e' ∈ edgeBlocksT f ctx B' L')
    (hl : e.label = e'.label) : bi = bi' := by
  have hn : (((f.blocks.zip bl).flatMap fun p => edgeBlocksT f ctx p.1 p.2).map (·.label)).Nodup := by
    rw [H.labs]; exact List.nodup_range'
  have hz := (List.getElem?_zip_eq_some (z := (B, L))).mpr ⟨hB, hL⟩
  have hz' := (List.getElem?_zip_eq_some (z := (B', L'))).mpr ⟨hB', hL'⟩
  rcases Nat.lt_trichotomy bi bi' with h | h | h
  · exact absurd hl (nodup_flat_lab (fun p => edgeBlocksT f ctx p.1 p.2) _ hn bi bi' _ _ h hz hz' e he e' he')
  · exact h
  · exact absurd hl.symm (nodup_flat_lab (fun p => edgeBlocksT f ctx p.1 p.2) _ hn bi' bi _ _ h hz' hz e' he' e he)

/-- **The targets of CLIF block `x`'s terminator** (typed edge blocks). -/
theorem LowT.raw_tgt {x : Nat} {B : Clif.Block} {L : BLow} (hB : f.blocks[x]? = some B)
    (hL : bl[x]? = some L) :
    (B.term.isTry = false → ∀ l ∈ L.targets,
      (∃ bc ∈ dests B.term, blockIdx? f bc.block = some l ∧ (bc.args = [] ∨ B.term = .jump bc)) ∨
      (∃ e ∈ edgeBlocksT f ctx B L, e.label = l)) ∧
    (∀ et, IsTryWith B.term et → L.targets.Nodup ∧
      ∀ l ∈ L.targets, ∃ e ∈ edgeBlocksT f ctx B L, e.label = l) := by
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
          (((dests B.term)[k]).args.map (fun a => vregOf ctx a)).toArray⟩, ?_, rfl⟩
        rw [shape_edgeBlocksT_other ht hj']
        exact List.mem_filterMap.mpr ⟨_, hpz, by simp [edgeOfBcT, ha, htl]⟩
  · intro et het
    obtain ⟨T, hT, -, -, htt, -⟩ := (lowTerm_spec hlt).2 et het
    obtain ⟨hts, -, hall⟩ := tryTargets_spec htt
    refine ⟨by rw [hts]; exact List.nodup_range', fun l hl => ?_⟩
    have hlabs := edgeOfTry_labels (f := f) (T := T) (ds := et.dests) (ls := L.targets)
      (by rw [hts]; simp) hall
    rw [← shape_edgeBlocks_try het hT, ← edgeBlocksT_labels ctx] at hlabs
    rw [← hlabs] at hl
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hl
    exact ⟨e, he, rfl⟩

/-- **A typed edge block** jumps to a non-entry block whose parameters its arguments (vregs, of
any class) match. -/
theorem LowT.edge_facts (hs : LowerScopeT f) {bi : Nat} {B : Clif.Block} {L : BLow}
    (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L) {e : VBlock} (he : e ∈ edgeBlocksT f ctx B L) :
    ∃ tl TB, e.insts = #[.jump tl] ∧ e.params = #[] ∧ f.blocks[tl]? = some TB ∧ tl ≠ 0 ∧
      TB.params.length = e.branchArgs.size ∧ ∀ a ∈ e.branchArgs.toList, ∃ v c, a = .vreg v c := by
  have hBm : B ∈ f.blocks := List.mem_of_getElem? hB
  obtain ⟨-, -, -, nl0, nl1, hlt⟩ := (lowBlocks_spec H.hbl).2 bi B L hB hL
  rcases try_or B.term with ht | ⟨et, het⟩
  · by_cases hj : ∃ bc, B.term = .jump bc
    · obtain ⟨bc, hj⟩ := hj
      unfold edgeBlocksT at he
      rw [hj] at he
      simp at he
    · have hj' : ∀ bc, B.term ≠ .jump bc := fun bc e => hj ⟨bc, e⟩
      rw [shape_edgeBlocksT_other ht hj'] at he
      obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.mp he
      simp only [edgeOfBcT] at hpe
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
        simp only [List.mem_map] at hm
        obtain ⟨v, -, rfl⟩ := hm
        exact ⟨v, _, rfl⟩
  · obtain ⟨T, hT, -, hexn, -, hregs, -, -⟩ := (lowTerm_spec hlt).2 et het
    rw [shape_edgeBlocksT_try het hT] at he
    obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.mp he
    simp only [edgeOfTryT] at hpe
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
      simp only [List.mem_map] at hm
      obtain ⟨ta, hta, rfl⟩ := hm
      have hok := hai ta hta
      rw [hregs']
      cases ta with
      | val v => exact ⟨v, _, rfl⟩
      | ret i =>
        simp only at hok
        rw [hregs'] at hok
        simp only [List.length_map, List.length_range] at hok
        exact ⟨L.tst.nextVreg + i, .int, by simp [tryEdgeArgT, hok.2]⟩
      | exn i =>
        simp only at hok
        rw [hregs'] at hok
        simp only [List.length_cons, List.length_nil] at hok
        have : i = 0 ∨ i = 1 := by omega
        rcases this with rfl | rfl
        · exact ⟨_, _, rfl⟩
        · exact ⟨_, _, rfl⟩

end

end Backend.Proof.Spill

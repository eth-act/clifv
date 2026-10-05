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

end

end Backend.Proof.Spill

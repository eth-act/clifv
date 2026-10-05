import FV.Backend.Proof.LowerLoop
import FV.Backend.Proof.LowerAlias
import FV.Backend.Proof.IselFlow
import FV.Backend.Proof.IselTermFacts
import FV.Backend.Proof.LowerShapeOkFacts

/-!
# Completeness of `lowerCheck`: the shape of the VCode

`shapeOk_complete`: on in-scope SSA input with well-founded aliases, `shapeOk` accepts
`lowerFunction`'s VCode (blocks = the renamed recorded code, labels, parameters, branch
arguments, edge blocks, the statements' alias facts, non-empty terminator segments).

`lowerFunction_run` gives the VCode as `vcBlocksOf f bl`: the raw blocks, then the edge blocks,
renamed by `lowerFunction`'s alias chase, which is `renOf gn` (`resolve_eq`). The raw blocks sit
at their indices and the edge blocks at the labels their terminators allocated (consecutive from
`f.blocks.length`, `lowBlocks_thread`), so every block is found at its label.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

variable {f : Clif.Function} {vc : VCode}

/-- **The shape part of `lowerCheck`.** -/
theorem shapeOk_complete (h : lowerFunction f = .ok vc) (hs : LowerScope f)
    (hssa : (valueDefs f).Nodup) {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    {bl : List BLow} (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl)
    (hu : ((aliasOf f bl).map (·.1)).Nodup) (hwf : AliasWF (aliasOf f bl)) :
    shapeOk f vc ctx st0 (gnAt (gnTable st0.nextVreg (aliasOf f bl))) bl = true := by
  -- the run
  obtain ⟨ctx', ranges', st0', bl', hb', hl', hvc, -, hlf⟩ := lowerFunction_run h
  rw [hb] at hb'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
  obtain ⟨rfl, rfl, rfl⟩ := hb'
  rw [hl, Option.some.injEq] at hl'
  subst hl'
  have hcf := ctxFacts_of hb
  obtain ⟨hlen, hlb⟩ := lowBlocks_spec hl
  obtain ⟨-, hstart⟩ := lowBlocks_start hl
  have hctxok := ctxOk_complete hs hb
  have hinv := ctxOk_sound hctxok
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
  -- the states and labels along the lowering
  have hmono : ∀ {c : Ctx} {term : String} {args : List V} {s : LState} {o : Option V}
      {s' : LState} {tr : List Isle.RuleId}, runTerm c term args s = .ok (o, s', tr) →
      s.nextVreg ≤ s'.nextVreg := fun h => (runTerm_mono h).1
  obtain ⟨⟨k, hek⟩, hth⟩ := lowBlocks_thread (fun _ _ _ _ _ h => hmono h)
    (fun _ _ _ _ _ _ _ _ h => hmono h) (fun _ _ _ _ _ _ _ _ h => hmono h) hl
  -- the VCode
  obtain ⟨raws, hraws⟩ : ∃ r : List VBlock,
      r = (f.blocks.zip bl).zipIdx.map fun p => rawBlock f bl p.2 p.1.1 := ⟨_, rfl⟩
  obtain ⟨edges, hedges⟩ : ∃ e : List VBlock,
      e = (f.blocks.zip bl).flatMap fun p => edgeBlocks f p.1 p.2 := ⟨_, rfl⟩
  rw [← hedges] at hek
  have hvc' : vc.blocks = ((raws ++ edges).map (fixBlock (renOf gn))).toArray := by
    rw [hvc, ← hR, hraws, hedges]; rfl
  have hraws_len : raws.length = f.blocks.length := by simp [hraws, hlen]
  have hedges_len : edges.length = k := by
    have := congrArg List.length hek
    simpa using this
  have hraw : ∀ bi B L, f.blocks[bi]? = some B → bl[bi]? = some L →
      raws[bi]? = some (rawBlock f bl bi B) := by
    intro bi B L hB hL
    have hz : (f.blocks.zip bl)[bi]? = some (B, L) := List.getElem?_zip_eq_some.mpr ⟨hB, hL⟩
    simp only [hraws, List.getElem?_map, List.getElem?_zipIdx, hz, Option.map_some, Nat.zero_add]
  have hlab : ∀ i (hi : i < (raws ++ edges).length), (raws ++ edges)[i].label = i := by
    intro i hi
    by_cases h1 : i < raws.length
    · rw [List.getElem_append_left h1]
      simp [hraws, rawBlock]
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
      vc.blocks[bi]? = some (fixBlock (renOf gn) (rawBlock f bl bi B)) := by
    intro bi B L hB hL
    have hbi : bi < raws.length := by rw [hraws_len]; exact lt_of_getElem? hB
    rw [hvc', List.getElem?_toArray, List.getElem?_map, List.getElem?_append_left hbi,
      hraw bi B L hB hL, Option.map_some]
  have hedge : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
      ∀ eb ∈ edgeBlocks f B L, ∀ l : Nat, eb.label = l → vc.blocks[l]? = some (fixBlock (renOf gn) eb) := by
    intro bi B L hB hL eb heb l hl
    have hm : eb ∈ raws ++ edges := by
      refine List.mem_append_right _ ?_
      rw [hedges]
      exact List.mem_flatMap.mpr ⟨(B, L),
        List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hB, hL⟩), heb⟩
    rw [hvc', List.getElem?_toArray, List.getElem?_map, ← hl, get_label hlab hm, Option.map_some]
  -- one block
  have hblock : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
      blockOk f vc ctx st0 (renOf gn) gn bl bi B L = true := by
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
        have hlt' := term_emits hinv hti hph ht hd htg hvb hbt hrun
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
    have hsucc : succOk f vc (renOf gn) B L = true := by
      have he := hedge bi B L hB hL
      rcases try_or B.term with ht | ⟨et, ht⟩
      · have htg := lowTerm_targets ht hlt
        by_cases hj : ∃ bc, B.term = .jump bc
        · obtain ⟨bc, hj⟩ := hj
          unfold succOk
          rw [hj] at htg ⊢
          simp only [targetsOf, Option.map_eq_some_iff, Prod.mk.injEq] at htg
          obtain ⟨tl, htl, h1, -⟩ := htg
          simp [htl, h1]
        · have hj' : ∀ bc, B.term ≠ .jump bc := fun bc e => hj ⟨bc, e⟩
          rw [shape_targetsOf_other hj'] at htg
          obtain ⟨h1, -, h3, -⟩ := edgeTargets_spec htg
          have hed := shape_edgeBlocks_other (L := L) (f := f) ht hj'
          unfold succOk
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
                           branchArgs := (bc.args.map fun a => Reg.vreg a .int).toArray } : VBlock) ∈
                  edgeBlocks f B L := by
                rw [hed]
                exact List.mem_filterMap.mpr ⟨(bc, tlab), hp, by simp [edgeOfBc, htl, hne']⟩
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
                     branchArgs := (et.normal.args.map (tryEdgeArg T.regs.1 T.regs.2)).toArray } :
              VBlock) ∈ edgeBlocks f B L := by
          rw [shape_edgeBlocks_try ht hT]
          exact List.mem_filterMap.mpr ⟨_, hmemz, by simp [edgeOfTry, htl]⟩
        have hvbl := he _ hm _ rfl
        have hnorm := hargs et.handlers.length et.normal (by simp [Clif.ExnTable.dests])
        have hnoexn : ∀ i, Clif.TryArg.exn i ∉ et.normal.args := fun i hi => by
          have := hnorm.2 _ hi
          simp at this
        unfold succOk
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
    unfold blockOk
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
    · exact rawBlock_insts f (renOf gn) bl bi B
    · cases h : tseg (renOf gn) bl bi with
      | nil => exact absurd h hne
      | cons => rfl
    · simp only [fixBlock, rawBlock]
      generalize B.term = t
      cases t <;> simp
    · rw [hph]; rfl
  -- the function
  simp only [shapeOk, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨hctxok, ?_⟩, ?_⟩, hlen⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
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

end Backend.Proof.Driver

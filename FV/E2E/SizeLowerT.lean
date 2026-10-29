import FV.E2E.SizeLower
import FV.E2E.DeadCleanupSize
import FV.Backend.Proof.IselSzTDriver
import FV.Backend.Proof.LowerLoopT
import FV.Backend.Proof.LowerShapeOkT
import FV.Backend.Proof.LowerCompleteT

/-!
# The size of `lowerFunction`'s output from the ISLE runs, on every input (typed V6c)

`SizeLower`'s walk over the typed loop simulation (`lowerFunction_runT`, the typed blocks
`vcBlocksOfT`: entry loads and result `mov`s of the values' classes, weighing as the integer
ones): `size_lowerT` gives `size_lower`'s three bounds from `IselSzT f` (the ISLE runs of the
driver for `f`'s own terminators) on every input, and `spillSizeOkB_of_sizeOkBT` /
`spillSizeOkB_cleanup_of_sizeOkBT` the size bound `spillSizeOkB` of the prepared VCode (without
and with the dead-code cleanup `prune`) on the typed scope with `sizeOkB f` (`iselSzT`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Cov Backend.Proof.Driver Backend.DeadCleanup

/-! ## The typed driver's own instructions -/

theorem extraOfT_facts {ctx : Ctx} {results : List Nat} {rss : List (List Reg)} :
    ∀ m ∈ extraOfT ctx results rss, szInstW m = movW ∧ m.targets = [] ∧ regCount m = 5 := by
  intro m hm
  obtain ⟨s, a, b, rfl⟩ := mem_extraOfT hm
  exact ⟨rfl, rfl, rfl⟩

theorem extraOfT_length (ctx : Ctx) (results : List Nat) (rss : List (List Reg)) :
    (extraOfT ctx results rss).length ≤ results.length :=
  Nat.le_trans (List.length_filterMap_le _ _) (by simp [List.length_zip, Nat.min_le_left])

/-- The entry block's code before its statements: `Args` and parameter loads. -/
theorem pre_factsT (f : Clif.Function) (ctx : Ctx) (R : Reg → Reg) {bi : Nat} {B : Clif.Block}
    (hB : f.blocks[bi]? = some B) :
    wtL (preT f ctx R bi) ≤ (if bi = 0 then entryIn B else 0) ∧ tgL (preT f ctx R bi) = 0 ∧
      ∀ m ∈ preT f ctx R bi, regCount m ≤ max 5 B.params.length := by
  unfold preT
  split
  · rename_i B0 hB0
    rw [hB] at hB0
    cases hB0
    have hlen : (entryParams f B).length ≤ B.params.length := by
      simp only [entryParams, List.length_zip]; omega
    have hr : (entryRegsT f ctx R B).length ≤ B.params.length :=
      Nat.le_trans (List.length_filterMap_le _ _) hlen
    have hl : (entryLoadsT f ctx R B).length ≤ B.params.length :=
      Nat.le_trans (List.length_filterMap_le _ _) hlen
    have hload : ∀ m ∈ entryLoadsT f ctx R B, szInstW m = 105 ∧ m.targets = [] ∧ regCount m = 5 := by
      intro m hm
      simp only [entryLoadsT, List.mem_filterMap] at hm
      obtain ⟨q, -, hq⟩ := hm
      unfold entryLoadOfT at hq
      split at hq
      · cases hq
        unfold stackArgLoad
        split <;> exact ⟨rfl, rfl, rfl⟩
      · cases hq
    refine ⟨?_, ?_, ?_⟩
    · rw [wtL_cons]
      have h1 := wtL_le_mul (fun m hm => Nat.le_of_eq (hload m hm).1)
      have h2 : szInstW (.args (entryRegsT f ctx R B)) = 1 + 20 * (entryRegsT f ctx R B).length := by
        simp [szInstW, szWords, regCount, MInst.targets]
      simp only [↓reduceIte, entryIn]
      rw [h2]
      have := Nat.mul_le_mul_left 105 hl
      have := Nat.mul_le_mul_left 20 hr
      omega
    · simp only [tgL, List.map_cons, List.sum_cons]
      have := tgL_eq_zero (fun m hm => (hload m hm).2.1)
      simpa [tgL, MInst.targets] using this
    · intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact Nat.le_trans hr (Nat.le_max_right _ _)
      · rw [(hload m hm).2.2]; exact Nat.le_max_left _ _
  · exact ⟨Nat.zero_le _, rfl, fun m hm => by cases hm⟩

theorem seg_eqT {f : Clif.Function} {ctx : Ctx} {R : Reg → Reg} {bl : List BLow} {bi j : Nat}
    {B : Clif.Block} {L : BLow} {stm : Clif.Stmt} {sl : SLow} (hB : f.blocks[bi]? = some B)
    (hL : bl[bi]? = some L) (hj : B.body[j]? = some stm) (hsl : L.sl[j]? = some sl) :
    segT f ctx R bl bi j =
      (sl.st'.emitted.toList ++ extraOfT ctx stm.results sl.rss).map (·.mapRegs R) := by
  unfold segT; rw [hB, hL]; simp only [hj, hsl]

theorem rawBlockT_branchArgs (f : Clif.Function) (ctx : Ctx) (bl : List BLow) (bi : Nat)
    (B : Clif.Block) : (rawBlockT f ctx bl bi B).branchArgs.size = jumpArgsIn B.term := by
  unfold rawBlockT
  cases B.term <;> simp [jumpArgsIn]

/-- The typed edge blocks of a block, summed by any measure bounded per branch-argument count. -/
theorem edges_leT {f : Clif.Function} {ctx : Ctx} {B : Clif.Block} {L : BLow} (W : VBlock → Nat)
    (w : Nat → Nat) (hW : ∀ e tl, e.insts = #[.jump tl] → W e ≤ w e.branchArgs.size) :
    ((edgeBlocksT f ctx B L).map W).sum ≤ ((edgeArgsIn B.term).map w).sum := by
  have hbr : ∀ bcs : List Clif.BlockCall, ∀ ls : List Label,
      ((((bcs.zip ls).filterMap fun (p : Clif.BlockCall × Label) =>
        if p.1.args.isEmpty then none else (blockIdx? f p.1.block).map fun tl =>
          ({ label := p.2, insts := #[.jump tl],
             branchArgs := (p.1.args.map fun a => vregOf ctx a).toArray } : VBlock))).map W).sum ≤
        ((bcs.filterMap fun bc => if bc.args.isEmpty then none else some bc.args.length).map w).sum :=
    sum_filterMap_zip_le W w _ _ (fun bc l e he => by
      simp only at he
      split at he
      · cases he
      · rename_i hne
        simp only [Option.map_eq_some_iff] at he
        obtain ⟨tl, -, rfl⟩ := he
        refine ⟨bc.args.length, by simp [hne], ?_⟩
        exact Nat.le_trans (hW _ tl rfl) (by simp))
  have htry : ∀ (et : Clif.ExnTable) (T : TryLow),
      ((((et.dests.zip L.targets).filterMap fun (x : Clif.TryDest × Label) => match x with
        | (td, l) => (blockIdx? f td.block).map fun tl =>
          ({ label := l, insts := #[.jump tl],
             branchArgs := (td.args.map (tryEdgeArgT ctx T.regs.1 T.regs.2)).toArray } : VBlock))).map W).sum ≤
        ((et.dests.map (·.args.length)).map w).sum := by
    intro et T
    refine Nat.le_trans (sum_filterMap_zip_le W w _ (fun td : Clif.TryDest => some td.args.length)
      (fun td l e he => ?_) et.dests L.targets) (Nat.le_of_eq ?_)
    · simp only [Option.map_eq_some_iff] at he
      obtain ⟨tl, -, rfl⟩ := he
      exact ⟨_, rfl, Nat.le_trans (hW _ tl rfl) (by simp)⟩
    · simp
  unfold edgeBlocksT
  split
  · rename_i ht _
    rw [ht]; exact htry _ _
  · rename_i ht _
    rw [ht]; exact htry _ _
  · simp
  · rename_i hj _ _
    refine Nat.le_trans (hbr (dests B.term) L.targets) ?_
    cases h : B.term with
    | jump bc => exact (hj bc h).elim
    | _ => simp [dests, edgeArgsIn]

/-! ## `lowerFunction`'s output -/

/-- **The size of `lowerFunction`'s output from the ISLE runs** (typed): given the driver's
contract on `f`'s own terminators `IselSzT f`, on every input (the typed loop simulation
`lowerFunction_runT`), every instruction of `lowerFunction f`'s VCode has at most `mIn f` register operands,
its weight (with `mIn f` bounding the operands) is at most `vcIn (mIn f) f`, and its branch
targets at most `tgIn f`. Integer externs (`hx`): `lowerFunction_runT`'s premise since #609. -/
theorem size_lowerT {f : Clif.Function} {vc : VCode} (hI : IselSzT f)
    (hx : f.externs.all (Compile.sigE ·.2.sig) = true) (hl : lowerFunction f = .ok vc) :
    maxRC vc ≤ mIn f ∧ vcW (mIn f) vc ≤ vcIn (mIn f) f ∧ vcTg vc ≤ tgIn f := by
  obtain ⟨ctx, ranges, st0, bl, hb, hlb, hvb, -, -⟩ := lowerFunction_runT hx hl
  obtain ⟨hS, hT, hY⟩ := hI ctx ranges st0 hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  -- a statement's segment: its run (from nothing emitted) and the result `mov`s
  have hseg : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
      f.blocks[bi]? = some B → bl[bi]? = some L → B.body[j]? = some stm →
      L.sl[j]? = some sl →
      wtL (sl.st'.emitted.toList ++ extraOfT ctx stm.results sl.rss) ≤ stmtIn stm ∧
      tgL (sl.st'.emitted.toList ++ extraOfT ctx stm.results sl.rss) = 0 ∧
      ∀ m ∈ sl.st'.emitted.toList ++ extraOfT ctx stm.results sl.rss, regCount m ≤ mIn f := by
    intro bi B L j stm sl hB hL hj hsl
    obtain ⟨-, hc, -, -⟩ := hspec bi B L hB hL
    obtain ⟨info, hi, hic, -⟩ := hcf.stmt bi B j stm hB hj
    obtain ⟨tr, hrun⟩ := hc j sl hsl
    rw [hstart bi L hL] at hrun
    obtain ⟨hw, htg⟩ := hS _ info stm.inst _ _ _ _ hi hic hrun
    rw [hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)] at hw htg
    have hw' : wtL sl.st'.emitted.toList ≤ stmtSzB stm.inst :=
      Nat.le_trans hw (Nat.le_of_eq (Nat.zero_add _))
    have htg' : tgL sl.st'.emitted.toList = 0 := Nat.le_zero.mp htg
    have hmax := (mIn_block (List.mem_of_getElem? hB)).2.1 stm (List.mem_of_getElem? hj)
    have hx := extraOfT_facts (ctx := ctx) (results := stm.results) (rss := sl.rss)
    refine ⟨?_, ?_, ?_⟩
    · rw [wtL_append]
      have h1 := wtL_le_mul (fun m hm => Nat.le_of_eq (hx m hm).1)
      have h2 := Nat.mul_le_mul_left movW (extraOfT_length ctx stm.results sl.rss)
      unfold stmtIn
      omega
    · rw [tgL_append, tgL_eq_zero (fun m hm => (hx m hm).2.1), htg']
    · intro m hm
      rcases List.mem_append.mp hm with hm | hm
      · exact Nat.le_trans (regCount_le_of_mem hm hw') hmax
      · rw [(hx m hm).2.2]; exact five_le_mIn f
  -- the terminator's segment: its run, and a `try_call`'s `tryCall`
  have hterm : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B →
      bl[bi]? = some L →
      wtL (fixTry L.tl L.tst'.emitted.toList) ≤ termIn B.term ∧
      tgL (fixTry L.tl L.tst'.emitted.toList) ≤ termTgB B.term + tryDestsIn B.term ∧
      ∀ m ∈ fixTry L.tl L.tst'.emitted.toList, regCount m ≤ mIn f := by
    intro bi B L hB hL
    obtain ⟨-, -, htst, nl0, nl', hlt⟩ := hspec bi B L hB hL
    obtain ⟨hn, hy⟩ := lowTerm_spec hlt
    have hph := hcf.term bi B hB
    rw [← hstart bi L hL] at hph
    have hti := (Array.getElem?_eq_some_iff.mp hph).1
    have hmax := (mIn_block (List.mem_of_getElem? hB)).2.2
    cases ht : B.term.isTry with
    | false =>
      obtain ⟨htl, hd, out, tr, hc⟩ := hn ht
      obtain ⟨hw, htg⟩ := hT B (List.mem_of_getElem? hB) _ _ _ _ _ _ _ hti hph ht hd (lowTerm_targets_le hlt ht) hc
      rw [htst] at hw htg
      have hw' : wtL L.tst'.emitted.toList ≤ termSzB B.term :=
        Nat.le_trans hw (Nat.le_of_eq (Nat.zero_add _))
      have htg' : tgL L.tst'.emitted.toList ≤ termTgB B.term :=
        Nat.le_trans htg (Nat.le_of_eq (Nat.zero_add _))
      obtain ⟨hi1, hi2⟩ := termIn_of_not_try ht
      rw [htl, hi1, hi2]
      simp only [fixTry, Nat.add_zero]
      exact ⟨hw', htg', fun m hm => Nat.le_trans (regCount_le_of_mem hm hw') hmax⟩
    | true =>
      obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := by
        cases hB' : B.term <;> rw [hB'] at ht <;> simp [Clif.Terminator.isTry] at ht
        · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
        · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
      obtain ⟨T, hT', hd, he, htt, hr, hi, out, tr, hc⟩ := hy et het
      obtain ⟨hw, htg⟩ := hY B (List.mem_of_getElem? hB) _ _ _ _ _ _ _ _ _ _ _ _ _ hti hph het hd he hr hc
      have hw' : wtL L.tst'.emitted.toList ≤ termSzB B.term :=
        Nat.le_trans hw (Nat.le_of_eq (Nat.zero_add _))
      have htg' : tgL L.tst'.emitted.toList ≤ termTgB B.term :=
        Nat.le_trans htg (Nat.le_of_eq (Nat.zero_add _))
      obtain ⟨hi1, hi2⟩ := termIn_of_try het
      have hlen : T.info.handlers.length + 1 = et.dests.length := by
        rw [tryInfoOf_handlers hi, tryTargets_length htt]
      obtain ⟨f1, f2, f3⟩ := tryFix_facts T.info L.tst'.emitted.toList
      rw [hT', hi1, hi2]
      simp only [fixTry]
      refine ⟨by omega, by omega, fun m hm => ?_⟩
      obtain ⟨m', hm', he⟩ := f3 m hm
      rw [he]
      exact Nat.le_trans (regCount_le_of_mem hm' hw') hmax
  -- a raw block
  have hraw : ∀ (R : Reg → Reg), (∃ gn, VRenaming R gn) → ∀ (bi : Nat) (B : Clif.Block) (L : BLow),
      f.blocks[bi]? = some B → bl[bi]? = some L →
      vbW (mIn f) (fixBlock R (rawBlockT f ctx bl bi B)) ≤ blockIn (mIn f) bi B ∧
      tgA (fixBlock R (rawBlockT f ctx bl bi B)).insts ≤ termTgB B.term + tryDestsIn B.term ∧
      ∀ m ∈ (fixBlock R (rawBlockT f ctx bl bi B)).insts.toList, regCount m ≤ mIn f := by
    intro R ⟨gn, hR⟩ bi B L hB hL
    have hins : (fixBlock R (rawBlockT f ctx bl bi B)).insts.toList = preT f ctx R bi ++
        ((List.range B.body.length).map (segT f ctx R bl bi)).flatten ++ tseg R bl bi :=
      rawBlockT_insts ctx hR bl bi B
    obtain ⟨hpar, -, -⟩ := mIn_block (List.mem_of_getElem? hB)
    obtain ⟨p1, p2, p3⟩ := pre_factsT f ctx R hB
    obtain ⟨hsl, -, -, -⟩ := hspec bi B L hB hL
    have hsegE : ∀ j stm, B.body[j]? = some stm → ∃ sl, L.sl[j]? = some sl ∧
        segT f ctx R bl bi j = (sl.st'.emitted.toList ++ extraOfT ctx stm.results sl.rss).map (·.mapRegs R) := by
      intro j stm hj
      have hjl : j < L.sl.length := by rw [hsl]; exact (List.getElem?_eq_some_iff.mp hj).1
      exact ⟨L.sl[j], List.getElem?_eq_getElem hjl, seg_eqT hB hL hj (List.getElem?_eq_getElem hjl)⟩
    have hts : tseg R bl bi = (fixTry L.tl L.tst'.emitted.toList).map (·.mapRegs R) := by
      unfold tseg; rw [hL]
    obtain ⟨t1, t2, t3⟩ := hterm bi B L hB hL
    have s1 : ((List.range B.body.length).map (wtL ∘ segT f ctx R bl bi)).sum ≤ (B.body.map stmtIn).sum :=
      sum_range_le stmtIn B.body _ (fun j stm hj => by
        obtain ⟨sl, hsl', he⟩ := hsegE j stm hj
        show wtL (segT f ctx R bl bi j) ≤ _
        rw [he, wtL_map_mapRegs]; exact (hseg bi B L j stm sl hB hL hj hsl').1)
    have s2 : ((List.range B.body.length).map (tgL ∘ segT f ctx R bl bi)).sum ≤
        (B.body.map fun _ => 0).sum :=
      sum_range_le _ B.body _ (fun j stm hj => by
        obtain ⟨sl, hsl', he⟩ := hsegE j stm hj
        show tgL (segT f ctx R bl bi j) ≤ _
        rw [he, tgL_map_mapRegs]; exact Nat.le_of_eq (hseg bi B L j stm sl hB hL hj hsl').2.1)
    have s2' : (B.body.map fun _ => (0 : Nat)).sum = 0 := by
      clear s2; induction B.body with
      | nil => rfl
      | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ih]
    refine ⟨?_, ?_, ?_⟩
    · have hba : (fixBlock R (rawBlockT f ctx bl bi B)).branchArgs.size = jumpArgsIn B.term := by
        simp only [fixBlock, Array.size_map]; exact rawBlockT_branchArgs f ctx bl bi B
      unfold vbW blockIn
      rw [show wtA (fixBlock R (rawBlockT f ctx bl bi B)).insts =
        wtL (fixBlock R (rawBlockT f ctx bl bi B)).insts.toList from rfl, hins, wtL_append, wtL_append,
        wtL_flatten, List.map_map, hts, wtL_map_mapRegs, hba]
      omega
    · rw [show tgA (fixBlock R (rawBlockT f ctx bl bi B)).insts =
        tgL (fixBlock R (rawBlockT f ctx bl bi B)).insts.toList from rfl, hins, tgL_append, tgL_append,
        tgL_flatten, List.map_map, hts, tgL_map_mapRegs]
      omega
    · intro m hm
      rw [hins] at hm
      rcases List.mem_append.mp hm with hm | hm
      · rcases List.mem_append.mp hm with hm | hm
        · exact Nat.le_trans (p3 m hm) (Nat.max_le.mpr ⟨five_le_mIn f, hpar⟩)
        · simp only [List.mem_flatten, List.mem_map, List.mem_range] at hm
          obtain ⟨sg, ⟨j, hj, rfl⟩, hm⟩ := hm
          obtain ⟨sl, hsl', he⟩ := hsegE j B.body[j] (List.getElem?_eq_getElem hj)
          rw [he, List.mem_map] at hm
          obtain ⟨m1, hm1, rfl⟩ := hm
          rw [regCount_mapRegs]
          exact (hseg bi B L j _ sl hB hL (List.getElem?_eq_getElem hj) hsl').2.2 m1 hm1
      · rw [hts, List.mem_map] at hm
        obtain ⟨m1, hm1, rfl⟩ := hm
        rw [regCount_mapRegs]
        exact t3 m1 hm1
  -- the edge blocks of a block
  have hedge : ∀ (R : Reg → Reg) (B : Clif.Block) (L : BLow),
      ((edgeBlocksT f ctx B L).map fun e => vbW (mIn f) (fixBlock R e)).sum ≤
        ((edgeArgsIn B.term).map (edgeIn (mIn f))).sum ∧
      ((edgeBlocksT f ctx B L).map fun e => tgA (fixBlock R e).insts).sum ≤ (edgeArgsIn B.term).length := by
    intro R B L
    refine ⟨edges_leT _ _ (fun e tl he => ?_), ?_⟩
    · simp [vbW, edgeIn, fixBlock, he, wtA, wtL, MInst.mapRegs, szInstW, szWords, regCount,
        MInst.targets]
    · rw [← sum_map_one]
      exact edges_leT _ _ (fun e tl he => by simp [fixBlock, he, tgA, tgL, MInst.mapRegs, MInst.targets])
  -- `vcBlocksOf`: the raw blocks, then the edge blocks
  have hsplit : ∀ g : VBlock → Nat, (vc.blocks.toList.map g).sum =
      ((f.blocks.zip bl).zipIdx.map fun p => g (fixBlock (lowerFunction.resolve
        (aliasArr (aliasOf f bl)) ((aliasArr (aliasOf f bl)).size + 1)) (rawBlockT f ctx bl p.2 p.1.1))).sum +
      ((f.blocks.zip bl).map fun p => ((edgeBlocksT f ctx p.1 p.2).map fun e => g (fixBlock
        (lowerFunction.resolve (aliasArr (aliasOf f bl)) ((aliasArr (aliasOf f bl)).size + 1)) e)).sum).sum := by
    intro g
    rw [hvb]
    simp only [vcBlocksOfT, List.toList_toArray, List.map_append, List.sum_append, List.map_map,
      sum_map_flatMap]
    rfl
  refine ⟨maxRC_le (five_le_mIn f) (fun vb hvb' m hm => ?_), ?_, ?_⟩
  · rw [hvb] at hvb'
    obtain ⟨R, hR, ⟨bi, B, L, hB, hL, rfl⟩ | ⟨B, L, e, -, he, rfl⟩⟩ := mem_vcBlocksOfT hvb'
    · exact (hraw R hR bi B L hB hL).2.2 m hm
    · obtain ⟨tl, hi⟩ := edgeBlocksT_insts he
      simp [fixBlock, hi, MInst.mapRegs] at hm
      subst hm
      exact five_le_mIn f
  · unfold vcW vcIn
    rw [hsplit]
    refine Nat.add_le_add (sum_zipIdx_zip_le _ _ f.blocks bl 0 (fun i B L hB hL => ?_))
      (sum_zip_le _ (fun B => ((edgeArgsIn B.term).map (edgeIn (mIn f))).sum) f.blocks bl
        (fun B L _ => (hedge _ B L).1))
    simp only [Nat.zero_add]
    exact (hraw _ (resolve_vrenaming _ _) i B L hB hL).1
  · unfold vcTg
    rw [hsplit]
    have htg : tgIn f = (f.blocks.map fun B => termTgB B.term + tryDestsIn B.term).sum +
        (f.blocks.map fun B => (edgeArgsIn B.term).length).sum := by
      unfold tgIn; exact sum_map_add _ _ _
    rw [htg, ← sum_zipIdx_fst (fun B => termTgB B.term + tryDestsIn B.term) f.blocks 0]
    refine Nat.add_le_add (sum_zipIdx_zip_le _ _ f.blocks bl 0 (fun i B L hB hL => ?_))
      (sum_zip_le _ (fun B => (edgeArgsIn B.term).length) f.blocks bl
        (fun B L _ => (hedge _ B L).2))
    simp only [Nat.zero_add]
    exact (hraw _ (resolve_vrenaming _ _) i B L hB hL).2.1

/-- The spill allocation's words are within the input-side bound, given `IselSzT`. -/
theorem spillWordBound_le_sizeBoundInT {f : Clif.Function} {vc vcp : VCode} (hI : IselSzT f)
    (hx : f.externs.all (Compile.sigE ·.2.sig) = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp) :
    spillWordBound vcp ≤ sizeBoundIn f := by
  obtain ⟨hM, hW, hT⟩ := size_lowerT hI hx hl
  have h1 := spillWordBound_le vcp
  have h2 := vcW_mono (Nat.le_trans (maxRC_prepare hp) hM) vcp
  have h3 := vcW_prepare hp (mIn f)
  have h4 : jumpBW (mIn f) * vcTg vc ≤ jumpBW (mIn f) * tgIn f := Nat.mul_le_mul_left _ hT
  unfold sizeBoundIn
  omega

/-- `spillWordBound_le_sizeBoundInT` through the dead-code cleanup. -/
theorem spillWordBound_cleanup_le_sizeBoundInT {f : Clif.Function} {vc vcp : VCode}
    (hI : IselSzT f) (hx : f.externs.all (Compile.sigE ·.2.sig) = true) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare (prune vc) = .ok vcp) : spillWordBound vcp ≤ sizeBoundIn f := by
  obtain ⟨hM, hW, hT⟩ := size_lowerT hI hx hl
  obtain ⟨hMc, hWc, hTc⟩ := prune_size vc (mIn f)
  have h1 := spillWordBound_le vcp
  have h2 := vcW_mono (Nat.le_trans (maxRC_prepare hp) (Nat.le_trans hMc hM)) vcp
  have h3 := vcW_prepare hp (mIn f)
  have h4 := Nat.mul_le_mul_left (jumpBW (mIn f)) (Nat.le_trans hTc hT)
  unfold sizeBoundIn
  omega

/-- **The size bound from the input on the typed scope**: for `f` in `Dominated` and
`LowerScopeT` with class-checked float `store`s and `select`s and `sizeOkB f`, the prepared VCode
meets `spillSizeOkB` when its literal loads reach the pool (`hpool`: new with the literal pool,
#565; the typed lowering may load an `f64` constant from the pool, and a function over 1 MiB with
such a load is outside `spillSizeOkB`). -/
theorem spillSizeOkB_of_sizeOkBT {f : Clif.Function} {vc vcp : VCode}
    (hdom : dominatedB f = true) (hs : LowerScopeT f) (hst : Compile.storeTypedB f = true)
    (hsel : Compile.selectTypedB f = true) (hsz : sizeOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hpool : poolReachB vcp = true) : spillSizeOkB vcp = true := by
  have h := spillWordBound_le_sizeBoundInT (iselSzT hdom hs hst hsel) hs.externsE hl hp
  have hs : sizeBoundIn f < 2 ^ 24 := of_decide_eq_true hsz
  exact spillSizeOkB_of (by omega) hpool

/-- `spillSizeOkB_of_sizeOkBT` through the dead-code cleanup (`prepare (prune vc)`). -/
theorem spillSizeOkB_cleanup_of_sizeOkBT {f : Clif.Function} {vc vcp : VCode}
    (hdom : dominatedB f = true) (hs : LowerScopeT f) (hst : Compile.storeTypedB f = true)
    (hsel : Compile.selectTypedB f = true) (hsz : sizeOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (prune vc) = .ok vcp)
    (hpool : poolReachB vcp = true) : spillSizeOkB vcp = true := by
  have h := spillWordBound_cleanup_le_sizeBoundInT (iselSzT hdom hs hst hsel) hs.externsE hl hp
  have hs : sizeBoundIn f < 2 ^ 24 := of_decide_eq_true hsz
  exact spillSizeOkB_of (by omega) hpool

/-- `poolReachB` from the input bound below `2 ^ 17` words (1 MiB) on the typed scope. -/
theorem poolReachB_of_sizeT {f : Clif.Function} {vc vcp : VCode}
    (hdom : dominatedB f = true) (hs : LowerScopeT f) (hst : Compile.storeTypedB f = true)
    (hsel : Compile.selectTypedB f = true) (h17 : sizeBoundIn f < 2 ^ 17)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp) : poolReachB vcp = true := by
  have h := spillWordBound_le_sizeBoundInT (iselSzT hdom hs hst hsel) hs.externsE hl hp
  simp only [poolReachB, Bool.or_eq_true, decide_eq_true_eq]
  exact .inl (by omega)

end E2E

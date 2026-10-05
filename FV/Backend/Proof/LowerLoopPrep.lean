import FV.Backend.Proof.LowerLoopSim
import FV.Backend.Proof.IselTermFacts
import FV.Backend.Proof.DriverCheckSound

/-!
# The VCode of `lowerFunction` is in `PrepDomain`

The edge blocks' labels continue the block indices (`lowB_labels`), every edge block only jumps
(`edge_insts`), and a `jump` block ends in the jump rule's last instruction (`branch_last`), so the
VCode has distinct labels and branch arguments only on blocks with one successor.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Prep

theorem brEdges_labels {f : Clif.Function} : ∀ (bcs : List Clif.BlockCall) (nl : Nat) (ts : List Label)
    (nl' : Nat), edgeTargets f bcs nl = some (ts, nl') →
    (brEdges f bcs ts).map (·.label) = List.range' nl (nl' - nl) ∧ nl ≤ nl'
  | [], nl, ts, nl', h => by
    simp only [edgeTargets, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [brEdges]
  | bc :: bcs, nl, ts, nl', h => by
    simp only [edgeTargets] at h
    cases hi : blockIdx? f bc.block with
    | none => rw [hi] at h; cases h
    | some tl =>
      rw [hi] at h
      simp only at h
      split at h
      · rename_i he
        cases hr : edgeTargets f bcs nl with
        | none => rw [hr] at h; cases h
        | some r =>
          rw [hr] at h
          obtain ⟨ts', nl1⟩ := r
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2⟩ := brEdges_labels bcs nl ts' nl1 hr
          refine ⟨?_, h2⟩
          simp only [brEdges, List.zip_cons_cons, List.filterMap_cons, he, ↓reduceIte] at h1 ⊢
          exact h1
      · rename_i he
        cases hr : edgeTargets f bcs (nl + 1) with
        | none => rw [hr] at h; cases h
        | some r =>
          rw [hr] at h
          obtain ⟨ts', nl1⟩ := r
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2⟩ := brEdges_labels bcs (nl + 1) ts' nl1 hr
          refine ⟨?_, by omega⟩
          simp only [brEdges, List.zip_cons_cons, List.filterMap_cons, he, Bool.false_eq_true,
            ↓reduceIte, hi, Option.map_some, List.map_cons] at h1 ⊢
          rw [h1, show nl1 - nl = (nl1 - (nl + 1)) + 1 by omega, List.range'_succ]

theorem tryEdges_labels {f : Clif.Function} {rets pays : List Reg} :
    ∀ (ds : List Clif.TryDest) (nl : Nat), (∀ td ∈ ds, (blockIdx? f td.block).isSome) →
    (tryEdges f ds ((List.range ds.length).map (nl + ·)) rets pays).map (·.label) = List.range' nl ds.length
  | [], nl, _ => by simp [tryEdges]
  | td :: ds, nl, h => by
    obtain ⟨tl, htl⟩ := Option.isSome_iff_exists.mp (h td List.mem_cons_self)
    have ih := tryEdges_labels (rets := rets) (pays := pays) ds (nl + 1)
      fun t ht => h t (List.mem_cons_of_mem _ ht)
    rw [List.length_cons, List.range_succ_eq_map, List.range'_succ]
    simp only [tryEdges, List.map_cons, List.map_map, Nat.add_zero, List.zip_cons_cons,
      List.filterMap_cons, htl, Option.map_some] at ih ⊢
    rw [← ih]
    congr 3
    congr 1
    apply List.map_congr_left
    intro x _; show nl + (x + 1) = nl + 1 + x; omega

theorem edge_labels {f : Clif.Function} {tc : TermCallF} {yc : TryCallF} {ti : Nat} {B : Clif.Block}
    {tst : LState} {nl : Nat} {data : V} {targets : List Label} {tl : Option TryLow} {tst' : LState}
    {nl' : Nat} (h : lowTerm f tc yc ti B.term tst nl = some (data, targets, tl, tst', nl')) (L : BLow)
    (hL : L.targets = targets) (hT : L.tl = tl) :
    (edgeBlocks f B L).map (·.label) = List.range' nl (nl' - nl) ∧ nl ≤ nl' := by
  cases hti : B.term.isTry with
  | true =>
    obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := by
      cases ht : B.term <;> rw [ht] at hti <;> simp [Clif.Terminator.isTry] at hti
      · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
      · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
    obtain ⟨T, rfl, -, -, htt, -⟩ := (lowTerm_spec h).2 et het
    rw [edgeBlocks_try L het (by rw [hT]), hL]
    unfold tryTargets at htt
    split at htt
    · rename_i hall
      simp only [Option.some.injEq, Prod.mk.injEq] at htt
      obtain ⟨rfl, rfl⟩ := htt
      refine ⟨?_, by omega⟩
      rw [show nl + et.dests.length - nl = et.dests.length by omega]
      exact tryEdges_labels et.dests nl fun td htd => List.all_eq_true.mp hall td htd
    · cases htt
  | false =>
    rw [lowTerm_nontry hti] at h
    split at h
    · rename_i data0 targets0 nl0 _ htg
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
        by_cases hj : ∃ bc, B.term = .jump bc
        · obtain ⟨bc, hbc⟩ := hj
          rw [edgeBlocks_jump L hbc]
          rw [hbc] at htg
          simp only [targetsOf] at htg
          cases hi : blockIdx? f bc.block with
          | none => rw [hi] at htg; cases htg
          | some t => rw [hi] at htg; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at htg
                      obtain ⟨-, rfl⟩ := htg; simp
        · have hnj : ∀ bc, B.term ≠ .jump bc := fun bc h => hj ⟨bc, h⟩
          rw [edgeBlocks_other L hnj hti, hL]
          rw [targetsOf_other hnj] at htg
          exact brEdges_labels _ _ _ _ htg
      · cases h
    · cases h

theorem lowB_labels {f : Clif.Function} {call : StmtCall} {tcall : TermCallF} {ycall : TryCallF} :
    ∀ (Bs : List Clif.Block) (start : Nat) (st : LState) (nl : Nat) (bl : List BLow) (st' : LState)
      (nl' : Nat), lowB f call tcall ycall start Bs st nl = some (bl, st', nl') →
      ((Bs.zip bl).flatMap fun p => edgeBlocks f p.1 p.2).map (·.label) = List.range' nl (nl' - nl) ∧
        nl ≤ nl'
  | [], start, st, nl, bl, st', nl', h => by
    simp only [lowB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp
  | B :: Bs, start, st, nl, bl, st', nl', h => by
    rw [lowB_cons] at h
    split at h
    · cases h
    rename_i sls stE _
    split at h
    · rename_i data targets tl tst' nl1 hlt
      cases hr : lowB f call tcall ycall (start + B.body.length + 1) Bs { tst' with emitted := #[] } nl1 with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        obtain ⟨bl1, st1, nl2⟩ := r
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := lowB_labels Bs _ _ _ bl1 _ _ hr
        obtain ⟨e1, e2⟩ := edge_labels hlt ⟨start, sls, data, targets, { stE with emitted := #[] }, tst', tl⟩
          rfl rfl
        refine ⟨?_, by omega⟩
        simp only [List.zip_cons_cons, List.flatMap_cons, List.map_append]
        have ha := @List.range'_append nl (nl1 - nl) (nl2 - nl1) 1
        rw [show nl + 1 * (nl1 - nl) = nl1 by omega] at ha
        rw [e1, h1, ha]
        congr 1; omega
    · cases h

theorem edge_insts {f : Clif.Function} {B : Clif.Block} {L : BLow} {e : VBlock} (h : e ∈ edgeBlocks f B L) :
    ∃ tl, e.insts = #[.jump tl] := by
  unfold edgeBlocks at h
  split at h
  · simp only [List.mem_filterMap, Option.map_eq_some_iff] at h
    obtain ⟨_, _, tl, _, rfl⟩ := h; exact ⟨tl, rfl⟩
  · simp only [List.mem_filterMap, Option.map_eq_some_iff] at h
    obtain ⟨_, _, tl, _, rfl⟩ := h; exact ⟨tl, rfl⟩
  · simp at h
  · simp only [List.mem_filterMap] at h
    obtain ⟨_, _, h⟩ := h
    split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨tl, _, rfl⟩ := h; exact ⟨tl, rfl⟩

theorem targets_mapRegs' (g : Reg → Reg) (i : MInst) : (i.mapRegs g).targets = i.targets := by
  cases i <;> rfl

/-- The statements' recorded lowering only allocates fresh vregs. -/
theorem lowStmts_mono {ctx : Ctx} (ss : List Clif.Stmt) : ∀ (ii : Nat) (st : LState) (sls : List SLow)
    (stE : LState), lowStmts (stmtCall ctx) ii ss st = some (sls, stE) → st.nextVreg ≤ stE.nextVreg := by
  induction ss with
  | nil =>
    intro ii st sls stE h
    simp only [lowStmts, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact Nat.le_refl _
  | cons s ss ih =>
    intro ii st sls stE h
    rw [lowStmts_cons] at h
    split at h
    · rename_i out st' _ hrun
      split at h
      · cases hr : lowStmts (stmtCall ctx) (ii + 1) ss { st' with emitted := #[] } with
        | none => rw [hr] at h; cases h
        | some r =>
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.2]
          obtain ⟨r1, r2⟩ := r
          exact Nat.le_trans (runTerm_mono hrun).1 (ih (ii + 1) { st' with emitted := #[] } r1 r2 hr)
      · cases h
    · cases h

set_option maxRecDepth 10000 in
/-- A terminator's recorded lowering only allocates fresh vregs. -/
theorem lowTerm_mono {f : Clif.Function} {ctx : Ctx} {ti : Nat} {t : Clif.Terminator} {tst : LState}
    {nl : Nat} {data : V} {targets : List Label} {tl : Option TryLow} {tst' : LState} {nl' : Nat}
    (h : lowTerm f (termCallF ctx) (tryCallF ctx) ti t tst nl = some (data, targets, tl, tst', nl')) :
    tst.nextVreg ≤ tst'.nextVreg := by
  cases hti : t.isTry with
  | false =>
    obtain ⟨-, -, out, tr, hrun⟩ := (lowTerm_spec h).1 hti
    exact (runTerm_mono hrun).1
  | true =>
    obtain ⟨et, het⟩ : ∃ et, IsTryWith t et := by
      cases t <;> simp [Clif.Terminator.isTry] at hti
      · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
      · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
    obtain ⟨T, -, -, -, -, htr, -, out, tr, hrun⟩ := (lowTerm_spec h).2 et het
    have h1 := (tryRegsOf_mono htr).1
    have h2 := (runTerm_mono hrun).1
    simp only at h2
    omega

theorem lowB_mono {f : Clif.Function} {ctx : Ctx} :
    ∀ (Bs : List Clif.Block) (start : Nat) (st : LState) (nl : Nat) (bl : List BLow) (st' : LState)
      (nl' : Nat), lowB f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) start Bs st nl = some (bl, st', nl') →
      ∀ (bi : Nat) (L : BLow), bl[bi]? = some L → st.nextVreg ≤ L.tst.nextVreg
  | [], start, st, nl, bl, st', nl', h => by
    simp only [lowB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    intro bi L h; simp at h
  | B :: Bs, start, st, nl, bl, st', nl', h => by
    rw [lowB_cons] at h
    split at h
    · cases h
    rename_i sls stE hs
    split at h
    · rename_i data targets tl tst' nl1 hlt
      cases hr : lowB f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) (start + B.body.length + 1) Bs
          { tst' with emitted := #[] } nl1 with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        obtain ⟨bl1, st1, nl2⟩ := r
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -, -⟩ := h
        have m1 := lowStmts_mono _ _ _ _ _ hs
        have m2 := lowTerm_mono hlt
        have ih := lowB_mono Bs _ _ _ bl1 _ _ hr
        intro bi L hL
        cases bi with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hL
          subst hL; exact m1
        | succ bi =>
          simp only [List.getElem?_cons_succ] at hL
          have := ih bi L hL
          simp only at this m2
          omega
    · cases h

theorem bsl_lt : ∀ {Bs : List Clif.Block} {b : Nat} {B : Clif.Block}, Bs[b]? = some B →
    bsl Bs b + B.body.length < bsl Bs Bs.length
  | [], _, _, h => by simp at h
  | B' :: Bs, 0, B, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [bsl_zero, List.length_cons, bsl_cons]; omega
  | B' :: Bs, b + 1, B, h => by
    simp only [List.getElem?_cons_succ] at h
    rw [List.length_cons, bsl_cons, bsl_cons]
    have := bsl_lt h; omega

/-- The targets of a `jump`'s lowering. -/
theorem jump_targets {f : Clif.Function} {tc : TermCallF} {yc : TryCallF} {ti : Nat} {t : Clif.Terminator}
    {bc : Clif.BlockCall} (ht : t = .jump bc) {tst : LState} {nl : Nat} {data : V}
    {targets : List Label} {tl : Option TryLow} {tst' : LState} {nl' : Nat}
    (h : lowTerm f tc yc ti t tst nl = some (data, targets, tl, tst', nl')) :
    ∃ l, targets = [l] := by
  subst ht
  rw [lowTerm_nontry rfl] at h
  split at h
  · rename_i data0 targets0 nl0 _ htg
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      simp only [targetsOf] at htg
      cases hi : blockIdx? f bc.block with
      | none => rw [hi] at htg; cases htg
      | some l =>
        rw [hi] at htg
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at htg
        exact ⟨l, htg.1.symm⟩
    · cases h
  · cases h

/-- `lowBlocks`' block starts, from any first instruction index. -/
theorem lowBlocks_start_gen {f : Clif.Function} {call : StmtCall} {tcall : TermCallF} {ycall : TryCallF} :
    ∀ (Bs : List Clif.Block) (start : Nat) (st : LState) (nl : Nat) (bl : List BLow),
      lowBlocks f call tcall ycall start Bs st nl = some bl →
      bl.length = Bs.length ∧ ∀ bi L, bl[bi]? = some L → L.start = start + bsl Bs bi
  | [], start, st, nl, bl, h => by
    simp only [lowBlocks, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun bi L h => by simp at h⟩
  | B :: Bs, start, st, nl, bl, h => by
    simp only [lowBlocks] at h
    split at h
    · cases h
    rename_i sls stE _
    split at h
    · rename_i data targets tl tst' nl' _
      cases hr : lowBlocks f call tcall ycall (start + B.body.length + 1) Bs { tst' with emitted := #[] } nl'
        with
      | none => rw [hr] at h; cases h
      | some bl' =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := lowBlocks_start_gen Bs _ _ _ bl' hr
        refine ⟨by simp [h1], fun bi L hL => ?_⟩
        cases bi with
        | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hL; subst hL; simp [bsl_zero]
        | succ bi =>
          simp only [List.getElem?_cons_succ] at hL
          rw [h2 bi L hL, bsl_cons]; omega
    · cases h

/-- **V2**: `lowerFunction`'s VCode is in `PrepDomain` (on in-scope input). -/
theorem prepDomain_of {f : Clif.Function} {vc : VCode} (hs : LowerScope f) (h : lowerFunction f = .ok vc) :
    PrepDomain vc := by
  obtain ⟨ctx, ranges, st0, pb, d, bl, hb, hpb, hI, rfl⟩ := loop_run h
  have sp := ctxSpec_of hb
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_of hs hb)
  have hlow := hI.low
  rw [List.take_of_length_le (Nat.le_refl _)] at hlow
  have hbl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
      some bl := by rw [lowBlocks_eq, hlow]; rfl
  have hspec := (lowBlocks_spec hbl).2
  obtain ⟨-, hstart⟩ := lowBlocks_start_gen f.blocks 0 st0 _ bl hbl
  have hlen : (f.blocks.zip bl).length = f.blocks.length := by simp [hI.len]
  have hnb : 0 < f.blocks.length := List.length_pos_iff.mpr hs.nonempty
  obtain ⟨hlab, -⟩ := lowB_labels _ _ _ _ _ _ _ hlow
  -- the blocks, as a list
  have hvb : (finishVC f d (slotLayout f.slots).2).blocks.toList =
      (((f.blocks.zip bl).zipIdx.map fun p => rawBlock f bl p.2 p.1.1) ++
        (f.blocks.zip bl).flatMap fun p => edgeBlocks f p.1 p.2).map
        (fixBlock (lowerFunction.resolve d.alias (d.alias.size + 1))) := by
    simp [finishVC, hI.blocks, hI.edges]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← Array.length_toList, hvb]; simp [hlen]; omega
  · unfold Lbls
    rw [hvb, List.map_map]
    have e1 : (VBlock.label ∘ fixBlock (lowerFunction.resolve d.alias (d.alias.size + 1))) =
      VBlock.label := rfl
    rw [e1, List.map_append, List.map_map]
    have e2 : (VBlock.label ∘ fun p : (Clif.Block × BLow) × Nat => rawBlock f bl p.2 p.1.1) = Prod.snd := rfl
    rw [e2, List.zipIdx_map_snd, hlab, hlen]
    have := @List.range'_append 0 f.blocks.length (d.nextLabel - f.blocks.length) 1
    simp only [Nat.zero_add, Nat.one_mul] at this
    rw [this]
    exact List.nodup_range'
  · intro b vb t hvb' hback h2
    rw [← Array.getElem?_toList, hvb, List.getElem?_map] at hvb'
    by_cases hb' : b < f.blocks.length
    · rw [List.getElem?_append_left (by simp [hlen, hb'])] at hvb'
      rw [List.getElem?_map, List.getElem?_zipIdx] at hvb'
      obtain ⟨B, hB⟩ : ∃ B, f.blocks[b]? = some B := ⟨_, List.getElem?_eq_getElem hb'⟩
      obtain ⟨L, hL⟩ : ∃ L, bl[b]? = some L := ⟨_, List.getElem?_eq_getElem (by rw [hI.len]; exact hb')⟩
      have hz : (f.blocks.zip bl)[b]? = some (B, L) := List.getElem?_zip_eq_some.mpr ⟨hB, hL⟩
      rw [hz] at hvb'
      simp only [Option.map_some, Option.some.injEq, Nat.zero_add] at hvb'
      subst hvb'
      simp only [fixBlock, rawBlock]
      cases ht : B.term with
      | jump bc =>
        exfalso
        obtain ⟨-, -, hem, nl0, nl1, hlt⟩ := hspec b B L hB hL
        have hlt' := hlt
        rw [ht] at hlt'
        obtain ⟨l, hl⟩ := jump_targets rfl hlt'
        obtain ⟨htl, hd, out, tr, hrun⟩ := (lowTerm_spec hlt).1 (by rw [ht]; rfl)
        have hst : L.start = blockStart f b := by rw [hstart b L hL, Nat.zero_add]; rfl
        have hti : L.start + B.body.length < ctx.insts.size := by
          rw [sp.facts.insts, hst, blockStart_eq, blockStart_eq]; exact bsl_lt hB
        have hph := sp.facts.term b B hB
        rw [← hst] at hph
        have hval : ValsBelow ctx L.tst := by
          intro x r hx
          have h1 : x < ctx.valReg.size := by
            simp only [Ctx.valueReg?] at hx
            cases hh : ctx.valReg[x]? with
            | none => rw [hh] at hx; cases hx
            | some _ => exact (Array.getElem?_eq_some_iff.mp hh).1
          have h2 := sp.facts.size
          have h3 := lowB_mono _ _ _ _ _ _ _ hlow b L hL
          omega
        have hem' := term_emits hctx hti (by simpa [placeholder] using hph) (t := B.term) (by rw [ht]; rfl) hd
          (by intro x d tbl h; rw [ht] at h; cases h) hval (by intro x d tbl h; rw [ht] at h; cases h) hrun
        rw [hem] at hem'
        simp only [List.size_toArray, List.length_nil] at hem'
        obtain ⟨i, hi⟩ : ∃ i, L.tst'.emitted.back? = some i := by
          cases hh : L.tst'.emitted.back? with
          | none => rw [Array.back?_eq_none_iff] at hh; rw [hh] at hem'; simp at hem'
          | some i => exact ⟨i, rfl⟩
        have hit := branch_last hctx hti (by simpa [placeholder] using hph) (t := B.term) (by rw [ht]; rfl)
          (by intro vs h; rw [ht] at h; cases h) (by intro c h; rw [ht] at h; cases h) hd
          (by intro x d tbl h; rw [ht] at h; cases h) hval (by intro x d tbl h; rw [ht] at h; cases h) hrun
          i hi (by rw [hem]; simpa using hem')
        simp only [fixBlock, rawBlock, tseg, hL, htl, fixTry, map_mapRegs_id] at hback
        rw [Array.back?_map] at hback
        have hlast : (pre f id b ++ ((List.range B.body.length).map (seg f id bl b)).flatten ++
            L.tst'.emitted.toList).toArray.back? = some i := by
          rw [List.back?_toArray, List.getLast?_append, back_toList, hi]; rfl
        rw [hlast] at hback
        simp only [Option.map_some, Option.some.injEq] at hback
        rw [← hback, targets_mapRegs', hit, hl] at h2
        simp at h2
      | _ => simp [ht]
    · exfalso
      rw [List.getElem?_append_right (by simp [hlen]; omega)] at hvb'
      cases hh : ((f.blocks.zip bl).flatMap fun p => edgeBlocks f p.1 p.2)[b - ((f.blocks.zip bl).zipIdx.map
          fun p => rawBlock f bl p.2 p.1.1).length]? with
      | none => rw [hh] at hvb'; cases hvb'
      | some e =>
        rw [hh] at hvb'
        simp only [Option.map_some, Option.some.injEq] at hvb'
        subst hvb'
        have hm := List.mem_of_getElem? hh
        simp only [List.mem_flatMap] at hm
        obtain ⟨p, -, he⟩ := hm
        obtain ⟨tl, htl⟩ := edge_insts he
        simp [fixBlock, htl, MInst.mapRegs] at hback
        rw [← hback] at h2
        simp [MInst.targets] at h2

end Backend.Proof.Driver

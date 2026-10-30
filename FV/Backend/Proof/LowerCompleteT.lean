import FV.Backend.Proof.LowerComplete
import FV.Backend.Proof.LowerCertT
import FV.Backend.Proof.LowerShapeOkT
import FV.Backend.Proof.IselTermFactsCallT

/-!
# Completeness of the typed lowering validator (S11e5 Stage C)

`lowerCheckT_complete`: on input in `Dominated` and the typed scope `LowerScopeT` (floats
included), `lowerCheckT` accepts every output of `lowerFunction`. The parts are typed versions
of `lowerCheck_complete`'s: the shape (`shapeOkT_completeT`), the SSA certificate
(`certOk_completeT`, aliases by `alias_factsT`), the `tryCall`/`ElfTlsGetAddr` flags over the
typed model (`vcBlocksT_all`, `stmt_noTlsT`, `termCall_noTlsT`, `tryCall_noTlsT`), the outgoing
area (`callOut_runTermT`, `tryOut_runTermT`) and the entry's parameter locations in x0..x8 or
v0..v7 (`entryOkBT_of`, from `sigArgLocs_shape`). `lowerCheck_complete` is unchanged; on the
integer scope `lowerCheckT_complete_int` gives `lowerCheckT` from it via `LowerScope.toT`.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## The entry's parameter locations -/

/-- `entryOkBT` holds when the parameter locations and byte sizes compute (any parameter
classes: `sigArgLocs` places them in x0..x8, v0..v7 or on the stack). -/
theorem entryOkBT_of {f : Clif.Function} {locs : List ArgLoc} {n : Nat} {bytes : List Nat}
    (hl : sigArgLocs f.sig = .ok (locs, n)) (hb : sigParamBytes f.sig = .ok bytes) :
    entryOkBT f = true := by
  have hlocs : locsOf f.sig = locs := by simp [locsOf, hl]
  obtain ⟨hlen, hok⟩ := sigArgLocs_shape hl
  simp only [entryOkBT, hlocs, hlen, beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
    List.all_eq_true, hb]
  refine ⟨fun l hm => ?_, trivial⟩
  match l, hok l hm with
  | .stack _, _ => rfl
  | .reg r, h =>
    rcases h with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · simpa using hk
    · simp; omega

/-! ## The typed VCode's instructions -/

/-- The blocks of `vcBlocksOfT`: a renamed typed raw block or a renamed typed edge block. -/
theorem mem_vcBlocksOfT {f : Clif.Function} {ctx : Ctx} {bl : List BLow} {vb : VBlock}
    (h : vb ∈ (vcBlocksOfT f ctx bl).toList) :
    ∃ R, (∃ gn, VRenaming R gn) ∧
      ((∃ bi B L, f.blocks[bi]? = some B ∧ bl[bi]? = some L ∧
        vb = fixBlock R (rawBlockT f ctx bl bi B)) ∨
      (∃ B L e, B ∈ f.blocks ∧ e ∈ edgeBlocksT f ctx B L ∧ vb = fixBlock R e)) := by
  simp only [vcBlocksOfT, List.toList_toArray, List.mem_map, List.mem_append, List.mem_flatMap] at h
  obtain ⟨vb0, h1, rfl⟩ := h
  refine ⟨lowerFunction.resolve (aliasArr (aliasOf f bl)) ((aliasArr (aliasOf f bl)).size + 1),
    resolve_vrenaming _ _, ?_⟩
  rcases h1 with ⟨p, hp, rfl⟩ | ⟨p, hp, he⟩
  · have := List.mem_zipIdx_iff_getElem?.mp hp
    rw [List.getElem?_zip_eq_some] at this
    exact .inl ⟨p.2, p.1.1, p.1.2, this.1, this.2, rfl⟩
  · exact .inr ⟨p.1, p.2, vb0, (List.of_mem_zip hp).1, he, rfl⟩

/-- `extraOfT`'s instructions are `mov`s. -/
theorem mem_extraOfT {ctx : Ctx} {results : List Nat} {rss : List (List Reg)} {m : MInst}
    (h : m ∈ extraOfT ctx results rss) : ∃ s a b, m = .mov s a b := by
  simp only [extraOfT, List.mem_filterMap] at h
  obtain ⟨q, -, hq⟩ := h
  split at hq
  · cases hq
  · cases hq; exact ⟨_, _, _, rfl⟩
  · cases hq

/-- A typed edge block is a single `jump`. -/
theorem edgeBlocksT_insts {f : Clif.Function} {ctx : Ctx} {B : Clif.Block} {L : BLow} {e : VBlock}
    (h : e ∈ edgeBlocksT f ctx B L) : ∃ tl, e.insts = #[.jump tl] := by
  unfold edgeBlocksT at h
  split at h
  · simp only [List.mem_filterMap, Option.map_eq_some_iff] at h
    obtain ⟨_, -, tl, -, rfl⟩ := h; exact ⟨tl, rfl⟩
  · simp only [List.mem_filterMap, Option.map_eq_some_iff] at h
    obtain ⟨_, -, tl, -, rfl⟩ := h; exact ⟨tl, rfl⟩
  · simp at h
  · simp only [List.mem_filterMap] at h
    obtain ⟨_, -, h⟩ := h
    split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨tl, -, rfl⟩ := h; exact ⟨tl, rfl⟩

/-- `vcBlocks_all` over the typed model: a property every vreg renaming keeps, which the
driver's own instructions (`args`, the parameter loads `stackArgLoad`, result `mov`s, `jump`s)
have, holds of every instruction of `vcBlocksOfT f ctx bl` if it holds of every statement's and
terminator's emitted code. -/
theorem vcBlocksT_all (P : MInst → Prop)
    (hR : ∀ R gn, VRenaming R gn → ∀ m, P m → P (m.mapRegs R))
    (hargs : ∀ ds, P (.args ds)) (hload : ∀ r b am, P (stackArgLoad r b am))
    (hmov : ∀ s a b, P (.mov s a b)) (hjump : ∀ l, P (.jump l))
    {f : Clif.Function} {ctx : Ctx} {bl : List BLow}
    (hs : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
      f.blocks[bi]? = some B → bl[bi]? = some L → B.body[j]? = some stm →
      L.sl[j]? = some sl → ∀ m ∈ sl.st'.emitted.toList, P m)
    (ht : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
      ∀ m ∈ fixTry L.tl L.tst'.emitted.toList, P m) :
    ∀ vb ∈ (vcBlocksOfT f ctx bl).toList, ∀ m ∈ vb.insts.toList, P m := by
  intro vb hvb m hm
  obtain ⟨R, ⟨gn, hRg⟩, ⟨bi, B, L, hB, hL, rfl⟩ | ⟨B, L, e, -, he, rfl⟩⟩ := mem_vcBlocksOfT hvb
  · simp only [fixBlock, rawBlockT, Array.toList_map, List.mem_map, List.mem_append,
      List.mem_flatten] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    apply hR R gn hRg
    rcases hm0 with (hpre | ⟨sg, hsg, hm0⟩) | htseg
    · unfold preT at hpre
      split at hpre
      · simp only [List.mem_cons] at hpre
        rcases hpre with rfl | hpre
        · exact hargs _
        · simp only [entryLoadsT, List.mem_filterMap] at hpre
          obtain ⟨q, -, hq⟩ := hpre
          unfold entryLoadOfT at hq
          split at hq
          · cases hq; exact hload _ _ _
          · cases hq
      · simp at hpre
    · simp only [List.mem_range] at hsg
      obtain ⟨j, -, rfl⟩ := hsg
      unfold segT at hm0
      rw [hB, hL] at hm0
      simp only at hm0
      split at hm0
      · rename_i stm sl hstm hsl
        simp only [List.mem_map] at hm0
        obtain ⟨m1, hm1, rfl⟩ := hm0
        refine hR id id vrenaming_id _ ?_
        rcases List.mem_append.mp hm1 with hm1 | hm1
        · exact hs bi B L j stm sl hB hL hstm hsl m1 hm1
        · obtain ⟨s, a, b, rfl⟩ := mem_extraOfT hm1
          exact hmov s a b
      · simp at hm0
    · unfold tseg at htseg
      rw [hL] at htseg
      simp only [List.mem_map] at htseg
      obtain ⟨m1, hm1, rfl⟩ := htseg
      exact hR id id vrenaming_id _ (ht bi B L hB hL m1 hm1)
  · obtain ⟨tl, hi⟩ := edgeBlocksT_insts he
    simp only [fixBlock, hi, Array.toList_map, List.mem_map] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    simp at hm0
    subst hm0
    exact hR R gn hRg _ (hjump tl)

theorem notTry_stackArgLoad (r : Reg) (b : Nat) (am : AMode) :
    ∀ c ti, stackArgLoad r b am ≠ .tryCall c ti := by
  intro c ti h; unfold stackArgLoad at h; split at h <;> cases h

theorem notTls_stackArgLoad (r : Reg) (b : Nat) (am : AMode) :
    ∀ s rd tmp, stackArgLoad r b am ≠ .elfTlsGetAddr s rd tmp := by
  intro s rd tmp h; unfold stackArgLoad at h; split at h <;> cases h

/-! ## Completeness -/

/-- **The parts of the typed lowering validators, float scope.** On input satisfying `Dominated`
and the float scope `LowerScopeTF`, `lowerFunction`'s run passes every conjunct of
`lowerCheckT`, with a supported-instruction check `sc` that holds on `buildCtx`'s context in
place of `instScopeOk` (`lowerCheckT_complete`: `instScopeOk`; `lowerCheckTCF_complete`:
`instScopeOkF`). -/
theorem lowerCheck_partsTF {f : Clif.Function} {vc : VCode} (hd : Dominated f)
    (hs : LowerScopeTF f) (h : lowerFunction f = .ok vc) {sc : Ctx → Bool}
    (hsc : ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) → sc ctx = true) :
    ∃ ctx ranges st0 bl, buildCtx f = .ok (ctx, ranges, st0) ∧
      lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length = some bl ∧
      (shapeOkTS (sc ctx) f vc ctx st0 (gnAt (gnTable st0.nextVreg (aliasOf f bl))) bl &&
        certOk f ctx st0 (gnAt (gnTable st0.nextVreg (aliasOf f bl))) bl
          (inFix f ctx (gnAt (gnTable st0.nextVreg (aliasOf f bl)))) && brIdxOk f ctx &&
        ((f.blocks.any (·.term.isTry) || !vc.hasTryCall) && (hasTls f || !vc.hasTls)) &&
        (callsStackOkB f vc.outgoing && entryOkBT f)) = true := by
  obtain ⟨ctx, ranges, st0, bl, hb, hl, hvb, hout, hlf⟩ := lowerFunction_runT hs.externsE h
  obtain ⟨hu, -, hwf⟩ := alias_factsTF hd hs hb hl
  have hctx : CtxInvT f ctx := ctxInvT_ofF hs hb
  have hnm : LowerNoMatch ctx := fun _ _ _ hi hc _ hr hroot =>
    lower_nonroot_nomatchTF_calls hctx ((ctxSpec_of hb).instScopeTF hs.subsetTF)
      (callsE_of_externs hs.externsE ctx) hi hc hr hroot
  have hcf := ctxFacts_of hb
  obtain ⟨hlen, hstart⟩ := lowBlocks_start hl
  obtain ⟨-, hspec⟩ := lowBlocks_spec hl
  have hemp := lowBlocks_emptied hl
  obtain ⟨-, hlo⟩ := lowBlocks_out (outMono_driver ctx) hl
  -- the statements' runs
  have hstm : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
      f.blocks[bi]? = some B → bl[bi]? = some L →
      B.body[j]? = some stm → L.sl[j]? = some sl →
      (∃ info, ctx.insts[L.start + j]? = some info ∧ info.clif = some stm.inst) ∧
      ∃ tr, runTerm ctx "lower" [.inst (L.start + j)] sl.st =
        .ok (some (.regsVec sl.rss), sl.st', tr) := by
    intro bi B L j stm sl hB hL hj hsl
    obtain ⟨-, hc, -, -⟩ := hspec bi B L hB hL
    obtain ⟨info, hi, hic, -⟩ := hcf.stmt bi B j stm hB hj
    rw [hstart bi L hL]
    exact ⟨⟨info, hi, hic⟩, by rw [← hstart bi L hL]; exact hc j sl hsl⟩
  refine ⟨ctx, ranges, st0, bl, hb, hl, ?_⟩
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨⟨shapeOkTS_completeI h hs hd.ssa hb (termEmitsTI_of_ctxInvT hctx) hl hu hwf
    (hsc ctx ranges st0 hb), certOk_completeTF hd hs hb hl⟩,
    (hs.ctxFacts ctx ranges st0 hb).1⟩, ?_, ?_⟩, ?_, ?_⟩
  · -- a `tryCall` only for a function with a `try_call`
    by_cases hT : (f.blocks.any fun x => x.term.isTry) = true
    · exact .inl hT
    · right
      have hnt : ∀ B ∈ f.blocks, B.term.isTry = false := by
        intro B hB
        simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hT
        exact hT B hB
      have hall := vcBlocksT_all (fun m => ∀ c ti, m ≠ .tryCall c ti)
        (fun R _ _ => notTry_mapRegs R)
        (fun _ _ _ h => nomatch h) notTry_stackArgLoad (fun _ _ _ _ _ h => nomatch h)
        (fun _ _ _ h => nomatch h) (f := f) (ctx := ctx) (bl := bl)
        (fun bi B L j stm sl hB hL hj hsl => by
          obtain ⟨-, tr, hrun⟩ := hstm bi B L j stm sl hB hL hj hsl
          exact emitted_of_run hrun (hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)))
        (fun bi B L hB hL => by
          obtain ⟨-, -, htst, nl0, nl', hterm⟩ := hspec bi B L hB hL
          obtain ⟨hn, -⟩ := lowTerm_spec hterm
          obtain ⟨htl, -, out, tr, hc⟩ := hn (hnt B (List.mem_of_getElem? hB))
          rw [htl]
          exact emitted_of_run hc htst)
      rw [VCode.hasTryCall, hvb, Bool.eq_false_iff]
      intro hc
      rw [← Array.any_toList, List.any_eq_true] at hc
      obtain ⟨vb, hvb', hi⟩ := hc
      rw [← Array.any_toList, List.any_eq_true] at hi
      obtain ⟨m, hm, hmt⟩ := hi
      have := hall vb hvb' m hm
      cases m <;> simp at hmt
      exact this _ _ rfl
  · -- an `ElfTlsGetAddr` only for a function with a `tls_value`
    by_cases hT : hasTls f = true
    · exact .inl hT
    · right
      have hnt : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ ty gv, st.inst ≠ .tlsValue ty gv := by
        intro B hB st hst ty gv he
        apply hT
        simp only [hasTls, List.any_eq_true]
        exact ⟨B, hB, st, hst, by rw [he]⟩
      have hall := vcBlocksT_all (fun m => ∀ s rd tmp, m ≠ .elfTlsGetAddr s rd tmp)
        (fun R _ _ => notTls_mapRegs R)
        (fun _ _ _ _ h => nomatch h) notTls_stackArgLoad (fun _ _ _ _ _ _ h => nomatch h)
        (fun _ _ _ _ h => nomatch h) (f := f) (ctx := ctx) (bl := bl)
        (fun bi B L j stm sl hB hL hj hsl => by
          obtain ⟨⟨info, hi, hic⟩, tr, hrun⟩ := hstm bi B L j stm sl hB hL hj hsl
          obtain ⟨ms, hms, hno⟩ := stmt_noTlsG hctx hnm hi hic
            (hnt B (List.mem_of_getElem? hB) stm (List.mem_of_getElem? hj)) hrun
          rw [hms, hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)]
          simpa using hno)
        (fun bi B L hB hL => by
          obtain ⟨-, -, htst, nl0, nl', hterm⟩ := hspec bi B L hB hL
          obtain ⟨hn, hy⟩ := lowTerm_spec hterm
          have hti : L.start + B.body.length < ctx.insts.size := by
            have := hcf.term bi B hB
            rw [← hstart bi L hL] at this
            exact (Array.getElem?_eq_some_iff.mp this).1
          intro m hm
          rcases mem_fixTry hm with hm | ⟨c, ti, rfl⟩
          · cases ht : B.term.isTry with
            | false =>
              obtain ⟨-, hd, out, tr, hc⟩ := hn ht
              obtain ⟨ms, hms, hno⟩ := termCall_noTlsT hctx hti hd hc
              rw [hms, htst] at hm
              exact hno m (by simpa using hm)
            | true =>
              obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := by
                cases hB' : B.term <;> rw [hB'] at ht <;> simp [Clif.Terminator.isTry] at ht
                · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
                · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
              obtain ⟨T, -, hd, -, -, -, -, out, tr, hc⟩ := hy et het
              obtain ⟨ms, hms, hno⟩ := tryCall_noTlsT hctx hti hd hc
              rw [hms] at hm
              exact hno m (by simpa using hm)
          · intro s rd tmp h; cases h)
      rw [VCode.hasTls, hvb, Bool.eq_false_iff]
      intro hc
      rw [← Array.any_toList, List.any_eq_true] at hc
      obtain ⟨vb, hvb', hi⟩ := hc
      rw [← Array.any_toList, List.any_eq_true] at hi
      obtain ⟨m, hm, hmt⟩ := hi
      have := hall vb hvb' m hm
      cases m <;> simp at hmt
      exact this _ _ _ rfl
  · -- the outgoing area holds every call's stack arguments
    have hfin : (bl.getLast?.map (·.tst'.outgoing)).getD st0.outgoing = vc.outgoing := by
      rw [hout]; rfl
    have hL : ∀ B ∈ f.blocks, ∃ (bi : Nat) (L : BLow), f.blocks[bi]? = some B ∧ bl[bi]? = some L := by
      intro B hB
      obtain ⟨bi, hbi⟩ := List.mem_iff_getElem?.mp hB
      have : bi < bl.length := by rw [hlen]; exact lt_of_getElem? hbi
      exact ⟨bi, _, hbi, List.getElem?_eq_getElem this⟩
    simp only [callsStackOkB, Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun B hB st hst => ?_, fun B hB => ?_⟩
    · obtain ⟨bi, L, hB', hL'⟩ := hL B hB
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hst
      obtain ⟨hsll, -⟩ := hspec bi B L hB' hL'
      obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl :=
        ⟨_, List.getElem?_eq_getElem (by rw [hsll]; exact lt_of_getElem? hj)⟩
      obtain ⟨⟨info, hi, hic⟩, tr, hrun⟩ := hstm bi B L j st sl hB' hL' hj hsl
      split
      · rename_i fn args hcall
        split
        · rename_i e he
          rw [hcall] at hic
          have h1 := callOut_runTermT hctx hi hic he hrun
          have h2 := (hlo L (List.mem_of_getElem? hL')).1 sl (List.mem_of_getElem? hsl)
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨by rw [← hfin]; omega, hs.stackLayout.1 B hB st hst fn args e hcall he⟩
        · rfl
      · rfl
    · obtain ⟨bi, L, hB', hL'⟩ := hL B hB
      split
      · rename_i fn args et ht
        split
        · rename_i e he
          obtain ⟨-, -, -, nl0, nl', hterm⟩ := hspec bi B L hB' hL'
          obtain ⟨-, hy⟩ := lowTerm_spec hterm
          obtain ⟨T, -, hd, -, -, -, -, out, tr, hc⟩ := hy et (.inl ⟨fn, args, ht⟩)
          have hti : L.start + B.body.length < ctx.insts.size := by
            have := hcf.term bi B hB'
            rw [← hstart bi L hL'] at this
            exact (Array.getElem?_eq_some_iff.mp this).1
          rw [ht] at hd
          have hip := termIntPos_ofF hs hb hB
          rw [ht] at hip
          have hlt : ctx.insts[L.start + B.body.length]? = some ctx.insts[L.start + B.body.length] :=
            Array.getElem?_eq_getElem hti
          have h1 := tryOut_runTermT (ctx := tryCtx ctx _ _ T.regs)
            ⟨hctx.func, fun x r h hx => hctx.valueReg_int h hx⟩
            (fun x hx => hip x (by simpa [Compile.termIntOperands] using hx)) hd
            (termCtx_insts_self hlt _) he hc
          have h2 := (hlo L (List.mem_of_getElem? hL')).2
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨by rw [← hfin]; omega, hs.stackLayout.2 B hB fn args et e ht he⟩
        · rfl
      · rfl
  · -- the entry's parameter locations
    obtain ⟨locs, n, hloc⟩ := hlf.entry hs.nonempty
    obtain ⟨bytes, hby⟩ := hlf.paramBytes
    exact entryOkBT_of hloc hby

/-- **Completeness of the typed lowering validator.** On input satisfying `Dominated` and the
typed scope `LowerScopeT` (floats included), `lowerCheckT` accepts `lowerFunction`'s output. -/
theorem lowerCheckT_complete {f : Clif.Function} {vc : VCode} (hd : Dominated f)
    (hs : LowerScopeT f) (h : lowerFunction f = .ok vc) : lowerCheckT f vc = true := by
  obtain ⟨ctx, ranges, st0, bl, hb, hl, hok⟩ := lowerCheck_partsTF hd hs.toTF h
    (sc := instScopeOk) fun _ _ _ hb => instScopeOk_complete ((ctxSpec_of hb).instScopeT hs.subsetT)
  unfold lowerCheckT
  rw [hb]; simp only; rw [hl]
  exact hok

/-- **Integer specialization**: on the integer scope `lowerCheckT` accepts `lowerFunction`'s
output (`lowerCheckT_complete` over `LowerScope.toT`). -/
theorem lowerCheckT_complete_int {f : Clif.Function} {vc : VCode} (hd : Dominated f)
    (hs : LowerScope f) (h : lowerFunction f = .ok vc) : lowerCheckT f vc = true :=
  lowerCheckT_complete hd hs.toT h

end Backend.Proof.Driver

import FV.E2E.SpillCtlCheck
import FV.E2E.LinkScopeInputDefsT
import FV.E2E.EmitTotalT
import FV.Backend.Proof.SpillCtlPipeT
import FV.Backend.Proof.SpillEdgesT

/-!
# The instruction part of `ctlCheck` on the typed pipeline's output (S11 #35)

`ctlInsts_pipelineT`: `ctlInsts_pipeline` (`SpillCtlCheck`) for the typed lowering, given the
typed ISLE inversion `IselCtlHypT`: every instruction of `prepare (lowerFunction f)` meets
`ctlInstOk` at its position, and block 0 starts with an `Args` and has at least two
instructions. The typed shapes' `Rets` pairs a float vreg with v0..v7 (`retPairOk`); the entry
`Args` pairs each parameter's vreg with a register of its class (`argPairOk`, from
`EntryClassOk`: `entryParams_factsT`, `entryDC_argRegC`). `ctlInstsB_of`: completeness of
`ctlInstsB`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill

/-- An `Args` whose pairs are class-compatible (`argPairOk`). -/
def ArgsOkT (i : MInst) : Prop :=
  ∃ ds, i = .args ds ∧ ds.all argPairOk = true

/-- A renamed typed control shape meets `ctlInstOk`. -/
theorem ctlNA_shapeT {R : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming R gn) {N : Nat} {m : MInst}
    (h : CtlShapeT N m) : CtlNA (m.mapRegs R) := by
  rcases h with h | ⟨ns, rfl, hr, -⟩
  · exact ctlNA_shape hg h
  · refine ⟨fun ds e => (by simp [MInst.mapRegs] at e), fun b k => ?_⟩
    simp only [MInst.mapRegs, ctlInstOk, argPairsC, List.map_map, List.all_map,
      List.all_eq_true, Function.comp_def]
    intro q hq
    rcases hr q hq with ⟨hc, k', hk, he⟩ | ⟨hc, k', hk, he⟩
    · simp [hc, he, hg.vreg, argPairOk, Reg.isVregInt, Reg.isArgReg] <;> omega
    · simp [hc, he, hg.vreg, argPairOk, Reg.isVregInt, Reg.isVregFloat, Reg.isFpArgReg, hk]

/-- Block `b` of `vcBlocksOfT`: the raw block `b`, or an edge block (then `0 < b`). -/
theorem vcBlocksOfT_get {f : Clif.Function} {ctx : Ctx} {bl : List BLow} {b : Nat} {vb : VBlock}
    (h : (vcBlocksOfT f ctx bl)[b]? = some vb) :
    (∃ B L, f.blocks[b]? = some B ∧ bl[b]? = some L ∧
      vb = fixBlock (lowerFunction.resolve (aliasArr (aliasOf f bl)) ((aliasArr (aliasOf f bl)).size + 1))
        (rawBlockT f ctx bl b B)) ∨
    (0 < b ∧ ∃ B L e, e ∈ edgeBlocksT f ctx B L ∧
      vb = fixBlock (lowerFunction.resolve (aliasArr (aliasOf f bl)) ((aliasArr (aliasOf f bl)).size + 1)) e) := by
  unfold vcBlocksOfT at h
  simp only [List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨vb0, h1, rfl⟩ := h
  by_cases hb : b < (f.blocks.zip bl).length
  · left
    rw [List.getElem?_append_left (by simpa using hb), List.getElem?_map, List.getElem?_zipIdx,
      Option.map_map, Option.map_eq_some_iff] at h1
    obtain ⟨⟨B, L⟩, hz, rfl⟩ := h1
    rw [List.getElem?_zip_eq_some] at hz
    exact ⟨B, L, hz.1, hz.2, by simp⟩
  · right
    rw [List.getElem?_append_right (by simpa using Nat.le_of_not_lt hb)] at h1
    obtain ⟨p, hp, he⟩ := List.mem_flatMap.mp (List.mem_of_getElem? h1)
    have : 0 < (f.blocks.zip bl).length := List.length_pos_of_mem hp
    exact ⟨by omega, p.1, p.2, vb0, he, rfl⟩

/-- **The control forms of the typed `lowerFunction`'s output** from the typed ISLE inversion of
the function (`IselCtlOn`; integer externs, a VCode in `prepare`'s domain), with `Args` only at
block 0, instruction 0, and block 0 starting with `Args`: `vc_ctlT`'s proof. -/
theorem vc_ctlG {f : Clif.Function} {vc : VCode}
    (hx : f.externs.all (Compile.sigE ·.2.sig) = true) (hIf : Spill.IselCtlOn f)
    (hpd : Prep.PrepDomain vc) (hdom : dominatedB f = true) (ha : AbiSigsOk f)
    (hec : EntryClassOk f) (hl : lowerFunction f = .ok vc) :
    (∀ b vb k i, vc.blocks[b]? = some vb → vb.insts[k]? = some i →
      CtlNA i ∨ (b = 0 ∧ k = 0 ∧ ArgsOkT i)) ∧
    ∃ vb0 ds, vc.blocks[0]? = some vb0 ∧ vb0.insts[0]? = some (.args ds) := by
  have hd := dominated_of hdom
  have hne := hpd.nonempty
  obtain ⟨ctx, ranges, st0, bl, hb, hlb, hvb, -, -⟩ := lowerFunction_runT hx hl
  obtain ⟨hS, hT, hY⟩ := hIf ctx ranges st0 hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  obtain ⟨hord, -⟩ := driver_ord hlb
  have hN : st0.nextVreg = ctx.valDef.size := hcf.size.1
  -- the alias renaming
  let al := aliasOf f bl
  let R := lowerFunction.resolve (aliasArr al) ((aliasArr al).size + 1)
  let gn := chaseF (fun n => ((aliasArr al)[n]?).join) ((aliasArr al).size + 1)
  have hg : VRenaming R gn := ⟨resolve_vreg _ _, fun r hr => by
    cases r with
    | vreg n c => exact absurd rfl (hr n c)
    | _ => rfl⟩
  -- the statement and terminator segments
  have hrest : ∀ bi B L, f.blocks[bi]? = some B → bl[bi]? = some L →
      ∀ i ∈ ((List.range B.body.length).map (segT f ctx R bl bi)).flatten ++ tseg R bl bi,
        CtlNA i := by
    intro bi B L hB hL i hi
    cases hct : i.isCtl with
    | false => exact ctlNA_of_not_isCtl hct
    | true =>
    simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at hi
    rcases hi with ⟨sg, ⟨j, -, rfl⟩, hm⟩ | htseg
    · -- a statement's segment
      unfold segT at hm
      rw [hB, hL] at hm
      simp only at hm
      split at hm
      · rename_i stm sl hstm hsl
        simp only [List.mem_map, List.mem_append] at hm
        obtain ⟨m, hm, rfl⟩ := hm
        rw [isCtl_mapRegs] at hct
        rcases hm with hm | hm
        · obtain ⟨-, hc, -, -⟩ := hspec bi B L hB hL
          obtain ⟨info, hinf, hic, -⟩ := hcf.stmt bi B j stm hB hstm
          obtain ⟨tr, hrun⟩ := hc j sl hsl
          rw [hstart bi L hL] at hrun
          have hge : ctx.valDef.size ≤ sl.st.nextVreg := hN ▸ ((hord bi L hL).stmt j sl hsl).1
          obtain ⟨ms, hms, hsh⟩ := hS _ info stm.inst _ _ _ _ hinf hic hge hrun
          rw [hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)] at hms
          rw [hms] at hm
          exact ctlNA_shapeT hg (hsh m (by simpa using hm) hct)
        · obtain ⟨s, a, b, rfl⟩ := mem_extraOfT hm
          cases hct
      · simp at hm
    · -- the terminator's segment
      unfold tseg at htseg
      rw [hL] at htseg
      simp only [List.mem_map] at htseg
      obtain ⟨m, hm, rfl⟩ := htseg
      rw [isCtl_mapRegs] at hct
      obtain ⟨-, -, htst, nl0, nl', hterm⟩ := hspec bi B L hB hL
      obtain ⟨hn, hy⟩ := lowTerm_spec hterm
      have hph := hcf.term bi B hB
      rw [← hstart bi L hL] at hph
      have hti := (Array.getElem?_eq_some_iff.mp hph).1
      have hge : ctx.valDef.size ≤ L.tst.nextVreg := hN ▸ (hord bi L hL).term.1
      have hBm : ∃ B' ∈ f.blocks, B'.term = B.term := ⟨B, List.mem_of_getElem? hB, rfl⟩
      cases ht : B.term.isTry with
      | false =>
        obtain ⟨htl, hdat, out, tr, hc⟩ := hn ht
        obtain ⟨ms, hms, hsh⟩ := hT _ _ _ _ _ _ _ _ hti hph ht hBm hdat hge hc
        rw [htst] at hms
        rw [htl] at hm
        simp only [fixTry, hms] at hm
        exact ctlNA_shapeT hg (hsh m (by simpa using hm) hct)
      | true =>
        obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := isTry_with ht
        obtain ⟨T, hT', hdat, hex, -, hreg, hinfo, out, tr, hc⟩ := hy et het
        obtain ⟨ms, hms, hsh⟩ := hY _ _ _ _ _ _ _ _ _ _ _ _ _ hti hph het hBm hdat hex hge hreg hc
        simp only [Array.empty_append] at hms
        rw [hT'] at hm
        simp only [fixTry, tryFix, hms, List.toList_toArray] at hm
        have hcl := tryInfo_clobberAll hex hinfo
        split at hm
        · rename_i c hlast
          rcases List.mem_append.mp hm with hm | hm
          · exact ctlNA_shapeT hg (hsh m (List.dropLast_subset _ hm) hct)
          · simp only [List.mem_singleton] at hm
            subst hm
            exact ctlNA_tryCall R c hcl
        · exact ctlNA_shapeT hg (hsh m hm hct)
  -- the instructions of a raw block, by index
  have hpre0 : ∀ B, f.blocks[0]? = some B →
      preT f ctx R 0 = .args (entryRegsT f ctx R B) :: entryLoadsT f ctx R B := by
    intro B hB
    simp only [preT, hB]
  have hraw : ∀ bi B L k i, f.blocks[bi]? = some B → bl[bi]? = some L →
      (fixBlock R (rawBlockT f ctx bl bi B)).insts[k]? = some i →
      CtlNA i ∨ (bi = 0 ∧ k = 0 ∧ ArgsOkT i) := by
    intro bi B L k i hB hL hi
    have hl' : ((rawBlockT f ctx bl bi B).insts.map (MInst.mapRegs R)).toList[k]? = some i := by
      rw [Array.getElem?_toList]; exact hi
    rw [rawBlockT_insts (ctx := ctx) hg bl bi B, List.append_assoc] at hl'
    by_cases hk : k < (preT f ctx R bi).length
    · rw [List.getElem?_append_left hk] at hl'
      rcases bi with _ | bi
      · rw [hpre0 B hB] at hl'
        rcases k with _ | k
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hl'
          subst hl'
          obtain ⟨-, hR, hcls⟩ := entryParams_factsT bl hd hec hb hB
          have he : entryRegsT f ctx R B = argPairsC (entryDC ctx (entryParams f B)) := by
            unfold entryRegsT
            refine entryRegsT_eqC ctx R _ (fun q hq => hR _ ?_)
            unfold entryParams at hq
            exact List.mem_map_of_mem (List.of_mem_zip (List.of_mem_zip hq).1).1
          have hA := entryDC_argRegC (B := B) (ctx := ctx) (sret_le_of_sigAbiOk ha.1.1)
            (sret_i64_of_sigAbiOk ha.1.1) hcls
          refine .inr ⟨rfl, rfl, _, rfl, ?_⟩
          rw [he]
          simp only [argPairsC, List.all_map, List.all_eq_true, Function.comp_def]
          intro q hq
          rcases hA q hq with ⟨hc, k', hk', he'⟩ | ⟨hc, k', hk', he'⟩
          · simp [hc, he', argPairOk, Reg.isVregInt, Reg.isArgReg, hk']
          · simp [hc, he', argPairOk, Reg.isVregInt, Reg.isVregFloat, Reg.isFpArgReg, hk']
        · simp only [List.getElem?_cons_succ] at hl'
          left
          apply ctlNA_of_not_isCtl
          have := List.mem_of_getElem? hl'
          simp only [entryLoadsT, List.mem_filterMap] at this
          obtain ⟨q, -, hq⟩ := this
          unfold entryLoadOfT at hq
          split at hq
          · cases hq; exact isCtl_stackArgLoad _ _ _
          · cases hq
      · simp [preT] at hk
    · rw [List.getElem?_append_right (by omega)] at hl'
      exact .inl (hrest bi B L hB hL i (List.mem_of_getElem? hl'))
  refine ⟨fun b vb k i hvb' hi => ?_, ?_⟩
  · rw [hvb] at hvb'
    rcases vcBlocksOfT_get hvb' with ⟨B, L, hB, hL, rfl⟩ | ⟨-, B, L, e, he, rfl⟩
    · exact hraw b B L k i hB hL hi
    · obtain ⟨tl, hie⟩ := edgeBlocksT_insts he
      have hm := Array.mem_of_getElem? hi
      simp only [fixBlock, hie] at hm
      simp at hm
      subst hm
      exact .inl (ctlNA_jump tl)
  · obtain ⟨vb0, hvb0⟩ : ∃ vb0, vc.blocks[0]? = some vb0 :=
      ⟨_, Array.getElem?_eq_getElem hne⟩
    have hvb0' := hvb0
    rw [hvb] at hvb0'
    rcases vcBlocksOfT_get hvb0' with ⟨B, L, hB, hL, rfl⟩ | ⟨h0, -⟩
    · refine ⟨_, entryRegsT f ctx R B, hvb0, ?_⟩
      have hl' : ((rawBlockT f ctx bl 0 B).insts.map (MInst.mapRegs R)).toList[0]? =
          some (.args (entryRegsT f ctx R B)) := by
        rw [rawBlockT_insts (ctx := ctx) hg bl 0 B, hpre0 B hB]; rfl
      rw [Array.getElem?_toList] at hl'
      exact hl'
    · exact absurd h0 (Nat.lt_irrefl 0)

/-- **The control forms of the typed `lowerFunction`'s output**, with `Args` only at block 0,
instruction 0, and block 0 starting with `Args`. -/
theorem vc_ctlT (hI : IselCtlHypT) {f : Clif.Function} {vc : VCode}
    (hdom : dominatedB f = true) (hs : LowerScopeT f) (hst : Compile.storeTypedB f = true)
    (hsel : Compile.selectTypedB f = true) (ha : AbiSigsOk f) (hec : EntryClassOk f)
    (hl : lowerFunction f = .ok vc) :
    (∀ b vb k i, vc.blocks[b]? = some vb → vb.insts[k]? = some i →
      CtlNA i ∨ (b = 0 ∧ k = 0 ∧ ArgsOkT i)) ∧
    ∃ vb0 ds, vc.blocks[0]? = some vb0 ∧ vb0.insts[0]? = some (.args ds) :=
  vc_ctlG hs.externsE (hI.on hdom hs hst hsel ha) (prepDomain_ofT (dominated_of hdom) hs hl) hdom
    ha hec hl

/-- `prepare` keeps the facts of `vc_ctlT` (`prep_ctl` with class-compatible `Args`). -/
theorem prep_ctlT {vc vcp : VCode} (hp : prepare vc = .ok vcp) (hd : Prep.PrepDomain vc)
    (hv : ∀ b vb k i, vc.blocks[b]? = some vb → vb.insts[k]? = some i →
      CtlNA i ∨ (b = 0 ∧ k = 0 ∧ ArgsOkT i)) :
    ∀ q vb k i, vcp.blocks[q]? = some vb → vb.insts[k]? = some i →
      CtlNA i ∨ (q = 0 ∧ k = 0 ∧ ArgsOkT i) := by
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl⟩ := Prep.prepare_facts hp
  have cs0 := Prep.cfg_spec hc0
  have cs2 : Prep.CfgSpec (B ++ E) ss2 := Prep.cfg_spec hc2
  obtain ⟨h10, hk0, -, hn1, -, hR, hRn, hR0, -, -⟩ := Prep.facts_basic hd cs0 cs2 hS
  intro q vb k i hvb hi
  have hqR : q < (prepOrder B.size ss2).size := by
    have := (Array.getElem?_eq_some_iff.mp hvb).1; simpa using this
  obtain ⟨hj, e⟩ := Prep.v3_get hR hqR
  rw [e] at hvb
  cases hvb
  by_cases hjB : (prepOrder B.size ss2)[q] < B.size
  · rw [Array.getElem_append_left hjB] at hi
    have hj1 : (prepOrder B.size ss2)[q] < (Prep.keep vc.blocks (reachable ss0)).size := by
      rw [← hS.size]; exact hjB
    obtain ⟨b, hb, eb, -⟩ := Prep.keep_src hj1
    have hsrc : ∃ i0, vc.blocks[b].insts[k]? = some i0 ∧
        (i0 = i ∨ ∃ ls, i0.setTargets ls = some i) := by
      rcases hS.rw _ hj1 hjB with h | ⟨t, t', ls, h1, -, h3, h4, -⟩
      · rw [h, eb] at hi; exact ⟨i, hi, .inl rfl⟩
      · rw [h4] at hi
        simp only [Array.getElem?_push] at hi
        split at hi
        · rename_i hk
          cases hi
          refine ⟨t, ?_, .inr ⟨ls, h3⟩⟩
          rw [eb, Array.back?_eq_getElem?] at h1
          rw [hk, Array.size_pop, eb]; exact h1
        · rw [Array.getElem?_pop] at hi
          split at hi
          · rw [eb] at hi; exact ⟨i, hi, .inl rfl⟩
          · cases hi
    obtain ⟨i0, hi0, hii⟩ := hsrc
    rcases hv b _ k i0 (Array.getElem?_eq_getElem hb) hi0 with hc | ⟨rfl, rfl, ds, rfl, hds⟩
    · rcases hii with rfl | ⟨ls, hset⟩
      · exact .inl hc
      · exact .inl (ctlNA_setTargets hset hc)
    · rcases hii with rfl | ⟨ls, hset⟩
      · refine .inr ⟨?_, rfl, ds, rfl, hds⟩
        have hV0 : (Prep.keep vc.blocks (reachable ss0))[0] = vc.blocks[0] := by
          have := hk0
          rw [Array.getElem?_eq_getElem h10, Array.getElem?_eq_getElem hb] at this
          exact Option.some.inj this
        have hj0 : (prepOrder B.size ss2)[q] = 0 :=
          Prep.lbl_inj hn1 hj1 h10 (by rw [eb, hV0])
        have h0 : 0 < (prepOrder B.size ss2).size := (Array.getElem?_eq_some_iff.mp hR0).1
        have e0 : (prepOrder B.size ss2)[0] = 0 := (Array.getElem?_eq_some_iff.mp hR0).2
        exact hRn.eq_of_getElem_eq (by simpa using hqR) (by simpa using h0) (by simp [e0, hj0])
      · simp [MInst.setTargets] at hset
  · have he : (prepOrder B.size ss2)[q] - B.size < E.size := by simp at hj; omega
    obtain ⟨l, hl⟩ := hS.edges _ he
    rw [Array.getElem_append_right (by omega), hl] at hi
    have hm := Array.mem_of_getElem? hi
    simp at hm
    subst hm
    exact .inl (ctlNA_jump l)

/-- **The instruction part of `ctlCheck` on the typed pipeline's output** from the typed ISLE
inversion of the function (`IselCtlOn`): `ctlInsts_pipelineT`'s proof. -/
theorem ctlInsts_pipelineG {f : Clif.Function} {vc vcp : VCode}
    (hx : f.externs.all (Compile.sigE ·.2.sig) = true) (hIf : Spill.IselCtlOn f)
    (hpd : Prep.PrepDomain vc) (hdom : dominatedB f = true) (ha : AbiSigsOk f)
    (hec : EntryClassOk f) (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp) :
    CtlInsts vcp := by
  obtain ⟨hv, h0⟩ := vc_ctlG hx hIf hpd hdom ha hec hl
  refine ⟨fun b vb k i hvb hi => ?_, prep_entry hp hpd h0⟩
  rcases prep_ctlT hp hpd hv b vb k i hvb hi with hc | ⟨rfl, rfl, ds, rfl, hds⟩
  · exact hc.2 b k
  · simpa [ctlInstOk] using hds

/-- **The instruction part of `ctlCheck` on the typed pipeline's output**: every instruction of
the prepared VCode meets `ctlInstOk` at its position, and block 0 starts with an `Args` and has
at least two instructions. -/
theorem ctlInsts_pipelineT (hI : IselCtlHypT) {f : Clif.Function} {vc vcp : VCode}
    (hdom : dominatedB f = true) (hs : LowerScopeT f) (hst : Compile.storeTypedB f = true)
    (hsel : Compile.selectTypedB f = true) (ha : AbiSigsOk f) (hec : EntryClassOk f)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp) : CtlInsts vcp :=
  ctlInsts_pipelineG hs.externsE (hI.on hdom hs hst hsel ha)
    (prepDomain_ofT (dominated_of hdom) hs hl) hdom ha hec hl hp

/-- **Completeness of `ctlInstsB`.** -/
theorem ctlInstsB_of {vc : VCode} (h : CtlInsts vc) : LinkCheck.ctlInstsB vc = true := by
  obtain ⟨h1, vb0, ds, hvb0, hi0, hsz⟩ := h
  unfold LinkCheck.ctlInstsB
  rw [Bool.and_eq_true]
  refine ⟨List.all_eq_true.mpr fun b _ => ?_, ?_⟩
  · split
    · rename_i vb hvb
      refine List.all_eq_true.mpr fun k _ => ?_
      split
      · rename_i i hi
        exact h1 b vb k i hvb hi
      · rfl
    · rfl
  · rw [hvb0]
    simp only [hi0, Bool.true_and, decide_eq_true_eq]
    exact hsz

end E2E

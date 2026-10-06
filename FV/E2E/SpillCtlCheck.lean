import FV.E2E.SpillCtlWitness

/-!
# The instruction part of `ctlCheck` on the pipeline's output

`ctlInsts_pipeline`: for in-scope input, every instruction of `prepare (lowerFunction f)` meets
`ctlInstOk` at its position, and block 0 starts with an `Args` and has at least two
instructions.

The lowering's walk is `ctlSpillHyp_of`'s (`SpillCtlPipe`): the ISLE runs emit the control
shapes `CtlShape` (`iselCtlHyp`), whose tested/defined registers are int vregs; the alias
renaming maps int vregs to int vregs; the entry block's `Args` pairs are renamed parameter vregs
fixed to registers of `locsOf f.sig` (x0..x8, `locsOf_regs`); the `tryCall` replacing a
`try_call` rule's last call has `clobberAll = false` (`tryInfo_clobberAll`); edge blocks are a
single `jump`. Positions: `Args` occurs only as the head of the entry block's `pre`, and the entry
block is `lowerFunction`'s block 0. `prepare` keeps block 0 in place (`rpo` starts at block 0,
`keep` keeps block 0 first, labels are distinct), keeps instruction indices (a retargeted block
only replaces its terminator), and retargeting keeps `ctlInstOk`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill

/-- A non-`Args` instruction meeting `ctlInstOk` at every position. -/
def CtlNA (i : MInst) : Prop := (∀ ds, i ≠ .args ds) ∧ ∀ b k, ctlInstOk b k i = true

/-- An `Args` whose pairs are int vregs fixed to argument registers. -/
def ArgsOk (i : MInst) : Prop :=
  ∃ ds, i = .args ds ∧ ds.all (fun p => p.1.isVregInt && p.2.isArgReg) = true

theorem ctlNA_of_not_isCtl {i : MInst} (h : i.isCtl = false) : CtlNA i := by
  refine ⟨fun ds e => (by subst e; cases h), fun b k => ?_⟩
  cases i <;> first | rfl | cases h

theorem ctlNA_jump (l : Label) : CtlNA (.jump l) := ⟨fun _ e => (by cases e), fun _ _ => rfl⟩

/-- A renamed control shape meets `ctlInstOk`. -/
theorem ctlNA_shape {R : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming R gn) {N : Nat} {m : MInst}
    (h : CtlShape N m) : CtlNA (m.mapRegs R) := by
  refine ⟨fun ds e => (by cases h <;> simp [MInst.mapRegs] at e), fun b k => ?_⟩
  cases h
  case condBr kd hk =>
    rcases kd with ⟨r, s⟩ | ⟨r, s⟩ | c <;> (try obtain ⟨n, rfl⟩ := hk) <;>
      simp [MInst.mapRegs, CondBrKind.mapRegs, ctlInstOk, hg.vreg, Reg.isVregInt]
  case trapIf kd c hk =>
    rcases kd with ⟨r, s⟩ | ⟨r, s⟩ | c <;> (try obtain ⟨n, rfl⟩ := hk) <;>
      simp [MInst.mapRegs, CondBrKind.mapRegs, ctlInstOk, hg.vreg, Reg.isVregInt]
  all_goals simp [MInst.mapRegs, ctlInstOk, retPairs, hg.vreg, Reg.isVregInt]

/-- The `tryCall` replacing a `try_call` rule's last call. -/
theorem ctlNA_tryCall (R : Reg → Reg) (c : CallInfo) {info : TryInfo} (h : info.clobberAll = false) :
    CtlNA ((MInst.tryCall c info).mapRegs R) :=
  ⟨fun _ e => (by simp [MInst.mapRegs] at e), fun _ _ => by simp [MInst.mapRegs, ctlInstOk, h]⟩

theorem ctlInstOk_condBr {n m : Nat} {a b a' b' : Label} {kd : CondBrKind} :
    ctlInstOk n m (.condBr a b kd) = ctlInstOk n m (.condBr a' b' kd) := by
  cases kd <;> rfl

/-- Retargeting keeps `CtlNA`. -/
theorem ctlNA_setTargets {i i' : MInst} {ls : List Label} (h : i.setTargets ls = some i')
    (hi : CtlNA i) : CtlNA i' := by
  have hc := hi.2
  unfold MInst.setTargets at h
  split at h
  all_goals (try split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨fun _ e => (by cases e), hc⟩)
    | (cases h; exact ⟨fun _ e => (by cases e), fun b k => ctlInstOk_condBr.trans (hc b k)⟩)

/-- The entry block's `Args` pairs: int vregs in argument registers. -/
theorem entryRegs_ok {f : Clif.Function} {R : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming R gn)
    (B : Clif.Block) (hsig : (f.sig.params.filter (·.purpose == .sret)).length ≤ 1) :
    (entryRegs f R B).all (fun p => p.1.isVregInt && p.2.isArgReg) = true := by
  obtain ⟨-, harg⟩ := locsOf_regs hsig
  rw [List.all_eq_true]
  intro q hq
  unfold entryRegs at hq
  obtain ⟨a, ha, hq⟩ := List.mem_filterMap.mp hq
  have hloc : a.1.2 ∈ locsOf f.sig := by
    unfold entryParams at ha
    exact (List.of_mem_zip (List.of_mem_zip ha).1).2
  unfold entryRegOf at hq
  split at hq
  · rename_i p hp
    cases hq
    have hpr : p ∈ locRegs (locsOf f.sig) := List.mem_filterMap.mpr ⟨_, hloc, by rw [hp]⟩
    obtain ⟨j, hj, rfl⟩ := harg p hpr
    simp [hg.vreg, Reg.isVregInt, Reg.isArgReg, hj]
  · cases hq

/-- Block `b` of `vcBlocksOf`: the raw block `b`, or an edge block (then `0 < b`). -/
theorem vcBlocksOf_get {f : Clif.Function} {bl : List BLow} {b : Nat} {vb : VBlock}
    (h : (vcBlocksOf f bl)[b]? = some vb) :
    (∃ B L, f.blocks[b]? = some B ∧ bl[b]? = some L ∧
      vb = fixBlock (lowerFunction.resolve (aliasArr (aliasOf f bl)) ((aliasArr (aliasOf f bl)).size + 1))
        (rawBlock f bl b B)) ∨
    (0 < b ∧ ∃ B L e, e ∈ edgeBlocks f B L ∧
      vb = fixBlock (lowerFunction.resolve (aliasArr (aliasOf f bl)) ((aliasArr (aliasOf f bl)).size + 1)) e) := by
  unfold vcBlocksOf at h
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

/-- **The control forms of `lowerFunction`'s output**, with `Args` only at block 0,
instruction 0, and block 0 starting with `Args`. -/
theorem vc_ctl {f : Clif.Function} {vc : VCode} (hd : Dominated f) (hs : LowerScope f)
    (ha : AbiSigsOk f) (hl : lowerFunction f = .ok vc) :
    (∀ b vb k i, vc.blocks[b]? = some vb → vb.insts[k]? = some i →
      CtlNA i ∨ (b = 0 ∧ k = 0 ∧ ArgsOk i)) ∧
    ∃ vb0 ds, vc.blocks[0]? = some vb0 ∧ vb0.insts[0]? = some (.args ds) := by
  have hne := (prepDomain_of_lower hs hl hs.nonempty).nonempty
  obtain ⟨ctx, ranges, st0, bl, hb, hlb, hvb, -, -⟩ := lowerFunction_run hl
  obtain ⟨hS, hT, hY⟩ := iselCtlHyp f ctx ranges st0 hd hs ha hb
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
      ∀ i ∈ ((List.range B.body.length).map (seg f R bl bi)).flatten ++ tseg R bl bi, CtlNA i := by
    intro bi B L hB hL i hi
    cases hct : i.isCtl with
    | false => exact ctlNA_of_not_isCtl hct
    | true =>
    simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at hi
    rcases hi with ⟨sg, ⟨j, -, rfl⟩, hm⟩ | htseg
    · -- a statement's segment
      unfold seg at hm
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
          exact ctlNA_shape hg (hsh m (by simpa using hm) hct)
        · obtain ⟨s, a, b, rfl⟩ := mem_extraOf hm
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
      cases ht : B.term.isTry with
      | false =>
        obtain ⟨htl, hdat, out, tr, hc⟩ := hn ht
        obtain ⟨ms, hms, hsh⟩ := hT _ _ _ _ _ _ _ _ hti hph ht hdat hge hc
        rw [htst] at hms
        rw [htl] at hm
        simp only [fixTry, hms] at hm
        exact ctlNA_shape hg (hsh m (by simpa using hm) hct)
      | true =>
        obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := isTry_with ht
        obtain ⟨T, hT', hdat, hex, -, hreg, hinfo, out, tr, hc⟩ := hy et het
        obtain ⟨ms, hms, hsh⟩ := hY _ _ _ _ _ _ _ _ _ _ _ _ _ hti hph het
          ⟨B, List.mem_of_getElem? hB, rfl⟩ hdat hex hge hreg hc
        simp only [Array.empty_append] at hms
        rw [hT'] at hm
        simp only [fixTry, tryFix, hms, List.toList_toArray] at hm
        have hcl := tryInfo_clobberAll hex hinfo
        split at hm
        · rename_i c hlast
          rcases List.mem_append.mp hm with hm | hm
          · exact ctlNA_shape hg (hsh m (List.dropLast_subset _ hm) hct)
          · simp only [List.mem_singleton] at hm
            subst hm
            exact ctlNA_tryCall R c hcl
        · exact ctlNA_shape hg (hsh m hm hct)
  -- the instructions of a raw block, by index
  have hpre0 : ∀ B, f.blocks[0]? = some B →
      pre f R 0 = .args (entryRegs f R B) :: entryLoads f R B := by
    intro B hB
    simp only [pre, hB]
  have hraw : ∀ bi B L k i, f.blocks[bi]? = some B → bl[bi]? = some L →
      (fixBlock R (rawBlock f bl bi B)).insts[k]? = some i →
      CtlNA i ∨ (bi = 0 ∧ k = 0 ∧ ArgsOk i) := by
    intro bi B L k i hB hL hi
    have hl' : ((rawBlock f bl bi B).insts.map (MInst.mapRegs R)).toList[k]? = some i := by
      rw [Array.getElem?_toList]; exact hi
    rw [rawBlock_insts, List.append_assoc] at hl'
    by_cases hk : k < (pre f R bi).length
    · rw [List.getElem?_append_left hk] at hl'
      rcases bi with _ | bi
      · rw [hpre0 B hB] at hl'
        rcases k with _ | k
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hl'
          subst hl'
          exact .inr ⟨rfl, rfl, _, rfl, entryRegs_ok hg B (sret_le_of_sigAbiOk ha.1.1)⟩
        · simp only [List.getElem?_cons_succ] at hl'
          left
          apply ctlNA_of_not_isCtl
          have := List.mem_of_getElem? hl'
          simp only [entryLoads, List.mem_filterMap] at this
          obtain ⟨q, -, hq⟩ := this
          unfold entryLoadOf at hq
          split at hq
          · cases hq; rfl
          · cases hq
      · simp [pre] at hk
    · rw [List.getElem?_append_right (by omega)] at hl'
      exact .inl (hrest bi B L hB hL i (List.mem_of_getElem? hl'))
  refine ⟨fun b vb k i hvb' hi => ?_, ?_⟩
  · rw [hvb] at hvb'
    rcases vcBlocksOf_get hvb' with ⟨B, L, hB, hL, rfl⟩ | ⟨-, B, L, e, he, rfl⟩
    · exact hraw b B L k i hB hL hi
    · obtain ⟨tl, hie⟩ := edgeBlocks_insts he
      have hm := Array.mem_of_getElem? hi
      simp only [fixBlock, hie] at hm
      simp at hm
      subst hm
      exact .inl (ctlNA_jump tl)
  · obtain ⟨vb0, hvb0⟩ : ∃ vb0, vc.blocks[0]? = some vb0 :=
      ⟨_, Array.getElem?_eq_getElem hne⟩
    have hvb0' := hvb0
    rw [hvb] at hvb0'
    rcases vcBlocksOf_get hvb0' with ⟨B, L, hB, hL, rfl⟩ | ⟨h0, -⟩
    · refine ⟨_, entryRegs f R B, hvb0, ?_⟩
      have hl' : ((rawBlock f bl 0 B).insts.map (MInst.mapRegs R)).toList[0]? =
          some (.args (entryRegs f R B)) := by
        rw [rawBlock_insts, hpre0 B hB]; rfl
      rw [Array.getElem?_toList] at hl'
      exact hl'
    · exact absurd h0 (Nat.lt_irrefl 0)

/-- `prepare` keeps the facts of `vc_ctl`: block 0 stays block 0, instruction indices stay, and
retargeting keeps `ctlInstOk`. -/
theorem prep_ctl {vc vcp : VCode} (hp : prepare vc = .ok vcp) (hd : Prep.PrepDomain vc)
    (hv : ∀ b vb k i, vc.blocks[b]? = some vb → vb.insts[k]? = some i →
      CtlNA i ∨ (b = 0 ∧ k = 0 ∧ ArgsOk i)) :
    ∀ q vb k i, vcp.blocks[q]? = some vb → vb.insts[k]? = some i →
      CtlNA i ∨ (q = 0 ∧ k = 0 ∧ ArgsOk i) := by
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl⟩ := Prep.prepare_facts hp
  have cs0 := Prep.cfg_spec hc0
  have cs2 : Prep.CfgSpec (B ++ E) ss2 := Prep.cfg_spec hc2
  obtain ⟨h10, hk0, -, hn1, -, hR, hRn, hR0, -, -⟩ := Prep.facts_basic hd cs0 cs2 hS
  intro q vb k i hvb hi
  have hqR : q < (rpo ss2).size := by
    have := (Array.getElem?_eq_some_iff.mp hvb).1; simpa using this
  obtain ⟨hj, e⟩ := Prep.v3_get hR hqR
  rw [e] at hvb
  cases hvb
  by_cases hjB : (rpo ss2)[q] < B.size
  · rw [Array.getElem_append_left hjB] at hi
    have hj1 : (rpo ss2)[q] < (Prep.keep vc.blocks (reachable ss0)).size := by
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
        have hj0 : (rpo ss2)[q] = 0 :=
          Prep.lbl_inj hn1 hj1 h10 (by rw [eb, hV0])
        have h0 : 0 < (rpo ss2).size := (Array.getElem?_eq_some_iff.mp hR0).1
        have e0 : (rpo ss2)[0] = 0 := (Array.getElem?_eq_some_iff.mp hR0).2
        exact hRn.eq_of_getElem_eq (by simpa using hqR) (by simpa using h0) (by simp [e0, hj0])
      · simp [MInst.setTargets] at hset
  · have he : (rpo ss2)[q] - B.size < E.size := by simp at hj; omega
    obtain ⟨l, hl⟩ := hS.edges _ he
    rw [Array.getElem_append_right (by omega), hl] at hi
    have hm := Array.mem_of_getElem? hi
    simp at hm
    subst hm
    exact .inl (ctlNA_jump l)

/-- `prepare` keeps block 0 starting with `Args`; it has a terminator after it. -/
theorem prep_entry {vc vcp : VCode} (hp : prepare vc = .ok vcp) (hd : Prep.PrepDomain vc)
    (h0 : ∃ vb0 ds, vc.blocks[0]? = some vb0 ∧ vb0.insts[0]? = some (.args ds)) :
    ∃ vb0 ds, vcp.blocks[0]? = some vb0 ∧ vb0.insts[0]? = some (.args ds) ∧
      1 < vb0.insts.size := by
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl⟩ := Prep.prepare_facts hp
  have cs0 := Prep.cfg_spec hc0
  have cs2 : Prep.CfgSpec (B ++ E) ss2 := Prep.cfg_spec hc2
  obtain ⟨h10, hk0, -, -, -, hR, -, hR0, -, -⟩ := Prep.facts_basic hd cs0 cs2 hS
  obtain ⟨vb0, ds, hvb0, hi0⟩ := h0
  obtain ⟨t, -, hback, hterm, -⟩ := cs0.blk 0 vb0 hvb0
  have hsz : 1 < vb0.insts.size := by
    have h0' : 0 < vb0.insts.size := (Array.getElem?_eq_some_iff.mp hi0).1
    refine Nat.lt_of_not_le fun hc => ?_
    have h1 : vb0.insts.size = 1 := by omega
    rw [Array.back?_eq_getElem?, h1] at hback
    rw [hback] at hi0
    cases hi0
    cases hterm
  have h0 : 0 < (rpo ss2).size := (Array.getElem?_eq_some_iff.mp hR0).1
  have e0 : (rpo ss2)[0] = 0 := (Array.getElem?_eq_some_iff.mp hR0).2
  obtain ⟨hj, e⟩ := Prep.v3_get hR h0
  have hB0 : 0 < B.size := by rw [hS.size]; exact h10
  have hV0 : (Prep.keep vc.blocks (reachable ss0))[0] = vb0 := by
    have := hk0
    rw [Array.getElem?_eq_getElem h10, hvb0] at this
    exact Option.some.inj this
  refine ⟨B[0], ds, ?_, ?_⟩
  · rw [e]; simp only [e0, Array.getElem_append_left hB0]
  rcases hS.rw 0 h10 hB0 with h | ⟨t, t', ls, -, -, -, h4, -⟩
  · rw [h, hV0]; exact ⟨hi0, hsz⟩
  · rw [h4, hV0]
    refine ⟨?_, by simp; omega⟩
    simp only [Array.getElem?_push, Array.size_pop, Array.getElem?_pop]
    split
    · omega
    · split
      · exact hi0
      · omega

/-- **The instruction part of `ctlCheck` on the pipeline's output**: every instruction of the
prepared VCode meets `ctlInstOk` at its position, and block 0 starts with an `Args` and has at
least two instructions. -/
theorem ctlInsts_pipeline {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    (hsub : InSubset p f) (hd : Dominated f) (hs : LowerScope f)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp) :
    (∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), vcp.blocks[b]? = some vb →
      vb.insts[k]? = some i → ctlInstOk b k i = true) ∧
    ∃ vb0 ds, vcp.blocks[0]? = some vb0 ∧ vb0.insts[0]? = some (.args ds) ∧
      1 < vb0.insts.size := by
  obtain ⟨hv, h0⟩ := vc_ctl hd hs (abiSigsOk_of_inSubset hsub) hl
  have hdom := prepDomain_of_lower hs hl hs.nonempty
  refine ⟨fun b vb k i hvb hi => ?_, prep_entry hp hdom h0⟩
  rcases prep_ctl hp hdom hv b vb k i hvb hi with hc | ⟨rfl, rfl, ds, rfl, hds⟩
  · exact hc.2 b k
  · simpa [ctlInstOk] using hds

end E2E

import FV.Backend.Proof.KillHypT
import FV.Backend.Proof.SpillEdgesT
import FV.Backend.Proof.SpillEdgesLowT
import FV.Backend.Proof.LowerLoopT
import FV.Backend.Proof.LowerLoopSimT
import FV.Backend.Proof.LowerLoopRunT
import FV.Backend.Proof.LowerCompleteT
import FV.Backend.Proof.LowerShapeOkT

/-!
# Killed vregs of `lowerFunction`'s VCode: the driver's assembly (V4, `SpillKillFree`), typed

`killFreeB_lowerT`: from the run facts `KillRunsHypT` and the exact defs of a `try_call`'s call
(`TryDefsExactT`), `lowerFunction`'s VCode passes `Spill.killFreeB`, on input of the typed
movement scope (`LowerScopeT`). The kill facts only look at vreg numbers (`useVregs`,
`unstored`, `killedL`, `homeNum`), so the class annotations do not matter: the proof is
`killFreeB_lower` with the typed models (`LowT`, `rawBlockT`, `edgeBlocksT`, `preT`, `segT`,
`LoopFactsT`, `vregOf ctx`, `tryEdgeArgT ctx`) in place of the integer ones.
-/

namespace Backend.Proof.Kill

open Backend Backend.Proof Backend.Proof.Spill Backend.Proof.Driver

/-! ## Instructions -/

/-- `stackArgLoad` of a vreg at a frame offset kills and reads nothing, in either class. -/
theorem asm_stackArgLoad (n : Nat) (c : RegClass) (b : Nat) (o : Int) :
    unstored (stackArgLoad (.vreg n c) b (.fpOffset o)) = [] ∧
      useVregs (stackArgLoad (.vreg n c) b (.fpOffset o)) = [] := by
  cases c <;> exact ⟨asm_unstored_nil rfl rfl, rfl⟩

/-- `asm_mov_uses` for a destination vreg of any class. -/
theorem asm_mov_usesC (s : OperandSize) (r : Nat) (c : RegClass) (out : Reg)
    (hout : ∀ n c, out ≠ .vreg n c) : useVregs (.mov s (.vreg r c) out) = [] := by
  unfold useVregs
  rw [operands_eq]
  simp only [MInst.visitOperands, StateT.run_bind]
  have h1 : (collectOp OpSpec.def_ (Reg.vreg r c)).run #[] =
      .ok (.vreg r c, #[⟨r, c, OpSpec.def_.kind, OpSpec.def_.pos, OpSpec.def_.con⟩]) := rfl
  rw [h1, Driver.except_ok_bind]
  cases h2 : (collectOp OpSpec.use out).run
      #[⟨r, c, OpSpec.def_.kind, OpSpec.def_.pos, OpSpec.def_.con⟩] with
  | error e => rfl
  | ok p =>
    obtain ⟨a, s'⟩ := p
    have := asm_collect_real hout h2
    subst this
    rfl

/-- The typed entry block's argument setup kills and reads nothing (`asm_pre`, typed). -/
theorem asm_preT {f : Clif.Function} {ctx : Ctx} {R : Reg → Reg} {gn : Nat → Nat}
    (hg : VRenaming R gn)
    {bi : Nat} {i : MInst} (h : i ∈ preT f ctx R bi) : unstored i = [] ∧ useVregs i = [] := by
  unfold preT at h
  split at h
  · simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨asm_unstored_nil rfl rfl, asm_args_uses _⟩
    · simp only [entryLoadsT, List.mem_filterMap] at h
      obtain ⟨q, -, hq⟩ := h
      unfold entryLoadOfT at hq
      split at hq
      · cases hq
        rw [show vregOf ctx q.1.1.1 = .vreg q.1.1.1 (valClassOf ctx q.1.1.1) from rfl, hg.vreg]
        exact asm_stackArgLoad _ _ _ _
      · cases hq
  · simp at h

/-! ## The members of `vcBlocksOfT` with the renaming named -/

/-- The members of `vcBlocksOfT` with the renaming: `lowerFunction`'s alias resolution
(`mem_vcBlocksOf'`, typed). -/
theorem mem_vcBlocksT' {f : Clif.Function} {ctx : Ctx} {bl : List BLow} {vb : VBlock}
    (h : vb ∈ (vcBlocksOfT f ctx bl).toList) :
    (∃ bi B L, f.blocks[bi]? = some B ∧ bl[bi]? = some L ∧
      vb = fixBlock (asmR f bl) (rawBlockT f ctx bl bi B)) ∨
    (∃ B L e, B ∈ f.blocks ∧ e ∈ edgeBlocksT f ctx B L ∧ vb = fixBlock (asmR f bl) e) := by
  simp only [vcBlocksOfT, List.toList_toArray, List.mem_map, List.mem_append, List.mem_flatMap] at h
  obtain ⟨vb0, h1, rfl⟩ := h
  rcases h1 with ⟨p, hp, rfl⟩ | ⟨p, hp, he⟩
  · have := List.mem_zipIdx_iff_getElem?.mp hp
    rw [List.getElem?_zip_eq_some] at this
    exact .inl ⟨p.2, p.1.1, p.1.2, this.1, this.2, rfl⟩
  · exact .inr ⟨p.1, p.2, vb0, (List.of_mem_zip hp).1, he, rfl⟩

section Insts
variable {f : Clif.Function} {ctx : Ctx} {vc : VCode} {bl : List BLow}
  (hvb : vc.blocks = vcBlocksOfT f ctx bl)
include hvb

/-- **An instruction of `lowerFunction`'s VCode** kills and reads nothing, or is the renaming of
an instruction of a run segment (`vb_inst_cases`, typed). -/
theorem vb_inst_casesT {vb : VBlock} (hvb' : vb ∈ vc.blocks.toList) {i : MInst}
    (hi : i ∈ vb.insts.toList) :
    (unstored i = [] ∧ useVregs i = []) ∨
      ∃ lo mid hi c m, Seg f bl lo mid hi c ∧ m ∈ c ∧ i = m.mapRegs (asmR f bl) := by
  have hg := asm_ren f bl
  rw [hvb] at hvb'
  rcases mem_vcBlocksT' hvb' with ⟨bi, B, L, hB, hL, rfl⟩ | ⟨B, L, e, -, he, rfl⟩
  · have hi' : i ∈ ((rawBlockT f ctx bl bi B).insts.map (MInst.mapRegs (asmR f bl))).toList := hi
    rw [rawBlockT_insts (ctx := ctx) hg bl bi B] at hi'
    simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at hi'
    rcases hi' with (hpre | ⟨sg, ⟨j, -, rfl⟩, hm⟩) | htseg
    · exact .inl (asm_preT hg hpre)
    · unfold segT at hm
      rw [hB, hL] at hm
      simp only at hm
      split at hm
      · rename_i stm sl hstm hsl
        simp only [List.mem_map, List.mem_append] at hm
        obtain ⟨m, hm, rfl⟩ := hm
        rcases hm with hm | hm
        · exact .inr ⟨_, _, _, _, m, ⟨bi, B, L, hB, hL, .inl ⟨j, sl, hsl, rfl, rfl, rfl, rfl⟩⟩,
            hm, rfl⟩
        · simp only [extraOfT, List.mem_filterMap] at hm
          obtain ⟨q, -, hq⟩ := hm
          split at hq
          · cases hq
          · rename_i out hout' _
            cases hq
            have hout : ∀ n c, out ≠ .vreg n c := fun n c e => hout' n c e
            have e : (MInst.mov .size64 (vregOf ctx q.1) out).mapRegs (asmR f bl) =
                .mov .size64 (.vreg (asmG f bl q.1) (valClassOf ctx q.1)) out := by
              show MInst.mov .size64 (asmR f bl (vregOf ctx q.1)) (asmR f bl out) = _
              rw [show vregOf ctx q.1 = .vreg q.1 (valClassOf ctx q.1) from rfl, hg.vreg,
                hg.real out hout]
            rw [e]
            exact .inl ⟨asm_unstored_nil rfl rfl, asm_mov_usesC _ _ _ _ hout⟩
          · cases hq
      · simp at hm
    · unfold tseg at htseg
      split at htseg
      · rename_i L' hL'
        rw [hL] at hL'
        cases hL'
        simp only [List.mem_map] at htseg
        obtain ⟨m, hm, rfl⟩ := htseg
        exact .inr ⟨_, _, _, _, m, ⟨bi, B, L, hB, hL, .inr ⟨rfl, rfl, rfl, rfl⟩⟩, hm, rfl⟩
      · simp at htseg
  · obtain ⟨tl, hie⟩ := edgeBlocksT_insts he
    simp only [fixBlock, hie] at hi
    simp at hi
    subst hi
    exact .inl (asm_jump tl)

end Insts

/-! ## The segments' facts -/

section Segs
variable {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
  {bl : List BLow} {S : Clif.Function → Prop}
  (hd : Dominated f) (hs : S f) (ha : AbiSigsOk f)
  (hb : buildCtx f = .ok (ctx, ranges, st0))
  (hlb : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
    some bl)
  (hlf : LoopFactsT f ctx bl)
include hd hs ha hb hlb hlf

/-- **A run segment's killed vregs and uses** (`seg_ok`, typed: the run facts are the typed
ones; the statements' code is the same). -/
theorem seg_okT (hK : KillRunsHypP S) (hX : TryDefsExactP S) {lo mid hi : Nat} {c : List MInst}
    (h : Seg f bl lo mid hi c) :
    ctx.valDef.size ≤ lo ∧ lo ≤ mid ∧ (∀ m ∈ c, ∀ k ∈ unstored m, lo ≤ k ∧ k < hi) ∧
      ∀ m ∈ c, ∀ u ∈ useVregs m,
        u < ctx.valDef.size ∨ (mid ≤ u ∧ u < hi ∧ ∀ m' ∈ c, u ∉ unstored m') := by
  obtain ⟨hS, hT, hY⟩ := hK f ctx ranges st0 hd hs ha hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  obtain ⟨hord, -⟩ := driver_ord hlb
  have hN : st0.nextVreg = ctx.valDef.size := hcf.size.1
  obtain ⟨bi, B, L, hB, hL, hc⟩ := h
  obtain ⟨-, hcs, htst, nl0, nl', hterm⟩ := hspec bi B L hB hL
  rcases hc with ⟨j, sl, hsl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, hmid, rfl⟩
  · -- a statement
    have hj : j < B.body.length := by
      rw [← (hspec bi B L hB hL).1]; exact (List.getElem?_eq_some_iff.mp hsl).1
    obtain ⟨stm, hstm⟩ : ∃ stm, B.body[j]? = some stm := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨info, hinf, hic, -⟩ := hcf.stmt bi B j stm hB hstm
    obtain ⟨tr, hrun⟩ := hcs j sl hsl
    rw [hstart bi L hL] at hrun
    have hge : ctx.valDef.size ≤ sl.st.nextVreg := hN ▸ ((hord bi L hL).stmt j sl hsl).1
    obtain ⟨hk, -⟩ := hS _ info stm.inst _ _ _ _ hinf hic hge hrun
    obtain ⟨h1, h2⟩ := asm_runKill hk (hemp L (List.mem_of_getElem? hL) sl
      (List.mem_of_getElem? hsl))
    refine ⟨hge, Nat.le_refl _, h1, fun m hm u hu => ?_⟩
    rcases (h2 m hm u hu).1 with h3 | h3
    · exact .inl h3
    · exact .inr ⟨h3.1, h3.2, (h2 m hm u hu).2⟩
  · -- the terminator
    have hph := hcf.term bi B hB
    rw [← hstart bi L hL] at hph
    have hti := (Array.getElem?_eq_some_iff.mp hph).1
    have hge : ctx.valDef.size ≤ L.tst.nextVreg := hN ▸ (hord bi L hL).term.1
    obtain ⟨hn, hy⟩ := lowTerm_spec hterm
    cases ht : B.term.isTry with
    | false =>
      obtain ⟨htl, hdat, out, tr, hc⟩ := hn ht
      have hk := hT _ _ _ _ _ _ _ _ hti hph ht hdat hge hc
      obtain ⟨h1, h2⟩ := asm_runKill hk htst
      rw [htl] at hmid ⊢
      simp only at hmid
      subst hmid
      refine ⟨hge, Nat.le_refl _, h1, fun m hm u hu => ?_⟩
      rcases (h2 m hm u hu).1 with h3 | h3
      · exact .inl h3
      · exact .inr ⟨h3.1, h3.2, (h2 m hm u hu).2⟩
    | true =>
      obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := isTry_with ht
      obtain ⟨T, hT', hdat, hex, -, hreg, hinfo, out, tr, hc⟩ := hy et het
      have hBt : ∃ B' ∈ f.blocks, B'.term = B.term := ⟨B, List.mem_of_getElem? hB, rfl⟩
      obtain ⟨hk, -⟩ := hY _ _ _ _ _ _ _ _ _ _ _ _ _ hti hph het hBt hdat hex hge hreg hc
      have hdefs := hX f ctx ranges st0 hd hs ha hb _ _ _ _ _ _ _ _ _ _ _ _ _ hti hph het hBt
        hdat hex hge hreg hc
      obtain ⟨h1, h2⟩ := asm_runKill hk rfl
      obtain ⟨-, -, hst1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc hex) hreg
      have hmono : T.st1.nextVreg ≤ L.tst'.nextVreg := (runTerm_mono hc).1
      rw [hT'] at hmid ⊢
      simp only at hmid
      subst hmid
      obtain ⟨cl, hcl⟩ := hlf.tryLast bi B L T hB hL hT'
      rw [← back_toList] at hcl
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hcl
      have hD := hdefs (.call cl) (by rw [hys]; simp) cl rfl
      have hcode : fixTry (some T) L.tst'.emitted.toList = ys ++ [.tryCall cl T.info] := by
        show tryFix T.info _ = _
        rw [hys, tryFix_append]
      rw [hcode]
      have hys' : ∀ m ∈ ys, m ∈ L.tst'.emitted.toList := fun m hm => by
        rw [hys]; exact List.mem_append_left _ hm
      have hcm : MInst.call cl ∈ L.tst'.emitted.toList := by rw [hys]; simp
      -- what the `tryCall` kills: the results, below `mid`
      have htk : ∀ k ∈ unstored (.tryCall cl T.info), L.tst.nextVreg ≤ k ∧ k < T.st1.nextVreg := by
        intro k hk'
        have := asm_unstored_tryCall hD hk'
        rw [asm_outDefs_vregs] at this
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp this
        rw [List.mem_range] at hj
        omega
      refine ⟨hge, by omega, fun m hm k hk' => ?_, fun m hm u hu => ?_⟩
      · rcases List.mem_append.mp hm with hm | hm
        · have := h1 m (hys' m hm) k hk'
          omega
        · rw [List.mem_singleton] at hm
          subst hm
          have := htk k hk'
          omega
      · have hu' : ∃ m0 ∈ L.tst'.emitted.toList, u ∈ useVregs m0 := by
          rcases List.mem_append.mp hm with hm | hm
          · exact ⟨m, hys' m hm, hu⟩
          · rw [List.mem_singleton] at hm
            subst hm
            exact ⟨_, hcm, by rw [← asm_useVregs_tryCall]; exact hu⟩
        obtain ⟨m0, hm0, hu0⟩ := hu'
        obtain ⟨h3, h4⟩ := h2 m0 hm0 u hu0
        rcases h3 with h3 | h3
        · exact .inl h3
        · refine .inr ⟨h3.1, h3.2, fun m' hm' hum => ?_⟩
          rcases List.mem_append.mp hm' with hm' | hm'
          · exact h4 m' (hys' m' hm') hum
          · rw [List.mem_singleton] at hm'
            subst hm'
            have := htk u hum
            omega

end Segs

/-! ## Killed vregs and uses of the assembled VCode -/

section Assemble
variable {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
  {bl : List BLow} {vc : VCode} {S : Clif.Function → Prop}
  (hd : Dominated f) (hs : S f) (ha : AbiSigsOk f)
  (hb : buildCtx f = .ok (ctx, ranges, st0))
  (hlb : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
    some bl)
  (hlf : LoopFactsT f ctx bl) (hvb : vc.blocks = vcBlocksOfT f ctx bl)
  (hK : KillRunsHypP S) (hX : TryDefsExactP S)
include hd hs ha hb hlb hlf hvb hK hX

/-- **A killed vreg** is killed by an instruction of a run segment, inside the segment's range
(`killed_seg`, typed). -/
theorem killed_segT {k : Nat} (hk : k ∈ killedOf vc) :
    ∃ lo mid hi c m, Seg f bl lo mid hi c ∧ m ∈ c ∧ k ∈ unstored m ∧ lo ≤ k ∧ k < hi := by
  simp only [killedOf, List.mem_flatMap] at hk
  obtain ⟨vb, hvb', i, hi, hki⟩ := hk
  rcases vb_inst_casesT hvb hvb' hi with ⟨h0, -⟩ | ⟨lo, mid, hi', c, m, hseg, hm, rfl⟩
  · rw [h0] at hki; cases hki
  · obtain ⟨k0, hk0, rfl⟩ := asm_unstored_mapRegs (asm_ren f bl) hki
    obtain ⟨hlo, -, hkill, -⟩ := seg_okT hd hs ha hb hlb hlf hK hX hseg
    obtain ⟨h1, h2⟩ := hkill m hm k0 hk0
    rw [asm_fix bl hb (by omega)]
    exact ⟨lo, mid, hi', c, m, hseg, hm, hk0, h1, h2⟩

/-- **A use** is a renamed CLIF value's vreg, or a vreg of a run segment's rule that the
segment does not kill (`use_src`, typed). -/
theorem use_srcT {vb : VBlock} (hvb' : vb ∈ vc.blocks.toList) {i : MInst}
    (hi : i ∈ vb.insts.toList)
    {u : Nat} (hu : u ∈ useVregs i) :
    (∃ x, x < ctx.valDef.size ∧ u = asmG f bl x) ∨
      ∃ lo mid hi c, Seg f bl lo mid hi c ∧ mid ≤ u ∧ u < hi ∧ ∀ m' ∈ c, u ∉ unstored m' := by
  rcases vb_inst_casesT hvb hvb' hi with ⟨-, h0⟩ | ⟨lo, mid, hi', c, m, hseg, hm, rfl⟩
  · rw [h0] at hu; cases hu
  · obtain ⟨u0, hu0, rfl⟩ := asm_useVregs_mapRegs (asm_ren f bl) hu
    obtain ⟨hlo, hlm, -, huse⟩ := seg_okT hd hs ha hb hlb hlf hK hX hseg
    rcases huse m hm u0 hu0 with h1 | ⟨h1, h2, h3⟩
    · exact .inl ⟨u0, h1, rfl⟩
    · rw [asm_fix bl hb (by omega : ctx.valDef.size ≤ u0)]
      exact .inr ⟨lo, mid, hi', c, hseg, h1, h2, h3⟩

omit hlf hvb hX in
/-- **An alias target**, a statement's result register, is a CLIF value's vreg or a vreg of the
statement's segment that the segment does not kill (`alias_ok`, typed). -/
theorem alias_okT {p : Nat × Nat} (hp : p ∈ aliasOf f bl) :
    p.2 < ctx.valDef.size ∨
      ∃ lo hi c, Seg f bl lo lo hi c ∧ lo ≤ p.2 ∧ p.2 < hi ∧ ∀ m ∈ c, p.2 ∉ unstored m := by
  obtain ⟨hS, -, -⟩ := hK f ctx ranges st0 hd hs ha hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  obtain ⟨hord, -⟩ := driver_ord hlb
  have hN : st0.nextVreg = ctx.valDef.size := hcf.size.1
  obtain ⟨bi, B, L, j, stm, sl, hB, hL, hstm, hsl, hr, rs, c, hrs, hrse⟩ := mem_aliasOf hp
  obtain ⟨-, hcs, -⟩ := hspec bi B L hB hL
  obtain ⟨info, hinf, hic, hres⟩ := hcf.stmt bi B j stm hB hstm
  obtain ⟨tr, hrun⟩ := hcs j sl hsl
  rw [hstart bi L hL] at hrun
  have hge : ctx.valDef.size ≤ sl.st.nextVreg := hN ▸ ((hord bi L hL).stmt j sl hsl).1
  obtain ⟨-, hout⟩ := hS _ info stm.inst _ _ _ _ hinf hic hge hrun
  have hne : info.results ≠ [] := by
    rw [hres]; intro h0; rw [h0] at hr; cases hr
  have he := hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)
  obtain ⟨h1, h2⟩ := hout hne _ rfl rs hrs p.2 c (by rw [hrse]; simp)
  have hes : emittedSince sl.st sl.st' = sl.st'.emitted.toList := by
    simp [emittedSince, he]
  rw [hes] at h2
  rcases h1 with h1 | h1
  · exact .inl h1
  · exact .inr ⟨_, _, _, ⟨bi, B, L, hB, hL, .inl ⟨j, sl, hsl, rfl, rfl, rfl, rfl⟩⟩, h1.1, h1.2,
      fun m hm hpm => h2 (asm_mem_killedL hm hpm)⟩

/-- **A renamed CLIF value's vreg is never killed** (`val_nk`, typed). -/
theorem val_nkT {x : Nat} (hx : x < ctx.valDef.size) : asmG f bl x ∉ killedOf vc := by
  intro hk
  obtain ⟨lo, mid, hi, c, m, hseg, hm, hkm, h1, h2⟩ :=
    killed_segT hd hs ha hb hlb hlf hvb hK hX hk
  have hlo := (seg_okT hd hs ha hb hlb hlf hK hX hseg).1
  rcases asm_gn_cases f bl x with e | ⟨p, hp, e⟩
  · rw [e] at h1; omega
  · rw [e] at h1 h2 hkm
    rcases alias_okT hd hs ha hb hlb hK hp with h3 | ⟨lo', hi', c', hseg', h3, h4, h5⟩
    · omega
    · have := asm_disj hlb hseg hseg' h1 h2 h3 h4
      subst this
      exact h5 m hm hkm

/-- **Part 1 of `killFreeB`**: no instruction reads a killed vreg (`uses_nk`, typed). -/
theorem uses_nkT {vb : VBlock} (hvb' : vb ∈ vc.blocks.toList) {i : MInst}
    (hi : i ∈ vb.insts.toList)
    {u : Nat} (hu : u ∈ useVregs i) : u ∉ killedOf vc := by
  rcases use_srcT hd hs ha hb hlb hlf hvb hK hX hvb' hi hu with ⟨x, hx, rfl⟩ |
      ⟨lo, mid, hi', c, hseg, h1, h2, h3⟩
  · exact val_nkT hd hs ha hb hlb hlf hvb hK hX hx
  · intro hk
    obtain ⟨lo', mid', hi'', c', m, hseg', hm, hkm, h1', h2'⟩ :=
      killed_segT hd hs ha hb hlb hlf hvb hK hX hk
    have hlm := (seg_okT hd hs ha hb hlb hlf hK hX hseg).2.1
    have := asm_disj hlb hseg hseg' (by omega) h2 h1' h2'
    subst this
    exact h3 m hm hkm

/-! ## A `try_call`'s block -/

omit hvb in
/-- **A `try_call`'s terminator segment** (`try_facts`, typed; the vreg numbers are the
integer ones). -/
theorem try_factsT {bi : Nat} {B : Clif.Block} {L : BLow} {et : Clif.ExnTable}
    (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L) (het : IsTryWith B.term et) :
    ∃ T ys cl, L.tl = some T ∧
      fixTry L.tl L.tst'.emitted.toList = ys ++ [.tryCall cl T.info] ∧
      cl.defs = callDefs (outDefs L.tst.nextVreg (max (sigRets T.sig).length 2)) ∧
      (∀ m ∈ ys, ∀ k ∈ unstored m, T.st1.nextVreg ≤ k) ∧
      T.regs = ((List.range (sigRets T.sig).length).map
        (fun j => Reg.vreg (L.tst.nextVreg + j) .int),
        [.vreg L.tst.nextVreg .int, .vreg (L.tst.nextVreg + 1) .int]) ∧
      T.st1.nextVreg = L.tst.nextVreg + max (sigRets T.sig).length 2 ∧
      T.st1.nextVreg ≤ L.tst'.nextVreg ∧ ctx.valDef.size ≤ L.tst.nextVreg ∧
      tryInfoOf T.sig T.items L.targets = some T.info ∧
      L.targets.length = et.dests.length ∧ L.targets.Nodup := by
  obtain ⟨-, -, hY⟩ := hK f ctx ranges st0 hd hs ha hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  obtain ⟨hord, -⟩ := driver_ord hlb
  have hN : st0.nextVreg = ctx.valDef.size := hcf.size.1
  obtain ⟨-, -, -, nl0, nl', hterm⟩ := hspec bi B L hB hL
  have hph := hcf.term bi B hB
  rw [← hstart bi L hL] at hph
  have hti := (Array.getElem?_eq_some_iff.mp hph).1
  have hge : ctx.valDef.size ≤ L.tst.nextVreg := hN ▸ (hord bi L hL).term.1
  obtain ⟨-, hy⟩ := lowTerm_spec hterm
  obtain ⟨T, hT', hdat, hex, htt, hreg, hinfo, out, tr, hc⟩ := hy et het
  have hBt : ∃ B' ∈ f.blocks, B'.term = B.term := ⟨B, List.mem_of_getElem? hB, rfl⟩
  obtain ⟨hk, -⟩ := hY _ _ _ _ _ _ _ _ _ _ _ _ _ hti hph het hBt hdat hex hge hreg hc
  have hdefs := hX f ctx ranges st0 hd hs ha hb _ _ _ _ _ _ _ _ _ _ _ _ _ hti hph het hBt hdat
    hex hge hreg hc
  obtain ⟨h1, -⟩ := asm_runKill hk rfl
  obtain ⟨-, htrs, hst1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc hex) hreg
  have hmono : T.st1.nextVreg ≤ L.tst'.nextVreg := (runTerm_mono hc).1
  obtain ⟨cl, hcl⟩ := hlf.tryLast bi B L T hB hL hT'
  rw [← back_toList] at hcl
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hcl
  have hD := hdefs (.call cl) (by rw [hys]; simp) cl rfl
  have hcode : fixTry L.tl L.tst'.emitted.toList = ys ++ [.tryCall cl T.info] := by
    rw [hT']
    show tryFix T.info _ = _
    rw [hys, tryFix_append]
  refine ⟨T, ys, cl, hT', hcode, hD, fun m hm k hkm => ?_, htrs, hst1, hmono, hge, hinfo,
    by rw [(tryTargets_spec htt).1, List.length_range'],
    by rw [(tryTargets_spec htt).1]; exact List.nodup_range'⟩
  exact (h1 m (by rw [hys]; exact List.mem_append_left _ hm) k hkm).1

end Assemble

/-! ## Branch arguments -/

section Edges
variable {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
  {bl : List BLow} {vc : VCode} {S : Clif.Function → Prop}
  (hd : Dominated f) (hs : S f) (ha : AbiSigsOk f)
  (hb : buildCtx f = .ok (ctx, ranges, st0))
  (hlb : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
    some bl)
  (hlf : LoopFactsT f ctx bl) (hvb : vc.blocks = vcBlocksOfT f ctx bl)
  (hK : KillRunsHypP S) (hX : TryDefsExactP S)
  (H : LowT f vc ctx st0 bl (asmR f bl)) (hv : LowOk vc)
include hd hs ha hb hlb hlf hvb hK hX H hv

/-- **A `try_call`'s edge block** passes a value's vreg (never killed) or a result vreg, which
its entry stores store when killed (the edge block kills nothing); `try_edge_ok`, typed: the
value arguments are vregs of their values' classes (`tryEdgeArgT`), the result/payload
arguments the integer vregs `L.tst.nextVreg + i`. -/
theorem try_edge_okT {succs preds : Array (Array Nat)} (hc : vc.cfg = .ok (succs, preds))
    {bi : Nat} {B : Clif.Block} {L : BLow} {et : Clif.ExnTable}
    (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L) (het : IsTryWith B.term et)
    {e : VBlock} (he : e ∈ edgeBlocksT f ctx B L) {a : Reg}
    (ha' : a ∈ (fixBlock (asmR f bl) e).branchArgs.toList) :
    (!(killedOf vc).contains a.homeNum ||
      ((entryStored vc succs preds e.label).contains a.homeNum &&
        (fixBlock (asmR f bl) e).insts.toList.all fun i => !(unstored i).contains a.homeNum)) =
      true := by
  have hg := asm_ren f bl
  have he0 := he
  obtain ⟨T, ys, cl, hT, hcode, hD, hys, hregs, hst1, hmono, hge, hinfo, htlen, htnd⟩ :=
    try_factsT hd hs ha hb hlb hlf hK hX hB hL het
  rw [shape_edgeBlocksT_try het hT] at he
  obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.mp he
  simp only [edgeOfTryT] at hpe
  obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.mp hpe
  obtain ⟨k, hk, hpk⟩ := List.getElem_of_mem hp
  have hzk : (et.dests.zip L.targets)[k]? = some p := by rw [List.getElem?_eq_getElem hk, hpk]
  obtain ⟨hdk, htk⟩ := List.getElem?_zip_eq_some.mp hzk
  obtain ⟨T', hT'', hargs⟩ := hlf.tryArgs bi B L et hB hL het
  rw [hT] at hT''
  cases hT''
  obtain ⟨-, hai⟩ := hargs k p.1 hdk
  simp only [fixBlock, Array.toList_map, List.map_map, List.mem_map,
    Function.comp_def] at ha'
  obtain ⟨ta, hta, rfl⟩ := ha'
  have hok := hai ta hta
  -- a result vreg `lo + i`
  have key : ∀ i, i < max (sigRets T.sig).length 2 →
      (k = et.handlers.length → i < (sigRets T.sig).length) →
      (!(killedOf vc).contains (L.tst.nextVreg + i) ||
        ((entryStored vc succs preds p.2).contains (L.tst.nextVreg + i) &&
          (#[MInst.jump tl].map (MInst.mapRegs (asmR f bl))).toList.all fun i' =>
            !(unstored i').contains (L.tst.nextVreg + i))) = true := by
    intro i hiM hin
    cases hkc : (killedOf vc).contains (L.tst.nextVreg + i)
    · rfl
    have hkm : L.tst.nextVreg + i ∈ killedOf vc := by simpa using hkc
    obtain ⟨lo', mid', hi', c', m, hseg', hm, hkm', h1', h2'⟩ :=
      killed_segT hd hs ha hb hlb hlf hvb hK hX hkm
    have hsegT : Seg f bl L.tst.nextVreg T.st1.nextVreg L.tst'.nextVreg
        (ys ++ [.tryCall cl T.info]) :=
      ⟨bi, B, L, hB, hL, .inr ⟨rfl, rfl, by rw [hT], by rw [hcode]⟩⟩
    have := asm_disj hlb hseg' hsegT h1' h2' (by omega) (by omega)
    subst this
    have hm' : m = .tryCall cl T.info := by
      rcases List.mem_append.mp hm with hm | hm
      · have := hys m hm _ hkm'; omega
      · simpa using hm
    subst hm'
    obtain ⟨ops, hops, -⟩ := asm_unstored_sub hkm'
    have hvbt := H.raw_at hB
    have hlast : (fixTry L.tl L.tst'.emitted.toList).getLast? = some (.tryCall cl T.info) := by
      rw [hcode]; simp
    have hback := raw_backT_of (f := f) (ctx := ctx) (RR := asmR f bl) (x := bi) (B := B) hL hlast
    obtain ⟨c', hc'⟩ : ∃ c', (MInst.tryCall cl T.info).mapRegs (asmR f bl) = .tryCall c' T.info :=
      ⟨_, rfl⟩
    rw [hc'] at hback
    have hops' : (MInst.tryCall c' T.info).operands = .ok (ops.map (rnOp (asmG f bl))) := by
      rw [← hc', operands_mapRegs hg, hops]; rfl
    have hfD : ∀ q ∈ outDefs L.tst.nextVreg (max (sigRets T.sig).length 2),
        asmG f bl q.2 = q.2 := by
      intro q hq
      simp only [outDefs, List.mem_map, List.mem_range] at hq
      obtain ⟨j, -, rfl⟩ := hq
      exact asm_fix bl hb (by simp only; omega)
    have hD0 : ops.toList.filter (·.kind == .def) =
        callDefOps (outDefs L.tst.nextVreg (max (sigRets T.sig).length 2)) := by
      rw [operands_tryCall_call] at hops
      exact asm_call_defs hD hops
    have hD' : (ops.map (rnOp (asmG f bl))).toList.filter (·.kind == .def) =
        callDefOps (outDefs L.tst.nextVreg (max (sigRets T.sig).length 2)) := by
      rw [asm_filter_map_rn, hD0, asm_callDefOps_rn _ _ hfD]
    have hte := asm_termEdge_try hback hops' hD' k
    -- the CFG
    have hbl : bi < vc.blocks.size := (Array.getElem?_eq_some_iff.mp hvbt).1
    obtain ⟨ss, hss⟩ := cfg_succs_some hc hbl
    have hsst := asm_succs hv hc hvbt hback hss
    rw [tryInfo_targets hinfo c'] at hsst
    obtain ⟨-, hat⟩ := H.edge_at hB hL he0
    have hsz : p.2 < vc.blocks.size := (Array.getElem?_eq_some_iff.mp hat).1
    have hidx : List.idxOf? p.2 ss.toList = some k := by rw [hsst]; exact asm_idxOf htnd htk
    have hj0 : ss[k]? = some p.2 := by rw [← Array.getElem?_toList, hsst]; exact htk
    have htk' : (MInst.tryCall c' T.info).targets[k]? = some p.2 := by
      rw [tryInfo_targets hinfo c']; exact htk
    have hu : ∀ (q : Nat) (sq : Array Nat) (j : Nat), succs[q]? = some sq → sq[j]? = some p.2 →
        q = bi ∧ j = k := by
      intro q sq j hq hj
      have hql : q < vc.blocks.size := by
        rw [← (Prep.cfg_spec hc).size]; exact (Array.getElem?_eq_some_iff.mp hq).1
      obtain ⟨t', ht', -⟩ := cfg_last hc (Array.getElem?_eq_getElem hql)
      have hsq := asm_succs hv hc (Array.getElem?_eq_getElem hql) ht' hq
      have htj : t'.targets[j]? = some p.2 := by rw [← hsq, Array.getElem?_toList]; exact hj
      exact hv.tryUniq bi _ c' T.info k p.2 hvbt hback htk' q _ t' j
        (Array.getElem?_eq_getElem hql) ht' htj
    have hpreds : preds[p.2]? = some #[bi] := preds_one hc hsz hss hj0 hu
    -- the stored vregs
    have hhl : T.info.handlers.length = et.handlers.length := by
      unfold tryInfoOf at hinfo
      split at hinfo
      · cases hinfo
      · rename_i hlen
        rw [← Option.some.inj hinfo]
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
        simp only [List.length_map, List.length_zip]
        have : et.dests.length = et.handlers.length + 1 := by simp [Clif.ExnTable.dests]
        omega
    have hrets : T.info.rets = (sigRets T.sig).length := by
      unfold tryInfoOf at hinfo
      split at hinfo
      · cases hinfo
      · rw [← Option.some.inj hinfo]
    have hmem : L.tst.nextVreg + i ∈
        (termEdgeDefs (fixBlock (asmR f bl) (rawBlockT f ctx bl bi B)) k).map (·.1.vreg) := by
      rw [hte, asm_outDefs_vregs]
      split
      · rename_i hkh
        rw [hrets]
        have hin' := hin (by rw [← hhl]; exact hkh)
        rw [← List.map_take, List.take_range, List.mem_map]
        exact ⟨i, List.mem_range.mpr (by omega), rfl⟩
      · exact List.mem_map.mpr ⟨i, List.mem_range.mpr hiM, rfl⟩
    have hes : (entryStored vc succs preds p.2).contains (L.tst.nextVreg + i) = true := by
      rw [entryStored_one hpreds, hvbt, hss]
      simp only
      rw [hidx]
      simpa using hmem
    have hall : ((#[MInst.jump tl].map (MInst.mapRegs (asmR f bl))).toList.all fun i' =>
        !(unstored i').contains (L.tst.nextVreg + i)) = true := by
      simp [MInst.mapRegs, (asm_jump tl).1]
    rw [hes, hall]
    rfl
  have hfixR : ∀ i, (asmR f bl (.vreg (L.tst.nextVreg + i) .int)).homeNum = L.tst.nextVreg + i := by
    intro i
    rw [hg.vreg, asm_fix bl hb (by omega)]
    rfl
  cases ta with
  | val v =>
    have hvlt : v < ctx.valDef.size := by
      have hcf := ctxFacts_of hb
      simp only [Ctx.valueReg?] at hok
      cases hh : ctx.valReg[v]? with
      | none => rw [hh] at hok; cases hok
      | some _ => rw [← hcf.size.2.1]; exact (Array.getElem?_eq_some_iff.mp hh).1
    have hnk := val_nkT hd hs ha hb hlb hlf hvb hK hX hvlt
    have e : (killedOf vc).contains
        (asmR f bl (tryEdgeArgT ctx T.regs.1 T.regs.2 (.val v))).homeNum = false := by
      show (killedOf vc).contains (asmR f bl (vregOf ctx v)).homeNum = false
      have hv' : vregOf ctx v = .vreg v (valClassOf ctx v) := rfl
      rw [hv', hg.vreg]
      simpa [Reg.homeNum] using hnk
    rw [e]
    rfl
  | ret i =>
    obtain ⟨hkh, hil⟩ := hok
    rw [hregs] at hil
    simp only [List.length_map, List.length_range] at hil
    have e : tryEdgeArgT ctx T.regs.1 T.regs.2 (.ret i) = .vreg (L.tst.nextVreg + i) .int := by
      simp [tryEdgeArgT, hregs, hil]
    rw [e, hfixR]
    exact key i (by omega) (fun _ => hil)
  | exn i =>
    obtain ⟨hkh, hil⟩ := hok
    rw [hregs] at hil
    simp only [List.length_cons, List.length_nil] at hil
    have e : tryEdgeArgT ctx T.regs.1 T.regs.2 (.exn i) = .vreg (L.tst.nextVreg + i) .int := by
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp [tryEdgeArgT, hregs]
    rw [e, hfixR]
    exact key i (by omega) (fun h => absurd h hkh)


/-- **A block's branch arguments** meet `killFreeB`'s second condition (`args_ok`, typed). -/
theorem args_okT {succs preds : Array (Array Nat)} (hc : vc.cfg = .ok (succs, preds)) {b : Nat}
    {vb : VBlock} (hvbb : vc.blocks[b]? = some vb) {a : Reg} (ha' : a ∈ vb.branchArgs.toList) :
    (!(killedOf vc).contains a.homeNum ||
      ((entryStored vc succs preds b).contains a.homeNum &&
        vb.insts.toList.all fun i => !(unstored i).contains a.homeNum)) = true := by
  have hg := asm_ren f bl
  -- a value's vreg (of any class)
  have val : ∀ y c, ctx.valueReg? y = some (.vreg y c) → a = asmR f bl (.vreg y c) →
      (!(killedOf vc).contains a.homeNum ||
        ((entryStored vc succs preds b).contains a.homeNum &&
          vb.insts.toList.all fun i => !(unstored i).contains a.homeNum)) = true := by
    intro y c hy e
    have hnk := val_nkT hd hs ha hb hlb hlf hvb hK hX (asm_valueReg_lt hb hy)
    have : (killedOf vc).contains a.homeNum = false := by
      rw [e, hg.vreg]; simpa [Reg.homeNum] using hnk
    rw [this]; rfl
  rcases H.cases hvbb with ⟨B, L, -, hB, hL, rfl⟩ | ⟨bi, B, L, e, hB, hL, he, hel, -, rfl⟩
  · have hBm := List.mem_of_getElem? hB
    simp only [fixBlock, rawBlockT] at ha'
    split at ha'
    · rename_i bc hj
      simp only [Array.toList_map, List.map_map, List.mem_map,
        Function.comp_def] at ha'
      obtain ⟨y, hy, rfl⟩ := ha'
      obtain ⟨-, -, -, hvals⟩ := hlf.args B hBm bc (by rw [hj]; simp [dests])
      exact val y _ (hvals y hy) rfl
    · simp at ha'
  · subst hel
    rcases try_or B.term with ht | ⟨et, het⟩
    · by_cases hj : ∃ bc, B.term = .jump bc
      · obtain ⟨bc, hj⟩ := hj
        rw [edgeBlocks_jumpT L hj] at he
        cases he
      · have hj' : ∀ bc, B.term ≠ .jump bc := fun bc e => hj ⟨bc, e⟩
        have he' := he
        rw [shape_edgeBlocksT_other ht hj'] at he'
        obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp he'
        simp only [edgeOfBcT] at hqe
        split at hqe
        · cases hqe
        obtain ⟨tl, -, rfl⟩ := Option.map_eq_some_iff.mp hqe
        have hbc : q.1 ∈ dests B.term := (List.of_mem_zip hq).1
        simp only [fixBlock, Array.toList_map, List.map_map, List.mem_map,
          Function.comp_def] at ha'
        obtain ⟨y, hy, rfl⟩ := ha'
        obtain ⟨-, -, -, hvals⟩ := hlf.args B (List.mem_of_getElem? hB) q.1 hbc
        exact val y _ (hvals y hy) rfl
    · exact try_edge_okT hd hs ha hb hlb hlf hvb hK hX H hv hc hB hL het he ha'

end Edges

/-! ## The theorem -/

/-- **`lowerFunction`'s VCode passes `killFreeB`** on typed-scope input, given the killed-vreg
facts of the ISLE runs (`KillRunsHypT`) and the exact defs of a `try_call`'s call
(`TryDefsExactT`). -/
theorem killFreeB_lowerT (hK : KillRunsHypT) (hX : TryDefsExactT) {f : Clif.Function} {vc : VCode}
    (hd : Dominated f) (hs : LowerScopeT f) (ha : AbiSigsOk f) (har : ArityOk f)
    (htc : Compile.tryArgClassOk f = true)
    (hl : lowerFunction f = .ok vc) : killFreeB vc = true := by
  obtain ⟨ctx, ranges, st0, bl, hb, hlb, hvb, -, hlf⟩ := lowerFunction_runT hs.externsE hl
  have H : LowT f vc ctx st0 bl (asmR f bl) := by
    have hlb' := hlb
    rw [lowBlocks_eq] at hlb'
    cases hr : lowB f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length with
    | none => rw [hr] at hlb'; cases hlb'
    | some r =>
      rw [hr] at hlb'
      obtain ⟨bl', stE, nlE⟩ := r
      cases hlb'
      exact ⟨⟨ranges, hb⟩, ⟨stE, nlE, hr⟩, by rw [hvb]; simp [vcBlocksOfT],
        ⟨_, asm_ren f bl'⟩, hlf, (lowBlocks_spec hlb).1⟩
  have hv := lowOk_ofT hd hs har htc hl
  unfold killFreeB
  simp only [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · refine List.all_eq_true.mpr fun vb hvb' => List.all_eq_true.mpr fun i hi =>
      List.all_eq_true.mpr fun u hu => ?_
    have := uses_nkT hd hs ha hb hlb hlf hvb hK hX hvb' hi hu
    simpa using this
  · split
    · rfl
    · rename_i succs preds hc
      refine List.all_eq_true.mpr fun b _ => ?_
      split
      · rfl
      · rename_i vb hvbb
        exact List.all_eq_true.mpr fun a ha' =>
          args_okT hd hs ha hb hlb hlf hvb hK hX H hv hc hvbb ha'

/-- **`lowerFunction`'s VCode passes `killFreeB`** on float-scope input (`killFreeB_lowerT` over
`LowerScopeTF`, with the float-scope run facts `killRunsHypTF`, `tryDefsExactTF`). -/
theorem killFreeB_lowerTF (hK : KillRunsHypTF) (hX : TryDefsExactTF) {f : Clif.Function}
    {vc : VCode} (hd : Dominated f) (hs : LowerScopeTF f) (ha : AbiSigsOk f) (har : ArityOk f)
    (htc : Compile.tryArgClassOk f = true)
    (hl : lowerFunction f = .ok vc) : killFreeB vc = true := by
  obtain ⟨ctx, ranges, st0, bl, hb, hlb, hvb, -, hlf⟩ := lowerFunction_runT hs.externsE hl
  have H : LowT f vc ctx st0 bl (asmR f bl) := by
    have hlb' := hlb
    rw [lowBlocks_eq] at hlb'
    cases hr : lowB f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length with
    | none => rw [hr] at hlb'; cases hlb'
    | some r =>
      rw [hr] at hlb'
      obtain ⟨bl', stE, nlE⟩ := r
      cases hlb'
      exact ⟨⟨ranges, hb⟩, ⟨stE, nlE, hr⟩, by rw [hvb]; simp [vcBlocksOfT],
        ⟨_, asm_ren f bl'⟩, hlf, (lowBlocks_spec hlb).1⟩
  have hv := lowOk_ofTF hd hs har htc hl
  unfold killFreeB
  simp only [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · refine List.all_eq_true.mpr fun vb hvb' => List.all_eq_true.mpr fun i hi =>
      List.all_eq_true.mpr fun u hu => ?_
    have := uses_nkT hd hs ha hb hlb hlf hvb hK hX hvb' hi hu
    simpa using this
  · split
    · rfl
    · rename_i succs preds hc
      refine List.all_eq_true.mpr fun b _ => ?_
      split
      · rfl
      · rename_i vb hvbb
        exact List.all_eq_true.mpr fun a ha' =>
          args_okT hd hs ha hb hlb hlf hvb hK hX H hv hc hvbb ha'

end Backend.Proof.Kill

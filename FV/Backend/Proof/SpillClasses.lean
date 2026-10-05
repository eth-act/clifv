import FV.Backend.Proof.SpillClsChain
import FV.Backend.Proof.SpillLocalPipe

/-!
# `ClassesHyp`: every vreg of the pipeline's code has the class `classes` records (V4)

`lowerFunction`'s classes are its final lowering state's: the values' int vregs, then one class
per fresh vreg. Every ISLE call keeps its emitted instructions to registers of their classes
(`stmt_cls`, `termCall_cls`, `tryCall_cls`), and so do the driver's own instructions (`Args`,
parameter loads, result `mov`s, `jump`s, the `tryCall`); the alias resolution keeps classes (an
alias goes from an int value to an int vreg, `stmt_cov`), so the renamed code meets `InstCls`.
Block parameters are int value vregs, branch arguments renamed int value vregs or `try_call`
vregs. `prepare` keeps blocks, retargets terminators and adds `jump` blocks, and keeps the
classes (`classesOkM_prepare`).
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Driver Isle

/-- `ClassesOk` by membership. -/
def ClassesOkM (vc : VCode) : Prop :=
  (∀ vb ∈ vc.blocks.toList, ∀ m ∈ vb.insts.toList, InstCls vc.classes m) ∧
  ∀ vb ∈ vc.blocks.toList, ∀ r ∈ vb.params.toList ++ vb.branchArgs.toList,
    ∃ n c, r = .vreg n c ∧ vc.classes[n]? = some c

theorem classesOk_of {vc : VCode} (h : ClassesOkM vc) : ClassesOk vc :=
  ⟨fun _ vb _ i ops hvb hi hops o ho =>
    h.1 vb (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hvb)) i
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)) ops hops o ho,
   fun _ vb hvb r hr => h.2 vb (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hvb)) r hr⟩

/-! ## `prepare` -/

theorem classesOkM_prepare {vc vcp : VCode} (h : prepare vc = .ok vcp) (hd : Prep.PrepDomain vc)
    (hc : ClassesOkM vc) : ClassesOkM vcp := by
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl⟩ := Prep.prepare_facts h
  have cs0 := Prep.cfg_spec hc0
  have cs2 : Prep.CfgSpec (B ++ E) ss2 := Prep.cfg_spec hc2
  refine ⟨fun vb hvb i hi => ?_, fun vb hvb r hr => ?_⟩
  · rcases Prep.insts3 hd cs0 cs2 hS hvb hi with ⟨vb0, hvb0, hi0⟩ | ⟨vb0, hvb0, i0, hi0, ls, hset⟩ | ⟨l, rfl⟩
    · exact hc.1 vb0 hvb0 i hi0
    · intro ops hops
      obtain ⟨h1, -, -, -⟩ := Driver.setTargets_facts hset
      exact hc.1 vb0 hvb0 i0 hi0 ops (h1.symm.trans hops)
    · intro ops hops o ho
      cases hops
      simp at ho
  · obtain ⟨-, -, -, -, -, hR, -, -, -, -⟩ := Prep.facts_basic hd cs0 cs2 hS
    rw [Array.mem_toList_iff, Array.mem_map] at hvb
    obtain ⟨i, hiR, rfl⟩ := hvb
    have hi2 : i < (B ++ E).size := hR i (by simpa using hiR)
    rw [getElem!_pos (B ++ E) i hi2] at hr
    by_cases hiB : i < B.size
    · rw [Array.getElem_append_left hiB] at hr
      have hi1 : i < (Prep.keep vc.blocks (reachable ss0)).size := by rw [← hS.size]; exact hiB
      obtain ⟨b, hb, e, -⟩ := Prep.keep_src hi1
      have hmem : (Prep.keep vc.blocks (reachable ss0))[i] ∈ vc.blocks.toList := by rw [e]; simp
      obtain ⟨-, hp, hba⟩ := Prep.rw_fields (hS.rw i hi1 hiB)
      rw [hp, hba] at hr
      exact hc.2 _ hmem r hr
    · rw [Array.getElem_append_right (Nat.le_of_not_lt hiB)] at hr
      have he : i - B.size < E.size := by simp at hi2; omega
      obtain ⟨l, hl⟩ := hS.edges _ he
      rw [hl] at hr
      simp at hr

/-! ## The driver's instructions -/

theorem fixTry_mem {T : Option TryLow} {ms : List MInst} {m : MInst} (h : m ∈ fixTry T ms) :
    m ∈ ms ∨ ∃ c ti, m = .tryCall c ti ∧ MInst.call c ∈ ms := by
  unfold fixTry at h
  split at h
  · unfold tryFix at h
    split at h
    · rename_i c hl
      simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact .inl (List.dropLast_subset _ h)
      · exact .inr ⟨_, _, rfl, List.mem_of_getLast? hl⟩
    · exact .inl h
  · exact .inl h

theorem regsFrom_tryCall {P : Reg → Prop} {c : CallInfo} {ti : TryInfo} (h : RegsFrom P (.call c)) :
    RegsFrom P (.tryCall c ti) := by
  intro g hg
  have := h g hg
  simp only [MInst.mapRegs, MInst.call.injEq] at this
  simp only [MInst.mapRegs, this]

theorem args_regsFrom {P : Reg → Prop} {ds : List (Reg × Reg)} (h : ∀ q ∈ ds, P q.1) :
    RegsFrom P (.args ds) := by
  intro g hg
  simp only [MInst.mapRegs, MInst.args.injEq]
  conv => rhs; rw [← List.map_id ds]
  exact List.map_congr_left fun x hx => by rw [hg x.1 (h x hx)]; rfl

theorem zip_idx {α β : Type} {as : List α} {bs : List β} {a : α} {b : β} (h : (a, b) ∈ as.zip bs) :
    ∃ i : Nat, as[i]? = some a ∧ bs[i]? = some b := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  rw [List.getElem?_zip_eq_some] at hi
  exact ⟨i, hi⟩

theorem mem_valueDefs_param {f : Clif.Function} {B : Clif.Block} (hB : B ∈ f.blocks) {p : Clif.ValueId × Clif.Ty}
    (hp : p ∈ B.params) : p.1 ∈ valueDefs f := by
  simp only [valueDefs, List.mem_flatMap, List.mem_append, List.mem_map]
  exact ⟨B, hB, .inl ⟨p, hp, rfl⟩⟩

theorem mem_valueDefs_result {f : Clif.Function} {B : Clif.Block} (hB : B ∈ f.blocks) {stm : Clif.Stmt}
    (hs : stm ∈ B.body) {r : Nat} (hr : r ∈ stm.results) : r ∈ valueDefs f := by
  simp only [valueDefs, List.mem_flatMap, List.mem_append, List.mem_map]
  exact ⟨B, hB, .inr ⟨stm, hs, hr⟩⟩

/-- The shape of an edge block. -/
theorem edgeBlocks_shape {f : Clif.Function} {B : Clif.Block} {L : BLow} {e : VBlock}
    (h : e ∈ edgeBlocks f B L) : (∃ tl, e.insts = #[.jump tl]) ∧ e.params = #[] ∧
    ∀ r ∈ e.branchArgs.toList, (∃ bc ∈ dests B.term, ∃ a ∈ bc.args, Reg.vreg a .int = r) ∨
      (∃ et T, IsTryWith B.term et ∧ L.tl = some T ∧ ∃ td ∈ et.dests, ∃ a ∈ td.args,
        tryEdgeArg T.regs.1 T.regs.2 a = r) := by
  unfold edgeBlocks at h
  split at h
  · rename_i fn args et T hBt hT
    simp only [List.mem_filterMap, Option.map_eq_some_iff] at h
    obtain ⟨⟨td, l⟩, hp, tl, -, rfl⟩ := h
    refine ⟨⟨tl, rfl⟩, rfl, fun r hr => .inr ⟨et, T, .inl ⟨_, _, hBt⟩, hT, td, (List.of_mem_zip hp).1, ?_⟩⟩
    simpa using hr
  · rename_i fn args et T hBt hT
    simp only [List.mem_filterMap, Option.map_eq_some_iff] at h
    obtain ⟨⟨td, l⟩, hp, tl, -, rfl⟩ := h
    refine ⟨⟨tl, rfl⟩, rfl, fun r hr => .inr ⟨et, T, .inr ⟨_, _, hBt⟩, hT, td, (List.of_mem_zip hp).1, ?_⟩⟩
    simpa using hr
  · simp at h
  · rename_i t _ _ _
    simp only [List.mem_filterMap] at h
    obtain ⟨⟨bc, l⟩, hp, h⟩ := h
    split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨tl, -, rfl⟩ := h
      refine ⟨⟨tl, rfl⟩, rfl, fun r hr => .inl ⟨bc, (List.of_mem_zip hp).1, ?_⟩⟩
      simpa using hr

/-! ## The lowering -/

theorem clsIs_termCtx {ctx : Ctx} {s0 s : LState} (h : ClsIs ctx s0 s) (ti : Nat) (data : V) :
    ClsIs (termCtx ctx ti data) s0 s := ⟨h.sz, h.vals, h.try1, h.try2, h.emitted⟩

/-- **`lowerFunction`'s VCode** meets `ClassesOkM`. -/
theorem classesOkM_lower {f : Clif.Function} {vc : VCode} (hs : LowerScope f)
    (h : lowerFunction f = .ok vc) : ClassesOkM vc := by
  obtain ⟨ctx, ranges, st0, bl, hb, hl, hvb, -, hlf⟩ := lowerFunction_run h
  obtain ⟨ctx', ranges', st0', pb, d, blk, hb', -, hI, hvc⟩ := loop_run h
  rw [hb] at hb'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
  obtain ⟨rfl, rfl, rfl⟩ := hb'
  have hlow := hI.low
  rw [List.take_of_length_le (Nat.le_refl _)] at hlow
  have hblk : bl = blk := by
    have := lowBlocks_eq f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) f.blocks 0 st0 f.blocks.length
    rw [hl, hlow] at this
    exact Option.some.inj this
  subst hblk
  have hcls : vc.classes = d.st.classes := by rw [hvc]; rfl
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  have hcl : Cov.Clean ctx := Cov.clean_of_build hb
  have hsp := ctxSpec_of hb
  have hcf := hsp.facts
  obtain ⟨-, hstart⟩ := lowBlocks_start hl
  obtain ⟨-, hspec⟩ := lowBlocks_spec hl
  have hemp := lowBlocks_emptied hl
  obtain ⟨hfin, hLs⟩ := lowB_chain (stepsCls_driver ctx) f.blocks 0 st0 f.blocks.length bl d.st _ hlow
  have hsz0 : Sz st0 := by rw [hsp.st0]; simp [Sz]
  have hval0 : ∀ x r, ctx.valueReg? x = some r → RegCls st0.classes r := by
    intro x r hx
    have hr := hctx.valueReg x r hx
    subst hr
    have hxl : x < ctx.valReg.size := by
      unfold Ctx.valueReg? at hx
      cases h' : ctx.valReg[x]? with
      | none => rw [h'] at hx; cases hx
      | some _ => exact (Array.getElem?_eq_some_iff.mp h').1
    rw [hsp.st0, regCls_vreg]
    rw [hcf.size.2.1] at hxl
    simp [Array.getElem?_replicate, hxl]
  have hIs : ∀ s, ClsStep st0 s → ClsIs ctx s s := fun s hs0 =>
    ⟨sz_step hs0 hsz0, fun x r hx => regCls_step hs0 (hval0 x r hx),
     (fun r hr => by rw [hcf.tryRegs] at hr; cases hr), (fun r hr => by rw [hcf.tryRegs] at hr; cases hr),
     ⟨[], by simp, by simp⟩⟩
  have hvalF : ∀ x, x ∈ valueDefs f → RegCls d.st.classes (.vreg x .int) := fun x hx =>
    regCls_step hfin (hval0 x _ (hcf.vals x hx).2)
  -- statements
  have hstm : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
      f.blocks[bi]? = some B → bl[bi]? = some L →
      B.body[j]? = some stm → L.sl[j]? = some sl →
      (∀ m ∈ sl.st'.emitted.toList, RegsFrom (RegCls d.st.classes) m) ∧
      (stm.results ≠ [] → GoodV d.st.classes (.regsVec sl.rss) ∧
        ∀ rs ∈ sl.rss, ∀ r ∈ rs, ∃ n, r = .vreg n .int) := by
    intro bi B L j stm sl hB hL hj hsl
    obtain ⟨-, hc, -, -⟩ := hspec bi B L hB hL
    obtain ⟨info, hi, hic, hres⟩ := hcf.stmt bi B j stm hB hj
    obtain ⟨tr, hrun⟩ := hc j sl hsl
    rw [hstart bi L hL] at hrun
    have hLm := hLs L (List.mem_of_getElem? hL)
    have hslm := hLm.2.2.1 sl (List.mem_of_getElem? hsl)
    obtain ⟨hI', hout⟩ := stmt_cls hctx hcl hi hic hrun (hIs sl.st hslm.1)
    have hcov := (stmt_cov Cov.logicImmComplete hctx hcl hi hic hrun).2
    obtain ⟨ms, hms, hall⟩ := hI'.emitted
    rw [hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)] at hms
    refine ⟨fun m hm => ?_, fun hne => ⟨fun r hr => regCls_step hslm.2
      (hout _ rfl (by rw [hres]; exact hne) r hr), hcov _ rfl (by rw [hres]; exact hne)⟩⟩
    rw [hms] at hm
    exact (hall m (by simpa using hm)).mono fun r hr => regCls_step hslm.2 hr
  -- terminators
  have hterm : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
      (∀ m ∈ L.tst'.emitted.toList, RegsFrom (RegCls d.st.classes) m) ∧
      (∀ T, L.tl = some T → ∀ r ∈ T.regs.1 ++ T.regs.2, IntCls d.st.classes r) := by
    intro bi B L hB hL
    obtain ⟨-, -, htst, nl0, nl', hlt⟩ := hspec bi B L hB hL
    obtain ⟨hn, hy⟩ := lowTerm_spec hlt
    have hLm := hLs L (List.mem_of_getElem? hL)
    have hph : ctx.insts[L.start + B.body.length]? = some ⟨.op .unit, [], [], none⟩ := by
      rw [hstart bi L hL]; exact hcf.term bi B hB
    cases ht : B.term.isTry with
    | false =>
      obtain ⟨htl, hd, out, tr, hc⟩ := hn ht
      have hI2 := termCall_cls hctx hcl hph hd hc (clsIs_termCtx (hIs L.tst hLm.1) _ _)
      obtain ⟨ms, hms, hall⟩ := hI2.emitted
      rw [htst] at hms
      refine ⟨fun m hm => ?_, fun T hT => by rw [htl] at hT; cases hT⟩
      rw [hms] at hm
      exact (hall m (by simpa using hm)).mono fun r hr => regCls_step hLm.2.1 hr
    | true =>
      obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := by
        cases hB' : B.term <;> rw [hB'] at ht <;> simp [Clif.Terminator.isTry] at ht
        · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
        · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
      obtain ⟨T, hT, hd, -, -, hr, -, out, tr, hc⟩ := hy et het
      obtain ⟨-, hr1⟩ := tryRegsOf_cls hr
      have hst1 : ClsStep st0 T.st1 := hLm.2.2.2 T hT
      have hs1' : ClsStep T.st1 L.tst' := clsStep_trans (clsStep_clear _) (runTerm_cls hc)
      have hgoodT : ∀ r ∈ T.regs.1 ++ T.regs.2, IntCls T.st1.classes r := hr1 (sz_step hLm.1 hsz0)
      have hIs' : ClsIs (tryCtx ctx (L.start + B.body.length) L.data T.regs)
          { T.st1 with emitted := #[] } { T.st1 with emitted := #[] } :=
        ⟨sz_step hst1 hsz0, fun x r hx => regCls_step hst1 (hval0 x r hx),
         fun r hr' => (hgoodT r (List.mem_append_left _ hr')).1,
         fun r hr' => (hgoodT r (List.mem_append_right _ hr')).1, ⟨[], by simp, by simp⟩⟩
      have hI2 := tryCall_cls hcl hd hc hIs'
      obtain ⟨ms, hms, hall⟩ := hI2.emitted
      refine ⟨fun m hm => ?_, fun T' hT' r hr' => ?_⟩
      · rw [hms] at hm
        exact (hall m (by simpa using hm)).mono fun r hr => regCls_step hLm.2.1 hr
      · rw [hT] at hT'; cases hT'
        exact intCls_step (clsStep_trans hs1' hLm.2.1) (hgoodT r hr')
  -- the alias resolution keeps classes
  have halias : ∀ n o : Nat, ((aliasArr (aliasOf f bl))[n]?).join = some o →
      d.st.classes[n]? = some RegClass.int ∧ d.st.classes[o]? = some RegClass.int := by
    intro n o hno
    have hmem := (faithful_arr (aliasOf f bl)).some n o hno
    rw [aliasOf_eq] at hmem
    simp only [List.mem_flatMap, stmtAl, List.mem_filterMap] at hmem
    obtain ⟨⟨B, L⟩, hBL, ⟨stm, sl⟩, hss, ⟨r, rs⟩, hrrs, hm⟩ := hmem
    split at hm
    · rename_i out c' heq
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      obtain ⟨bi, hB, hL⟩ := zip_idx hBL
      obtain ⟨j, hj, hsl⟩ := zip_idx hss
      have hB' : B ∈ f.blocks := List.mem_of_getElem? hB
      have hrm : r ∈ stm.results := (List.of_mem_zip hrrs).1
      have hrss : rs ∈ sl.rss := (List.of_mem_zip hrrs).2
      subst heq
      have hne : stm.results ≠ [] := List.ne_nil_of_mem hrm
      obtain ⟨hg, hint⟩ := (hstm bi B L j stm sl hB hL hj hsl).2 hne
      obtain ⟨k, hk⟩ := hint _ hrss _ (List.mem_singleton_self _)
      cases hk
      refine ⟨regCls_vreg.mp (hvalF r (mem_valueDefs_result hB' (List.mem_of_getElem? hj) hrm)), ?_⟩
      exact regCls_vreg.mp (hg _ (by simp only [V.regsIn, List.mem_flatten]; exact ⟨_, hrss, List.mem_singleton_self _⟩))
    · cases hm
  have hR := resolve_cls halias ((aliasArr (aliasOf f bl)).size + 1)
  -- the raw code
  have hraw : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
      ∀ m ∈ (rawBlock f bl bi B).insts.toList, RegsFrom (RegCls d.st.classes) m := by
    intro bi B L hB hL m hm
    simp only [rawBlock, List.toList_toArray, List.mem_append, List.mem_flatten] at hm
    rcases hm with (hpre | ⟨sg, hsg, hm0⟩) | htseg
    · unfold pre at hpre
      split at hpre
      · rename_i B0 hB0
        have hB0m : B0 ∈ f.blocks := List.mem_of_getElem? hB0
        simp only [List.mem_cons] at hpre
        rcases hpre with rfl | hpre
        · refine args_regsFrom fun q hq => ?_
          simp only [entryRegs, List.mem_filterMap] at hq
          obtain ⟨q0, hq0, hq⟩ := hq
          unfold entryRegOf at hq
          split at hq
          · cases hq
            exact hvalF _ (mem_valueDefs_param hB0m (List.of_mem_zip (List.of_mem_zip hq0).1).1)
          · cases hq
        · simp only [entryLoads, List.mem_filterMap] at hpre
          obtain ⟨q, hq0, hq⟩ := hpre
          unfold entryLoadOf at hq
          split at hq
          · cases hq
            intro g hg
            simp [MInst.mapRegs, AMode.mapRegs,
              hg _ (hvalF _ (mem_valueDefs_param hB0m (List.of_mem_zip (List.of_mem_zip hq0).1).1))]
          · cases hq
      · simp at hpre
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hsg
      unfold seg at hm0
      rw [hB, hL] at hm0
      simp only at hm0
      split at hm0
      · rename_i stm sl hstm' hsl
        simp only [List.mem_map, mapRegs_id] at hm0
        obtain ⟨m1, hm1, rfl⟩ := hm0
        rcases List.mem_append.mp hm1 with hm1 | hm1
        · exact (hstm bi B L j stm sl hB hL hstm' hsl).1 m1 hm1
        · simp only [extraOf, List.mem_filterMap] at hm1
          obtain ⟨⟨r, rs⟩, hrrs, hq⟩ := hm1
          split at hq
          · cases hq
          · rename_i out hnv hout
            cases hq
            have hrv := hvalF r (mem_valueDefs_result (List.mem_of_getElem? hB) (List.mem_of_getElem? hstm')
              (List.of_mem_zip hrrs).1)
            have hreal : ∀ n c, out ≠ .vreg n c := fun n c he => hnv n c he
            intro g hg
            simp [MInst.mapRegs, hg _ hrv, hg _ (regCls_real hreal)]
          · cases hq
      · simp at hm0
    · unfold tseg at htseg
      rw [hL] at htseg
      simp only [List.mem_map, mapRegs_id] at htseg
      obtain ⟨m1, hm1, rfl⟩ := htseg
      have ht := (hterm bi B L hB hL).1
      rcases fixTry_mem hm1 with hm1 | ⟨c, ti, rfl, hc⟩
      · exact ht _ hm1
      · exact regsFrom_tryCall (ht _ hc)
  -- the final code
  unfold ClassesOkM
  rw [hvb, hcls]
  have hblocks : ∀ vb ∈ (vcBlocksOf f bl).toList, ∃ (vb0 : VBlock) (bi : Nat) (B : Clif.Block) (L : BLow),
      f.blocks[bi]? = some B ∧
      bl[bi]? = some L ∧ vb = fixBlock (lowerFunction.resolve (aliasArr (aliasOf f bl))
        ((aliasArr (aliasOf f bl)).size + 1)) vb0 ∧
      (vb0 = rawBlock f bl bi B ∨ vb0 ∈ edgeBlocks f B L) := by
    intro vb hvb'
    simp only [vcBlocksOf, List.toList_toArray, List.mem_map, List.mem_append, List.mem_flatMap] at hvb'
    obtain ⟨vb0, h1, rfl⟩ := hvb'
    rcases h1 with ⟨p, hp, rfl⟩ | ⟨p, hp, he⟩
    · have := List.mem_zipIdx_iff_getElem?.mp hp
      rw [List.getElem?_zip_eq_some] at this
      exact ⟨_, p.2, p.1.1, p.1.2, this.1, this.2, rfl, .inl rfl⟩
    · obtain ⟨bi, hB, hL⟩ := zip_idx (show (p.1, p.2) ∈ f.blocks.zip bl from hp)
      exact ⟨vb0, bi, p.1, p.2, hB, hL, rfl, .inr he⟩
  refine ⟨fun vb hvb' m hm => ?_, fun vb hvb' r hr => ?_⟩
  · obtain ⟨vb0, bi, B, L, hB, hL, rfl, hraw' | hedge⟩ := hblocks vb hvb'
    · simp only [fixBlock, Array.toList_map, List.mem_map] at hm
      obtain ⟨m0, hm0, rfl⟩ := hm
      subst hraw'
      exact instCls_mapRegs (hraw bi B L hB hL m0 hm0) hR
    · obtain ⟨⟨tl, htl⟩, -, -⟩ := edgeBlocks_shape hedge
      simp only [fixBlock, htl, Array.toList_map, List.mem_map] at hm
      obtain ⟨m0, hm0, rfl⟩ := hm
      simp at hm0
      subst hm0
      exact instCls_mapRegs (fun g _ => rfl) hR
  · obtain ⟨vb0, bi, B, L, hB, hL, rfl, hraw' | hedge⟩ := hblocks vb hvb'
    · subst hraw'
      have hB' : B ∈ f.blocks := List.mem_of_getElem? hB
      simp only [fixBlock, rawBlock, List.mem_append, Array.toList_map, List.mem_map] at hr
      rcases hr with hr | ⟨r0, hr0, rfl⟩
      · split at hr
        · simp at hr
        · simp only [List.toList_toArray, List.mem_map] at hr
          obtain ⟨p, hp, rfl⟩ := hr
          exact ⟨_, _, rfl, regCls_vreg.mp (hvalF _ (mem_valueDefs_param hB' hp))⟩
      · split at hr0
        · rename_i bc hBt
          simp only [List.mem_map] at hr0
          obtain ⟨a, ha, rfl⟩ := hr0
          obtain ⟨tb, -, -, hargs⟩ := hlf.args B hB' bc (by simp [hBt, dests])
          have hg := hR _ (regCls_step hfin (hval0 a _ (hargs a ha)))
          rw [resolve_vreg] at hg ⊢
          exact ⟨_, _, rfl, regCls_vreg.mp hg⟩
        · simp at hr0
    · obtain ⟨-, hp, hba⟩ := edgeBlocks_shape hedge
      have hB' : B ∈ f.blocks := List.mem_of_getElem? hB
      simp only [fixBlock, hp, Array.toList_map, List.mem_append, List.mem_map] at hr
      rcases hr with hr | ⟨r0, hr0, rfl⟩
      · simp at hr
      · have hg0 : IntCls d.st.classes r0 := by
          rcases hba r0 hr0 with ⟨bc, hbc, a, ha, rfl⟩ | ⟨et, T, het, hT, td, htd, a, ha, rfl⟩
          · obtain ⟨tb, -, -, hargs⟩ := hlf.args B hB' bc hbc
            exact ⟨regCls_step hfin (hval0 a _ (hargs a ha)), a, rfl⟩
          · obtain ⟨T', hT', hk⟩ := hlf.tryArgs bi B L et hB hL het
            rw [hT] at hT'; cases hT'
            obtain ⟨k, hk'⟩ := List.mem_iff_getElem?.mp htd
            have hka := (hk k td hk').2 a ha
            have hTg := (hterm bi B L hB hL).2 T hT
            cases a with
            | val v => exact ⟨regCls_step hfin (hval0 v _ hka), v, rfl⟩
            | ret i =>
              simp only [tryEdgeArg]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hka.2, Option.getD_some]
              exact hTg _ (List.mem_append_left _ (List.getElem_mem _))
            | exn i =>
              simp only [tryEdgeArg]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hka.2, Option.getD_some]
              exact hTg _ (List.mem_append_right _ (List.getElem_mem _))
        obtain ⟨n, rfl⟩ := hg0.2
        have hg := hR _ hg0.1
        rw [resolve_vreg] at hg ⊢
        exact ⟨_, _, rfl, regCls_vreg.mp hg⟩

/-- **`ClassesHyp`**: the prepared code's vreg classes are consistent. -/
theorem classesHyp : ClassesHyp := by
  intro f vc vcp _hd hs hl hp
  exact classesOk_of (classesOkM_prepare hp (prepDomain_of_lower hs hl hs.nonempty) (classesOkM_lower hs hl))

end Backend.Proof.Spill

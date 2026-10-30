import FV.Backend.Proof.SpillCtlShapeT
import FV.Backend.Proof.AbiClassRegs
import FV.Backend.Proof.EntryClass
import FV.Backend.Proof.LowerShapeOkT
import FV.Backend.Proof.LowerCompleteT

/-!
# `CtlSpillHyp` on the typed pipeline's output (S11 #35)

`ctlSpillHypT_of`: `ctlSpillHyp_of` (`SpillCtlPipe`) for the typed lowering. Given the typed
ISLE inversion `IselCtlHypT`, every control form of `lowerFunction f` meets `SpillInstOk`:

* the ISLE runs' control forms have the typed shapes (`CtlShapeT`, `spillInstOk_of_ctlShapeT`)
  with fresh defs, which the alias renaming fixes (`ctlShapeT_defs`);
* the entry block's `Args` is `spillInstOk_entryArgsT`: its parameters' vregs are distinct
  (SSA), not renamed (no parameter is an alias key), and of the class of the signature's
  parameter at their position: the block parameter's type (`CtxFacts.types`) has the class of
  the signature's (`EntryClassOk`, the CLIF verifier's entry-block typing);
* the `tryCall` replacing a `try_call` rule's last call has `clobberAll = false`, the edge
  blocks are a single `jump`, the entry loads and result `mov`s are not control forms.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Driver

/-- A typed control shape's defs are fresh (`≥ N`). -/
theorem ctlShapeT_defs {N : Nat} {m : MInst} (h : CtlShapeT N m) :
    ∀ ops, m.operands = .ok ops → ∀ o ∈ ops.toList, o.kind = .def → N ≤ o.vreg := by
  rcases h with h | ⟨ns, rfl, -, -⟩
  · exact ctlShape_defs h
  · intro ops hops o ho hd
    rw [operands_retsC] at hops
    cases hops
    simp only [retOpsC, List.toList_toArray, List.mem_map] at ho
    obtain ⟨q, -, rfl⟩ := ho
    cases hd

/-- A renamed typed control shape with fixed defs meets `SpillInstOk`. -/
theorem spillInstOk_renamedT {R : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming R gn) {N : Nat}
    (hfix : ∀ n, N ≤ n → gn n = n) {m : MInst} (h : CtlShapeT N m) : SpillInstOk (m.mapRegs R) :=
  spillInstOk_mapRegs hg (spillInstOk_of_ctlShapeT h)
    (fun ops hops o ho hd => hfix _ (ctlShapeT_defs h ops hops o ho hd))

theorem isCtl_stackArgLoad (r : Reg) (b : Nat) (am : AMode) : (stackArgLoad r b am).isCtl = false := by
  unfold stackArgLoad; split <;> rfl

/-- The members of `vcBlocksOfT` with the renaming named (`mem_vcBlocksOf'`, typed). -/
theorem mem_vcBlocksOfT' {f : Clif.Function} {ctx : Ctx} {bl : List BLow} {vb : VBlock}
    (h : vb ∈ (vcBlocksOfT f ctx bl).toList) :
    (∃ bi B L, f.blocks[bi]? = some B ∧ bl[bi]? = some L ∧
      vb = fixBlock (lowerFunction.resolve (aliasArr (aliasOf f bl)) ((aliasArr (aliasOf f bl)).size + 1))
        (rawBlockT f ctx bl bi B)) ∨
    (∃ B L e, B ∈ f.blocks ∧ e ∈ edgeBlocksT f ctx B L ∧
      vb = fixBlock (lowerFunction.resolve (aliasArr (aliasOf f bl)) ((aliasArr (aliasOf f bl)).size + 1)) e) := by
  simp only [vcBlocksOfT, List.toList_toArray, List.mem_map, List.mem_append, List.mem_flatMap] at h
  obtain ⟨vb0, h1, rfl⟩ := h
  rcases h1 with ⟨p, hp, rfl⟩ | ⟨p, hp, he⟩
  · have := List.mem_zipIdx_iff_getElem?.mp hp
    rw [List.getElem?_zip_eq_some] at this
    exact .inl ⟨p.2, p.1.1, p.1.2, this.1, this.2, rfl⟩
  · exact .inr ⟨p.1, p.2, vb0, (List.of_mem_zip hp).1, he, rfl⟩

/-! ## The entry block's `Args` -/

/-- An `sret` parameter of an ABI-checked signature is an `i64`. -/
theorem sret_i64_of_sigAbiOk {s : Clif.Signature} (h : sigAbiOk s = true) :
    ∀ p ∈ s.params, p.purpose = .sret → p.ty = .i64 := by
  unfold sigAbiOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  intro p hp hps
  rcases h.1.1.1 p hp with h | h
  · rw [h] at hps; cases hps
  · exact h.2

/-- The typed entry pairs' registers have their vregs' classes (`spillInstOk_entryArgsT`'s
placement argument). -/
theorem entryDC_argRegC {f : Clif.Function} {ctx : Ctx} {B : Clif.Block}
    (hsig : (f.sig.params.filter (·.purpose == .sret)).length ≤ 1)
    (hsret : ∀ p ∈ f.sig.params, p.purpose = .sret → p.ty = .i64)
    (hcls : ∀ (i : Nat) (x : Clif.ValueId) (t : Clif.Ty) (sp : Clif.AbiParam),
      B.params[i]? = some (x, t) → f.sig.params[i]? = some sp →
      valClassOf ctx x = tyClass sp.ty) :
    ∀ q ∈ entryDC ctx (Driver.entryParams f B), ArgRegC q.2.1 q.2.2 := by
  intro q hq
  obtain ⟨i, x, t, p, hb, hlc, rfl⟩ := mem_entryDC hq
  cases hloc : sigArgLocs f.sig with
  | error e => simp [locsOf, hloc] at hlc
  | ok r =>
    obtain ⟨locs, n⟩ := r
    have hl : locsOf f.sig = locs := by simp [locsOf, hloc]
    obtain ⟨-, hP⟩ := sigArgLocs_regsC hsig hloc
    rw [hl] at hlc
    obtain ⟨sp, hsp, hpl⟩ := hP.get hlc
    have hc := hcls i x t sp hb hsp
    simp only
    rw [hc]
    rcases hpl with ⟨hs, he8⟩ | ⟨-, hlc'⟩
    · cases he8
      rw [hsret sp (List.mem_of_getElem? hsp) hs]
      exact .inl ⟨rfl, 8, Nat.le_refl _, rfl⟩
    · exact retRegC_argRegC (hlc' p rfl)

/-- **The facts of the typed entry block's parameters**: distinct vregs (SSA), not renamed by
the alias resolution (no parameter is an alias key), of the classes of the signature's
parameters (`EntryClassOk`). -/
theorem entryParams_factsT {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (bl : List BLow) (hd : Dominated f) (hec : EntryClassOk f)
    (hb : buildCtx f = .ok (ctx, ranges, st0)) {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0) :
    (B0.params.map (·.1)).Nodup ∧
    (∀ x ∈ B0.params.map (·.1),
      lowerFunction.resolve (aliasArr (aliasOf f bl)) ((aliasArr (aliasOf f bl)).size + 1)
        (Driver.vregOf ctx x) = Driver.vregOf ctx x) ∧
    (∀ (i : Nat) (x : Clif.ValueId) (t : Clif.Ty) (sp : Clif.AbiParam),
      B0.params[i]? = some (x, t) → f.sig.params[i]? = some sp →
      valClassOf ctx x = tyClass sp.ty) := by
  have hcf := ctxFacts_of hb
  have hB0m : B0 ∈ f.blocks := List.mem_of_getElem? hB0
  have hvd := hd.ssa
  refine ⟨?_, fun x hx => ?_, fun k x t sp hx hsp => ?_⟩
  · unfold valueDefs at hvd
    have := (List.pairwise_flatMap.mp hvd).1 B0 hB0m
    exact (List.nodup_append.mp this).1
  · show lowerFunction.resolve _ _ (Reg.vreg x (valClassOf ctx x)) = _
    rw [resolve_vreg]
    congr 1
    refine resolve_fix _ (fun o hm => ?_)
    obtain ⟨B', hB', stm, hstm, hr⟩ := aliasOf_key hm
    exact param_not_result hvd hB0m hB' hx (List.mem_flatMap.mpr ⟨stm, hstm, hr⟩)
  · have hty := (hcf.types hvd).2 B0 hB0m (x, t) (List.mem_of_getElem? hx)
    have hhead : f.blocks.head? = some B0 := by
      rw [List.head?_eq_getElem?]; exact hB0
    rw [← hec B0 hhead k x t sp hx hsp,
      show tyClass t = (CTy.ofClif t).valClass by cases t <;> rfl]
    simp [valClassOf, hty]

/-- **The struct pointer an `sret` function returns has an integer vreg** (#587: `gen_return`
returns it in x8): it is the entry block's `sret` parameter (`sretRet`), whose class is the
signature's (`EntryClassOk`), an `i64`'s (`sigAbiOk`). -/
theorem sretRet_valClass_int {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hd : Dominated f) (hec : EntryClassOk f) (hsig : sigAbiOk f.sig = true)
    (hb : buildCtx f = .ok (ctx, ranges, st0)) : ∀ y ∈ sretRet f, valClassOf ctx y = .int := by
  intro y hy
  unfold sretRet at hy
  split at hy
  · split at hy
    · rename_i b0 i hb0 hi
      cases hp : b0.params[i]? with
      | none => simp [hp] at hy
      | some q =>
        obtain ⟨x, t⟩ := q
        simp only [hp, Option.map_some, Option.toList_some, List.mem_singleton] at hy
        rw [hy]
        obtain ⟨hil, hpi, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
        have hB0 : f.blocks[0]? = some b0 := by rw [← List.head?_eq_getElem?]; exact hb0
        rw [(entryParams_factsT [] hd hec hb hB0).2.2 i x t _ hp (List.getElem?_eq_getElem hil),
          sret_i64_of_sigAbiOk hsig _ (List.getElem_mem hil) (by simpa using hpi)]
        rfl
    · simp at hy
  · simp at hy

/-- **`CtlSpillHyp` from the typed ISLE inversion**, for typed-scope input whose signatures pass
the end-to-end subset's ABI check and whose entry block is typed like the signature. -/
theorem ctlSpillHypT_of (hI : IselCtlHypT) {f : Clif.Function} {vc : VCode}
    (hdom : dominatedB f = true) (hs : LowerScopeT f) (hst : Compile.storeTypedB f = true)
    (hsel : Compile.selectTypedB f = true) (ha : AbiSigsOk f) (hec : EntryClassOk f)
    (hl : lowerFunction f = .ok vc) :
    ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i := by
  have hd := dominated_of hdom
  obtain ⟨ctx, ranges, st0, bl, hb, hlb, hvb, -, -⟩ := lowerFunction_runT hs.externsE hl
  obtain ⟨hS, hT, hY⟩ := hI f ctx ranges st0 hdom hs hst hsel ha hb
    (sretRet_valClass_int hd hec ha.1.1 hb)
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
  have hkey : ∀ n o, (n, o) ∈ al → n < ctx.valDef.size := by
    intro n o hm
    have := (aliasOf_keys f bl).subset (List.mem_map_of_mem (f := (·.1)) hm)
    exact hN ▸ (hcf.vals n this).1
  have hfix : ∀ n, ctx.valDef.size ≤ n → gn n = n := fun n hn =>
    resolve_fix al (fun o hm => absurd (hkey n o hm) (by omega))
  intro vb hvb' i hi hct
  rw [hvb] at hvb'
  rcases mem_vcBlocksOfT' hvb' with ⟨bi, B, L, hB, hL, rfl⟩ | ⟨B, L, e, -, he, rfl⟩
  · have hi' : i ∈ ((rawBlockT f ctx bl bi B).insts.map (MInst.mapRegs R)).toList := hi
    rw [rawBlockT_insts (ctx := ctx) hg bl bi B] at hi'
    simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at hi'
    rcases hi' with (hpre | ⟨sg, ⟨j, -, rfl⟩, hm⟩) | htseg
    · -- the entry block's `Args` and parameter loads
      unfold preT at hpre
      split at hpre
      · rename_i B0 hB0
        simp only [List.mem_cons] at hpre
        rcases hpre with rfl | hpre
        · obtain ⟨hpar, hR, hcls⟩ := entryParams_factsT bl hd hec hb hB0
          exact spillInstOk_entryArgsT (sret_le_of_sigAbiOk ha.1.1) (sret_i64_of_sigAbiOk ha.1.1)
            hpar hR hcls
        · simp only [entryLoadsT, List.mem_filterMap] at hpre
          obtain ⟨q, -, hq⟩ := hpre
          unfold entryLoadOfT at hq
          split at hq
          · cases hq; exact absurd (isCtl_stackArgLoad _ _ _ ▸ hct) Bool.false_ne_true
          · cases hq
      · simp at hpre
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
          exact spillInstOk_renamedT hg hfix (hsh m (by simpa using hm) hct)
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
        exact spillInstOk_renamedT hg hfix (hsh m (by simpa using hm) hct)
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
          · exact spillInstOk_renamedT hg hfix (hsh m (List.dropLast_subset _ hm) hct)
          · simp only [List.mem_singleton] at hm
            subst hm
            have hcm : MInst.call c ∈ ms := List.mem_of_getLast? hlast
            have hsc := hsh _ hcm rfl
            refine spillInstOk_mapRegs hg
              (spillInstOk_tryCall_of_call hcl (spillInstOk_of_ctlShapeT hsc))
              (fun ops hops o ho hdf => hfix _ (ctlShapeT_defs hsc ops
                ((operands_tryCall_call c T.info).symm.trans hops) o ho hdf))
        · exact spillInstOk_renamedT hg hfix (hsh m hm hct)
  · obtain ⟨tl, hie⟩ := edgeBlocksT_insts he
    simp only [fixBlock, hie] at hi
    simp at hi
    subst hi
    exact spillInstOk_jump tl

end Backend.Proof.Spill

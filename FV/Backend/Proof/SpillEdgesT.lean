import FV.Backend.Proof.SpillEdges
import FV.Backend.Proof.SpillEdgesLowT
import FV.Backend.Proof.LowerCompleteT
import FV.Compile.TryArgClass

/-!
# The spill allocator's CFG facts on the typed pipeline's output (S11e5 Stage C, slice 6)

`edgesHyp_ofT`: `edgesHyp_of` over the typed scope `LowerScopeT`. The CFG facts of
`lowerFunction`'s VCode (`lowOk_ofT`) are `lowOk_of`'s over the typed lowering run `LowT`
(`lowT_of`); what changes is the class of a branch argument and of its target parameter, both of
the value's type: a branch argument or a `try_call`'s value argument has its parameter's class
(`Compile.edgeClassOk`, `CtxSpec.edgeClass`/`tryEdgeClass`), a `try_call`'s return/payload
argument is an integer vreg of `tryRegsOf` and goes to an integer parameter
(`Compile.tryArgClassOk`, an explicit input check; `Compile.tryArgClassOk_of_functionE`).
`edgesHyp_of` is the integer case (`edgesHyp_of_toT`).
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Driver

theorem valClassOf_of_type {ctx : Ctx} {x : Nat} {t : CTy} (h : ctx.valueType? x = some t) :
    valClassOf ctx x = t.valClass := by
  simp [valClassOf, h]

theorem valClass_int_of_not_float {ty : Clif.Ty} (h : ty.isFloat = false) :
    (CTy.ofClif ty).valClass = .int := by
  cases ty <;> simp_all [Clif.Ty.isFloat, CTy.ofClif, CTy.valClass, CTy.regClass?]

theorem zip_mem_of_idx {α β : Type} {as : List α} {bs : List β} {k : Nat} {a : α} {b : β}
    (ha : as[k]? = some a) (hb : bs[k]? = some b) : (a, b) ∈ as.zip bs :=
  List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨ha, hb⟩)

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {bl : List BLow} {RR : Reg → Reg}
  (H : LowT f vc ctx st0 bl RR)
include H

/-- A block parameter's class is that of its declared type. -/
theorem LowT.param_cls (hd : Dominated f) {TB : Clif.Block} (hTB : TB ∈ f.blocks)
    {p : Clif.ValueId × Clif.Ty} (hp : p ∈ TB.params) :
    valClassOf ctx p.1 = (CTy.ofClif p.2).valClass := by
  obtain ⟨ranges, hb⟩ := H.hb
  exact valClassOf_of_type (((ctxFacts_of hb).types hd.ssa).2 TB hTB p hp)

/-- **Branch arguments have their target parameters' classes**, from `Compile.edgeClassOk`
(`CtxSpec.edgeClass`'s proof). -/
theorem _root_.Backend.Proof.Driver.CtxSpec.edgeClassE {ranges : Array (Nat × Nat)}
    (sp : CtxSpec f ctx ranges st0) (hE : Compile.edgeClassOk f = true)
    {B : Clif.Block} (hB : B ∈ f.blocks) {bc : Clif.BlockCall} (hbc : bc ∈ dests B.term)
    {tb : Clif.Block} (htb : f.block? bc.block = some tb) {a : Nat} {p : Clif.ValueId × Clif.Ty}
    (hap : (a, p) ∈ bc.args.zip tb.params) :
    ∀ t, ctx.valueType? a = some t → t.valClass = (CTy.ofClif p.2).valClass := by
  simp only [Compile.edgeClassOk, Bool.and_eq_true, List.all_eq_true] at hE
  have h := (hE B hB).1 bc (by rw [blockCalls_eq_dests]; exact hbc)
  rw [htb] at h
  exact sp.class_of_argClassOk (List.all_eq_true.mp h _ hap)
    ((sp.blockC tb (block?_mem htb)).1 p (List.of_mem_zip hap).2)

/-- **A `try_call`'s value arguments have their target parameters' classes**, from
`Compile.edgeClassOk` (`CtxSpec.tryEdgeClass`'s proof). -/
theorem _root_.Backend.Proof.Driver.CtxSpec.tryEdgeClassE {ranges : Array (Nat × Nat)}
    (sp : CtxSpec f ctx ranges st0) (hE : Compile.edgeClassOk f = true)
    {B : Clif.Block} (hB : B ∈ f.blocks) {et : Clif.ExnTable} (het : IsTryWith B.term et)
    {td : Clif.TryDest} (htd : td ∈ et.dests) {tb : Clif.Block} (htb : f.block? td.block = some tb)
    {v : Nat} {p : Clif.ValueId × Clif.Ty} (hap : (Clif.TryArg.val v, p) ∈ td.args.zip tb.params) :
    ∀ t, ctx.valueType? v = some t → t.valClass = (CTy.ofClif p.2).valClass := by
  simp only [Compile.edgeClassOk, Bool.and_eq_true, List.all_eq_true] at hE
  have h := (hE B hB).2
  have hv := (sp.blockC tb (block?_mem htb)).1 p (List.of_mem_zip hap).2
  rcases het with ⟨fn, args, he⟩ | ⟨c, args, he⟩ <;> rw [he] at h <;> simp only at h <;>
  · have h2 := List.all_eq_true.mp h td htd
    rw [htb] at h2
    have h3 := List.all_eq_true.mp h2 _ hap
    exact sp.class_of_argClassOk h3 hv

/-- **A branch argument has its target parameter's class** (`Compile.edgeClassOk`). -/
theorem LowT.arg_clsE (hd : Dominated f) (hE : Compile.edgeClassOk f = true) {B : Clif.Block}
    (hB : B ∈ f.blocks)
    {bc : Clif.BlockCall} (hbc : bc ∈ dests B.term) {tb : Clif.Block}
    (htb : f.block? bc.block = some tb) {a : Nat} {p : Clif.ValueId × Clif.Ty}
    (hap : (a, p) ∈ bc.args.zip tb.params) : valClassOf ctx a = valClassOf ctx p.1 := by
  obtain ⟨ranges, hb⟩ := H.hb
  have sp := ctxSpec_of hb
  obtain ⟨tb', htb', -, hargs⟩ := H.lf.args B hB bc hbc
  rw [htb] at htb'
  cases htb'
  obtain ⟨t, ht, -⟩ := sp.regEq a _ (hargs a (List.of_mem_zip hap).1)
  rw [valClassOf_of_type ht, sp.edgeClassE hE hB hbc htb hap t ht,
    H.param_cls hd (block?_mem htb) (List.of_mem_zip hap).2]

/-- **A branch argument has its target parameter's class** (typed scope). -/
theorem LowT.arg_cls (hd : Dominated f) (hs : LowerScopeT f) {B : Clif.Block} (hB : B ∈ f.blocks)
    {bc : Clif.BlockCall} (hbc : bc ∈ dests B.term) {tb : Clif.Block}
    (htb : f.block? bc.block = some tb) {a : Nat} {p : Clif.ValueId × Clif.Ty}
    (hap : (a, p) ∈ bc.args.zip tb.params) : valClassOf ctx a = valClassOf ctx p.1 :=
  H.arg_clsE hd (functionETF_parts hs.toTF.subsetTF).2.2.2.2.1 hB hbc htb hap

/-- **A typed edge block's arguments have their target parameters' classes**
(`Compile.edgeClassOk`). -/
theorem LowT.edge_clsE (hd : Dominated f) (hE : Compile.edgeClassOk f = true)
    (htc : Compile.tryArgClassOk f = true)
    {bi : Nat} {B : Clif.Block} {L : BLow} (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L)
    {e : VBlock} (he : e ∈ edgeBlocksT f ctx B L) :
    ∃ tl TB, e.insts = #[.jump tl] ∧ f.blocks[tl]? = some TB ∧
      ∀ (k : Nat) (a : Reg) (p : Clif.ValueId × Clif.Ty), e.branchArgs[k]? = some a →
        TB.params[k]? = some p → ∃ v, a = .vreg v (valClassOf ctx p.1) := by
  have hBm : B ∈ f.blocks := List.mem_of_getElem? hB
  obtain ⟨-, -, -, nl0, nl1, hlt⟩ := (lowBlocks_spec H.hbl).2 bi B L hB hL
  rcases try_or B.term with ht | ⟨et, het⟩
  · by_cases hj : ∃ bc, B.term = .jump bc
    · obtain ⟨bc, hj⟩ := hj
      unfold edgeBlocksT at he
      rw [hj] at he
      simp at he
    · have hj' : ∀ bc, B.term ≠ .jump bc := fun bc e => hj ⟨bc, e⟩
      rw [shape_edgeBlocksT_other ht hj'] at he
      obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.mp he
      simp only [edgeOfBcT] at hpe
      split at hpe
      · cases hpe
      obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.mp hpe
      have hbc : p.1 ∈ dests B.term := (List.of_mem_zip hp).1
      obtain ⟨TB, hTB, hTBi⟩ := block?_of_idx htl
      refine ⟨tl, TB, rfl, hTBi, fun k a q hak hq => ?_⟩
      simp only [List.getElem?_toArray, List.getElem?_map] at hak
      obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.mp hak
      exact ⟨a0, by rw [vregOf, H.arg_clsE hd hE hBm hbc hTB (zip_mem_of_idx ha0 hq)]⟩
  · obtain ⟨T, hT, -, hexn, -, hregs, -, -⟩ := (lowTerm_spec hlt).2 et het
    rw [shape_edgeBlocksT_try het hT] at he
    obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.mp he
    simp only [edgeOfTryT] at hpe
    obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.mp hpe
    obtain ⟨k0, hk0, hpk⟩ := List.getElem_of_mem hp
    have hdk : et.dests[k0]? = some p.1 :=
      (List.getElem?_zip_eq_some.mp (by rw [List.getElem?_eq_getElem hk0, hpk])).1
    have htd : p.1 ∈ et.dests := List.mem_of_getElem? hdk
    obtain ⟨T', hT', hargs⟩ := H.lf.tryArgs bi B L et hB hL het
    rw [hT] at hT'
    cases hT'
    obtain ⟨⟨tb, htb, -⟩, hai⟩ := hargs k0 p.1 hdk
    obtain ⟨TB, hTB, hTBi⟩ := block?_of_idx htl
    obtain rfl : tb = TB := Option.some.inj (htb.symm.trans hTB)
    obtain ⟨-, hregs', -⟩ := tryRegsOf_spec (exnTableOpnd_cc hexn) hregs
    obtain ⟨ranges, hb⟩ := H.hb
    have sp := ctxSpec_of hb
    refine ⟨tl, tb, rfl, hTBi, fun k a q hak hq => ?_⟩
    simp only [List.getElem?_toArray, List.getElem?_map] at hak
    obtain ⟨ta, hta, rfl⟩ := Option.map_eq_some_iff.mp hak
    have hz : (ta, q) ∈ p.1.args.zip tb.params := zip_mem_of_idx hta hq
    have hok := hai ta (List.mem_of_getElem? hta)
    have hint : (∀ v, ta ≠ .val v) → valClassOf ctx q.1 = .int := fun hv => by
      rw [H.param_cls hd (block?_mem htb) (List.of_mem_zip hz).2]
      exact valClass_int_of_not_float
        (Compile.tryArgClassOk_sound htc B hBm et het p.1 htd tb htb ta q hz hv)
    cases ta with
    | val v =>
      obtain ⟨t, ht, -⟩ := sp.regEq v _ hok
      refine ⟨v, ?_⟩
      simp only [tryEdgeArgT, vregOf]
      rw [valClassOf_of_type ht, sp.tryEdgeClassE hE hBm het htd htb hz t ht,
        H.param_cls hd (block?_mem htb) (List.of_mem_zip hz).2]
    | ret i =>
      simp only at hok
      rw [hregs'] at hok
      simp only [List.length_map, List.length_range] at hok
      refine ⟨L.tst.nextVreg + i, ?_⟩
      rw [hint (fun v h => by cases h), hregs']
      simp [tryEdgeArgT, hok.2]
    | exn i =>
      simp only at hok
      rw [hregs'] at hok
      simp only [List.length_cons, List.length_nil] at hok
      rw [hint (fun v h => by cases h), hregs']
      have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩

/-- **A typed edge block's arguments have their target parameters' classes.** -/
theorem LowT.edge_cls (hd : Dominated f) (hs : LowerScopeT f) (htc : Compile.tryArgClassOk f = true)
    {bi : Nat} {B : Clif.Block} {L : BLow} (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L)
    {e : VBlock} (he : e ∈ edgeBlocksT f ctx B L) :
    ∃ tl TB, e.insts = #[.jump tl] ∧ f.blocks[tl]? = some TB ∧
      ∀ (k : Nat) (a : Reg) (p : Clif.ValueId × Clif.Ty), e.branchArgs[k]? = some a →
        TB.params[k]? = some p → ∃ v, a = .vreg v (valClassOf ctx p.1) :=
  H.edge_clsE hd (functionETF_parts hs.toTF.subsetTF).2.2.2.2.1 htc hB hL he

end

/-- **`lowerFunction`'s VCode meets `LowOk`** on `Dominated`, float-scope (`LowerScopeTF`),
`ArityOk` input whose `try_call` return/payload arguments go to integer parameters (`lowOk_of`,
float scope; the `br_table` indices typed by `brIdxOk`). -/
theorem lowOk_ofTF {f : Clif.Function} {vc : VCode} (hd : Dominated f) (hs : LowerScopeTF f)
    (ha : ArityOk f) (htc : Compile.tryArgClassOk f = true) (h : lowerFunction f = .ok vc) :
    LowOk vc := by
  obtain ⟨ctx, st0, bl, RR, H⟩ := lowT_of hs.externsE h
  obtain ⟨gn, hRR⟩ := H.ren
  obtain ⟨ranges, hb⟩ := H.hb
  have hE : Compile.edgeClassOk f = true := (functionETF_parts hs.subsetTF).2.2.2.2.1
  have hbt : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term := brIdx_of_ok (hs.ctxFacts ctx ranges st0 hb).1
  have hrb := fun {x : Nat} {B : Clif.Block} {L : BLow} (hB : f.blocks[x]? = some B)
    (hL : bl[x]? = some L) => H.raw_backG (ctxInvT_ofF hs hb)
      (fun B' hB' => termIntPos_ofF hs hb hB') hbt hB hL
  have hn : 0 < f.blocks.length := List.length_pos_iff.mpr hs.nonempty
  obtain ⟨B0, hB0⟩ : ∃ B0, f.blocks[0]? = some B0 := ⟨_, List.getElem?_eq_getElem hn⟩
  -- the block at a CLIF block's index
  have tgtBlk : ∀ (tl : Nat) (TB : Clif.Block), f.blocks[tl]? = some TB → tl ≠ 0 →
      ∃ tb, vc.blocks[tl]? = some tb ∧ tb.params = (TB.params.map fun p => vregOf ctx p.1).toArray ∧
        (tb.params.toList.map Reg.homeNum).Nodup := by
    intro tl TB hTB h0
    refine ⟨_, H.raw_at hTB, by simp [fixBlock, rawBlockT, h0], ?_⟩
    simp only [fixBlock, rawBlockT, h0, ite_false, List.toList_toArray, List.map_map]
    have hnd := nodup_flatMap_mem _ hd.ssa (List.mem_of_getElem? hTB)
    exact (List.nodup_append.mp hnd).1
  have backE : ∀ (e : VBlock) (tl : Label), e.insts = #[.jump tl] →
      (fixBlock RR e).insts.back? = some (.jump tl) := by
    intro e tl he; simp [fixBlock, he]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- nonempty
    have := H.raw_at hB0
    exact (Array.getElem?_eq_some_iff.mp this).1
  · -- labels
    intro l vb hvb
    rcases H.cases hvb with ⟨B, L, -, -, -, rfl⟩ | ⟨bi, B, L, e, -, -, -, hl, -, rfl⟩
    · rfl
    · exact hl
  · -- entry
    intro vb hvb
    rw [H.raw_at hB0] at hvb
    cases hvb
    rfl
  · -- no branch to the entry
    intro b vb t hvb hback h0
    rcases H.cases hvb with ⟨B, L, -, hB, hL, rfl⟩ | ⟨bi, B, L, e, hB, hL, he, -, -, rfl⟩
    · obtain ⟨t', hb', -, hnt, htry⟩ := hrb hB hL
      rw [hb'] at hback
      cases hback
      have hBm := List.mem_of_getElem? hB
      rcases try_or B.term with ht | ⟨et, het⟩
      · rw [(hnt ht).1] at h0
        rcases (H.raw_tgt hB hL).1 ht 0 h0 with ⟨bc, hbc, hidx, -⟩ | ⟨e, he, hl⟩
        · exact hs.noEntryPred B hBm bc.block (by rw [succIds_of ht]; exact List.mem_map_of_mem hbc) hidx
        · have := (H.edge_at hB hL he).1; rw [hl] at this; omega
      · obtain ⟨c, ti, -, htg⟩ := htry et het
        rw [htg] at h0
        obtain ⟨e, he, hl⟩ := ((H.raw_tgt hB hL).2 et het).2 0 h0
        have := (H.edge_at hB hL he).1; rw [hl] at this; omega
    · obtain ⟨tl, TB, hins, -, -, htl0, -⟩ := H.edge_factsG hs.noEntryPred hB hL he
      rw [backE e tl hins] at hback
      cases hback
      simp [MInst.targets] at h0
      exact htl0 h0.symm
  · -- branch arguments
    intro b vb hvb hba
    rcases H.cases hvb with ⟨B, L, -, hB, hL, rfl⟩ | ⟨bi, B, L, e, hB, hL, he, -, -, rfl⟩
    · have hBm := List.mem_of_getElem? hB
      obtain ⟨t', hb', hjump, -, -⟩ := hrb hB hL
      obtain ⟨bc, hj⟩ : ∃ bc, B.term = .jump bc := by
        refine Classical.byContradiction fun hj => hba ?_
        simp only [fixBlock, rawBlockT]
        split
        · rename_i bc hbc; exact absurd ⟨bc, hbc⟩ hj
        · simp
      obtain ⟨tl, rfl, hLt⟩ := hjump bc hj
      have ht : B.term.isTry = false := by rw [hj]; rfl
      obtain ⟨bc', hbc', hidx, -⟩ | ⟨e, he, -⟩ := (H.raw_tgt hB hL).1 ht tl (by rw [hLt]; simp)
      · rw [hj] at hbc'
        simp only [dests, List.mem_singleton] at hbc'
        subst hbc'
        obtain ⟨TB, hTB, hTBi⟩ := block?_of_idx hidx
        have htl0 : tl ≠ 0 := fun h0 => hs.noEntryPred B hBm bc'.block
          (by rw [hj]; simp [succIds, dests]) (h0 ▸ hidx)
        obtain ⟨tb, htb, hpar, hnd⟩ := tgtBlk tl TB hTBi htl0
        obtain ⟨tb', htb', hlen, -⟩ := H.lf.args B hBm bc' (by rw [hj]; simp [dests])
        obtain rfl : tb' = TB := Option.some.inj (htb'.symm.trans hTB)
        have hba' : (fixBlock RR (rawBlockT f ctx bl b B)).branchArgs =
            ((bc'.args.map fun a => vregOf ctx a).toArray).map RR := by
          simp only [fixBlock, rawBlockT, hj]
        have hne : bc'.args ≠ [] := by
          intro h0; rw [hba', h0] at hba; exact hba (by simp)
        refine ⟨tl, tb, hb', htb, by rw [hpar, hba']; simp [hlen hne], fun k a p hak hpk => ?_, hnd⟩
        rw [hba'] at hak
        rw [hpar] at hpk
        simp only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_map] at hak hpk
        obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.mp (by simpa using hak)
        obtain ⟨p0, hp0, rfl⟩ := Option.map_eq_some_iff.mp hpk
        refine ⟨gn a0, p0.1, valClassOf ctx p0.1, ?_, rfl⟩
        rw [vregOf, hRR.vreg, H.arg_clsE hd hE hBm (by rw [hj]; simp [dests]) hTB
          (zip_mem_of_idx ha0 hp0)]
      · unfold edgeBlocksT at he
        rw [hj] at he
        simp at he
    · obtain ⟨tl, TB, hins, -, hTB, htl0, hlen, -⟩ := H.edge_factsG hs.noEntryPred hB hL he
      obtain ⟨tl', TB', hins', hTB', hcls⟩ := H.edge_clsE hd hE htc hB hL he
      rw [hins] at hins'
      obtain rfl : tl = tl' := by simpa using hins'
      obtain rfl : TB = TB' := Option.some.inj (hTB.symm.trans hTB')
      obtain ⟨tb, htb, hpar, hnd⟩ := tgtBlk tl TB hTB htl0
      refine ⟨tl, tb, backE e tl hins, htb, by rw [hpar]; simp [fixBlock, hlen],
        fun k a p hak hpk => ?_, hnd⟩
      simp only [fixBlock, Array.getElem?_map] at hak
      obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.mp hak
      rw [hpar] at hpk
      simp only [List.getElem?_toArray, List.getElem?_map] at hpk
      obtain ⟨p0, hp0, rfl⟩ := Option.map_eq_some_iff.mp hpk
      obtain ⟨v, rfl⟩ := hcls k a0 p0 ha0 hp0
      exact ⟨_, _, _, hRR.vreg _ _, rfl⟩
  · -- no branch arguments
    intro b vb t l tb hvb hba hback hl htb
    have viaE : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (e : VBlock), f.blocks[bi]? = some B →
        bl[bi]? = some L → e ∈ edgeBlocksT f ctx B L → e.label = l → tb.params = #[] := by
      intro bi B L e hB hL he hel
      obtain ⟨-, hat⟩ := H.edge_at hB hL he
      rw [hel, htb] at hat
      cases hat
      obtain ⟨-, -, -, hpar, -⟩ := H.edge_factsG hs.noEntryPred hB hL he
      exact hpar
    have viaB : ∀ (TB : Clif.Block), f.blocks[l]? = some TB → TB.params = [] → tb.params = #[] := by
      intro TB hTB hp
      rw [H.raw_at hTB] at htb
      cases htb
      simp [fixBlock, rawBlockT, hp]
    rcases H.cases hvb with ⟨B, L, -, hB, hL, rfl⟩ | ⟨bi, B, L, e, hB, hL, he, -, -, rfl⟩
    · have hBm := List.mem_of_getElem? hB
      obtain ⟨t', hb', -, hnt, htry⟩ := hrb hB hL
      rw [hb'] at hback
      cases hback
      rcases try_or B.term with ht | ⟨et, het⟩
      · rw [(hnt ht).1] at hl
        rcases (H.raw_tgt hB hL).1 ht l hl with ⟨bc, hbc, hidx, hcase⟩ | ⟨e, he, hel⟩
        · have hnil : bc.args = [] := by
            rcases hcase with h0 | hj
            · exact h0
            · have : (fixBlock RR (rawBlockT f ctx bl b B)).branchArgs =
                  ((bc.args.map fun a => vregOf ctx a).toArray).map RR := by
                simp only [fixBlock, rawBlockT, hj]
              rw [this] at hba
              simpa using hba
          obtain ⟨TB, hTB, hTBi⟩ := block?_of_idx hidx
          have := ha B hBm bc hbc TB hTB
          rw [hnil] at this
          exact viaB TB hTBi (List.eq_nil_of_length_eq_zero this)
        · exact viaE _ _ _ e hB hL he hel
      · obtain ⟨c, ti, -, htg⟩ := htry et het
        rw [htg] at hl
        obtain ⟨e, he, hel⟩ := ((H.raw_tgt hB hL).2 et het).2 l hl
        exact viaE _ _ _ e hB hL he hel
    · obtain ⟨tl, TB, hins, -, hTB, -, hlen, -⟩ := H.edge_factsG hs.noEntryPred hB hL he
      rw [backE e tl hins] at hback
      cases hback
      simp [MInst.targets] at hl
      subst hl
      have : e.branchArgs.size = 0 := by
        have := congrArg Array.size hba; simpa [fixBlock] using this
      exact viaB TB hTB (List.eq_nil_of_length_eq_zero (by omega))
  · -- a `try_call`'s block has no branch arguments
    intro b vb info ti hvb hback
    rcases H.cases hvb with ⟨B, L, -, hB, hL, rfl⟩ | ⟨bi, B, L, e, hB, hL, he, -, -, rfl⟩
    · obtain ⟨t', hb', -, hnt, -⟩ := hrb hB hL
      rw [hb'] at hback
      cases hback
      rcases try_or B.term with ht | ⟨et, het⟩
      · exact absurd rfl ((hnt ht).2 info ti)
      · simp only [fixBlock, rawBlockT]
        split
        · rename_i bc hbc; rcases het with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] at hbc <;> cases hbc
        · simp
    · obtain ⟨tl, TB, hins, -⟩ := H.edge_factsG hs.noEntryPred hB hL he
      rw [backE e tl hins] at hback
      cases hback
  · -- a `try_call`'s successor is its own
    intro b vb info ti j l hvb hback hj b' vb' t' j' hvb' hback' hj'
    rcases H.cases hvb with ⟨B, L, -, hB, hL, rfl⟩ | ⟨bi, B, L, e, hB, hL, he, -, -, rfl⟩
    · obtain ⟨t0, hb0, -, hnt, htry⟩ := hrb hB hL
      rw [hb0] at hback
      cases hback
      rcases try_or B.term with ht | ⟨et, het⟩
      · exact absurd rfl ((hnt ht).2 info ti)
      obtain ⟨c, ti', -, htg⟩ := htry et het
      have hlm : l ∈ L.targets := by rw [← htg]; exact List.mem_of_getElem? hj
      obtain ⟨hnodup, hall⟩ := (H.raw_tgt hB hL).2 et het
      obtain ⟨e, he, hel⟩ := hall l hlm
      have hge := (H.edge_at hB hL he).1
      rw [hel] at hge
      rcases H.cases hvb' with ⟨B', L', -, hB', hL', rfl⟩ | ⟨bi', B', L', e', hB', hL', he', -, -, rfl⟩
      · obtain ⟨t1, hb1, -, hnt', htry'⟩ := hrb hB' hL'
        rw [hb1] at hback'
        cases hback'
        have hlm' : ∀ hl' : l ∈ L'.targets, ∃ e' ∈ edgeBlocksT f ctx B' L', e'.label = l := by
          intro hl'
          rcases try_or B'.term with ht' | ⟨et', het'⟩
          · rcases (H.raw_tgt hB' hL').1 ht' l hl' with ⟨bc, -, hidx, -⟩ | h
            · obtain ⟨TB, -, hTBi⟩ := block?_of_idx hidx
              have := (List.getElem?_eq_some_iff.mp hTBi).1
              omega
            · exact h
          · exact ((H.raw_tgt hB' hL').2 et' het').2 l hl'
        rcases try_or B'.term with ht' | ⟨et', het'⟩
        · rw [(hnt' ht').1] at hj'
          obtain ⟨e', he', hel'⟩ := hlm' (List.mem_of_getElem? hj')
          have := H.edge_disj hB hL hB' hL' he he' (by rw [hel, hel'])
          subst this
          rw [hB] at hB'
          cases hB'
          rw [isTry_of het] at ht'
          cases ht'
        · obtain ⟨c', ti'', -, htg'⟩ := htry' et' het'
          rw [htg'] at hj'
          obtain ⟨e', he', hel'⟩ := hlm' (List.mem_of_getElem? hj')
          have := H.edge_disj hB hL hB' hL' he he' (by rw [hel, hel'])
          subst this
          rw [hL] at hL'
          cases hL'
          refine ⟨rfl, ?_⟩
          rw [htg] at hj
          exact nodup_idx hnodup hj' hj
      · obtain ⟨tl, TB, hins, -, hTB, -⟩ := H.edge_factsG hs.noEntryPred hB' hL' he'
        rw [backE e' tl hins] at hback'
        cases hback'
        have hj0 : j' = 0 := by
          have := (List.getElem?_eq_some_iff.mp hj').1; simp [MInst.targets] at this; omega
        subst hj0
        simp [MInst.targets] at hj'
        subst hj'
        have := (List.getElem?_eq_some_iff.mp hTB).1
        omega
    · obtain ⟨tl, TB, hins, -⟩ := H.edge_factsG hs.noEntryPred hB hL he
      rw [backE e tl hins] at hback
      cases hback

/-- **`lowerFunction`'s VCode meets `LowOk`** on `Dominated`, `LowerScopeT`, `ArityOk` input whose
`try_call` return/payload arguments go to integer parameters (`lowOk_of`, typed). -/
theorem lowOk_ofT {f : Clif.Function} {vc : VCode} (hd : Dominated f) (hs : LowerScopeT f)
    (ha : ArityOk f) (htc : Compile.tryArgClassOk f = true) (h : lowerFunction f = .ok vc) :
    LowOk vc :=
  lowOk_ofTF hd hs.toTF ha htc h

/-- **`lowerFunction`'s VCode is in `prepare`'s domain** (`prepDomain_of_lower`, float scope):
the `br_table` indices are typed by `brIdxOk` (`LowerScopeTF.ctxFacts`). -/
theorem prepDomain_ofTF {f : Clif.Function} {vc : VCode} (hs : LowerScopeTF f)
    (h : lowerFunction f = .ok vc) : Prep.PrepDomain vc := by
  obtain ⟨ctx, st0, bl, RR, H⟩ := lowT_of hs.externsE h
  obtain ⟨ranges, hb⟩ := H.hb
  have hbt : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term :=
    brIdx_of_ok (hs.ctxFacts ctx ranges st0 hb).1
  have hn : 0 < f.blocks.length := List.length_pos_iff.mpr hs.nonempty
  obtain ⟨B0, hB0⟩ : ∃ B0, f.blocks[0]? = some B0 := ⟨_, List.getElem?_eq_getElem hn⟩
  refine ⟨(Array.getElem?_eq_some_iff.mp (H.raw_at hB0)).1, ?_, fun b vb t hvb hback h2 => ?_⟩
  · unfold Prep.Lbls
    have : vc.blocks.toList.map VBlock.label = List.range vc.blocks.size := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_map, Array.getElem_toList, List.getElem_range]
        simp only [List.length_map, Array.length_toList] at h1
        rcases H.cases (Array.getElem?_eq_getElem h1) with ⟨B, L, -, -, -, he⟩ | ⟨bi, B, L, e, -, -, -, hl, -, he⟩
        · rw [he]; rfl
        · rw [he]; exact hl
    rw [this]; exact List.nodup_range
  · refine Classical.byContradiction fun hba => ?_
    rcases H.cases hvb with ⟨B, L, -, hB, hL, rfl⟩ | ⟨bi, B, L, e, hB, hL, he, -, -, rfl⟩
    · obtain ⟨t', hb', hjump, -, -⟩ := H.raw_backG (ctxInvT_ofF hs hb)
        (fun B' hB' => termIntPos_ofF hs hb hB') hbt hB hL
      obtain ⟨bc, hj⟩ : ∃ bc, B.term = .jump bc := by
        refine Classical.byContradiction fun hj => hba ?_
        simp only [fixBlock, rawBlockT]
        split
        · rename_i bc hbc; exact absurd ⟨bc, hbc⟩ hj
        · simp
      obtain ⟨tl, rfl, -⟩ := hjump bc hj
      rw [hb'] at hback
      cases hback
      simp [MInst.targets] at h2
    · obtain ⟨tl, TB, hins, -⟩ := H.edge_factsG hs.noEntryPred hB hL he
      simp [fixBlock, hins] at hback
      subst hback
      simp [MInst.targets, MInst.mapRegs] at h2

/-- **`lowerFunction`'s VCode is in `prepare`'s domain** (`prepDomain_of_lower`, typed scope). -/
theorem prepDomain_ofT {f : Clif.Function} {vc : VCode} (_hd : Dominated f) (hs : LowerScopeT f)
    (h : lowerFunction f = .ok vc) : Prep.PrepDomain vc :=
  prepDomain_ofTF hs.toTF h

/-- **The CFG facts of the typed pipeline's output** (`edgesHyp_of` over `LowerScopeT`, with the
input check `Compile.tryArgClassOk`). -/
theorem edgesHyp_ofT {f : Clif.Function} {vc vcp : VCode} (hd : Dominated f) (hs : LowerScopeT f)
    (ha : ArityOk f) (htc : Compile.tryArgClassOk f = true) (hl : lowerFunction f = .ok vc)
    (hp : prepare vc = .ok vcp) :
    ∀ succs preds, vcp.cfg = .ok (succs, preds) → EdgesOk vcp succs preds :=
  edgesOk_prepare (lowOk_ofT hd hs ha htc hl) hp

/-- **Integer specialization**: `edgesHyp_of` from `edgesHyp_ofT`. -/
theorem edgesHyp_of_toT {f : Clif.Function} {vc vcp : VCode} (hd : Dominated f) (hs : LowerScope f)
    (ha : ArityOk f) (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp) :
    ∀ succs preds, vcp.cfg = .ok (succs, preds) → EdgesOk vcp succs preds :=
  edgesHyp_ofT hd hs.toT ha (Compile.tryArgClassOk_of_functionE hs.subsetE) hl hp

end Backend.Proof.Spill

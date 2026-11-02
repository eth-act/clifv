import FV.E2E.LinkScopeInputDefsT
import FV.E2E.LinkScopeInput
import FV.E2E.LinkScopeT
import FV.Backend.Proof.PrepareTotalT
import FV.E2E.EmitTotalT
import FV.E2E.SpillDefined
import FV.E2E.SpillKillFreeT

/-! # The typed input conditions and the compiler's per-function totality (S11e5 Stage C, slice 8)

Soundness of `fnScopeInTB`/`InScopeInT` (`LinkScopeInputDefsT.lean`):

* `fnScopeInT_parts`, `ctlInsts_of_ctlInstsB`, `lowerOutTB_spec`;
* **integer inclusion**: `fnScopeInTB_of_fnScopeInB` (`fnScopeInB g → fnScopeInTB g`, no extra
  premise), `inScopeInT_of_inScopeIn`; back to the integer scope on subset E:
  `fnScopeInB_of_fnScopeInTB`;
* outside subset E, `fnScopeInTB` gives the typed scope `fnScopeTB` (`fnScopeTB_of_inT`), so
  every typed theorem stated over `fnScopeTB` (`backend_correct_finalT_scope`,
  `compiledAT_of_fnScopeT`, …) applies;
* **totality**: `pipeT_okT`: the compiler's pipeline `pipeT` (`lowerFunction`, `prepare`,
  `lowerAllocReady`, `emitFunc`, `layout`) succeeds on every function of the typed input scope,
  whatever the untrusted allocator answered, with the artifact passing the typed lowering
  validator, the `prepare` validator, `AllocChecked` and the covered forms (`pipeT_ok` over the
  typed scope: integer functions through `pipeT_ok`, the others through `Prep.prepare_okT` and
  `backend_total_emitT`); `resultsT_ok_inT`: every function of an `InScopeInT` crate compiles;
  `resultsT_ok_input`: the integer `InScopeIn` conclusion re-derived through the typed theorem.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill

/-- `fnScopeInTB`'s conjuncts. -/
theorem fnScopeInT_parts {g : Clif.Function} (h : fnScopeInTB g = true) :
    Compile.functionET g = true ∧ Compile.storeTypedB g = true ∧ Compile.tryArgClassOk g = true ∧
    sigAbiOk g.sig = true ∧ g.externs.all (fun e => sigAbiOk e.2.sig) = true ∧
    indSigsOk g = true ∧ decide (regLocs g.sig).Nodup = true ∧
    (regLocs g.sig).all (·.isArgReg) = true ∧
    g.sig.params.all (fun p => decide (p.ty.width ≤ 64)) = true ∧ linkFreeB g = true ∧
    dominatedB g = true ∧ lowerScopeTB g = true ∧ Spill.arityOkB g = true ∧
    extendsWidenB g = true ∧ sizeOkB g = true ∧ driverInB g = true ∧ Prg.iselInB g = true ∧
    Spill.entryParamsB g = true ∧
    (Compile.functionE g = true ∨ (Spill.resClassOkB g = true ∧ lowerOutTB g = true)) := by
  simp only [fnScopeInTB, Bool.and_eq_true, Bool.or_eq_true, and_assoc] at h
  exact h

/-- **Soundness of `ctlInstsB`.** -/
theorem ctlInsts_of_ctlInstsB {vc : VCode} (h : ctlInstsB vc = true) : CtlInsts vc := by
  unfold ctlInstsB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun b vb k i hvb hi => ?_, ?_⟩
  · have hb : b < vc.blocks.size := (Array.getElem?_eq_some_iff.mp hvb).1
    have hk : k < vb.insts.size := (Array.getElem?_eq_some_iff.mp hi).1
    have h3 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
    simp only [hvb] at h3
    have h4 := List.all_eq_true.mp h3 k (List.mem_range.mpr hk)
    simp only [hi] at h4
    exact h4
  · split at h2
    · rename_i vb0 hvb0
      rw [Bool.and_eq_true] at h2
      obtain ⟨ha, hs⟩ := h2
      split at ha
      · rename_i ds hds
        exact ⟨vb0, ds, hvb0, hds, of_decide_eq_true hs⟩
      · cases ha
    · cases h2

/-- `lowerOutTB`: `lowerFunction` succeeds, its output meets `ctlSpillB`, and every output of
`prepare` on it meets `emitCondsB`, `formsCoveredB default`, `killFreeB` and `ctlInstsB`. -/
theorem lowerOutTB_spec {g : Clif.Function} (h : lowerOutTB g = true) :
    ∃ vc, lowerFunction g = .ok vc ∧ Spill.ctlSpillB vc = true ∧
      ∀ vcp, prepare vc = .ok vcp → emitCondsB vcp = true ∧ formsCoveredB default vcp = true ∧
        Spill.killFreeB vcp = true ∧ ctlInstsB vcp = true := by
  unfold lowerOutTB at h
  split at h
  · rename_i vc hl
    rw [Bool.and_eq_true] at h
    obtain ⟨hc, h⟩ := h
    refine ⟨vc, hl, hc, fun vcp hp => ?_⟩
    simp only [hp, Bool.and_eq_true] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · cases h

/-- **Integer inclusion**: every function of the integer input scope is in the typed one. -/
theorem fnScopeInTB_of_fnScopeInB {g : Clif.Function} (h : fnScopeInB g = true) :
    fnScopeInTB g = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := fnScopeIn_parts h
  simp only [fnScopeInTB, Compile.functionET_of_functionE h1, Compile.storeTypedB_of_functionE h1,
    Compile.tryArgClassOk_of_functionE h1, h2, h3, h4, h5, h6, h7, h8,
    lowerScopeTB_of_lowerScopeB h9, h10, h11, h12, h13, h14, h15, h1, Bool.and_self,
    Bool.true_and, Bool.and_true, Bool.true_or]

/-- **Integer inclusion** of crates: `InScopeIn I → InScopeInT I`. -/
theorem inScopeInT_of_inScopeIn {I : LinkInput} (h : InScopeIn I = true) : InScopeInT I = true := by
  simp only [InScopeIn, Bool.and_eq_true, List.all_eq_true] at h
  simp only [InScopeInT, Bool.and_eq_true, List.all_eq_true]
  exact ⟨h.1, fun g hg => fnScopeInTB_of_fnScopeInB (h.2 g hg)⟩

/-- `lowerScopeTB` of a subset-E function is `lowerScopeB`. -/
theorem lowerScopeB_of_lowerScopeTB {f : Clif.Function} (h : lowerScopeTB f = true)
    (hE : Compile.functionE f = true) : lowerScopeB f = true := by
  unfold lowerScopeTB at h
  unfold lowerScopeB
  rw [Compile.functionET_of_functionE hE] at h
  rw [hE]
  exact h

/-- **Back to the integer input scope**: a subset-E function of the typed input scope is in
`fnScopeInB`. -/
theorem fnScopeInB_of_fnScopeInTB {g : Clif.Function} (h : fnScopeInTB g = true)
    (hE : Compile.functionE g = true) : fnScopeInB g = true := by
  obtain ⟨-, -, -, h4a, h4b, h5, h6, h7, h8, h9, h10, h11, h12, h13a, h13b, h13c, h13d, h14, -⟩ :=
    fnScopeInT_parts h
  simp only [fnScopeInB, hE, h4a, h4b, h5, h6, h7, h8, h9, h10, lowerScopeB_of_lowerScopeTB h11 hE,
    h12, h13a, h13b, h13c, h13d, h14, Bool.and_self, Bool.true_and, Bool.and_true]

/-- **Outside subset E, the typed input scope is in the typed scope** `fnScopeTB`: `lowersTB`
from `lowerOutTB` and `prepare`'s totality (`Prep.prepare_okT`). -/
theorem fnScopeTB_of_inT {g : Clif.Function} (h : fnScopeInTB g = true)
    (hE : Compile.functionE g = false) : fnScopeTB g = true := by
  obtain ⟨h1, h2, h3, h4a, h4b, h5, h6, h7, h8, h9, h10, h11, h12, h13a, -, -, -, h14, hor⟩ :=
    fnScopeInT_parts h
  obtain ⟨hrc, hout⟩ := hor.resolve_left (by rw [hE]; decide)
  obtain ⟨vc, hl, hcs, hpost⟩ := lowerOutTB_spec hout
  obtain ⟨vcp, hp⟩ := Prep.prepare_okT (dominated_of h10) (lowerScopeT_of h11) hl
  obtain ⟨hem, hfc, -, -⟩ := hpost vcp hp
  have hk := killFreeB_of_scopeT h10 h11 h4a h4b h5 h12 h3 hl hp
  have hsz : spillSizeOkB vcp = true := by
    simp only [emitCondsB, Bool.and_eq_true] at hem
    exact hem.1.1.1
  have hlo : lowersTB g = true := by
    simp only [lowersTB, h13a, hl, hcs, hp, hsz, hfc, hk, Bool.and_self, Bool.true_and]
  simp only [fnScopeTB, h1, h2, h3, h4a, h4b, h5, h6, h7, h8, h9, h10, h11, h12, hrc, hlo, h14,
    Bool.and_self, Bool.true_and, Bool.and_true]

/-- **The compiler's pipeline succeeds on every function of the typed input scope**, whatever
the untrusted allocator answered (`o`), and its artifact passes the typed lowering validator
(`lowerCheckT`), the `prepare` validator, `AllocChecked` and the covered forms: `pipeT_ok` over
the typed scope. A subset-E function goes through `pipeT_ok` (`fnScopeInB_of_fnScopeInTB`); any
other through `Prep.prepare_okT` (`prepare`), slice 6's spill acceptance and
`backend_total_emitT` (allocation, emission, layout), with `lowerOutTB`'s run-time facts. -/
theorem pipeT_okT {g : Clif.Function} (h : fnScopeInTB g = true) (k : Nat) (base : BitVec 64)
    (o : Lean.Json) :
    ∃ a, pipeT g k base o = .ok a ∧ lowerCheckT g a.vc = true ∧ prepCheck a.vc a.vcp = true ∧
      AllocChecked a.vcp a.rf ∧ FormsCovered ⟨a.fa.k, a.af.slotBase⟩ a.vcp := by
  by_cases hE : Compile.functionE g = true
  · have hsc := fnScopeB_of_input (fnScopeInB_of_fnScopeInTB h hE)
    obtain ⟨-, -, -, -, -, -, -, hd, hs, -⟩ := fnScope_parts hsc
    obtain ⟨a, ha, -, hpc, hca, hcov⟩ := pipeT_ok hsc spillDefinedHyp k base o
    obtain ⟨hl, -⟩ := pipeT_spec ha
    exact ⟨a, ha, lowerCheckT_complete_int (dominated_of hd) (lowerScope_of hs) hl, hpc,
      allocChecked_of_checkAlloc hca, hcov⟩
  · obtain ⟨-, -, htc, habi, hext, hind, -, -, -, -, hd, hs, har, -, -, -, -, -, hor⟩ :=
      fnScopeInT_parts h
    obtain ⟨hrc, hout⟩ := hor.resolve_left hE
    obtain ⟨vc, hl, hcs, hpost⟩ := lowerOutTB_spec hout
    have hD := dominated_of hd
    have hS := lowerScopeT_of hs
    obtain ⟨vcp, hp⟩ := Prep.prepare_okT hD hS hl
    obtain ⟨hem, hfc, -, hci⟩ := hpost vcp hp
    have hk := killFreeB_of_scopeT hd hs habi hext hind har htc hl hp
    have hcov := (formsCoveredB_iff _ _).mp hfc
    obtain ⟨hacc, af, ha, fa, fb, he, hla⟩ := backend_total_emitT hD hS (arityOk_of har) htc
      (resClassOk_of_resClassOkB hrc) hl hp (ctlSpill_of_ctlSpillB hcs) hcov hk
      (ctlInsts_of_ctlInstsB hci) hem (raAnswer vcp o) k
    refine ⟨⟨k, vc, vcp, allocResult vcp (readyAnswer vcp (raAnswer vcp o)), af, fa, fb, base⟩,
      ?_, lowerCheckT_complete hD hS hl, Prep.prepCheck_complete hp (prepDomain_ofT hD hS hl),
      hacc, formsCovered_ctx hcov _⟩
    simp [pipeT, pipeTWithLowering, Backend.Stock.D0.defaultLower_eq_legacy, hl, hp, ha, he, hla,
      bind, Except.bind, pure, Except.pure]

/-- **Every function of a crate in the typed input scope compiles** (`results_of` over
`InScopeInT`): the compiler's pipeline succeeds on each. -/
theorem resultsT_ok_inT {I : LinkInput} (hin : InScopeInT I = true) :
    I.resultsT.all (·.2.toBool) = true := by
  simp only [InScopeInT, Bool.and_eq_true, List.all_eq_true] at hin
  rw [List.all_eq_true]
  intro e he
  obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 he
  have hsc := hin.2 fi.func (List.mem_map_of_mem hfi)
  obtain ⟨a, ha, -⟩ := pipeT_okT hsc fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j)
  simp only [ha]
  rfl

/-- **Integer corollary**: every function of an `InScopeIn` crate compiles, through the typed
theorem (`inScopeInT_of_inScopeIn`). -/
theorem resultsT_ok_input {I : LinkInput} (hin : InScopeIn I = true) :
    I.resultsT.all (·.2.toBool) = true :=
  resultsT_ok_inT (inScopeInT_of_inScopeIn hin)

/-- **`lowerOutTB`'s `killFreeB` conjunct is implied by the rest of the typed input scope.** -/
theorem killFreeB_of_fnScopeInT {g : Clif.Function} {vc vcp : VCode} (h : fnScopeInTB g = true)
    (hl : lowerFunction g = .ok vc) (hp : Backend.prepare vc = .ok vcp) :
    Spill.killFreeB vcp = true := by
  obtain ⟨-, -, htc, habi, hext, hind, -, -, -, -, hd, hs, har, -⟩ := fnScopeInT_parts h
  exact killFreeB_of_scopeT hd hs habi hext hind har htc hl hp


end E2E.LinkCheck

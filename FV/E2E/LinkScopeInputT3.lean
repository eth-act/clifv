import FV.E2E.LinkScopeInputDefsT3
import FV.E2E.LinkScopeCtlT2
import FV.E2E.LinkScopeInputCleanupT
import FV.E2E.LinkScopeIntT
import FV.E2E.EmitCondsT
import FV.Backend.Proof.IselPrgDriverT

/-!
# The typed input conditions without the run-time decider: the checks are theorems (S11, #35)

On `fnScopeInTB3` (`LinkScopeInputDefsT3.lean`) every run-time check of `fnScopeInTB2` holds:

* `lowerOutTB_of_T3`: `lowerFunction` succeeds (`Prg.lowerFunction_ok_inputT`), `ctlSpillB` of its
  output and, of `prepare`'s output, `emitCondsB` (`emitConds_lowerT`, the literal loads' reach
  `poolReachB_of_T3`), `formsCoveredB` (`Driver.formsCoveredB_completeT`), `killFreeB`
  (`killFreeB_of_scopeT`) and `ctlInstsB`;
* `resClassOkB_of_T3`; hence `fnScopeInTB2_of_T3`, `fnScopeInTB_of_T3`, `inScopeInT_of_T3`.

Consequences: the per-function totality `pipeT_okT3`, `pipeCleanupT_okT3` (`pipeT_okT`,
`pipeCleanupT_okT`), `resultsT_ok_inT3`, `resultsCleanupT_ok_inT3`, and `inScopePT_of_inT3`
(`InScopeInT3` is inside `InScopePT`, the scope of `compileExe_correctT`).
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

theorem fnScopeInT3_parts {g : Clif.Function} (h : fnScopeInTB3 g = true) :
    Compile.functionET g = true ∧ Compile.storeTypedB g = true ∧ Compile.tryArgClassOk g = true ∧
    sigAbiOk g.sig = true ∧ g.externs.all (fun e => sigAbiOk e.2.sig) = true ∧
    indSigsOk g = true ∧ decide (regLocs g.sig).Nodup = true ∧
    (regLocs g.sig).all (·.isArgReg) = true ∧
    g.sig.params.all (fun p => decide (p.ty.width ≤ 64)) = true ∧ linkFreeB g = true ∧
    dominatedB g = true ∧ lowerScopeTB g = true ∧ Spill.arityOkB g = true ∧
    extendsWidenB g = true ∧ sizeOkB g = true ∧ driverInB g = true ∧ Prg.iselInB g = true ∧
    Spill.entryParamsB g = true ∧ entryClassOkB g = true ∧ Compile.selectTypedB g = true ∧
    bitcastWidthB g = true ∧ poolReachInB g = true := by
  simp only [fnScopeInTB3, Bool.and_eq_true, and_assoc] at h
  exact h

/-- **`resClassOkB` holds on `fnScopeInTB3`.** -/
theorem resClassOkB_of_T3 {g : Clif.Function} (h : fnScopeInTB3 g = true) :
    Spill.resClassOkB g = true := by
  obtain ⟨-, hst, -, -, -, -, -, -, -, -, hd, hs, -, -, -, -, -, -, -, hsel, -⟩ :=
    fnScopeInT3_parts h
  exact resClassOkB_of (Spill.resClassOk_of_lowerScopeT hd (lowerScopeT_of hs) hst hsel)

/-- **The literal loads reach the pool on `fnScopeInTB3`** (#565): below `2 ^ 17` words by the
input bound (`poolReachB_of_sizeT`), else `poolReachInB`'s run-time check. -/
theorem poolReachB_of_T3 {g : Clif.Function} {vc vcp : VCode} (h : fnScopeInTB3 g = true)
    (hl : lowerFunction g = .ok vc) (hp : prepare vc = .ok vcp) : poolReachB vcp = true := by
  obtain ⟨-, hst, -, -, -, -, -, -, -, -, hd, hs, -, -, -, -, -, -, -, hsel, -, hpr⟩ :=
    fnScopeInT3_parts h
  simp only [poolReachInB, Bool.or_eq_true, decide_eq_true_eq] at hpr
  rcases hpr with h17 | hn
  · exact poolReachB_of_sizeT hd (lowerScopeT_of hs) hst hsel h17 hl hp
  · simp only [hl, hp] at hn
    exact poolReachB_of_noPool hn

/-- **`lowerOutTB` holds on `fnScopeInTB3`**: every run-time check of the typed input scope is a
theorem on the decided input checks. -/
theorem lowerOutTB_of_T3 {g : Clif.Function} (h : fnScopeInTB3 g = true) : lowerOutTB g = true := by
  obtain ⟨hET, hst, htc, habi, hext, hind, -, -, -, -, hd, hs, har, hw, hsz, hdrv, hin, hent, hec,
    hsel, hbw, -⟩ := fnScopeInT3_parts h
  have hS := lowerScopeT_of hs
  obtain ⟨vc, hl⟩ := Prg.lowerFunction_ok_inputT hET habi hd hS har hent hw hdrv hin
  have ha := abiSigsOk_of_checks habi hext hind
  have hE := entryClassOk_of hec
  have hcs := Spill.ctlSpillB_of (Spill.ctlSpillHypT_of CovT.iselCtlHypT hd hS hst hsel ha hE hl)
  unfold lowerOutTB
  rw [hl]
  simp only [hcs, Bool.true_and]
  split
  · rename_i vcp hp
    rw [emitConds_lowerT hd hS hst hsel hw hbw hsz hl hp (poolReachB_of_T3 h hl hp),
      Driver.formsCoveredB_completeT hd hS hst hsel hl hp default,
      killFreeB_of_scopeT hd hs habi hext hind har htc hl hp,
      ctlInstsB_of (ctlInsts_pipelineT CovT.iselCtlHypT hd hS hst hsel ha hE hl hp)]
    rfl
  · rfl

/-- **`fnScopeInTB3` is inside `fnScopeInTB2`.** -/
theorem fnScopeInTB2_of_T3 {g : Clif.Function} (h : fnScopeInTB3 g = true) :
    fnScopeInTB2 g = true := by
  have hrc := resClassOkB_of_T3 h
  have hout := lowerOutTB_of_T3 h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, -⟩ := fnScopeInT3_parts h
  simp only [fnScopeInTB2, fnScopeInTB, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, hrc, hout, Bool.and_self, Bool.or_true]

/-- `fnScopeInTB3` is inside `fnScopeInTB`. -/
theorem fnScopeInTB_of_T3 {g : Clif.Function} (h : fnScopeInTB3 g = true) : fnScopeInTB g = true :=
  fnScopeInTB_of_T2 (fnScopeInTB2_of_T3 h)

/-- `InScopeInT3` is inside `InScopeInT2`. -/
theorem inScopeInT2_of_T3 {I : LinkInput} (h : InScopeInT3 I = true) : InScopeInT2 I = true := by
  simp only [InScopeInT3, Bool.and_eq_true, List.all_eq_true] at h
  simp only [InScopeInT2, Bool.and_eq_true, List.all_eq_true]
  exact ⟨h.1, fun g hg => fnScopeInTB2_of_T3 (h.2 g hg)⟩

/-- `InScopeInT3` is inside `InScopeInT`. -/
theorem inScopeInT_of_T3 {I : LinkInput} (h : InScopeInT3 I = true) : InScopeInT I = true :=
  inScopeInT_of_T2 (inScopeInT2_of_T3 h)

/-- The four run-time checks and the emission conditions on `fnScopeInTB3`. -/
theorem ctlSpillB_of_T3 {g : Clif.Function} {vc : VCode} (h : fnScopeInTB3 g = true)
    (hl : lowerFunction g = .ok vc) : Spill.ctlSpillB vc = true :=
  ctlSpillB_of_T2 (fnScopeInTB2_of_T3 h) hl

theorem ctlInstsB_of_T3 {g : Clif.Function} {vc vcp : VCode} (h : fnScopeInTB3 g = true)
    (hl : lowerFunction g = .ok vc) (hp : prepare vc = .ok vcp) : ctlInstsB vcp = true :=
  ctlInstsB_of_T2 (fnScopeInTB2_of_T3 h) hl hp

theorem formsCoveredB_of_T3 {g : Clif.Function} {vc vcp : VCode} (h : fnScopeInTB3 g = true)
    (hl : lowerFunction g = .ok vc) (hp : prepare vc = .ok vcp) (cx : FnCtx) :
    formsCoveredB cx vcp = true :=
  formsCoveredB_of_T2 (fnScopeInTB2_of_T3 h) hl hp cx

theorem emitCondsB_of_T3 {g : Clif.Function} {vc vcp : VCode} (h : fnScopeInTB3 g = true)
    (hl : lowerFunction g = .ok vc) (hp : prepare vc = .ok vcp) : emitCondsB vcp = true := by
  obtain ⟨-, hst, -, -, -, -, -, -, -, -, hd, hs, -, hw, hsz, -, -, -, -, hsel, hbw, -⟩ :=
    fnScopeInT3_parts h
  exact emitConds_lowerT hd (lowerScopeT_of hs) hst hsel hw hbw hsz hl hp (poolReachB_of_T3 h hl hp)

/-- **`lowerFunction` succeeds on `fnScopeInTB3`** (`Prg.lowerFunction_ok_inputT`). -/
theorem lowerFunction_ok_T3 {g : Clif.Function} (h : fnScopeInTB3 g = true) :
    ∃ vc, lowerFunction g = .ok vc := by
  obtain ⟨hET, -, -, habi, -, -, -, -, -, -, hd, hs, har, hw, -, hdrv, hin, hent, -⟩ :=
    fnScopeInT3_parts h
  exact Prg.lowerFunction_ok_inputT hET habi hd (lowerScopeT_of hs) har hent hw hdrv hin

/-- **The compiler's pipeline succeeds on every function of `fnScopeInTB3`** (`pipeT_okT`). -/
theorem pipeT_okT3 {g : Clif.Function} (h : fnScopeInTB3 g = true) (k : Nat) (base : BitVec 64)
    (o : Lean.Json) :
    ∃ a, pipeT g k base o = .ok a ∧ lowerCheckT g a.vc = true ∧ prepCheck a.vc a.vcp = true ∧
      AllocChecked a.vcp a.rf ∧ FormsCovered ⟨a.fa.k, a.af.slotBase⟩ a.vcp :=
  pipeT_okT (fnScopeInTB_of_T3 h) k base o

/-- **The pipeline with dead-instruction cleanup succeeds on every function of `fnScopeInTB3`**
(`pipeCleanupT_okT`). -/
theorem pipeCleanupT_okT3 {g : Clif.Function} (h : fnScopeInTB3 g = true) (k : Nat)
    (base : BitVec 64) (o : Lean.Json) :
    ∃ a, pipeCleanupT g k base o = .ok a ∧ lowerCheckT g a.vc = true ∧
      prepCheck (Backend.DeadCleanup.prune a.vc) a.vcp = true ∧ AllocChecked a.vcp a.rf ∧
      FormsCovered ⟨a.fa.k, a.af.slotBase⟩ a.vcp :=
  pipeCleanupT_okT (fnScopeInTB_of_T3 h) k base o

theorem resultsT_ok_inT3 {I : LinkInput} (hin : InScopeInT3 I = true) :
    I.resultsT.all (·.2.toBool) = true :=
  resultsT_ok_inT (inScopeInT_of_T3 hin)

theorem resultsCleanupT_ok_inT3 {I : LinkInput} (hin : InScopeInT3 I = true) :
    I.resultsCleanupT.all (·.2.toBool) = true :=
  resultsCleanupT_ok_inT (inScopeInT_of_T3 hin)

/-- **`InScopeInT` is inside `InScopePT`**: a subset-E function through `fnScopeB_of_input`,
any other through `fnScopeTB_of_inT`. -/
theorem inScopePT_of_inT {I : LinkInput} (h : InScopeInT I = true) : InScopePT I = true := by
  simp only [InScopeInT, Bool.and_eq_true, List.all_eq_true] at h
  simp only [InScopePT, Bool.and_eq_true, List.all_eq_true]
  refine ⟨progScopeB_of_input h.1, fun g hg => ?_⟩
  by_cases hE : Compile.functionE g = true
  · exact fnScopeTB_of_fnScopeB (fnScopeB_of_input (fnScopeInB_of_fnScopeInTB (h.2 g hg) hE))
  · exact fnScopeTB_of_inT (h.2 g hg) (by simpa using hE)

/-- `InScopeInT3` is inside `InScopePT`. -/
theorem inScopePT_of_inT3 {I : LinkInput} (h : InScopeInT3 I = true) : InScopePT I = true :=
  inScopePT_of_inT (inScopeInT_of_T3 h)

end E2E.LinkCheck

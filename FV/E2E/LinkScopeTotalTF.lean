import FV.E2E.LinkScopeChecksTF
import FV.E2E.LinkScopeInputDefsTC
import FV.E2E.LinkScopeInputCleanupT
import FV.E2E.SpillKillFreeT
import FV.Backend.Proof.LowerCompleteTCF

/-!
# Decider-free totality over the float scope (S11f, #35, stage 2)

`fnScopeInTB3F g`: `fnScopeInTB3`'s decided input checks (`LinkScopeInputDefsT3.lean`) over the
float scope: `lowerScopeTFB` (the scope `Compile.functionETF`: float arithmetic, rounding,
conversions, scalar `fcmp`) for `Compile.functionET`/`lowerScopeTB`, plus `Compile.floatArgsTyped`
(the float operands of the float operations are float-defined; without it a `fadd` of an
integer-defined value lowers to an `fpu_rrr` reading an integer vreg), and the literal loads' reach
`poolReachInB` (#565, as in `fnScopeInTB3`). Only `poolReachInB` may run the compiler, and only
for a function whose size bound `sizeBoundIn` is at least `2 ^ 17` words.

* `lowersTCB_of_T3F`: the run-time decider of the typed-try_call scope `lowersTCB`
  (`lowerFunction` succeeds and its output passes the float validator `lowerCheckTCF`) is a
  theorem (`lowerFunction_ok_inT3F`, `Driver.lowerCheckTCF_complete`);
  `fnScopeInTCB_of_T3F`: so `fnScopeInTB3F` is inside `fnScopeInTCB`;
* `pipeCleanupT_okT3F`: the cleanup pipeline `pipeCleanupT` succeeds on every function of
  `fnScopeInTB3F`, whatever the untrusted allocator answered, with the artifact passing
  `lowerCheckTCF`, the `prepare` validator on the pruned code, `AllocChecked` and the covered forms
  (`pipeCleanupT_okT`'s non-E branch over `LowerScopeTF`: `Prep.prepare_okTF`,
  `backend_total_emit_cleanupTF`, `spillKillFreeTF` and the run-time checks of
  `LinkScopeChecksTF.lean`); `resultsCleanupT_ok_inT3F`: every function of an `InScopeInT3F`
  crate compiles with cleanup.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.DeadCleanup

/-- **The float per-function input conditions without the run-time decider.** -/
def fnScopeInTB3F (g : Clif.Function) : Bool :=
  Compile.storeTypedB g && Compile.tryArgClassOk g && Compile.floatArgsTyped g &&
  (sigAbiOk g.sig && g.externs.all (fun e => sigAbiOk e.2.sig)) && indSigsOk g &&
  decide (regLocs g.sig).Nodup && (regLocs g.sig).all (·.isArgReg) &&
  g.sig.params.all (fun p => decide (p.ty.width ≤ 64)) && linkFreeB g &&
  dominatedB g && lowerScopeTFB g && Spill.arityOkB g &&
  (extendsWidenB g && sizeOkB g && driverInB g && Prg.iselInB g) && Spill.entryParamsB g &&
  entryClassOkB g && Compile.selectTypedB g && Driver.bitcastWidthB g && poolReachInB g

/-- **`InScopeInT3F`**: `InScopeInT3` with `fnScopeInTB3F`. -/
def InScopeInT3F (I : LinkInput) : Bool :=
  progScopeInB I.prog (fun n => I.syms.lookup n) && I.prog.funcs.all fnScopeInTB3F

theorem fnScopeInT3F_parts {g : Clif.Function} (h : fnScopeInTB3F g = true) :
    Compile.storeTypedB g = true ∧ Compile.tryArgClassOk g = true ∧
    Compile.floatArgsTyped g = true ∧
    sigAbiOk g.sig = true ∧ g.externs.all (fun e => sigAbiOk e.2.sig) = true ∧
    indSigsOk g = true ∧ decide (regLocs g.sig).Nodup = true ∧
    (regLocs g.sig).all (·.isArgReg) = true ∧
    g.sig.params.all (fun p => decide (p.ty.width ≤ 64)) = true ∧ linkFreeB g = true ∧
    dominatedB g = true ∧ lowerScopeTFB g = true ∧ Spill.arityOkB g = true ∧
    extendsWidenB g = true ∧ sizeOkB g = true ∧ driverInB g = true ∧ Prg.iselInB g = true ∧
    Spill.entryParamsB g = true ∧ entryClassOkB g = true ∧ Compile.selectTypedB g = true ∧
    bitcastWidthB g = true ∧ poolReachInB g = true := by
  simp only [fnScopeInTB3F, Bool.and_eq_true, and_assoc] at h
  exact h

/-- **The literal loads reach the pool on `fnScopeInTB3F`** (#565): below `2 ^ 17` words by the
input bound (`poolReachB_of_sizeTF`), else `poolReachInB`'s run-time check. -/
theorem poolReachB_of_T3F {g : Clif.Function} {vc vcp : VCode} (h : fnScopeInTB3F g = true)
    (hl : lowerFunction g = .ok vc) (hp : prepare vc = .ok vcp) : poolReachB vcp = true := by
  obtain ⟨hst, -, hfa, -, -, -, -, -, -, -, hd, hs, -, -, -, -, -, -, -, hsel, -, hpr⟩ :=
    fnScopeInT3F_parts h
  simp only [poolReachInB, Bool.or_eq_true, decide_eq_true_eq] at hpr
  rcases hpr with h17 | hn
  · exact poolReachB_of_sizeTF hd (lowerScopeTF_of hs) hfa hst hsel h17 hl hp
  · simp only [hl, hp] at hn
    exact poolReachB_of_noPool hn

/-- **The float scope is in the scope with typed `try_call`s and the float operations.** -/
theorem functionETCF_of_functionETF {f : Clif.Function} (h : Compile.functionETF f = true) :
    Compile.functionETCF f = true := by
  simp only [Compile.functionETF, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hs, hg⟩, hx⟩, hb⟩, ho⟩, he⟩, -⟩ := h
  simp only [Compile.functionETCF, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨hs, hg⟩, ?_⟩, Compile.callsE_of_externs hx⟩, hb⟩, ?_⟩, he⟩
  · exact List.all_eq_true.mpr fun p hp => Compile.sigET_of_sigE (List.all_eq_true.mp hx p hp)
  · simp only [Compile.opsTypedTF, Compile.opsTypedTCF, Bool.and_eq_true, List.all_eq_true] at ho ⊢
    exact fun b hb' => ⟨(ho b hb').1, fun x hx => (ho b hb').2 x (Compile.termIntOperandsC_sub _ x hx)⟩

/-- `driverInB` contains `driverInTCB`. -/
theorem driverInTCB_of_driverInB {g : Clif.Function} (h : driverInB g = true) :
    driverInTCB g = true := by
  simp only [driverInB, driverInTCB, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun B hB => (h.2 B hB).1⟩

/-- **The run-time decider `lowersTCB` holds on `fnScopeInTB3F`**: `lowerFunction` succeeds
(`lowerFunction_ok_inT3F`) and its output passes the float validator `lowerCheckTCF`
(`Driver.lowerCheckTCF_complete`). -/
theorem lowersTCB_of_T3F {g : Clif.Function} (h : fnScopeInTB3F g = true) : lowersTCB g = true := by
  obtain ⟨-, -, -, habi, -, -, -, -, -, -, hd, hs, har, hw, -, hdrv, hin, hent, -⟩ :=
    fnScopeInT3F_parts h
  obtain ⟨vc, hl⟩ := lowerFunction_ok_inT3F habi hd hs har hent hw hdrv hin
  unfold lowersTCB
  rw [hl]
  exact lowerCheckTCF_complete (dominated_of hd) (lowerScopeTF_of hs) hl

/-- **`fnScopeInTB3F` is inside `fnScopeInTCB`**: the decided input checks give the
typed-try_call scope's run-time decider (`lowersTCB_of_T3F`) and `Spill.resClassOkB`
(`resClassOkB_of_TF`). -/
theorem fnScopeInTCB_of_T3F {g : Clif.Function} (h : fnScopeInTB3F g = true) :
    fnScopeInTCB g = true := by
  have hlow := lowersTCB_of_T3F h
  obtain ⟨hst, -, hfa, habi, hext, hind, h7, h8, h9, h10, hd, hs, har, hw, hsz, hdrv, -, hent,
    -, hsel, -⟩ := fnScopeInT3F_parts h
  have hrc := resClassOkB_of_TF hd hs hfa hst hsel
  have hE : Compile.functionETCF g = true :=
    functionETCF_of_functionETF (lowerScopeTF_of hs).subsetTF
  simp only [fnScopeInTCB, hE, hst, habi, hext, hind, h7, h8, h9, h10, hd, har, hw, hsz,
    driverInTCB_of_driverInB hdrv, hent, hrc, hlow, Bool.and_self, Bool.or_true]

/-- **The cleanup pipeline succeeds on every function of `fnScopeInTB3F`**, whatever the
untrusted allocator answered (`o`), and its artifact passes the float lowering validator
(`lowerCheckTCF`), the `prepare` validator on the pruned code, `AllocChecked` and the covered
forms. -/
theorem pipeCleanupT_okT3F {g : Clif.Function} (h : fnScopeInTB3F g = true) (k : Nat)
    (base : BitVec 64) (o : Lean.Json) :
    ∃ a, pipeCleanupT g k base o = .ok a ∧ lowerCheckTCF g a.vc = true ∧
      prepCheck (prune a.vc) a.vcp = true ∧ AllocChecked a.vcp a.rf ∧
      FormsCovered ⟨a.fa.k, a.af.slotBase⟩ a.vcp := by
  obtain ⟨hst, htc, hfa, habi, hext, hind, -, -, -, -, hd, hs, har, hw, hsz, hdrv, hin, hent,
    hec, hsel, hbw, -⟩ := fnScopeInT3F_parts h
  obtain ⟨vc, hl⟩ := lowerFunction_ok_inT3F habi hd hs har hent hw hdrv hin
  have hD := dominated_of hd
  have hS := lowerScopeTF_of hs
  have ha := abiSigsOk_of_checks habi hext hind
  have hE := entryClassOk_of hec
  have hcs := ctlSpillB_of_TF hd hS hfa hst hsel ha hE hl
  obtain ⟨vcp, hp⟩ := Prep.prepare_okTF hS hl
  have hem := emitConds_lowerTF hd hS hfa hst hsel hw hbw hsz hl hp (poolReachB_of_T3F h hl hp)
  have hcov := formsCovered_completeTF hd hS hfa hst hsel hl hp default
  have hk := spillKillFreeTF hD hS ha (arityOk_of har) htc hl hp
  have hci := ctlInsts_pipelineTF hd hS hfa hst hsel ha hE hl hp
  have hrc := resClassOk_of_lowerScopeTF hd hS hfa hst hsel
  have hp' := prune_prepare_ok hp
  obtain ⟨hacc, af, ha', fa, fb, he, hla⟩ := backend_total_emit_cleanupTF hD hS (arityOk_of har)
    htc hrc hl hp (ctlSpill_of_ctlSpillB hcs) hcov hk hci hem
    (raAnswer (preparedCleanup vc vcp) o) k
  refine ⟨⟨k, vc, preparedCleanup vc vcp, allocResult (preparedCleanup vc vcp)
      (readyAnswer (preparedCleanup vc vcp) (raAnswer (preparedCleanup vc vcp) o)), af, fa, fb,
      base⟩, ?_, lowerCheckTCF_complete hD hS hl,
    Prep.prepCheck_complete hp' (prune_prepDomain (prepDomain_ofTF hS hl)), hacc,
    formsCovered_ctx (preparedCleanup_formsCovered hcov) _⟩
  simp [pipeCleanupT, pipeTWithLowering, Backend.Stock.D0.defaultLower_eq_legacy, hl, hp', ha',
    he, hla, bind, Except.bind, pure, Except.pure]

/-- **Every function of a crate in `InScopeInT3F` compiles with cleanup**
(`resultsCleanupT_ok_inT` over the float scope, without the run-time decider). -/
theorem resultsCleanupT_ok_inT3F {I : LinkInput} (hin : InScopeInT3F I = true) :
    I.resultsCleanupT.all (·.2.toBool) = true := by
  simp only [InScopeInT3F, Bool.and_eq_true, List.all_eq_true] at hin
  rw [List.all_eq_true]
  intro e he
  obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 he
  have hsc := hin.2 fi.func (List.mem_map_of_mem hfi)
  obtain ⟨a, ha, -⟩ := pipeCleanupT_okT3F hsc fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name))
    (raJ fi.ra fi.j)
  simp only [ha]
  rfl

end E2E.LinkCheck

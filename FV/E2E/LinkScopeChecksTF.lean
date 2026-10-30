import FV.Backend.Proof.IselDriversTF
import FV.Backend.Proof.SpillResClassTF
import FV.Backend.Proof.FormsCoverCompleteT
import FV.E2E.EmitCondsT
import FV.E2E.SpillCtlCheckT
import FV.E2E.LinkScopeIntT
import FV.E2E.LinkScopeInputT3F

/-!
# The run-time checks on the float scope (S11f, #35, #686 stage 2)

On the float scope (`Backend.Proof.Driver.LowerScopeTF`, decided by `LinkCheck.lowerScopeTFB`)
whose float positions are float-defined (`Compile.floatArgsTyped`), with the conditions of the
typed scope's theorems, the run-time checks of the lowering's output hold:

* `Spill.resClassOkB` (`resClassOkB_of_TF`, from `Spill.resClassOk_of_lowerScopeTF`);
* `Spill.ctlSpillB` of `lowerFunction`'s output (`ctlSpillB_of_TF`, `Spill.ctlSpillHypG_of`
  with `CovT.iselCtlOnF`);
* of `prepare`'s output: `formsCoveredB` (`formsCoveredB_completeTF`), `ctlInstsB`
  (`ctlInsts_pipelineTF`), `emitCondsB` (`emitConds_lowerTF`; also after the dead-code cleanup,
  `emitConds_cleanup_lowerTF`).

The analyses' tables cover the float families 31-35 of `CovT.famTab`; `prepare`'s domain comes
from `Spill.prepDomain_ofTF` (no lowering validator).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- **Completeness of `formsCoveredB` on the float scope** (`formsCovered_completeT`). -/
theorem formsCovered_completeTF {f : Clif.Function} {vc vcp : VCode} (hdom : dominatedB f = true)
    (hs : LowerScopeTF f) (hfa : Compile.floatArgsTyped f = true)
    (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true)
    (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp) (cx : FnCtx) :
    FormsCovered cx vcp :=
  formsCovered_of_runsG hs.externsE (Spill.prepDomain_ofTF hs hl) hl hp (fun ctx ranges st0 hb => by
    have hctx : CtxInvT f ctx := ctxInvT_ofF hs hb
    have hcl : Cov.Clean ctx := Cov.clean_of_build hb
    have hfam := CovT.famCover_ofF hs hfa hdom hst hsel hb
    have hx := hs.externsE
    refine ⟨fun ii info inst s out s' tr hi hc h => ?_, fun B hB ti data targets s out s' tr _ hph _ hd h =>
      CovT.termCall_covT Cov.logicImmComplete hctx hcl hfam hph hd
        (CovT.termFam_ofF hs hb hB (.inl hd)) h,
      fun B hB ti data trs targets s out s' tr _ hph hd h =>
      CovT.tryCall_covT Cov.logicImmComplete hctx hcl hfam hph hd
        (CovT.termFam_ofF hs hb hB (.inr hd)) h⟩
    obtain ⟨h1, h2⟩ := CovT.stmt_covT Cov.logicImmComplete hctx hx hcl hfam hi hc h
    refine ⟨h1, fun rss hout hne rs hrs r hr => ?_⟩
    obtain ⟨n, c, hrc, -⟩ := h2 rss hout hne rs hrs r hr
    exact ⟨n, c, hrc⟩) cx

/-- `formsCovered_completeTF`, decided: `formsCoveredB` holds of `prepare (lowerFunction f)`. -/
theorem formsCoveredB_completeTF {f : Clif.Function} {vc vcp : VCode} (hdom : dominatedB f = true)
    (hs : LowerScopeTF f) (hfa : Compile.floatArgsTyped f = true)
    (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true)
    (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp) (cx : FnCtx) :
    formsCoveredB cx vcp = true :=
  (formsCoveredB_iff cx vcp).mpr (formsCovered_completeTF hdom hs hfa hst hsel hl hp cx)

end Backend.Proof.Driver

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **`ctlSpillB` of the float scope's lowering** (`ctlSpillHypT_of`). -/
theorem ctlSpillB_of_TF {f : Clif.Function} {vc : VCode} (hdom : dominatedB f = true)
    (hs : LowerScopeTF f) (hfa : Compile.floatArgsTyped f = true)
    (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true)
    (ha : Spill.AbiSigsOk f) (hec : EntryClassOk f) (hl : lowerFunction f = .ok vc) :
    Spill.ctlSpillB vc = true :=
  Spill.ctlSpillB_of (Spill.ctlSpillHypG_of hs.externsE (CovT.iselCtlOnF hdom hs hfa hst hsel ha)
    hdom ha hec hl)

/-- **The instruction part of `ctlCheck` on the float scope's pipeline** (`ctlInsts_pipelineT`). -/
theorem ctlInsts_pipelineTF {f : Clif.Function} {vc vcp : VCode} (hdom : dominatedB f = true)
    (hs : LowerScopeTF f) (hfa : Compile.floatArgsTyped f = true)
    (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true)
    (ha : Spill.AbiSigsOk f) (hec : EntryClassOk f) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare vc = .ok vcp) : CtlInsts vcp :=
  ctlInsts_pipelineG hs.externsE (CovT.iselCtlOnF hdom hs hfa hst hsel ha)
    (Spill.prepDomain_ofTF hs hl) hdom ha hec hl hp

/-- **The size bound on the float scope** (`spillSizeOkB_of_sizeOkBT`). -/
theorem spillSizeOkB_of_sizeOkBTF {f : Clif.Function} {vc vcp : VCode}
    (hdom : dominatedB f = true) (hs : LowerScopeTF f) (hfa : Compile.floatArgsTyped f = true)
    (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true)
    (hsz : sizeOkB f = true) (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp) :
    spillSizeOkB vcp = true := by
  have h := spillWordBound_le_sizeBoundInT (iselSzTF hdom hs hfa hst hsel) hs.externsE hl hp
  have hb : sizeBoundIn f < 2 ^ 24 := of_decide_eq_true hsz
  exact decide_eq_true (by omega)

/-- `spillSizeOkB_of_sizeOkBTF` through the dead-code cleanup (`prepare (prune vc)`). -/
theorem spillSizeOkB_cleanup_of_sizeOkBTF {f : Clif.Function} {vc vcp : VCode}
    (hdom : dominatedB f = true) (hs : LowerScopeTF f) (hfa : Compile.floatArgsTyped f = true)
    (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true)
    (hsz : sizeOkB f = true) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare (prune vc) = .ok vcp) : spillSizeOkB vcp = true := by
  have h := spillWordBound_cleanup_le_sizeBoundInT (iselSzTF hdom hs hfa hst hsel) hs.externsE hl hp
  have hb : sizeBoundIn f < 2 ^ 24 := of_decide_eq_true hsz
  exact decide_eq_true (by omega)

/-- **The emission conditions of the float scope's pipeline output** (`emitConds_lowerT`). -/
theorem emitConds_lowerTF {f : Clif.Function} {vc vcp : VCode} (hdom : dominatedB f = true)
    (hs : LowerScopeTF f) (hfa : Compile.floatArgsTyped f = true)
    (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true)
    (hw : extendsWidenB f = true) (hbw : bitcastWidthB f = true) (hsz : sizeOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp) : emitCondsB vcp = true := by
  have h0 := spillSizeOkB_of_sizeOkBTF hdom hs hfa hst hsel hsz hl hp
  obtain ⟨h1, h2, h3⟩ := emitParts_lowerTF hs (iselEmitTF hdom hs hfa hst hsel hw hbw) hl hp
  simp [emitCondsB, h0, h1, h2, h3]

/-- **`emitConds_lowerTF` after the dead-code cleanup** (`emitConds_cleanup_lowerT`). -/
theorem emitConds_cleanup_lowerTF {f : Clif.Function} {vc vcp : VCode}
    (hdom : dominatedB f = true) (hs : LowerScopeTF f) (hfa : Compile.floatArgsTyped f = true)
    (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true)
    (hw : extendsWidenB f = true) (hbw : bitcastWidthB f = true) (hsz : sizeOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (prune vc) = .ok vcp) :
    emitCondsB vcp = true := by
  have h0 := spillSizeOkB_cleanup_of_sizeOkBTF hdom hs hfa hst hsel hsz hl hp
  obtain ⟨h1, h2, h3⟩ := emitParts_cleanup_lowerTF hs (iselEmitTF hdom hs hfa hst hsel hw hbw) hl hp
  simp [emitCondsB, h0, h1, h2, h3]

namespace LinkCheck

/-- **`resClassOkB` on the float scope** (`resClassOkB_of_T3`). -/
theorem resClassOkB_of_TF {g : Clif.Function} (hd : dominatedB g = true)
    (hs : lowerScopeTFB g = true) (hfa : Compile.floatArgsTyped g = true)
    (hst : Compile.storeTypedB g = true) (hsel : Compile.selectTypedB g = true) :
    Spill.resClassOkB g = true :=
  resClassOkB_of (Spill.resClassOk_of_lowerScopeTF hd (lowerScopeTF_of hs) hfa hst hsel)

end LinkCheck

end E2E

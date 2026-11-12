import FV.Backend.Proof.IselSzTDriver
import FV.Backend.Proof.IselEmitTDriver
import FV.Backend.Proof.IselShpTDriver
import FV.Backend.Proof.IselCovTFamCoverF

/-!
# The size, emission and control-shape analyses on the float scope

The typed abstract interpretations (`IselSzTDriver`, `IselEmitTDriver`, `IselShpTDriver`) take
the context invariant, the instruction families (`FamCover`) and the terminators' families; their
tables cover the S11f float families 31-35 (`famTab`). On the float scope (`LowerScopeTF`) with
float-defined float positions (`Compile.floatArgsTyped`):

* `iselSzTF`: `IselSzT f` (`iselSzT`);
* `iselEmitTF`: `IselEmitT f` (`iselEmitT`);
* `iselCtlOnF`: `Spill.IselCtlOn f` (`iselCtlHypT`'s conclusion for `f`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- `buildCtx`'s context of a float-scope function meets `CtxT`. -/
theorem ctxT_ofF {f : Clif.Function} (hs : LowerScopeTF f) {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st0 : LState} (hb : buildCtx f = .ok (ctx, ranges, st0)) :
    CtxT f ctx :=
  ⟨ctxInvT_ofF hs hb, (ctxSpec_of hb).instScopeTF hs.subsetTF, callsE_of_externs hs.externsE ctx⟩

/-- **The size analysis on the float scope** (`iselSzT`). -/
theorem iselSzTF {f : Clif.Function} (hdom : dominatedB f = true) (hs : LowerScopeTF f)
    (hfa : Compile.floatArgsTyped f = true) (hst : Compile.storeTypedB f = true)
    (hsel : Compile.selectTypedB f = true) : IselSzT f := by
  intro ctx ranges st0 hb
  have hctx : CtxT f ctx := ctxT_ofF hs hb
  have hcl : Cov.Clean ctx := Cov.clean_of_build hb
  have hfam := CovT.famCover_ofF hs hfa hdom hst hsel hb
  exact ⟨fun ii info inst s out s' tr hi hc h => CovT.stmt_szT hctx hcl hfam hi hc h,
    fun B hB ti data targets s out s' tr _ hph hty hd hlen h =>
      CovT.termCall_szT hctx hcl hfam hph hty hd (CovT.termFam_ofF hs hb hB (.inl hd)) hlen h,
    fun B hB ti et data sig items lo st1 trs targets s out s' tr _ hph het hd he htr h =>
      CovT.tryCall_szT hctx hcl hfam hph het hd (CovT.termFam_ofF hs hb hB (.inr hd)) he htr h⟩

/-- **The emission analysis on the float scope** (`iselEmitT`). -/
theorem iselEmitTF {f : Clif.Function} (hdom : dominatedB f = true) (hs : LowerScopeTF f)
    (hfa : Compile.floatArgsTyped f = true) (hst : Compile.storeTypedB f = true)
    (hsel : Compile.selectTypedB f = true) (hw : extendsWidenB f = true)
    (hbw : bitcastWidthB f = true) : IselEmitT f := by
  intro ctx ranges st0 hb
  have hctx : CtxInvT f ctx := ctxInvT_ofF hs hb
  have hcl : Cov.Clean ctx := Cov.clean_of_build hb
  have hfam := CovT.famCover_ofF hs hfa hdom hst hsel hb
  have hW := extendsWiden_of hw hb
  have hB := bitcastsSameWidth_of hbw hb
  exact ⟨fun ii info inst s out s' tr hi hc h => CovT.stmt_emitT hctx hcl hfam hW hB hi hc h,
    fun B hB' ti data targets s out s' tr _ hph hty hd h =>
      CovT.termCall_emitT hctx hcl hfam hph hty hd (CovT.termFam_ofF hs hb hB' (.inl hd)) h,
    fun B hB' ti data trs targets s out s' tr _ hph hd h =>
      CovT.tryCall_emitT hctx hcl hfam hph hd (CovT.termFam_ofF hs hb hB' (.inr hd)) h⟩

end Backend.Proof.Driver

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Driver

/-- **The control-shape analysis on the float scope** (`iselCtlHypT`'s conclusion). -/
theorem iselCtlOnF {f : Clif.Function} (hdom : dominatedB f = true) (hs : LowerScopeTF f)
    (hfa : Compile.floatArgsTyped f = true) (hst : Compile.storeTypedB f = true)
    (hsel : Compile.selectTypedB f = true) (ha : Spill.AbiSigsOk f) : Spill.IselCtlOn f := by
  intro ctx ranges st0 hb hsr
  have hx := hs.externsE
  have hctx : CtxT f ctx := ctxT_ofF hs hb
  have hcl : Cov.Clean ctx := Cov.clean_of_build hb
  have hfam := famCover_ofF hs hfa hdom hst hsel hb
  refine ⟨fun ii info inst s out s' tr hi hc hN h => ?_,
    fun ti t data targets s out s' tr _ hph hty hB hd hN h => ?_,
    fun ti t et data sig items lo trs st1 targets out s' tr _ hph het hB hd he hlo htr h => ?_⟩
  · have hmem : ∃ B ∈ f.blocks, ∃ st ∈ B.body, st.inst = inst := by
      rcases (ctxSpec_of hb).insts info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)) with
        rfl | ⟨B, hB, st, hst, rfl⟩
      · cases hc
      · exact ⟨B, hB, st, hst, Option.some.inj hc⟩
    exact stmt_shpT hctx hx hcl hfam ha hi hc hmem hN h
  · obtain ⟨B, hBm, rfl⟩ := hB
    exact termCall_shpT hctx hcl hfam hph hty (termIntPos_ofF hs hb hBm) hd
      (termFam_ofF hs hb hBm (.inl hd)) hsr hN h
  · obtain ⟨B, hBm, hBt⟩ := hB
    subst hBt
    exact tryCall_shpT hctx hcl hfam ha hph het ⟨B, hBm, rfl⟩ hd
      (termFam_ofF hs hb hBm (.inr hd)) he (termIntPos_ofF hs hb hBm) hlo htr h

end Backend.Proof.CovT

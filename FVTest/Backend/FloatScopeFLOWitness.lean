import FV.E2E.VerifiableT
import FVTest.E2E.FloatFinalT
import FVTest.Backend.FloatArithCtxT
import FV.E2E.LinkCheck
import FV.Backend.Proof.LowerCompleteTCF
import FV.E2E.EmitSize
import FVTest.Backend.FnVerdict
import FV.E2E.LinkScopeInputDefsTC

/-!
Witnesses of the typed scope with `fcopysign` and `fma` (#35, `Compile.instETFLO`).

* `fCs` (`fcopysign.f64`), `fCs32` (`fcopysign.f32`), `fFma` (`fma.f64`), `fFmaNegZ` (`fma.f32`
  whose addend is an `fneg`: `rule_lower_609`, `fnmsub`) and `fFmaNegX` (`fma.f64` whose first
  operand is an `fneg`: `fmadd` rule 2, `fmsub`) are in `Compile.functionETCF`, their lowering
  passes the validator `lowerCheckTCF`, and the backend reports them verified;
  `fFmaNegY` (`fma` whose second operand is an `fneg`: `fmadd` rule 3, not exact on NaN signs) is
  outside it (`Compile.fmaNegYFree`), and `typedScopeFails` names the conjunct.
* `shapeOkTF_eq_S_old_false`: the statement of `Driver.shapeOkTF_eq_S` before #35 (the check
  `instScopeOkFL`) is false: `shapeOkTF` accepts `fCs`'s lowering, which `instScopeOkFL`
  rejects.
* `loweringTCF_of_check_old_false`, `lowerShapeTC_of_okF_old_false`: the statements of
  `Driver.loweringTCF_of_check` and `Driver.lowerShapeTC_of_okF` before #35 (the shape
  `LowerShapeTCS InstScope.tfl`) are false: `lowerCheckTCF` accepts `fCs`'s lowering, whose
  context has an instruction outside `Compile.instETFL` (they now give
  `LowerShapeTCS InstScope.tflo`).

Checks by `native_decide` (witness only). `lake build FVTest.Backend.FloatScopeFLOWitness`.
-/

open Backend Backend.Proof Backend.Proof.Driver E2E E2E.LinkCheck

namespace FloatScopeFLOWitness

/-- `fcopysign.f64`. -/
def fCs : Clif.Function := fnOfTextA
  "function %cs64(f64, f64) -> f64 {\nblock0(v0: f64, v1: f64):\n    v2 = fcopysign v0, v1\n    return v2\n}\n"

/-- `fcopysign.f32`. -/
def fCs32 : Clif.Function := fnOfTextA
  "function %cs32(f32, f32) -> f32 {\nblock0(v0: f32, v1: f32):\n    v2 = fcopysign v0, v1\n    return v2\n}\n"

/-- `fma.f64`. -/
def fFma : Clif.Function := fnOfTextA
  "function %fma64(f64, f64, f64) -> f64 {\nblock0(v0: f64, v1: f64, v2: f64):\n    v3 = fma v0, v1, v2\n    return v3\n}\n"

/-- `fma.f32` whose addend is an `fneg` (`rule_lower_609`: `fnmsub`). -/
def fFmaNegZ : Clif.Function := fnOfTextA
  "function %fma_negz(f32, f32, f32) -> f32 {\nblock0(v0: f32, v1: f32, v2: f32):\n    v3 = fneg v2\n    v4 = fma v0, v1, v3\n    return v4\n}\n"

/-- `fma.f64` whose first operand is an `fneg` (`fmadd` rule 2: `fmsub`). -/
def fFmaNegX : Clif.Function := fnOfTextA
  "function %fma_negx(f64, f64, f64) -> f64 {\nblock0(v0: f64, v1: f64, v2: f64):\n    v3 = fneg v0\n    v4 = fma v3, v1, v2\n    return v4\n}\n"

/-- `fma.f64` whose second operand is an `fneg` (`fmadd` rule 3: outside the scope). -/
def fFmaNegY : Clif.Function := fnOfTextA
  "function %fma_negy(f64, f64, f64) -> f64 {\nblock0(v0: f64, v1: f64, v2: f64):\n    v3 = fneg v1\n    v4 = fma v0, v3, v2\n    return v4\n}\n"

-- in the scope with `fcopysign` and `fma`, not in the scopes before it
#guard Compile.functionETCF fCs && Compile.functionETCF fCs32 && Compile.functionETCF fFma &&
  Compile.functionETCF fFmaNegZ && Compile.functionETCF fFmaNegX
#guard !Compile.functionETF fCs && !Compile.functionETF fFma
-- the validator accepts their lowering, and the backend reports them verified
#guard lowerCheckTCF fCs (FloatDriverT.vcOf fCs) && lowerCheckTCF fCs32 (FloatDriverT.vcOf fCs32) &&
  lowerCheckTCF fFma (FloatDriverT.vcOf fFma) &&
  lowerCheckTCF fFmaNegZ (FloatDriverT.vcOf fFmaNegZ) &&
  lowerCheckTCF fFmaNegX (FloatDriverT.vcOf fFmaNegX)
#guard (unverifiedReason? fCs).isNone && (unverifiedReason? fCs32).isNone &&
  (unverifiedReason? fFma).isNone && (unverifiedReason? fFmaNegZ).isNone &&
  (unverifiedReason? fFmaNegX).isNone
-- an `fma` whose second operand is an `fneg` is outside, by `fmaNegYFree` only
#guard !Compile.fmaNegYFree fFmaNegY && !Compile.functionETCF fFmaNegY
#guard typedScopeFails fFmaNegY == ["fmaNegYFree (an fma's second operand is an fneg's result)"]
-- `lean-backend`'s verdict (`FnVerdict`, `Main.lean`'s scope choice): outside `functionE`,
-- `functionET`, `functionETC`, so the scope `typedTCF`, whose theorem is
-- `E2E.backend_correct_world_cleanupTCF` (with dead cleanup) / `E2E.backend_correct_finalTCF`
#guard [fCs, fCs32, fFma, fFmaNegZ, fFmaNegX].all fun f =>
  !Compile.functionE f && !Compile.functionET f && !Compile.functionETC f
#guard (FVTest.Backend.FnVerdict.verdict { scope := .typedTCF, path := .stock }).thm =
  some "E2E.backend_correct_world_cleanupTCF"
#guard (FVTest.Backend.FnVerdict.verdict { scope := .typedTCF, path := .stock, cleanup := false }).thm =
  some "E2E.backend_correct_finalTCF"
-- lean-link's admission predicate admits them (`fnScopeInTCB`), not `fFmaNegY`
#guard [fCs, fCs32, fFma, fFmaNegZ, fFmaNegX].all E2E.LinkCheck.fnScopeInTCB
#guard !E2E.LinkCheck.fnScopeInTCB fFmaNegY

/-- `shapeOkTF` accepts `f`'s lowering, and `shapeOkTS` at the check `instScopeOkFL` rejects it
(an instruction outside `Compile.instETFL`). -/
def oldDiffers (f : Clif.Function) (vc : VCode) : Bool :=
  match buildCtx f with
  | .error _ => false
  | .ok (ctx, _, st0) =>
    match lowBlocksC f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => false
    | some bl =>
      let gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))
      shapeOkTF f vc ctx st0 gn bl && !shapeOkTS (instScopeOkFL ctx) f vc ctx st0 gn bl

/-- **The statement of `Driver.shapeOkTF_eq_S` before #35 is false**: `shapeOkTF` changed (its
check is `instScopeOkFLO`), and on `fCs`'s lowering it differs from `shapeOkTS` at the old check
`instScopeOkFL`. -/
theorem shapeOkTF_eq_S_old_false :
    ¬ ∀ (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (gn : Nat → Nat)
      (bl : List BLow),
      shapeOkTF f vc ctx st0 gn bl = shapeOkTS (instScopeOkFL ctx) f vc ctx st0 gn bl := by
  intro h
  have hd : oldDiffers fCs (FloatDriverT.vcOf fCs) = true := by native_decide
  unfold oldDiffers at hd
  split at hd
  · cases hd
  · split at hd
    · cases hd
    · simp [h] at hd

/-- The validator accepts `fCs`'s lowering. -/
theorem lowerCheckTCF_cs : lowerCheckTCF fCs (FloatDriverT.vcOf fCs) = true := by
  native_decide

/-- `f`'s lowering context has an instruction outside `Compile.instETFL`. -/
def ctxNotTFL (f : Clif.Function) : Bool :=
  match buildCtx f with
  | .error _ => false
  | .ok (ctx, _, _) => !instScopeOkFL ctx

/-- **The statement of `Driver.loweringTCF_of_check` before #35 is false**: the shape
`LowerShapeTCS InstScope.tfl` has the scope `InstScopeTFL`, which `fCs`'s context (its
`fcopysign`) fails. -/
theorem loweringTCF_of_check_old_false :
    ¬ ∀ (f : Clif.Function) (vc : VCode), lowerCheckTCF f vc = true →
      ∃ ctx st0 R gn bl A, LowerShapeTCS InstScope.tfl f vc ctx st0 R gn bl ∧
        Cert f ctx st0 gn bl A ∧ ∀ B ∈ f.blocks, BrIdxTyped ctx B.term := by
  intro h
  obtain ⟨ctx, st0, R, gn, bl, A, hs, -, -⟩ := h fCs _ lowerCheckTCF_cs
  obtain ⟨ranges, hb⟩ := hs.hctx
  have hd : ctxNotTFL fCs = true := by native_decide
  unfold ctxNotTFL at hd
  rw [hb] at hd
  simp [instScopeOkFL_complete hs.scope] at hd

/-- **The statement of `Driver.lowerShapeTC_of_okF` before #35 is false**: with it,
`loweringTCF_of_check`'s proof gives the false statement `loweringTCF_of_check_old_false`. -/
theorem lowerShapeTC_of_okF_old_false :
    ¬ ∀ (f : Clif.Function) (vc : VCode) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState)
      (bl : List BLow) (gn : Nat → Nat), buildCtx f = .ok (ctx, ranges, st0) →
      lowBlocksC f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length = some bl →
      (∀ n, st0.nextVreg ≤ n → gn n = n) → shapeOkTF f vc ctx st0 gn bl = true →
      LowerShapeTCS InstScope.tfl f vc ctx st0 (renOf gn) gn bl := by
  intro h
  apply loweringTCF_of_check_old_false
  intro f vc hc
  unfold lowerCheckTCF at hc
  split at hc
  · cases hc
  · rename_i ctx ranges st0 hb
    split at hc
    · cases hc
    · rename_i bl hl
      simp only [Bool.and_eq_true] at hc
      have hS := h f vc ctx ranges st0 bl (gnAt (gnTable st0.nextVreg (aliasOf f bl))) hb hl
        (fun n hn => gnAt_temp hn) hc.1.1.1.1
      exact ⟨ctx, st0, _, _, bl, _, hS, cert_of_ok hS.len hc.1.1.1.2, brIdx_of_ok hc.1.1.2⟩

end FloatScopeFLOWitness

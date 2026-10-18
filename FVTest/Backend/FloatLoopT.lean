import FV.Backend.Proof.SpillEdgesLowT
import FV.Backend.Proof.LowerDecide
import FVTest.Backend.FloatDriverT

/-!
Non-vacuity of the typed loop simulation and the edge-class check (S11e5 Stage C, slice 3):
`lowerFunction_runT`/`lowT_of` on the float-movement function `fMv` (its VCode is the typed model
`vcBlocksOfT`, whose block parameters and edge arguments are float vregs, and not the integer
model `vcBlocksOf`); `CtxSpec.edgeClass` on its float branch argument; class-mismatched branch
arguments and returns are outside `Compile.functionET`; `shapeOkT_complete`/`lowerShapeT_of_lower`
on an integer function (their terminator premise `TermEmitsT` from `term_emits`). Checks by
`native_decide` (witness only). `lake build FVTest.Backend.FloatLoopT`.
-/

open Backend Backend.Proof Backend.Proof.Driver

namespace FloatLoopT

open FloatDriverT

-- the edge-class check: an `i64` passed to an `f64` parameter, an `i64` returned as `f64`
#guard !Compile.functionET (fnOfText
  "function %e(i64, f64) -> f64 {\nblock0(v0: i64, v1: f64):\n    jump block1(v0)\nblock1(v2: f64):\n    return v2\n}\n")
#guard !Compile.functionET (fnOfText
  "function %r(i64) -> f64 {\nblock0(v0: i64):\n    return v0\n}\n")
#guard Compile.functionET fMv

/-- `buildCtx`'s context and the recorded lowering of `f` (empty if they fail). -/
def ctxBlOf (f : Clif.Function) : Ctx × List BLow :=
  match buildCtx f with
  | .ok (ctx, _, st0) =>
    (ctx, (lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length).getD [])
  | .error _ => ({ func := f, insts := #[], valTy := #[], valDef := #[], valReg := #[], slotOff := [] }, [])

-- the typed model is `lowerFunction`'s VCode for `fMv`, the integer model is not
#guard reprStr (vcOf fMv).blocks == reprStr (vcBlocksOfT fMv (ctxBlOf fMv).1 (ctxBlOf fMv).2)
#guard reprStr (vcOf fMv).blocks != reprStr (vcBlocksOf fMv (ctxBlOf fMv).2)
-- block1's parameter and the `brif` edge arguments are float vregs in the typed model
#guard (rawBlockT fMv (ctxBlOf fMv).1 (ctxBlOf fMv).2 1 fMv.blocks[1]!).params == #[.vreg 10 .float]
#guard (fMv.blocks.zip (ctxBlOf fMv).2).any fun p =>
  (edgeBlocksT fMv (ctxBlOf fMv).1 p.1 p.2).any fun e => e.branchArgs.any (·.homeCls == .float)

/-- **Slice 3 witness**: the typed loop simulation of a float-movement function. -/
theorem runT_mv : ∃ ctx ranges st0 bl, buildCtx fMv = .ok (ctx, ranges, st0) ∧
    lowBlocks fMv (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 fMv.blocks st0 fMv.blocks.length =
      some bl ∧
    (vcOf fMv).blocks = vcBlocksOfT fMv ctx bl ∧ (vcOf fMv).outgoing = outOf st0 bl ∧
    LoopFactsT fMv ctx bl :=
  lowerFunction_runT lowerFunction_mv

/-- **Slice 3 witness**: the typed lowering run (`LowT`) of a float-movement function. -/
theorem lowT_mv : ∃ ctx st0 bl RR, Spill.LowT fMv (vcOf fMv) ctx st0 bl RR :=
  Spill.lowT_of lowerFunction_mv

/-- **Slice 3 witness**: `fMv`'s float `brif` argument `v8` has its target parameter's class. -/
theorem edgeClass_mv : ∃ ctx ranges st0, buildCtx fMv = .ok (ctx, ranges, st0) ∧
    ∀ t, ctx.valueType? 8 = some t → t.valClass = (CTy.ofClif .f64).valClass := by
  have hok : (buildCtx fMv).toBool = true := by native_decide
  cases hb : buildCtx fMv with
  | error e => rw [hb] at hok; cases hok
  | ok r =>
    obtain ⟨ctx, ranges, st0⟩ := r
    refine ⟨ctx, ranges, st0, rfl, ?_⟩
    exact (ctxSpec_of hb).edgeClass functionET_mv (B := fMv.blocks[0]!) (by native_decide)
      (bc := { block := 1, args := [8] }) (by native_decide) (tb := fMv.blocks[1]!) (by native_decide)
      (p := (10, .f64)) (by native_decide)

/-- An integer function with a block parameter (for the shape-completeness witnesses). -/
def fI : Clif.Function := fnOfText
  "function %i(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iadd v0, v0\n    jump block1(v1)\nblock1(v2: i64):\n    return v2\n}\n"

theorem lowerFunction_fI : lowerFunction fI = .ok (vcOf fI) := by
  have hok : (lowerFunction fI).toBool = true := by native_decide
  unfold vcOf
  cases h : lowerFunction fI with
  | error e => rw [h] at hok; cases hok
  | ok vc => rfl

/-- **Slice 3 witness**: `shapeOkT_complete` (premises from the integer scope). -/
theorem shapeOkT_fI : ∃ ctx ranges st0 bl, buildCtx fI = .ok (ctx, ranges, st0) ∧
    lowBlocks fI (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 fI.blocks st0 fI.blocks.length =
      some bl ∧
    shapeOkT fI (vcOf fI) ctx st0 (gnAt (gnTable st0.nextVreg (aliasOf fI bl))) bl = true := by
  have hd := dominated_of (by native_decide : dominatedB fI = true)
  have hs := lowerScope_of (by native_decide : lowerScopeB fI = true)
  obtain ⟨ctx, ranges, st0, bl, hb, hl, -, -, -⟩ := lowerFunction_runT lowerFunction_fI
  obtain ⟨hu, -, hwf⟩ := alias_facts hd hs hb hl
  exact ⟨ctx, ranges, st0, bl, hb, hl, shapeOkT_complete lowerFunction_fI hs.toT hd.ssa hb
    (termEmitsT_of_ctxInv (ctxOk_sound (ctxOk_complete hs hb))) hl hu hwf⟩

/-- **Slice 3 witness**: `lowerShapeT_of_lower` (premises from the integer scope). -/
theorem lowerShapeT_fI : ∃ ctx st0 R gn bl, LowerShapeT fI (vcOf fI) ctx st0 R gn bl := by
  have hd := dominated_of (by native_decide : dominatedB fI = true)
  have hs := lowerScope_of (by native_decide : lowerScopeB fI = true)
  obtain ⟨ctx, ranges, st0, bl, hb, hl, -, -, -⟩ := lowerFunction_runT lowerFunction_fI
  obtain ⟨hu, -, hwf⟩ := alias_facts hd hs hb hl
  exact ⟨ctx, st0, _, _, bl, lowerShapeT_of_lower lowerFunction_fI hs.toT hd.ssa hb
    (termEmitsT_of_ctxInv (ctxOk_sound (ctxOk_complete hs hb))) hl hu hwf⟩

/-- **Slice 3 witness**: the integer loop simulation from the typed one. -/
theorem run_fI : ∃ ctx ranges st0 bl, buildCtx fI = .ok (ctx, ranges, st0) ∧
    lowBlocks fI (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 fI.blocks st0 fI.blocks.length =
      some bl ∧
    (vcOf fI).blocks = vcBlocksOf fI bl ∧ (vcOf fI).outgoing = outOf st0 bl ∧ LoopFacts fI ctx bl :=
  lowerFunction_run_of_runT (by native_decide) lowerFunction_fI

/-- **Slice 3 witness**: a typed run of an integer function is the integer `Low`. -/
theorem low_fI : ∃ ctx st0 bl RR, Spill.Low fI (vcOf fI) ctx st0 bl RR := by
  obtain ⟨ctx, st0, bl, RR, H⟩ := Spill.lowT_of lowerFunction_fI
  obtain ⟨ranges, hb⟩ := H.hb
  exact ⟨ctx, st0, bl, RR, H.toLow ((ctxSpec_of hb).ctxE (by native_decide))⟩

end FloatLoopT

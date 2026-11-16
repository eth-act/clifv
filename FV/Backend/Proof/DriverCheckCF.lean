import FV.Backend.Proof.DriverCheckC
import FV.Backend.Proof.InstScopeTF

/-!
# The typed lowering validator with the proven float operations (S11f, #35)

`lowerCheckTCF`: `lowerCheckTC` (`DriverCheckC.lean`) whose supported-instruction check is
`instScopeOkF` (`Compile.instETF`: the typed movement scope, the S11f float arithmetic and
rounding, the saturating and `from` conversions, the scalar `fcmp`) in place of `instScopeOk`
(`shapeOkTF`).
Executable only: the compiler runs it outside `Compile.functionETC` (`Backend.lowerCheckFor`);
its soundness is `DriverCheckTCF.lean`'s.

#1002 part 2: the supported-instruction check is `instScopeOkFL` (`Compile.instETFL`: an
`f64const` from the literal pool also; it was `instScopeOkF`), the scope `Compile.functionETCF`
admits.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- `shapeOkT` with `instScopeOkFL` (#1002 part 2; it was `instScopeOkF`). -/
def shapeOkTF (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (gn : Nat → Nat)
    (bl : List BLow) : Bool :=
  (ctxOkT f ctx && instScopeOkFL ctx) && decide (ctx.valReg.size ≤ st0.nextVreg) &&
  f.blocks.all (fun B => B.params.all fun p => decide (gn p.1 = p.1)) &&
  decide (bl.length = f.blocks.length) && decide (f.blocks.length ≤ vc.blocks.size) &&
  (List.range vc.blocks.size).all (fun l => match vc.blocks[l]? with
    | some vb => decide (vb.label = l)
    | none => true) &&
  ((List.range f.blocks.length).all fun bi => match f.blocks[bi]?, bl[bi]? with
    | some B, some L => blockOkT f vc ctx st0 (renOf gn) gn bl bi B L
    | _, _ => false) &&
  decide (st0.nextVreg ≤ f.freshValue)

/-- **The typed lowering validator with the proven float operations** (`lowerCheckTC` with
`shapeOkTF`). -/
def lowerCheckTCF (f : Clif.Function) (vc : VCode) : Bool :=
  match buildCtx f with
  | .error _ => false
  | .ok (ctx, _, st0) =>
    match lowBlocksC f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => false
    | some bl =>
      let gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))
      shapeOkTF f vc ctx st0 gn bl && certOk f ctx st0 gn bl (inFix f ctx gn) && brIdxOk f ctx &&
        ((f.blocks.any (·.term.isTry) || !vc.hasTryCall) && (hasTls f || !vc.hasTls)) &&
        (callsStackOkB f vc.outgoing && entryOkBT f)

/-! ## `lowerCheckTCF` in linear memory (#1057) -/

theorem shapeOkTF_lite (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState)
    (gn : Nat → Nat) (bl : List BLow) :
    shapeOkTF f vc ctx st0 gn (bl.map liteBL) = shapeOkTF f vc ctx st0 gn bl := by
  unfold shapeOkTF
  erw [all_congr_lite _ (blocksOkT_lite f vc ctx st0 gn bl)]
  simp only [List.length_map]
  try rfl

/-- **`lowerCheckTCF` in linear memory** (`lowerCheckTCF_eq_lite`). -/
def lowerCheckTCFLite (f : Clif.Function) (vc : VCode) : Bool :=
  match buildCtx f with
  | .error _ => false
  | .ok (ctx, _, st0) =>
    match lowBlocksCLite f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => false
    | some bl =>
      let gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))
      shapeOkTF f vc ctx st0 gn bl && certOk f ctx st0 gn bl (inFix f ctx gn) && brIdxOk f ctx &&
        ((f.blocks.any (·.term.isTry) || !vc.hasTryCall) && (hasTls f || !vc.hasTls)) &&
        (callsStackOkB f vc.outgoing && entryOkBT f)

/-- The compiler runs `lowerCheckTCFLite` in place of `lowerCheckTCF`. -/
@[csimp] theorem lowerCheckTCF_eq_lite : @lowerCheckTCF = @lowerCheckTCFLite := by
  funext f vc
  unfold lowerCheckTCF lowerCheckTCFLite
  cases buildCtx f with
  | error _ => rfl
  | ok r =>
    obtain ⟨ctx, _, st0⟩ := r
    simp only [lowBlocksCLite_eq]
    cases lowBlocksC f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length with
    | none => rfl
    | some bl => simp only [Option.map_some, aliasOf_lite, shapeOkTF_lite, certOk_lite]

end Backend.Proof.Driver

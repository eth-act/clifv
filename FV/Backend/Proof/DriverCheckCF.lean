import FV.Backend.Proof.DriverCheckC
import FV.Backend.Proof.InstScopeTF

/-!
# The typed lowering validator with the proven float operations (S11f, #35)

`lowerCheckTCF`: `lowerCheckTC` (`DriverCheckC.lean`) whose supported-instruction check is
`instScopeOkF` (`Compile.instETF`: the typed movement scope, the S11f float arithmetic and
rounding, the saturating and `from` conversions) in place of `instScopeOk` (`shapeOkTF`).
Executable only: the compiler runs it outside `Compile.functionETC` (`Backend.lowerCheckFor`);
its soundness is `DriverCheckTCF.lean`'s.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- `shapeOkT` with `instScopeOkF`. -/
def shapeOkTF (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (gn : Nat → Nat)
    (bl : List BLow) : Bool :=
  (ctxOkT f ctx && instScopeOkF ctx) && decide (ctx.valReg.size ≤ st0.nextVreg) &&
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

end Backend.Proof.Driver

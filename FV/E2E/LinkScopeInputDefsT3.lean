import FV.E2E.LinkScopeInputDefsT2
import FV.Backend.Proof.IselEmitTDefs

/-!
# The typed input conditions without the run-time decider (S11, #35)

`fnScopeInTB3 g`: the decided input checks of `fnScopeInTB2` (`fnScopeInTB`'s conjuncts except
the non-E branch `Spill.resClassOkB g && lowerOutTB g`, plus `entryClassOkB` and
`Compile.selectTypedB`), the CLIF verifier's `bitcast` width rule
`Backend.Proof.Driver.bitcastWidthB`, and the literal loads' reach `poolReachInB` (#565). Only
`poolReachInB` may run `lowerFunction`, and only for a function whose size bound `sizeBoundIn` is
at least `2 ^ 17` words: there an `ldr (literal)` may not reach the pool after the body (Cranelift
emits a constant island), so such a function with a literal-pool load falls back to cg_clif's
code. Every check of `lowerOutTB` (`lowerFunction` succeeds, `ctlSpillB`, `emitCondsB`,
`formsCoveredB`, `killFreeB`, `ctlInstsB`) and `resClassOkB` is a theorem on it
(`LinkScopeInputT3.lean`: `fnScopeInTB2_of_T3`). `fnScopeInTB`, `fnScopeInTB2` and their
theorems are unchanged.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-- **The literal loads reach the pool** (#565): the size bound below `2 ^ 17` words (1 MiB, the
reach of an `ldr (literal)`), or the prepared VCode has no literal-pool load (`VCode.noPoolB`,
run only above the bound). -/
def poolReachInB (g : Clif.Function) : Bool :=
  decide (sizeBoundIn g < 2 ^ 17) ||
    match lowerFunction g with
    | .ok vc => match prepare vc with
      | .ok vcp => vcp.noPoolB
      | .error _ => true
    | .error _ => true

/-- **The typed per-function input conditions without the run-time decider.** -/
def fnScopeInTB3 (g : Clif.Function) : Bool :=
  Compile.functionET g && Compile.storeTypedB g && Compile.tryArgClassOk g &&
  (sigAbiOk g.sig && g.externs.all (fun e => sigAbiOk e.2.sig)) && indSigsOk g &&
  decide (regLocs g.sig).Nodup && (regLocs g.sig).all (·.isArgReg) &&
  g.sig.params.all (fun p => decide (p.ty.width ≤ 64)) && linkFreeB g &&
  dominatedB g && lowerScopeTB g && Spill.arityOkB g &&
  (extendsWidenB g && sizeOkB g && driverInB g && Prg.iselInB g) && Spill.entryParamsB g &&
  entryClassOkB g && Compile.selectTypedB g && Driver.bitcastWidthB g && poolReachInB g

/-- **`InScopeInT3`**: `InScopeInT` with `fnScopeInTB3`. -/
def InScopeInT3 (I : LinkInput) : Bool :=
  progScopeInB I.prog (fun n => I.syms.lookup n) && I.prog.funcs.all fnScopeInTB3

/-- The conjuncts of `fnScopeInTB3` a function fails, by name. -/
def fnScopeInFailsT3 (g : Clif.Function) : List String :=
  let c (b : Bool) (n : String) : List String := if b then [] else [n]
  c (Compile.functionET g) "functionET" ++ c (Compile.storeTypedB g) "storeTypedB" ++
  c (Compile.tryArgClassOk g) "tryArgClassOk" ++
  c (sigAbiOk g.sig && g.externs.all (fun e => sigAbiOk e.2.sig)) "sigAbiOk" ++
  c (indSigsOk g) "indSigsOk" ++
  c (decide (regLocs g.sig).Nodup && (regLocs g.sig).all (·.isArgReg) &&
    g.sig.params.all (fun p => decide (p.ty.width ≤ 64))) "regParams" ++
  c (linkFreeB g) "linkFreeB" ++ c (dominatedB g) "dominatedB" ++ c (lowerScopeTB g) "lowerScopeTB" ++
  c (Spill.arityOkB g) "arityOkB" ++ c (extendsWidenB g) "extendsWidenB" ++ c (sizeOkB g) "sizeOkB" ++
  c (driverInB g) "driverInB" ++ c (Prg.iselInB g) "iselInB" ++ c (Spill.entryParamsB g) "entryParamsB" ++
  c (entryClassOkB g) "entryClassOkB" ++ c (Compile.selectTypedB g) "selectTypedB" ++
  c (Driver.bitcastWidthB g) "bitcastWidthB" ++ c (poolReachInB g) "poolReachInB"

end E2E.LinkCheck

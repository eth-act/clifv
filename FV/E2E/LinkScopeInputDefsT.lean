import FV.E2E.LinkScopeInputDefs
import FV.E2E.LinkScopeDefsT
import FV.E2E.EmitCondsDefs

/-! # The typed input conditions (S11e5 Stage C, slice 8): the definitions

`fnScopeInB` (`LinkScopeInputDefs.lean`) with the typed movement scope: `fnScopeInTB` keeps every
conjunct of `fnScopeInB`, with `Compile.functionET` for `Compile.functionE` and `lowerScopeTB` for
`lowerScopeB`, and the typed input checks of `fnScopeTB` (`Compile.storeTypedB`,
`Compile.tryArgClassOk`). A function outside subset E must also meet `Spill.resClassOkB` and the
run-time decider `lowerOutTB`; a subset-E function needs neither (`fnScopeInB`'s proofs cover it).

`lowerOutTB` decides what the typed totality chain does not prove yet:

* `lowerFunction` succeeds (the ISLE progress analysis `Prg.lowerFunction_ok_input` covers subset-E
  statement forms only; its root table has no float forms);
* on its output, the typed spill chain's control forms (`Spill.ctlSpillB`);
* on `prepare`'s output (`prepare` itself is proven total on the typed scope,
  `Prep.prepare_okT`, so an error there is not checked): the emission conditions
  (`emitCondsB`: the size bound, immediates, no `al`/`nv` branch, block-label targets; proven from
  the input for subset E by the ISLE size and emission analyses `iselSz`, `iselEmit`), the covered
  forms (`formsCoveredB default`), definitions before kills (`Spill.killFreeB`) and the control
  check (`ctlInstsB`: `ctlInstOk` everywhere, `Args` first in block 0; for subset E,
  `ctlInsts_pipeline` from the integer control-shape analysis).

`InScopeInT I`: `InScopeIn I` with `fnScopeInTB`. `fnScopeInFailsT`: the conjuncts a function
fails. Kept free of proofs (`LinkScopeInputT.lean`), like `LinkScopeInputDefs`.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-- The instruction part of `ctlCheck`, decided: `ctlInstOk` at every position, and block 0
starts with `Args` followed by another instruction (`E2E.CtlInsts`). -/
def ctlInstsB (vc : VCode) : Bool :=
  ((List.range vc.blocks.size).all fun b => match vc.blocks[b]? with
    | some vb => (List.range vb.insts.size).all fun k => match vb.insts[k]? with
      | some i => ctlInstOk b k i
      | none => true
    | none => true) &&
  (match vc.blocks[0]? with
    | some vb0 => (match (vb0.insts[0]? : Option MInst) with
      | some (MInst.args _) => true
      | _ => false) && decide (1 < vb0.insts.size)
    | none => false)

/-- **The run-time decider of the typed input scope**: `lowerFunction` succeeds, its output meets
`Spill.ctlSpillB`, and `prepare`'s output (`prepare` does not fail on the typed scope:
`Prep.prepare_okT`) meets `emitCondsB`, `formsCoveredB default` and `ctlInstsB` (`Spill.killFreeB`
is a theorem on the typed scope: `LinkCheck.killFreeB_of_scopeT`). -/
def lowerOutTB (g : Clif.Function) : Bool :=
  match lowerFunction g with
  | .ok vc => Spill.ctlSpillB vc && match prepare vc with
    | .ok vcp => emitCondsB vcp && formsCoveredB default vcp && ctlInstsB vcp
    | .error _ => true
  | .error _ => false

/-- **The typed per-function input conditions**: `fnScopeInB`'s conjuncts over the typed
movement scope (`Compile.functionET`, `lowerScopeTB`) with the typed input checks
(`Compile.storeTypedB`, `Compile.tryArgClassOk`); outside subset E also `Spill.resClassOkB` and
`lowerOutTB`. -/
def fnScopeInTB (g : Clif.Function) : Bool :=
  Compile.functionET g && Compile.storeTypedB g && Compile.tryArgClassOk g &&
  (sigAbiOk g.sig && g.externs.all (fun e => sigAbiOk e.2.sig)) && indSigsOk g &&
  decide (regLocs g.sig).Nodup && (regLocs g.sig).all (·.isArgReg) &&
  g.sig.params.all (fun p => decide (p.ty.width ≤ 64)) && linkFreeB g &&
  dominatedB g && lowerScopeTB g && Spill.arityOkB g &&
  (extendsWidenB g && sizeOkB g && driverInB g && Prg.iselInB g) && Spill.entryParamsB g &&
  (Compile.functionE g || (Spill.resClassOkB g && lowerOutTB g))

/-- **`InScopeInT`: the typed input conditions of a crate** (`InScopeIn` with `fnScopeInTB`). -/
def InScopeInT (I : LinkInput) : Bool :=
  progScopeInB I.prog (fun n => I.syms.lookup n) && I.prog.funcs.all fnScopeInTB

/-- The typed per-function input conditions `g` fails (the conjuncts of `fnScopeInTB`, by name;
`lowerOutTB`'s parts separately). -/
def fnScopeInFailsT (g : Clif.Function) : List String :=
  let c (b : Bool) (n : String) : List String := if b then [] else [n]
  let outE := Compile.functionE g
  c (Compile.functionET g) "functionET" ++ c (Compile.storeTypedB g) "storeTypedB" ++
  c (Compile.tryArgClassOk g) "tryArgClassOk" ++
  c (sigAbiOk g.sig && g.externs.all (fun e => sigAbiOk e.2.sig)) "sigAbiOk" ++
  c (indSigsOk g) "indSigsOk" ++
  c (decide (regLocs g.sig).Nodup && (regLocs g.sig).all (·.isArgReg) &&
    g.sig.params.all (fun p => decide (p.ty.width ≤ 64))) "regParams" ++
  c (linkFreeB g) "linkFreeB" ++ c (dominatedB g) "dominatedB" ++ c (lowerScopeTB g) "lowerScopeTB" ++
  c (Spill.arityOkB g) "arityOkB" ++ c (extendsWidenB g) "extendsWidenB" ++ c (sizeOkB g) "sizeOkB" ++
  c (driverInB g) "driverInB" ++ c (Prg.iselInB g) "iselInB" ++ c (Spill.entryParamsB g) "entryParamsB" ++
  c (outE || Spill.resClassOkB g) "resClassOkB" ++
  (if outE then [] else match lowerFunction g with
    | .error _ => ["lowerFunction"]
    | .ok vc => c (Spill.ctlSpillB vc) "ctlSpillB" ++ match prepare vc with
      | .error _ => []
      | .ok vcp => c (emitCondsB vcp) "emitCondsB" ++ c (formsCoveredB default vcp) "formsCoveredB" ++
        c (Spill.killFreeB vcp) "killFreeB" ++ c (ctlInstsB vcp) "ctlInstsB")

end E2E.LinkCheck

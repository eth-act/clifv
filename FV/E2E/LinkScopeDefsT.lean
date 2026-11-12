import FV.E2E.LinkScopeDefs
import FV.Backend.Proof.SpillClassesT
import FV.Backend.Proof.SpillInstCheck
import FV.Backend.Proof.SpillAvail
import FV.Compile.StoreTyped
import FV.Compile.TryArgClass

/-! # The typed input conditions (S11e5 Stage C, slice 7)

The executable definitions of the typed per-function and program scopes, beside `fnScopeB`/
`InScopeP` (`LinkScopeDefs.lean`, unchanged) and kept free of proofs so that a proof file can
decide them by `native_decide`. Soundness: `FV/E2E/LinkScopeT.lean`.

* `lowerScopeTB`: `lowerScopeB` with the typed movement scope `Compile.functionET`
  (decides `LowerScopeT`).
* `lowersTB`: `lowersB` with the typed spill chain's run-time deciders on the lowering and its
  prepared code: `ctlSpillB` (control forms), `formsCoveredB default` (straight-line forms),
  `killFreeB` (definitions before kills).
* `fnScopeTB`: `fnScopeB` over the typed scope, with the typed input checks
  `Compile.storeTypedB` (float stores store float values), `Compile.tryArgClassOk` (`try_call`
  results to integer parameters), `Spill.resClassOkB` (results in their class's registers),
  `lowerScopeTB` and `lowersTB` in place of `lowerScopeB` and `lowersB`.
* `InScopePT`: `InScopeP` with `fnScopeTB`.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-- `LowerScopeT f`, decided (`lowerScopeT_of`): `lowerScopeB` with `Compile.functionET`. -/
def lowerScopeTB (f : Clif.Function) : Bool :=
  Compile.functionET f && !f.blocks.isEmpty &&
  f.blocks.all (fun B => (succIds B.term).all fun b => blockIdx? f b != some 0) &&
  (match buildCtx f with
    | .error _ => true
    | .ok (ctx, _, _) => brIdxOk f ctx &&
      ctx.insts.toList.all fun info => match info.clif with
        | some inst => match memAddr? inst with
          | some x => decide (ctx.valueType? x = some (.int 64))
          | none => true
        | none => true) &&
  f.blocks.all (fun B => match B.term with
    | .tryCall _ _ et | .tryCallIndirect _ _ et => match f.sigDecls.lookup et.sig with
      | some sig => et.normal.args.all fun
        | .ret i => decide (i < sig.returns.length)
        | _ => true
      | none => true
    | _ => true) &&
  f.blocks.all (fun B => B.body.all fun st => match st.inst with
    | .call fn _ => match f.extern? fn with
      | some e => stackLayoutOk e.sig
      | none => true
    | _ => true) &&
  (f.blocks.all fun B => match B.term with
    | .tryCall fn _ _ => match f.extern? fn with
      | some e => stackLayoutOk e.sig
      | none => true
    | _ => true) &&
  (indSigs f).all stackLayoutOk

/-- `lowerFunction` and `prepare` accept `f`, every extension widens, the spill code's word
bound is below `2 ^ 24` (`lowersB`), and the typed spill chain's run-time facts hold of the
lowering (`ctlSpillB`) and of the prepared code (`formsCoveredB default`, `killFreeB`). -/
def lowersTB (f : Clif.Function) : Bool :=
  extendsWidenB f &&
  match lowerFunction f with
  | .ok vc => Spill.ctlSpillB vc && match prepare vc with
    | .ok vcp => spillSizeOkB vcp && formsCoveredB default vcp && Spill.killFreeB vcp
    | .error _ => false
  | .error _ => false

/-- **The typed per-function input conditions** of `g`: `fnScopeB`'s with the typed movement
scope `Compile.functionET` and the typed checks (`Compile.storeTypedB`,
`Compile.tryArgClassOk`, `Spill.resClassOkB`, `lowerScopeTB`, `lowersTB`). -/
def fnScopeTB (g : Clif.Function) : Bool :=
  Compile.functionET g && Compile.storeTypedB g && Compile.tryArgClassOk g &&
  (sigAbiOk g.sig && g.externs.all (fun e => sigAbiOk e.2.sig)) && indSigsOk g &&
  decide (regLocs g.sig).Nodup && (regLocs g.sig).all (·.isArgReg) &&
  g.sig.params.all (fun p => decide (p.ty.width ≤ 64)) && linkFreeB g &&
  dominatedB g && lowerScopeTB g && Spill.arityOkB g && Spill.resClassOkB g && lowersTB g &&
  Spill.entryParamsB g

/-- **`InScopePT`: the typed input conditions of a crate** (`InScopeP` with `fnScopeTB`). -/
def InScopePT (I : LinkInput) : Bool :=
  progScopeB I.prog (fun n => I.syms.lookup n) && I.prog.funcs.all fnScopeTB

end E2E.LinkCheck

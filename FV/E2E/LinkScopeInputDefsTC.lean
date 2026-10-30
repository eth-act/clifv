import FV.Compile.SubsetTF
import FV.E2E.LinkCheck
import FV.Backend.Proof.IselEmitDefs
import FV.Backend.Proof.EntryParams
import FV.E2E.SizeDefs
import FV.Backend.Proof.LowerTotalCtx
import FV.Backend.Proof.SpillClassesT
import FV.Backend.Proof.DriverCheckCF

/-! # The typed-try_call input conditions (S11e6, #419): the definitions

`fnScopeInTB` (`LinkScopeInputDefsT.lean`) for functions whose direct `try_call`s have
`f32`/`f64` parameters or returns (`Compile.functionETC`): `fnScopeInTCB` keeps every
program-independent structural conjunct of `fnScopeInTB` that is meaningful for such functions,
and replaces the checks that reject them by construction — `lowerScopeTB` (its first conjunct is
`Compile.functionET`), `Prg.iselInB` (the ISLE input analysis's table has no float-`try_call`
forms), `Compile.tryArgClassOk` (a `try_call`'s payload/return arguments must go to
non-`float` parameters) and the terminator half of `driverInB` (`termInB`: `tryInB` requires
`sigIntB` on the `try_call`'s signature; both evaluated `false` on the typed-try_call witness
function) — by the decided output check `lowersTCB` (`lowerFunction` succeeds and its output
meets the typed-try_call validator `lowerCheckTC`, `Proof.Driver.lowerCheckTC`, the validator
the production `lowerCheck` runs on such functions) or, for the driver's remaining conditions,
by `driverInTCB` (`driverInB` without `termInB`). Sound as an admission predicate:
`compileExeT`'s third branch decides `okBCleanupT` on the compiled output anyway — the
third-branch correctness chain (`binary_correct_exec_provenT`) needs `okBCleanupT` only — so
the input conditions only select the region.

S11f (#35): widened in place to the scope with the proven float operations
(`Compile.functionETCF` for `Compile.functionETC`, the validator `lowerCheckTCF` for
`lowerCheckTC` in `lowersTCB`, as `staticChksWithT`'s lowering check): `compileExeT`'s third
branch accepts such functions (`okBCleanupT`), so the input conditions admit them.

`fnScopeInFailsTC`: the conjuncts a function fails, by name (the analogue of `fnScopeInFailsT`;
the shared conjuncts keep `fnScopeInFailsT`'s names). Kept free of proofs, like
`LinkScopeInputDefs(T)`.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-- **The run-time decider of the typed-try_call input scope**: `lowerFunction` succeeds and its
output meets the validator of the scope with the proven float operations `lowerCheckTCF` (what
the production `lowerCheck` runs on such functions, `Backend.lowerCheckFor`; S11f, it was
`lowerCheckTC`). -/
def lowersTCB (g : Clif.Function) : Bool :=
  match lowerFunction g with
  | .ok vc => lowerCheckTCF g vc
  | .error _ => false

/-- **The driver's input conditions for the typed-try_call scope**: `driverInB`
(`LowerTotal.lean`) without `termInB` (which rejects a float-`try_call` by construction:
`tryInB`'s `sigIntB`); the terminator conditions are covered by `lowersTCB`. -/
def driverInTCB (g : Clif.Function) : Bool :=
  aapcsConv g.sig.callConv && decide (g.sig.returns.length ≤ 8) &&
  g.blocks.all fun B => B.body.all (stmtInB g)

/-- **The typed-try_call per-function input conditions**: `fnScopeInTB`'s structural conjuncts
with `Compile.functionETCF` (S11f; it was `Compile.functionETC`) for `Compile.functionET`,
without `Compile.tryArgClassOk`, `lowerScopeTB`, `Prg.iselInB` and `driverInB`'s terminator half
(all reject such functions by construction), with `driverInTCB` for `driverInB` and `lowersTCB`
in the `functionE` disjunct's output checks (in place of `lowerOutTB`). -/
def fnScopeInTCB (g : Clif.Function) : Bool :=
  Compile.functionETCF g && Compile.storeTypedB g &&
  (sigAbiOk g.sig && g.externs.all (fun e => sigAbiOk e.2.sig)) && indSigsOk g &&
  decide (regLocs g.sig).Nodup && (regLocs g.sig).all (·.isArgReg) &&
  g.sig.params.all (fun p => decide (p.ty.width ≤ 64)) && linkFreeB g &&
  dominatedB g && Spill.arityOkB g &&
  (extendsWidenB g && sizeOkB g && driverInTCB g) && Spill.entryParamsB g &&
  (Compile.functionE g || (Spill.resClassOkB g && lowersTCB g))

/-- The typed-try_call per-function input conditions `g` fails (the conjuncts of
`fnScopeInTCB`, by name). -/
def fnScopeInFailsTC (g : Clif.Function) : List String :=
  let c (b : Bool) (n : String) : List String := if b then [] else [n]
  let outE := Compile.functionE g
  c (Compile.functionETCF g) "functionETCF" ++ c (Compile.storeTypedB g) "storeTypedB" ++
  c (sigAbiOk g.sig && g.externs.all (fun e => sigAbiOk e.2.sig)) "sigAbiOk" ++
  c (indSigsOk g) "indSigsOk" ++
  c (decide (regLocs g.sig).Nodup && (regLocs g.sig).all (·.isArgReg) &&
    g.sig.params.all (fun p => decide (p.ty.width ≤ 64))) "regParams" ++
  c (linkFreeB g) "linkFreeB" ++ c (dominatedB g) "dominatedB" ++
  c (Spill.arityOkB g) "arityOkB" ++ c (extendsWidenB g) "extendsWidenB" ++ c (sizeOkB g) "sizeOkB" ++
  c (driverInTCB g) "driverInTCB" ++ c (Spill.entryParamsB g) "entryParamsB" ++
  c (outE || Spill.resClassOkB g) "resClassOkB" ++
  (if outE then [] else match lowerFunction g with
    | .error _ => ["lowerFunction"]
    | .ok vc => c (lowerCheckTCF g vc) "lowerCheckTCF")

end E2E.LinkCheck

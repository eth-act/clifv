import FV.E2E.LinkScopeDefs
import FV.E2E.SizeDefs
import FV.Backend.Proof.IselPrgCtx

/-! # The input conditions without running the compiler (V7): the definitions

`fnScopeB` (`FV/E2E/LinkScopeDefs.lean`) contains `lowersB`: `lowerFunction` and `prepare`
accept the function and the prepared VCode meets `spillSizeOkB` — decided by running the
compiler's first stages. `fnScopeInB` replaces it with conditions on the CLIF function alone:

* `extendsWidenB` (V6c): every `uextend`/`sextend` widens;
* `sizeOkB` (V6c, `FV/E2E/SizeDefs.lean`): the input-side word bound below `2 ^ 24`;
* `driverInB` (V7, `FV/Backend/Proof/LowerTotal.lean`): the lowering driver's conditions (calling
  conventions, declared callees and symbols, successor blocks, the `try_call` table rules);
* `iselInB` (V7, `FV/Backend/Proof/IselPrgCtx.lean`): the instruction selector's conditions
  (callee signatures with argument locations and at most 8 ABI returns, declared `func_addr`
  callees and `stack_addr` slots, the return arity).

`InScopeIn I` is `InScopeP I` with `fnScopeInB` for `fnScopeB`. `FV/E2E/LinkScopeInput.lean`
proves `InScopeIn I → InScopeP I` (`inScopeP_of_input`). Kept free of proofs, like
`LinkScopeDefs`.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-- **The per-function input conditions, decided on the CLIF function alone**: `fnScopeB` with
`lowersB` replaced by `extendsWidenB`, `sizeOkB`, `driverInB` and `iselInB`. -/
def fnScopeInB (g : Clif.Function) : Bool :=
  Compile.functionE g &&
  (sigAbiOk g.sig && g.externs.all (fun e => sigAbiOk e.2.sig)) && indSigsOk g &&
  decide (regLocs g.sig).Nodup && (regLocs g.sig).all (·.isArgReg) &&
  g.sig.params.all (fun p => decide (p.ty.width ≤ 64)) && linkFreeB g &&
  dominatedB g && lowerScopeB g && Spill.arityOkB g &&
  (extendsWidenB g && sizeOkB g && driverInB g && Prg.iselInB g) && Spill.entryParamsB g

/-- **`InScopeIn`: the input conditions of a crate without running the compiler's stages per
function** — `InScopeP` with `fnScopeInB` for `fnScopeB`. -/
def InScopeIn (I : LinkInput) : Bool :=
  progScopeB I.prog (fun n => I.syms.lookup n) && I.prog.funcs.all fnScopeInB

/-- The per-function input conditions `g` fails (the conjuncts of `fnScopeInB`, by name). -/
def fnScopeInFails (g : Clif.Function) : List String :=
  let c (b : Bool) (n : String) : List String := if b then [] else [n]
  c (Compile.functionE g) "functionE" ++
  c (sigAbiOk g.sig && g.externs.all (fun e => sigAbiOk e.2.sig)) "sigAbiOk" ++
  c (indSigsOk g) "indSigsOk" ++
  c (decide (regLocs g.sig).Nodup && (regLocs g.sig).all (·.isArgReg) &&
    g.sig.params.all (fun p => decide (p.ty.width ≤ 64))) "regParams" ++
  c (linkFreeB g) "linkFreeB" ++ c (dominatedB g) "dominatedB" ++ c (lowerScopeB g) "lowerScopeB" ++
  c (Spill.arityOkB g) "arityOkB" ++ c (extendsWidenB g) "extendsWidenB" ++ c (sizeOkB g) "sizeOkB" ++
  c (driverInB g) "driverInB" ++ c (Prg.iselInB g) "iselInB" ++ c (Spill.entryParamsB g) "entryParamsB"

end E2E.LinkCheck

module

import FV.Backend.Isel
import FV.Compile.Subset
public import FV.Compile.StoreTyped

public section

namespace Backend

/-- The signatures of `f` and of every callee are ones the end-to-end theorem covers
(`sigAbiOk`, `E2E.InSubset.abiSigs`): `normal` parameters plus at most one `sret` pointer (in
x8, returned in x0), `normal` returns. Other special-purpose parameters (`vmctx`, `sarg`) are
compiled but flagged unverified. -/
@[expose] def abiSigs (f : Clif.Function) : Bool :=
  sigAbiOk f.sig && f.externs.all (sigAbiOk ·.2.sig)

/-- The theorem's conditions that do not need the rest of the file (`E2E.InSubset.subsetE`,
`E2E.InSubset.abiSigs`, `E2E.InSubset.indSigs`). -/
@[expose] def verifiable (f : Clif.Function) : Bool :=
  Compile.functionE f && abiSigs f && indSigsOk f

/-- The typed theorem's conditions that do not need the rest of the file (`E2E.InSubsetT`:
`subsetET`, `storeTyped`, `abiSigs`, `indSigs`; S11e5 Stage C): the typed movement scope
`Compile.functionET` (float parameters, returns, block parameters, loads, stores, constants,
`select`, `bitcast`), float stores storing float values. -/
def verifiableT (f : Clif.Function) : Bool :=
  Compile.functionET f && Compile.storeTypedB f && abiSigs f && indSigsOk f

end Backend

import FV.Backend.Isel
import FV.Compile.Subset
import FV.Compile.StoreTyped

namespace Backend

/-- The signatures of `f` and of every callee are ones the end-to-end theorem covers
(`sigAbiOk`, `E2E.InSubset.abiSigs`): `normal` parameters plus at most one `sret` pointer (in
x8, returned in x0), `normal` returns. Other special-purpose parameters (`vmctx`, `sarg`) are
compiled but flagged unverified. -/
def abiSigs (f : Clif.Function) : Bool :=
  sigAbiOk f.sig && f.externs.all (sigAbiOk ·.2.sig)

/-- The call-site signatures of `f`'s indirect calls (`call_indirect`, `try_call_indirect`) are
ones the end-to-end theorem covers (`sigAbiOk`, `E2E.InSubset.indSigs`); their parameters beyond
x0..x7 are passed on the stack (S5). `indSigsOk` additionally limits them to 8 parameters (the
scope before S5, all arguments in registers). -/
def indSigsAbiOk (f : Clif.Function) : Bool :=
  (indSigs f).all fun s => sigAbiOk s

/-- An indirect-call scope of at most 8 parameters (`indSigsOk`, before S5) is in `indSigsAbiOk`. -/
theorem indSigsAbiOk_of_indSigsOk {f : Clif.Function} (h : indSigsOk f = true) :
    indSigsAbiOk f = true := by
  simp only [indSigsOk, indSigsAbiOk, List.all_eq_true, Bool.and_eq_true] at h ⊢
  exact fun s hs => (h s hs).2

/-- The theorem's conditions that do not need the rest of the file (`E2E.InSubset.subsetE`,
`E2E.InSubset.abiSigs`, `E2E.InSubset.indSigs`). -/
def verifiable (f : Clif.Function) : Bool :=
  Compile.functionE f && abiSigs f && indSigsAbiOk f

/-- The typed theorem's conditions that do not need the rest of the file (`E2E.InSubsetT`:
`subsetET`, `storeTyped`, `abiSigs`, `indSigs`; S11e5 Stage C): the typed movement scope
`Compile.functionET` (float parameters, returns, block parameters, loads, stores, constants,
`select`, `bitcast`), float stores storing float values. -/
def verifiableT (f : Clif.Function) : Bool :=
  Compile.functionET f && Compile.storeTypedB f && abiSigs f && indSigsAbiOk f

end Backend

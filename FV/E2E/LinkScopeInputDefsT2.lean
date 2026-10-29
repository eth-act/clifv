module

public import FV.E2E.LinkScopeInputDefsT
public import FV.Compile.SelectTyped
public import FV.Backend.Proof.EntryClass

@[expose] public section

/-!
# The typed input conditions with the verifier's entry and `select` typing (S11 slice 8)

`fnScopeInTB2 g`: `fnScopeInTB g` and two input checks of the CLIF verifier's typing that the
typed movement scope does not make:

* `Backend.Proof.entryClassOkB`: the entry block's parameters have the register classes of the
  signature's parameters. Without it the entry `Args` pairs an int vreg with `v0` (or a float vreg
  with `x0`): `function %a(f64, i64) -> i64 { block0(v0: i64, v1: i64): return v0 }` is in
  `fnScopeInTB`'s other conjuncts and fails `Spill.ctlSpillB` (and `ctlInstsB` when the pair
  survives `prepare`);
* `Compile.selectTypedB`: a float `select` selects float-defined values. Without it
  `select.f64 c, x, y` with an integer `x` lowers to an `fcsel` of an int vreg, which fails
  `formsCoveredB`.

On `fnScopeInTB2` the run-time checks `Spill.ctlSpillB`, `formsCoveredB`, `Spill.resClassOkB`
and `ctlInstsB` of `fnScopeInTB`'s `lowerOutTB` are theorems (`LinkScopeInputT2.lean`).
`fnScopeInTB` and `InScopeInT` are unchanged; `InScopeInT2` is `InScopeInT` with
`fnScopeInTB2`.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof

/-- **The typed per-function input conditions with the entry and `select` typing**. -/
def fnScopeInTB2 (g : Clif.Function) : Bool :=
  fnScopeInTB g && entryClassOkB g && Compile.selectTypedB g

/-- **`InScopeInT2`**: `InScopeInT` with `fnScopeInTB2`. -/
def InScopeInT2 (I : LinkInput) : Bool :=
  progScopeInB I.prog (fun n => I.syms.lookup n) && I.prog.funcs.all fnScopeInTB2

/-- The conjuncts of `fnScopeInTB2` a function fails (`fnScopeInFailsT`'s, then the two typing
checks). -/
def fnScopeInFailsT2 (g : Clif.Function) : List String :=
  fnScopeInFailsT g ++ (if entryClassOkB g then [] else ["entryClassOkB"]) ++
    (if Compile.selectTypedB g then [] else ["selectTypedB"])

end E2E.LinkCheck

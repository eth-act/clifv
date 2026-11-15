import FV.Link.OptCompile

/-! # Constant-phi removal in the linked compiler's input: the definition (#990)

`lean-backend` compiles every function after the `i128` legalisation and constant-phi removal
(`Opt.ConstPhi.select`, `FV/Opt/ConstPhiSelect.lean`). As for the mid-end (`FnInput.opt`,
`FV/Link/OptCompile.lean`) and the self tail calls (`FnInput.tail`), the input of the linked
compiler is CLIF text: `FnInput.cp` prints the transformed function after the file's header lines
when `Opt.ConstPhi.keeps` holds (the pass changes the function and that text parses, and
legalises, back to it); otherwise the function keeps its input. That is `lean-backend`'s decision,
so `link-check` and `lean-link`, which compile `LinkSpec.cp S`, compile what `lean-backend`
compiled. Theorems: `FV/Link/ConstPhiExe.lean`. Kept free of proofs.
-/

namespace Link

open E2E.LinkCheck

/-- **The constant-phi-removed input of a function**: `Opt.ConstPhi.run` of its function, printed
after the file's header, when `Opt.ConstPhi.keeps` holds; the input itself otherwise. -/
def _root_.E2E.LinkCheck.FnInput.cp (fi : FnInput) : FnInput :=
  if Opt.ConstPhi.keeps (clifHeader fi.clif) fi.func then
    { fi with clif := clifHeader fi.clif ++ (Opt.ConstPhi.run fi.func).print, k := 0 }
  else fi

/-- The input with every function's constant phis removed (`FnInput.cp`). -/
def LinkSpec.cp (S : LinkSpec) : LinkSpec := { S with funcs := S.funcs.map FnInput.cp }

/-- The functions of `S` whose constant phis are removed. -/
def LinkSpec.cpChanged (S : LinkSpec) : List String :=
  S.funcs.filterMap fun fi => if fi.cp.clif != fi.clif then some fi.func.name else none

/-- The functions of `S` the pass changes whose printed form does not parse back to them (they
keep their input). -/
def LinkSpec.cpFallbacks (S : LinkSpec) : List String :=
  S.funcs.filterMap fun fi =>
    let f := fi.func
    if !decide (Opt.ConstPhi.run f = f) && fi.cp.clif == fi.clif then some f.name else none

end Link

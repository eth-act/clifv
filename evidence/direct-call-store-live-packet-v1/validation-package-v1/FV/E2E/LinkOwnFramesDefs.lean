import FV.E2E.LinkCheck

/-! # Input condition of the `outFits` link check (docs/TO-PROVE.md §3, L2)

`okB`'s check "outFits" asks that the stack-passed parameters of every callee of `g` in the
program fit `g`'s outgoing argument area (`outFitsB e.2.sig fr.intBase`). The lowering sizes that
area by the calls `g` makes (`call` statements and `try_call` terminators: `CallsStack`,
`TryStack`), so it covers the stack arguments of every extern `g` calls; a declared extern that
`g` never calls directly does not raise it. `outScopeB` asks exactly that every program-internal
extern's stack-passed parameters fit the largest stack-argument area of the externs `g` calls
directly (`callStack`); `FV/E2E/LinkOwnFrames.lean` proves the check from it for every in-scope
function. -/

namespace E2E.LinkCheck

open Backend

/-- The function references `g` calls directly: of its `call` statements and `try_call`
terminators, in block order. -/
def calledRefs (g : Clif.Function) : List Clif.FnRef :=
  g.blocks.flatMap fun B =>
    B.body.filterMap (fun st => match st.inst with
      | .call fn _ => some fn
      | _ => none) ++
    (match B.term with
      | .tryCall fn _ _ => [fn]
      | _ => [])

/-- The largest stack-argument area (`stackBytes`) of the externs `g` calls directly. -/
def callStack (g : Clif.Function) : Nat :=
  (calledRefs g).foldr (fun fn m => max m (((g.extern? fn).map fun e => stackBytes e.sig).getD 0)) 0

/-- **Input condition of "outFits"**: the stack-passed parameters of every extern of `g` naming a
function of `P` fit the stack-argument area of the externs `g` calls directly. -/
def outScopeB (P : Clif.Program) (g : Clif.Function) : Bool :=
  g.externs.all fun e => !(P.func? e.2.name).isSome || outFitsB e.2.sig (callStack g)

end E2E.LinkCheck

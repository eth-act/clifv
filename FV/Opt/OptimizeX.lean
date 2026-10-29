module

public import FV.Opt.Optimize

@[expose] public section

/-!
# `Opt.optimizeX`: the mid-end with the fresh-value guard

A `try_call` binds its results at the function's fresh values (`Clif.Function.freshValue`), and
its normal-return successor reads them there. `removeUnreachable` may lower the fresh value (it
drops the blocks that define the largest values); a function that reads, in a reachable
block, a value it does not define then reads different registers before and after. On
well-formed functions (`Opt.check`) every operand is defined, so this cannot happen; the
pipeline returns ill-formed inputs with only their unreachable blocks removed.
`optimizeX` runs `optimize` unless the function with its unreachable blocks removed reads a
value at or above its fresh value while that fresh value differs from the input's (never on
the CLIF cg_clif writes, whose operands are all defined); then it returns the input unchanged.
Its theorems are in `FV/Opt/Proof/PipelineX.lean`.

`optimizeExe` (the mid-end of the executable compiler and of `lean-backend --opt`) is
`optimizeX` with a guard on the shape of the result (`keepsShapeB`, never observed to fire): the
callees of its `try_call`s and the signatures of its indirect calls are the input's (what the
backend's subset `E2E.InSubset` asks of them), and it keeps a `return_call` and an indirect
call if the input has one (what the linking theorem's program facts `LinkFree`/`IndFree` read),
and has no block when the input has none.
-/

namespace Opt

open Clif

/-- Every operand of `g` (statements and terminators) is below its fresh value. -/
def closedB (g : Function) : Bool :=
  g.blocks.all fun b => b.body.all (fun st => (operands st.inst).all (· < g.freshValue)) &&
    (termOperands b.term).all (· < g.freshValue)

/-- The guard of `optimizeX`: removing unreachable blocks keeps every operand read the same
register (module doc). -/
def freshOkB (f : Function) : Bool :=
  let g := removeUnreachable f
  closedB g || g.freshValue == f.freshValue

/-- The mid-end with the fresh-value guard (module doc). -/
def optimizeX (f : Function) (cfg : Config := {}) : Function :=
  if freshOkB f then optimize f cfg else f

/-- `optimizeX` on every function of a program. -/
def optimizeProgramX (p : Program) (cfg : Config := {}) : Program :=
  { p with funcs := p.funcs.map (optimizeX · cfg) }

/-- The callees of the `try_call` terminators. -/
def tryCallees (f : Function) : List FnRef :=
  f.blocks.filterMap fun b => match b.term with
    | .tryCall fn _ _ => some fn
    | _ => none

/-- The signature ids of the indirect calls (`call_indirect`, `try_call_indirect`). -/
def indSigIds (f : Function) : List Nat :=
  f.blocks.flatMap fun b =>
    (b.body.filterMap fun st => match st.inst with
      | .callIndirect sig _ _ => some sig
      | _ => none) ++
    match b.term with
    | .tryCallIndirect _ _ et => [et.sig]
    | _ => []

/-- No `return_call` (`E2E.LinkCheck.linkFreeB`). -/
def retCallFreeB (g : Function) : Bool :=
  g.blocks.all fun b => match b.term with | .returnCall .. => false | _ => true

/-- No `call_indirect`, `try_call_indirect` (`E2E.LinkCheck.indFreeB`). -/
def indCallFreeB (g : Function) : Bool :=
  g.blocks.all fun b =>
    b.body.all (fun st => match st.inst with | .callIndirect .. => false | _ => true) &&
    (match b.term with | .tryCallIndirect .. => false | _ => true)

/-- The result keeps the shape the backend's and the linker's theorems read (module doc). -/
def keepsShapeB (f g : Function) : Bool :=
  (tryCallees g).all (tryCallees f).contains && (indSigIds g).all (indSigIds f).contains &&
    (retCallFreeB f || !retCallFreeB g) && (indCallFreeB f || !indCallFreeB g) &&
    (!f.blocks.isEmpty || g.blocks.isEmpty)

/-- **The mid-end of the executable compiler** (module doc). -/
def optimizeExe (f : Function) (cfg : Config := {}) : Function :=
  let g := optimizeX f cfg
  if keepsShapeB f g then g else f

/-- `optimizeExe` on every function of a program. -/
def optimizeProgramExe (p : Program) (cfg : Config := {}) : Program :=
  { p with funcs := p.funcs.map (optimizeExe · cfg) }

/-- The configuration of the executable compiler's mid-end: the Cranelift rules restricted to
the proven ones (`--opt-proven-only`), the other options the defaults. -/
def exeConfig : Config := { rules := .cranelift, ruleAllow := .proven }

end Opt

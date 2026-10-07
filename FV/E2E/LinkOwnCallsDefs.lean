import FV.E2E.LinkCheck

/-! # The input condition of the call sites (`callRegs/blrRegs`, `tryRets/blrTry`; L2a)

`callScopeB P S g`: decidable on the CLIF program alone (the signatures, the call sites'
arguments, which names have a symbol in `S`). A call passes its register arguments in
`callRegs s args` (the register locations of the call-site signature `s`, one per argument);
`siteOk` asks them to be the parameter registers of every program function the call may enter.

* a direct call (`call`/`try_call`) of an extern `e` that is a function `h` of `P`:
  `callRegs e.sig args = regLocs h.sig` (with the declared signature, `e.sig = h.sig`, this is
  only the arity of the call: one argument per parameter);
* an indirect call (`call_indirect`, `try_call_indirect`) of signature `s`: every function `h`
  of `P` that `g` may enter through an address (`indToB`) with as many register parameters as
  the call passes takes them in the call's registers, and at a `try_call_indirect` has at least
  as many results as `s` (`tryB`). The checker restricts this to the GOT symbol of the target
  where it knows one (`gotOf`); an input condition cannot, so it covers every such `h`.
-/

namespace E2E.LinkCheck

open Backend

/-- The registers of the register-passed arguments of a call of signature `s` with arguments
`args`: the register locations of `s`, one per argument (`regLocs s` when `args` has one value
per parameter). -/
def callRegs (s : Clif.Signature) (args : List Nat) : List Reg :=
  ((locsOf s).zip args).filterMap fun q => match q.1 with
    | .reg r => some r
    | .stack _ => none

/-- A direct call of `e` with arguments `args`: if `e` names a function `h` of `P`, the call's
argument registers are `h`'s parameter registers. -/
def dirSiteB (P : Clif.Program) (e : Clif.ExtFunc) (args : List Nat) : Bool :=
  match P.func? e.name with
  | some h => decide (callRegs e.sig args = regLocs h.sig)
  | none => true

/-- An indirect call of signature `s` with arguments `args` (`isTry`: a `try_call_indirect`):
every function `h` of `P` that `g` may enter through an address (`indToB`) with as many
register parameters as the call passes takes them in the call's registers (and has at least
the call's ABI results, at a `try_call_indirect`). -/
def indSiteB (P : Clif.Program) (S : String → Option Nat) (g : Clif.Function)
    (s : Clif.Signature) (args : List Nat) (isTry : Bool) : Bool :=
  P.funcs.all fun h => !indToB S g h ||
    decide ((regLocs h.sig).length ≠ (callRegs s args).length) ||
    (decide (regLocs h.sig = callRegs s args) &&
      (!isTry || decide ((sigRets s).length ≤ (sigRets h.sig).length)))

/-- **The input condition of `g`'s call sites** (`dirSiteB` at every direct call, `indSiteB`
at every indirect call). -/
def callScopeB (P : Clif.Program) (S : String → Option Nat) (g : Clif.Function) : Bool :=
  g.blocks.all fun B =>
    B.body.all (fun st => match st.inst with
      | .call fn args => match g.extern? fn with
        | some e => dirSiteB P e args
        | none => true
      | .callIndirect sg _ args => match g.sigDecls.lookup sg with
        | some s => indSiteB P S g s args false
        | none => true
      | _ => true) &&
    match B.term with
    | .tryCall fn args _ => match g.extern? fn with
      | some e => dirSiteB P e args
      | none => true
    | .tryCallIndirect _ args et => match g.sigDecls.lookup et.sig with
      | some s => indSiteB P S g s args true
      | none => true
    | _ => true

end E2E.LinkCheck

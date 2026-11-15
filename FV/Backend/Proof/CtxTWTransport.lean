import Lean
import Std.Data.HashSet

/-!
# `CtxT` → `CtxTW`: the rule families' proofs over the contexts without `call` facts (S11g)

The typed rule families over `CtxT` (`LowerContractT`, `LowerContractTP`) have `…W` forms over
`CtxTW` (`CtxInvT` and the typed scope, without `CallsE`/`CallArgsInt`: the contexts of the typed
scope with float `call`s), and `E2E.TypedRules` has `E2E.TypedRulesW`. The proofs over `program`
never read the `call` facts: a proof uses a `CtxT` premise only through `CtxT.inv`, `CtxT.scope`
and `CtxT.toW`. So the `CtxTW` form of a `CtxT` theorem is the same proof term with every `CtxT`
constant replaced by its `CtxTW` counterpart, as Mathlib's `to_additive` transports
multiplicative declarations.

`ctxW_transport src => dst` declares the theorem `dst`: the statement of `src` with the
replacement `basePairs` (`CtxT ↦ CtxTW`, `CtxT.inv ↦ CtxTW.inv`, `CtxT.scope ↦ CtxTW.scope`,
`CtxT.toW ↦ CtxTW.self`, each family `X ↦ XW`, `TypedRules ↦ TypedRulesW` with its fields),
proven by `src`'s proof term with the same replacement. Every theorem that proof uses whose
statement mentions a replaced constant is transported first, under the name `<name>.ctxW` (reused
when it exists). The kernel checks every transported declaration (`addDecl`), so a proof that
reads a `call` fact (`CtxT.calls`, `CtxT.callArgs`, a `CtxT` constructor or recursor) fails to
transport instead of giving a wrong theorem; so does a definition outside `basePairs` whose
statement or body mentions a replaced constant.
-/

namespace Backend.Proof.CtxTWTransport

open Lean Meta Elab Command

/-- The fields of `E2E.TypedRules` (and `E2E.TypedRulesW`), in order. -/
def typedRulesFields : List String :=
  ["calls", "ind", "term", "termUn", "branch", "branchEx", "try_", "tryUn", "tryInd", "tryIndUn"]

/-- The constants of the `CtxT` world and their `CtxTW` counterparts. -/
def basePairs : List (Name × Name) := [
  (`Backend.Proof.CtxT, `Backend.Proof.CtxTW),
  (`Backend.Proof.CtxT.inv, `Backend.Proof.CtxTW.inv),
  (`Backend.Proof.CtxT.scope, `Backend.Proof.CtxTW.scope),
  (`Backend.Proof.CtxT.toW, `Backend.Proof.CtxTW.self),
  (`Backend.Proof.Driver.ctxT_termCtx, `Backend.Proof.Driver.ctxTW_termCtx),
  (`Backend.Proof.Driver.ctxT_tryRegs, `Backend.Proof.Driver.ctxTW_tryRegs),
  (`Backend.Proof.LowerRuleOkTX, `Backend.Proof.LowerRuleOkTXW),
  (`Backend.Proof.LowerRuleOkTI, `Backend.Proof.LowerRuleOkTIW),
  (`Backend.Proof.LowerRulesCorrectTI, `Backend.Proof.LowerRulesCorrectTIW),
  (`Backend.Proof.MemRuleOkRTX, `Backend.Proof.MemRuleOkRTXW),
  (`Backend.Proof.MemRulesCorrectRTI, `Backend.Proof.MemRulesCorrectRTIW),
  (`Backend.Proof.IndRuleOkT, `Backend.Proof.IndRuleOkTW),
  (`Backend.Proof.IndRulesCorrectT, `Backend.Proof.IndRulesCorrectTW),
  (`Backend.Proof.LowerTermRuleOkT, `Backend.Proof.LowerTermRuleOkTW),
  (`Backend.Proof.LowerTermRulesCorrectT, `Backend.Proof.LowerTermRulesCorrectTW),
  (`Backend.Proof.TermUnmatchableT, `Backend.Proof.TermUnmatchableTW),
  (`Backend.Proof.BranchRuleOkT, `Backend.Proof.BranchRuleOkTW),
  (`Backend.Proof.BranchRulesCorrectT, `Backend.Proof.BranchRulesCorrectTW),
  (`Backend.Proof.BranchExcludedUnmatchableT, `Backend.Proof.BranchExcludedUnmatchableTW),
  (`Backend.Proof.TryIndRuleOkT, `Backend.Proof.TryIndRuleOkTW),
  (`Backend.Proof.TryIndRulesCorrectT, `Backend.Proof.TryIndRulesCorrectTW),
  (`Backend.Proof.TryIndUnmatchableT, `Backend.Proof.TryIndUnmatchableTW),
  (`Backend.Proof.IndRuleOkTP, `Backend.Proof.IndRuleOkTPW),
  (`Backend.Proof.IndRulesCorrectTP, `Backend.Proof.IndRulesCorrectTPW),
  (`Backend.Proof.TryIndRuleOkTP, `Backend.Proof.TryIndRuleOkTPW),
  (`Backend.Proof.TryIndRulesCorrectTP, `Backend.Proof.TryIndRulesCorrectTPW),
  (`E2E.TypedRules, `E2E.TypedRulesW), (`E2E.TypedRules.mk, `E2E.TypedRulesW.mk)] ++
  typedRulesFields.map fun f => (Name.str `E2E.TypedRules f, Name.str `E2E.TypedRulesW f)

/-- The structures whose projections are replaced, with the fields that may be projected. -/
def structPairs : List (Name × Name × Nat) :=
  [(`Backend.Proof.CtxT, `Backend.Proof.CtxTW, 2), (`E2E.TypedRules, `E2E.TypedRulesW, 10)]

/-- The name of the transported form of a theorem used by a transported proof. -/
def autoName (c : Name) : Name := Name.str c "ctxW"

structure St where
  map : NameMap Name
  clean : NameSet := {}

abbrev M := StateRefT St CoreM

/-- The projections of a replaced structure under `e` (visiting each subterm once). -/
partial def projsAux (e : Expr) : StateM (Std.HashSet Expr × List (Name × Nat)) Unit := do
  if (← get).1.contains e then return
  modify fun (v, l) => (v.insert e, l)
  match e with
  | .proj s i b =>
    if structPairs.any (·.1 == s) then modify fun (v, l) => (v, (s, i) :: l)
    projsAux b
  | .app f a => projsAux f; projsAux a
  | .lam _ t b _ => projsAux t; projsAux b
  | .forallE _ t b _ => projsAux t; projsAux b
  | .letE _ t v b _ => projsAux t; projsAux v; projsAux b
  | .mdata _ b => projsAux b
  | _ => pure ()

/-- The projections of a replaced structure in `e`: (structure, field). -/
def projs (e : Expr) : List (Name × Nat) := ((projsAux e).run ({}, [])).2.2

/-- `e` mentions a constant of `m` (no transport). -/
def direct (m : NameMap Name) (e : Expr) : Bool :=
  !(projs e).isEmpty || e.getUsedConstants.any m.contains

/-- The replacement, once every constant `e` uses is in `m` or kept. -/
partial def replaceAll (m : NameMap Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => (m.find? n).map (.const · ls)
    | .proj s i b => (structPairs.find? (·.1 == s)).map fun (_, s', _) => .proj s' i (replaceAll m b)
    | _ => none

mutual
/-- Whether `e` mentions a replaced constant (transporting the theorems it uses whose statements
mention one). -/
partial def needs (e : Expr) : M Bool := do
  let mut r := !(projs e).isEmpty
  for c in e.getUsedConstants do
    if (← ensure c).isSome then r := true
  return r

/-- The counterpart of `c`: a theorem whose statement mentions a replaced constant is
transported; `none` if `c` is kept. -/
partial def ensure (c : Name) : M (Option Name) := do
  let s ← get
  if let some c' := s.map.find? c then return some c'
  if s.clean.contains c then return none
  modify fun s => { s with clean := s.clean.insert c }
  if (← getEnv).contains (autoName c) then
    modify fun s => { s with map := s.map.insert c (autoName c) }
    return some (autoName c)
  match ← getConstInfo c with
  | .thmInfo t =>
    if ← needs t.type then
      transportThm t (autoName c)
      return some (autoName c)
    return none
  | .defnInfo d =>
    let m := (← get).map
    if direct m d.type || direct m d.value then
      throwError "ctxW_transport: definition {c} mentions a replaced constant; give it a counterpart in `basePairs`"
    return none
  | info =>
    if direct (← get).map info.type then
      throwError "ctxW_transport: {c} mentions a replaced constant and is not a theorem (a `CtxT` constructor, recursor or field other than `inv`/`scope`?)"
    return none

/-- Declare `n`: theorem `t` with the replacement. -/
partial def transportThm (t : TheoremVal) (n : Name) : M Unit := do
  for (s, i) in projs t.type ++ projs t.value do
    if let some (_, _, k) := structPairs.find? (·.1 == s) then
      unless i < k do
        throwError "ctxW_transport: {t.name} reads field {i} of {s} (a `call` fact)"
  for c in t.value.getUsedConstants do
    discard <| ensure c
  let m := (← get).map
  let val : TheoremVal := ⟨⟨n, t.levelParams, replaceAll m t.type⟩, replaceAll m t.value, [n]⟩
  addDecl (Declaration.thmDecl val)
  modify fun s => { s with map := s.map.insert t.name n }
end

/-- The map of `basePairs`. -/
def baseMap : NameMap Name := basePairs.foldl (fun m (a, b) => m.insert a b) {}

/-- `ctxW_transport src => dst`: the `CtxTW` form of theorem `src`, named `dst` (in the current
namespace). -/
elab "ctxW_transport " src:ident " => " dst:ident : command => do
  let srcName ← liftCoreM <| realizeGlobalConstNoOverload src
  let dstName := (← getCurrNamespace) ++ dst.getId
  liftCoreM do
    let some c' ← (ensure srcName).run' { map := baseMap }
      | throwError "ctxW_transport: {srcName} does not mention `CtxT`"
    let info ← getConstInfo c'
    let val : TheoremVal :=
      ⟨⟨dstName, info.levelParams, info.type⟩, .const c' (info.levelParams.map Level.param), [dstName]⟩
    addDecl (Declaration.thmDecl val)

end Backend.Proof.CtxTWTransport

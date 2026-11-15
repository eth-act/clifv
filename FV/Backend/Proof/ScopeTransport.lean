import Lean

/-!
# `CtxTW` → `CtxTS S`: the typed families and the typed driver over an abstract scope (#1002 part 2)

The typed rule families over `CtxTW` (`LowerContractT`, `LowerContractTP`, `LowerContractTF`),
`E2E.TypedRulesW`, the shape `Driver.LowerShapeTC` and the driver hypothesis
`Driver.DriverHypTC` mention an instruction scope (`InstScopeTF`) that their proofs over `program`
and the typed simulation (`LowerSimTC`) never read: a proof uses it only to pass it on. So their
forms over an abstract scope `S : Backend.Proof.InstScope` (`CtxTS S`, `TypedRulesS S`,
`LowerShapeTCS S`, `DriverHypTCS S`: the same fields, the scope `S.P`) are the same proof terms
with every such constant replaced by its counterpart applied to `S`, abstracted over `S`, as
`CtxTWTransport.lean` transports the `CtxT` proofs to `CtxTW`.

* `scopeS_transport src => dst` declares the theorem `dst : ∀ S, …`: the statement of `src` with
  the replacement, proven by `src`'s proof term with the replacement. Every theorem or definition
  that proof uses whose statement mentions a replaced constant is transported first, under the
  name `<name>.scopeS` (reused when it exists).
* `scopeS_transport_defs` declares the scope-generic families (`defPairs`): the definitions over
  `CtxTW` with the replacement, abstracted over `S`.

The counterparts take `S` as their first argument. The kernel checks every transported
declaration (`addDecl`), so a proof that reads the scope as `InstScopeTF` (the exclusion and
non-E unmatchability proofs, the `f64const` root) fails to transport instead of giving a wrong
theorem; those are proven over `CtxTS S` by hand.
-/

namespace Backend.Proof.ScopeTransport

open Lean Meta Elab Command

/-- The structures and their scope-generic counterparts (the same fields in the same order; the
counterpart takes the scope first). Their constructors, recursors and projections follow. -/
def structPairs : List (Name × Name) := [
  (`Backend.Proof.CtxTW, `Backend.Proof.CtxTS),
  (`E2E.TypedRulesW, `E2E.TypedRulesS),
  (`Backend.Proof.Driver.LowerShapeTC, `Backend.Proof.Driver.LowerShapeTCS),
  (`Backend.Proof.Driver.DriverHypTC, `Backend.Proof.Driver.DriverHypTCS)]

/-- The theorems proven by hand over the abstract scope. -/
def thmPairs : List (Name × Name) := [
  (`Backend.Proof.CtxTW.self, `Backend.Proof.CtxTS.self),
  (`Backend.Proof.Driver.ctxTW_termCtx, `Backend.Proof.Driver.ctxTS_termCtx),
  (`Backend.Proof.Driver.ctxTW_tryRegs, `Backend.Proof.Driver.ctxTS_tryRegs)]

/-- The rule families over `CtxTW` and their scope-generic forms (`scopeS_transport_defs`). -/
def defPairs : List (Name × Name) := [
  (`Backend.Proof.LowerRuleOkTXW, `Backend.Proof.LowerRuleOkTXS),
  (`Backend.Proof.LowerRuleOkTIW, `Backend.Proof.LowerRuleOkTIS),
  (`Backend.Proof.LowerRulesCorrectTIW, `Backend.Proof.LowerRulesCorrectTIS),
  (`Backend.Proof.MemRuleOkRTXW, `Backend.Proof.MemRuleOkRTXS),
  (`Backend.Proof.MemRulesCorrectRTIW, `Backend.Proof.MemRulesCorrectRTIS),
  (`Backend.Proof.IndRuleOkTW, `Backend.Proof.IndRuleOkTS),
  (`Backend.Proof.IndRulesCorrectTW, `Backend.Proof.IndRulesCorrectTS),
  (`Backend.Proof.LowerTermRuleOkTW, `Backend.Proof.LowerTermRuleOkTS),
  (`Backend.Proof.LowerTermRulesCorrectTW, `Backend.Proof.LowerTermRulesCorrectTS),
  (`Backend.Proof.TermUnmatchableTW, `Backend.Proof.TermUnmatchableTS),
  (`Backend.Proof.BranchRuleOkTW, `Backend.Proof.BranchRuleOkTS),
  (`Backend.Proof.BranchRulesCorrectTW, `Backend.Proof.BranchRulesCorrectTS),
  (`Backend.Proof.BranchExcludedUnmatchableTW, `Backend.Proof.BranchExcludedUnmatchableTS),
  (`Backend.Proof.TryIndRuleOkTW, `Backend.Proof.TryIndRuleOkTS),
  (`Backend.Proof.TryIndRulesCorrectTW, `Backend.Proof.TryIndRulesCorrectTS),
  (`Backend.Proof.TryIndUnmatchableTW, `Backend.Proof.TryIndUnmatchableTS),
  (`Backend.Proof.IndRuleOkTPW, `Backend.Proof.IndRuleOkTPS),
  (`Backend.Proof.IndRulesCorrectTPW, `Backend.Proof.IndRulesCorrectTPS),
  (`Backend.Proof.TryIndRuleOkTPW, `Backend.Proof.TryIndRuleOkTPS),
  (`Backend.Proof.TryIndRulesCorrectTPW, `Backend.Proof.TryIndRulesCorrectTPS),
  (`Backend.Proof.NonEUnmatchableTFW, `Backend.Proof.NonEUnmatchableTFS)]

/-- The type of the abstract scope. -/
def scopeType : Expr := .const `Backend.Proof.InstScope []

/-- The name of the transported form of a declaration used by a transported proof. -/
def autoName (c : Name) : Name := Name.str c "scopeS"

structure St where
  /-- every replaced constant and its counterpart -/
  map : NameMap Name
  /-- the replaced structures -/
  structs : NameMap Name
  /-- the constants checked to need no transport -/
  clean : NameSet := {}

abbrev M := StateRefT St MetaM

/-- The replacement map of the structures declared so far, with their constructors, recursors and
projections. -/
def initState : MetaM St := do
  let env ← getEnv
  let mut m : NameMap Name := {}
  let mut sm : NameMap Name := {}
  for (a, b) in thmPairs ++ defPairs do
    m := m.insert a b
  for (s, s') in structPairs do
    unless env.contains s && env.contains s' do continue
    let fs := getStructureFields env s
    unless fs == getStructureFields env s' do
      throwError "scopeS_transport: {s} and {s'} have different fields"
    sm := sm.insert s s'
    m := m.insert s s'
    for fl in fs do
      m := m.insert (s ++ fl) (s' ++ fl)
    if let (some c, some c') := (getStructureCtor? env s, getStructureCtor? env s') then
      m := m.insert c.name c'.name
    for suf in [`rec, `recOn, `casesOn] do
      if env.contains (s ++ suf) && env.contains (s' ++ suf) then
        m := m.insert (s ++ suf) (s' ++ suf)
  return { map := m, structs := sm }
where
  getStructureCtor? (env : Environment) (s : Name) : Option ConstructorVal :=
    if isStructure env s then some (getStructureCtor env s) else none

/-- The replacement: a replaced constant becomes its counterpart applied to the scope `S`. -/
partial def replaceAll (m sm : NameMap Name) (S : Expr) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => (m.find? n).map fun n' => mkApp (.const n' ls) S
    | .proj s i b => (sm.find? s).map fun s' => .proj s' i (replaceAll m sm S b)
    | _ => none

/-- `e` mentions a replaced constant or projects a replaced structure. -/
partial def direct (m sm : NameMap Name) (e : Expr) : Bool :=
  (e.find? fun
    | .const n _ => m.contains n
    | .proj s _ _ => sm.contains s
    | _ => false).isSome

mutual
/-- Whether `e` mentions a replaced constant (transporting the declarations it uses whose
statements mention one). -/
partial def needs (e : Expr) : M Bool := do
  let mut r := direct (← get).map (← get).structs e
  for c in e.getUsedConstants do
    if (← ensure c).isSome then r := true
  return r

/-- The counterpart of `c`: a declaration whose statement mentions a replaced constant is
transported; `none` if `c` is kept. -/
partial def ensure (c : Name) : M (Option Name) := do
  let s ← get
  if let some c' := s.map.find? c then
    if (← getEnv).contains c' then return some c'
    match ← getConstInfo c with
    | .defnInfo d => transportDefn d c'; return some c'
    | _ => throwError "scopeS_transport: {c'}, the counterpart of {c}, is not declared"
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
    if ← needs d.type then
      transportDefn d (autoName c)
      return some (autoName c)
    return none
  | info =>
    if direct (← get).map (← get).structs info.type then
      throwError "scopeS_transport: {c} mentions a replaced constant and is not a theorem or definition"
    return none

/-- `type` and `value` with the replacement, abstracted over the scope. -/
partial def abstractS (type value : Expr) : M (Expr × Expr) := do
  for c in type.getUsedConstants ++ value.getUsedConstants do
    discard <| ensure c
  let m := (← get).map
  let sm := (← get).structs
  withLocalDeclD `S scopeType fun S => do
    let t ← mkForallFVars #[S] (replaceAll m sm S type)
    let v ← mkLambdaFVars #[S] (replaceAll m sm S value)
    return (t, v)

/-- Declare `n`: theorem `t` with the replacement. -/
partial def transportThm (t : TheoremVal) (n : Name) : M Unit := do
  let (ty, val) ← abstractS t.type t.value
  addDecl (Declaration.thmDecl ⟨⟨n, t.levelParams, ty⟩, val, [n]⟩)
  modify fun s => { s with map := s.map.insert t.name n }

/-- Declare `n`: definition `d` with the replacement. -/
partial def transportDefn (d : DefinitionVal) (n : Name) : M Unit := do
  let (ty, val) ← abstractS d.type d.value
  let hints := match d.hints with
    | .regular h => .regular (h + 1)
    | h => h
  addDecl (Declaration.defnDecl ⟨⟨n, d.levelParams, ty⟩, val, hints, d.safety, [n]⟩)
  modify fun s => { s with map := s.map.insert d.name n }
end

/-- `scopeS_transport src => dst`: the scope-generic form of theorem `src`, named `dst` (in the
current namespace). -/
elab "scopeS_transport " src:ident " => " dst:ident : command => do
  let srcName ← liftCoreM <| realizeGlobalConstNoOverload src
  let dstName := (← getCurrNamespace) ++ dst.getId
  liftTermElabM do
    let some c' ← (ensure srcName).run' (← initState)
      | throwError "scopeS_transport: {srcName} does not mention a replaced constant"
    let info ← getConstInfo c'
    addDecl (Declaration.thmDecl
      ⟨⟨dstName, info.levelParams, info.type⟩, .const c' (info.levelParams.map Level.param), [dstName]⟩)

/-- `scopeS_transport_defs`: the scope-generic families of `defPairs` not declared yet. -/
elab "scopeS_transport_defs" : command => do
  liftTermElabM do
    let go : M Unit := do
      for (a, _) in defPairs do
        discard <| ensure a
    go.run' (← initState)

end Backend.Proof.ScopeTransport

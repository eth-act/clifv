/-
Import-use facts for `scripts/shake/shake.py` (the unused-import remover).

usage: lake env lean --run scripts/shake/Facts.lean <out.jsonl> <modules.txt>

Imports every module listed in <modules.txt> (one per line; all must be built) and writes one JSON
line `{"g": module, "imports": [...], "ns": [...], "tokens": [...],
"simpsets": [...], "orderkeys": [...]}` per other module of the import closure, and one per listed
module:
  {"m": module, "imports": [...], "nconsts": n, "rev": bool,
   "needs": [...], "indirect": [...], "extra": [...], "quoted": [...], "ns": [...],
   "tokens": [...], "simpsets": [...], "orderkeys": [...]}
* needs: modules defining a constant that a constant of `m` mentions in its type or value (as
  `lake shake` computes them: reserved names are skipped, `_simp_*` count as their base name);
* indirect: modules that applied an attribute to one of those constants (Lean's
  `indirectModUseExt`); shake.py keeps such a module if it is still reachable;
* extra: modules recorded by the elaborator as extra dependencies of `m` (notations, macros,
  elaborators, attributes, simp sets, instances used only during elaboration, ...);
* quoted: modules of the global names `m`'s syntax quotations refer to (`quotedOf`);
* rev: `m` asked to be preserved in every importer (`recordExtraRevUseOfCurrentModule`);
* ns: the namespaces `m` registers (`open X` fails unless some imported module registers `X`);
* tokens: the parser tokens `m` adds (`tokensOf`);
* simpsets: the simp sets `m` adds lemmas to (`simpSetsOf`). A simp lemma that rewrote only a
  hypothesis the proof then did not use leaves no trace in the proof term or in `extra`;
* orderkeys: `orderKeysOf`.
This is the analysis of Lean 4.34's `lake shake` (Lake/CLI/Shake.lean, `calcNeeds`), which itself
refuses non-`module` files; the import edits are made by shake.py.
-/
import Lean
open Lean

def depName? (reserved : NameHashSet) (ref : Name) : Option Name := do
  guard <| !reserved.contains ref
  return if ref.isStr && ref.getString!.startsWith "_simp_" then ref.getPrefix else ref

def jsonArr (ns : Array Name) : Json := Json.arr (ns.map (Json.str ·.toString))

/-- The namespaces module `i` registers (the entries of Lean's private `namespacesExt`). -/
unsafe def namespacesOf (env : Environment) (i : Nat) : Array Name := Id.run do
  for (n, es) in env.header.moduleData[i]!.entries do
    if toString n == "_private.Lean.Namespace.0.Lean.namespacesExt" then
      return es.map fun e => (unsafeCast e : Name)
  return #[]

/-- The tokens module `i` adds to the parser (Lean's `parserExtension` entries, global or scoped):
using one needs the module even when no constant of it is used, for example a tactic in a `first`
alternative that never runs. -/
unsafe def tokensOf (env : Environment) (i : Nat) : Array String := Id.run do
  let mut out := #[]
  for (n, es) in env.header.moduleData[i]!.entries do
    if n == `Lean.Parser.parserExtension then
      for e in es do
        match (unsafeCast e : ScopedEnvExtension.Entry Parser.ParserExtension.OLeanEntry) with
        | .global (.token t) | .scoped _ (.token t) => out := out.push t
        | _ => pure ()
  return out

/-- The simp sets module `i` adds lemmas to: Lean's default set (`simp`), and the sets of
`register_simp_attr` (extensions named `ext._@.<declaring module>._hyg...`). -/
def simpSetsOf (env : Environment) (i : Nat) : Array String := Id.run do
  let mut out := #[]
  for (n, es) in env.header.moduleData[i]!.entries do
    let s := toString n
    if es.size > 0 && (n == `Lean.Meta.simpExtension || s.startsWith "ext._@.") then
      out := out.push s
  return out

/-- Keys of the extensions in which the order of modules matters (Lean tries later-loaded entries
first): macro_rules and elaborators per syntax kind, instances per class, simp lemmas per simp set
(custom sets only). Two modules adding entries under the same key must keep their relative load
order in every importer. -/
unsafe def orderKeysOf (env : Environment) (i : Nat) : Array String := Id.run do
  let mut out : Std.HashSet String := {}
  for (n, es) in env.header.moduleData[i]!.entries do
    let s := toString n
    if n == `Lean.Elab.macroAttribute || n == `Lean.Elab.Tactic.tacticElabAttribute ||
        n == `Lean.Elab.Term.termElabAttribute || n == `Lean.Elab.Command.commandElabAttribute then
      for e in es do
        match (unsafeCast e : ScopedEnvExtension.Entry KeyedDeclsAttribute.OLeanEntry) with
        | .global x | .scoped _ x => out := out.insert s!"{n}:{x.key}"
    else if n == `Lean.Meta.instanceExtension then
      for e in es do
        match (unsafeCast e : ScopedEnvExtension.Entry Meta.InstanceEntry) with
        | .global x | .scoped _ x =>
          -- the first four discrimination-tree keys (`Decidable (Eq Foo ..)`: `Decidable Eq Foo`)
          let ks := (x.keys.extract 0 4).toList.map fun
            | Meta.DiscrTree.Key.const a _ => toString a
            | _ => "_"
          out := out.insert s!"instance:{" ".intercalate ks}"
    else if s.startsWith "ext._@." && es.size > 0 then
      out := out.insert s!"simp:{s}"
  return out.toArray

/-- The name `e` builds, if it is a `Name` literal (`Name.mkStr1 "a"`, `Name.mkStr p "a"`, ...). -/
partial def nameLit? (e : Expr) : Option Name :=
  match e.getAppFn, e.getAppArgs with
  | .const ``Name.anonymous _, #[] => some .anonymous
  | .const c _, args =>
    if c == ``Name.mkStr || c == ``Name.str then
      match args with
      | #[p, .lit (.strVal s)] => (nameLit? p).map (·.str s)
      | _ => none
    else if c.getPrefix == ``Name && (c.getString!.startsWith "mkStr") then
      args.foldlM (init := Name.anonymous) fun n a =>
        match a with | .lit (.strVal s) => some (n.str s) | _ => none
    else none
  | _, _ => none

/-- Global names quoted in the syntax quotations of the definitions of module `i` (a macro's
identifiers are resolved when it is defined: `Syntax.Preresolved.decl`), as constants of other
modules: the module defining a macro needs them although no constant of it mentions them. -/
unsafe def quotedOf (env : Environment) (i : Nat) : NameHashSet := Id.run do
  let mut out : NameHashSet := {}
  for ci in env.header.moduleData[i]!.constants do
    let some v := ci.value? (allowOpaque := true) | continue
    unless v.getUsedConstants.any (· == ``Syntax.Preresolved.decl) do continue
    let mut seen : Std.HashSet USize := {}
    let mut todo := #[v]
    while h : todo.size > 0 do
      let e := todo[todo.size - 1]
      todo := todo.pop
      let a := ptrAddrUnsafe e
      if seen.contains a then continue
      seen := seen.insert a
      if let some n := nameLit? e then
        if !n.isAnonymous && env.contains n then out := out.insert n
        continue
      match e with
      | .app f x => todo := todo.push f |>.push x
      | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
      | .letE _ t x b _ => todo := todo.push t |>.push x |>.push b
      | .mdata _ x | .proj _ _ x => todo := todo.push x
      | _ => pure ()
  return out

/-- The module of `c` as seen from module `i` (whose import closure is `clos`). Several modules
can define the same realized constant (equation lemmas and the like, made on demand) without an
import conflict; in an environment holding modules that are never imported together the constant
may then belong to a module outside `i`'s closure: it is attributed to the module of the nearest
prefix that is in the closure. -/
partial def ownerIn (env : Environment) (clos : Std.HashSet Nat) (i : Nat) (c : Name) : Option Nat :=
  let up := if c.getPrefix.isAnonymous then none else ownerIn env clos i c.getPrefix
  match env.getModuleIdxFor? c with
  | some j => if j == i || clos.contains j then some j else up
  | none => up

unsafe def main (args : List String) : IO UInt32 := do
  let [outPath, listPath] := args | throw <| .userError "usage: Facts.lean <out.jsonl> <modules.txt>"
  let mods := (← IO.FS.lines listPath).filter (!·.isEmpty) |>.map String.toName
  initSearchPath (← findSysroot)
  let env ← importModules (mods.map ({ module := · })) {} (loadExts := false)
  let mut reserved : NameHashSet := {}
  for (c, _) in env.constants do
    if isReservedName env c then reserved := reserved.insert c
  -- decl name -> modules that applied an attribute to it
  let mut indirect : Std.HashMap Name (Array Name) := {}
  for j in [0:env.header.moduleData.size] do
    for e in getIndirectModUses env j do
      indirect := indirect.alter e.declName (·.getD #[] |>.push env.header.moduleNames[j]!)
  let wanted : NameHashSet := mods.foldl (·.insert ·) {}
  -- import closures (moduleData is in import order)
  let mut clos : Array (Std.HashSet Nat) := #[]
  for i in [0:env.header.moduleData.size] do
    let mut s : Std.HashSet Nat := {}
    for imp in env.header.moduleData[i]!.imports do
      if let some j := env.getModuleIdx? imp.module then
        s := s.insert j
        for k in clos[j]! do s := s.insert k
    clos := clos.push s
  let h ← IO.FS.Handle.mk outPath .write
  for i in [0:env.header.moduleData.size] do
    let m := env.header.moduleNames[i]!
    unless wanted.contains m do
      -- the rest of the import graph (Lean, Std, ...)
      let imps := env.header.moduleData[i]!.imports.map (·.module)
      h.putStrLn (Json.mkObj [("g", m.toString), ("imports", jsonArr imps),
        ("ns", jsonArr (namespacesOf env i)),
        ("tokens", Json.arr ((tokensOf env i).map Json.str)),
        ("simpsets", Json.arr ((simpSetsOf env i).map Json.str)),
        ("orderkeys", Json.arr ((orderKeysOf env i).map Json.str))]).compress
      continue
    let md := env.header.moduleData[i]!
    let mut needs : NameHashSet := {}
    let mut ind : NameHashSet := {}
    for ci in md.constants do
      let visit (e : Expr) (acc : NameHashSet × NameHashSet) : NameHashSet × NameHashSet :=
        e.foldConsts acc fun c (needs, ind) => Id.run do
          let some c := depName? reserved c | return (needs, ind)
          let mut needs := needs
          let mut ind := ind
          if let some j := ownerIn env clos[i]! i c then
            if j != i then needs := needs.insert env.header.moduleNames[j]!
          for n in indirect[c]?.getD #[] do
            if n != m then ind := ind.insert n
          return (needs, ind)
      (needs, ind) := visit ci.type (needs, ind)
      if let some v := ci.value? (allowOpaque := true) then
        (needs, ind) := visit v (needs, ind)
    let mut quoted : NameHashSet := {}
    for c in (quotedOf env i).toArray do
      if let some j := ownerIn env clos[i]! i c then
        if j != i then quoted := quoted.insert env.header.moduleNames[j]!
    let extra := (getExtraModUses env i).map (·.module) |>.filter (· != m)
    let sortNames (s : Array Name) := s.qsort (·.toString < ·.toString)
    let j := Json.mkObj [
      ("m", m.toString),
      ("imports", jsonArr (md.imports.map (·.module))),
      ("nconsts", md.constants.size),
      ("rev", isExtraRevModUse env i),
      ("needs", jsonArr (sortNames needs.toArray)),
      ("indirect", jsonArr (sortNames ind.toArray)),
      ("extra", jsonArr (sortNames extra)),
      ("quoted", jsonArr (sortNames quoted.toArray)),
      ("ns", jsonArr (namespacesOf env i)),
      ("tokens", Json.arr ((tokensOf env i).map Json.str)),
      ("simpsets", Json.arr ((simpSetsOf env i).map Json.str)),
      ("orderkeys", Json.arr ((orderKeysOf env i).map Json.str))]
    h.putStrLn j.compress
  return 0

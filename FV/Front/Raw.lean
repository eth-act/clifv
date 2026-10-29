module

public import FV.Clif.Parse
public import FV.Front.Rename
public import Std.Data.HashMap

@[expose] public section

/-!
# cg_clif's raw dumps and their decoding (T7b, T7c, docs/contracts/frontend.md)

**The raw format.** cg_clif writes one file per function (`<symbol>.unopt.clif`,
`<symbol>.opt.clif`): the `set`/`target` header, comments (`; symbol <symbol>`, `; instance …`,
`; abi …`), the function in Cranelift's text syntax, and — with this repository's patch of cg_clif
(`scripts/patches/cg-clif-extnames.patch`) — after it the function's **external-name table** and
the module's **declarations** of the names it uses:

```text
; clifv-extnames 1
; userextnameJ = uNS:IDX                                  (every entry of the table)
; decl u0:IDX func LINKAGE "SYMBOL"                       (FuncIds, the function's own included)
; decl u1:IDX data LINKAGE rw|ro tls|notls "SYMBOL"       (DataIds)
; libcall %NAME "SYMBOL"                                  (Cranelift libcalls)
; end clifv-extnames
```

The function names code and data by **external names**: its own name and every callee
`fnK = [colocated] u0:IDX sigM` by a module identity `uNS:IDX` (namespace 0: a `FuncId`,
1: a `DataId` of the codegen unit's module), every symbol global value
`gvK = symbol [colocated] [tls] userextnameJ[+off]` by entry `J` of the function's
external-name table, libcalls by `%NAME`. Instructions may carry a source location `@XXXX`.

**Reading** (`Raw.parseDump`, `readDump`): the function is parsed by the CLIF parser's own
combinators (`Clif.Parse`), with three extensions of the accepted syntax only — an external name
may be `uNS:IDX`, `userextnameJ` or `%NAME`, a callee's signature may be a reference `sigM` to a
signature declared before it, and an instruction's source location is skipped — into a
`Clif.Function` whose names are the external names as written (`"u0:7"`, `"userextname1"`,
`"Memcpy"`); comments are ignored. The table is read line by line; a key declared twice, a
missing or malformed table is an error.

**Decoding** (`decodeFn`): `Dump.raw` resolves `userextnameJ` through the function's table to the
module identity it denotes (`Dump.refRen`): the function in **module identities**. `decodeFn ρ`
then renames every module identity and libcall by `ρ`, the unit's declarations (`unitTable`:
identity ↦ the CLIF name of its symbol, `clifName`; one name per identity across the unit's
functions), and checks that every name is declared, of the right kind (a callee a function or
libcall, a `symbol` a non-TLS and a `tls` one a TLS data object), and expressible as a CLIF name.
`decodeFn_spec`: the decoded function **is** the function in module identities renamed by `ρ`
(`Function.rename`); `FV/Front/BundleProof.lean` lifts this to the units' program.
-/

namespace Front

open Clif Clif.Parse

/-! ## The function -/

namespace Raw

/-- An external name: `%NAME`, `userextnameJ`, or `uNS:IDX` (as `"uNS:IDX"`, numbers in
decimal). -/
def rawName : P String := do
  match ← peek with
  | some (.name n) => advance; return n
  | some (.word w) =>
    if (numSuffix? "userextname" w).isSome then
      advance; return w
    else match numSuffix? "u" w with
      | some ns =>
        advance
        expectPunct ':'
        match ← next with
        | .int s =>
          if !s.isEmpty && s.all Char.isDigit then return s!"u{ns}:{s.toNat!}"
          else malformed s!"bad external name u{ns}:{s}"
        | t => malformed s!"expected u{ns}:N, got '{t.show}'"
      | none => malformed s!"expected an external name, got '{w}'"
  | _ => malformed s!"expected an external name, got {← describe}"

/-- A preamble declaration: symbol global values and callees with external names (a callee's
signature inline or by reference), the others as `Parse.decl`. -/
def rawDecl : P Decl := do
  let t ← peek
  if isEntity "gv" t && (← peekAt 2) == some (.word "symbol") then
    let id ← entity "gv"
    expectPunct '='
    expectWord "symbol"
    let colocated ← optWord "colocated"
    let tls ← optWord "tls"
    let n ← rawName
    let off ← optOffset
    return .global id (if tls then .tlsSymbol n off colocated else .symbol n off colocated)
  else if isEntity "fn" t then
    let id ← entity "fn"
    expectPunct '='
    let colocated ← optWord "colocated"
    if ← optWord "patchable" then unsupported "patchable function reference"
    let n ← rawName
    let sig ← if isEntity "sig" (← peek) then do
        let s ← entity "sig"
        match (← get).sigDecls.lookup s with
        | some sg => pure sg
        | none => malformed s!"fn{id}: sig{s} is not declared before it"
      else signature
    let e : ExtFunc := { name := n, sig, colocated }
    modify fun s => { s with externs := (id, e) :: s.externs }
    return .extern id e
  else decl

/-- `function NAME sig { decls blocks }` (`Parse.function` with `rawName`, `rawDecl`). -/
def rawFunction : P Function := do
  collectAliases
  expectWord "function"
  let name ← rawName
  let sig ← signature
  expectPunct '{'
  let mut slots := #[]
  let mut globals := #[]
  let mut externs := #[]
  let mut sigDecls := #[]
  while !(isEntity "block" (← peek)) && !(← isPunct '}') do
    match ← rawDecl with
    | .slot i s => slots := slots.push (i, s)
    | .global i g => globals := globals.push (i, g)
    | .extern i e => externs := externs.push (i, e)
    | .sigDecl i s => sigDecls := sigDecls.push (i, s)
  let mut blocks := #[]
  while !(← isPunct '}') do
    blocks := blocks.push (← block)
  expectPunct '}'
  if !(← atEnd) then malformed s!"unexpected {← describe} after function body"
  return { name, sig, slots := slots.toList, globals := globals.toList,
           externs := externs.toList, sigDecls := sigDecls.toList, blocks := blocks.toList }

/-- The tokens of one line, without an instruction's source location `@XXXX`. -/
def lexRaw (l : String) : Array Tok :=
  let ts := (lexLine l.toList #[]).1
  let hex (s : String) := !s.isEmpty && s.all fun c => c.isDigit || ('a' ≤ c ∧ c ≤ 'f')
  match (ts[0]? : Option Tok), (ts[1]? : Option Tok) with
  | some (.punct '@'), some (.int s) | some (.punct '@'), some (.word s) =>
    if hex s then ts.extract 2 ts.size else ts
  | _, _ => ts

/-- Parse the function of the lines from its `function` line on (comments ignored). -/
def parseFunction (lines : List String) : Except ParseError Function :=
  let toks := lines.foldl (fun acc l => acc ++ lexRaw l) #[]
  match (rawFunction.run toks |>.run {}) with
  | .ok (f, _) => .ok f
  | .error e => .error e

end Raw

/-! ## The external-name table -/

/-- A module declaration (`; decl …`): `func` or `data`, the linkage, for data its writability
and whether it is thread-local, and its symbol (`none`: not representable without escapes). -/
structure Decl where
  kind : String
  linkage : String
  rw : Bool := false
  tls : Bool := false
  sym : Option String
  deriving Inhabited, Repr, BEq

/-- A function's external-name table and the declarations of the names it uses. -/
structure ExtTable where
  /-- `userextnameJ` ↦ `uNS:IDX`. -/
  refs : List (String × String) := []
  /-- `uNS:IDX` ↦ its declaration. -/
  decls : List (String × Decl) := []
  /-- libcall `NAME` ↦ its symbol. -/
  libcalls : List (String × Option String) := []
  deriving Inhabited, Repr

/-- A Rust `{:?}` string without escapes: its contents. -/
def unquote (s : String) : Option String :=
  match s.toList with
  | '"' :: cs =>
    match cs.reverse with
    | '"' :: inner =>
      let inner := inner.reverse
      if inner.any (fun c => c == '"' || c == '\\') then none else some (String.ofList inner)
    | _ => none
  | _ => none

/-- `uNS:IDX` with decimal numbers, canonical (as `Raw.rawName` writes it). -/
def modId? (s : String) : Option String :=
  match s.splitOn ":" with
  | [a, b] =>
    match numSuffix? "u" a with
    | some ns => if !b.isEmpty && b.all Char.isDigit then some s!"u{ns}:{b.toNat!}" else none
    | none => none
  | _ => none

/-- The words of a table line before its quoted symbol, and the quoted symbol. -/
def splitSym (l : String) : List String × String :=
  let cs := l.toList
  let pre := cs.takeWhile (· != '"')
  ((String.ofList pre).splitOn " " |>.filter (!·.isEmpty), String.ofList (cs.drop pre.length))

/-- Add one table line (without its `; `). -/
def ExtTable.addLine (t : ExtTable) (l : String) : Except String ExtTable := do
  let (ws, q) := splitSym l
  match ws with
  | [r, "=", m] =>
    if q != "" || (numSuffix? "userextname" r).isNone then throw s!"bad table line `{l}`"
    let some m := modId? m | throw s!"bad table line `{l}`"
    if (t.refs.lookup r).isSome then throw s!"{r} is in the table twice"
    pure { t with refs := t.refs ++ [(r, m)] }
  | "decl" :: m :: kind :: rest =>
    let some m := modId? m | throw s!"bad table line `{l}`"
    if (t.decls.lookup m).isSome then throw s!"{m} is declared twice"
    let d ← match kind, rest with
      | "func", [lk] => pure { kind, linkage := lk, sym := unquote q : Decl }
      | "data", [lk, rw, tls] =>
        if (rw == "rw" || rw == "ro") && (tls == "tls" || tls == "notls") then
          pure { kind, linkage := lk, rw := rw == "rw", tls := tls == "tls", sym := unquote q }
        else throw s!"bad table line `{l}`"
      | "unknown", [] => pure { kind, linkage := "", sym := none }
      | _, _ => throw s!"bad table line `{l}`"
    pure { t with decls := t.decls ++ [(m, d)] }
  | ["libcall", n] =>
    if !n.startsWith "%" || n.length < 2 then throw s!"bad table line `{l}`"
    let n := String.ofList (n.toList.drop 1)
    if (t.libcalls.lookup n).isSome then throw s!"libcall {n} is in the table twice"
    pure { t with libcalls := t.libcalls ++ [(n, unquote q)] }
  | _ => throw s!"bad table line `{l}`"

/-- The table after the function (`; clifv-extnames 1` … `; end clifv-extnames`). -/
def parseTable (lines : List String) : Except String ExtTable := do
  let body := (lines.dropWhile (· != "; clifv-extnames 1")).drop 1
  if (lines.dropWhile (· != "; clifv-extnames 1")).isEmpty then
    throw "no external-name table (`; clifv-extnames 1`): not a dump of the patched cg_clif (scripts/build-cg-clif.sh)"
  let mut t : ExtTable := {}
  let mut ended := false
  for l in body do
    if l == "; end clifv-extnames" then
      ended := true
      break
    match (l.toList : List Char) with
    | ';' :: ' ' :: rest => t ← t.addLine (String.ofList rest)
    | _ => throw s!"bad table line `{l}`"
  if !ended then throw "the external-name table has no end"
  pure t

/-! ## A dump -/

/-- A raw dump read: its header lines (`set`/`target`), its `; symbol` comment, the function as
written (external names), the table. -/
structure Dump where
  header : List String
  symbol : Option String
  func : Clif.Function
  table : ExtTable
  deriving Inhabited

/-- **Read a raw dump**: exactly one function, its table. -/
def readDump (src : String) : Except String Dump := do
  let lines := src.splitOn "\n"
  let pre := lines.takeWhile (!isFunctionLine ·)
  let rest := lines.drop pre.length
  if (rest.drop 1).any isFunctionLine then throw "the dump holds more than one function"
  if rest.isEmpty then throw "the dump holds no function"
  let header := pre.filterMap fun l =>
    let t := (l.toList.takeWhile (· != ';') |> String.ofList).trimAscii.toString
    if t.isEmpty then none else some t
  let symbol := pre.findSome? fun l =>
    match (l.toList : List Char) with
    | ';' :: ' ' :: 's' :: 'y' :: 'm' :: 'b' :: 'o' :: 'l' :: ' ' :: s => some (String.ofList s).trimAscii.toString
    | _ => none
  let func ← match Raw.parseFunction rest with
    | .ok f => pure f
    | .error e => throw (toString e)
  let table ← parseTable rest
  pure { header, symbol, func, table }

/-- `userextnameJ` ↦ the module identity it denotes (other names unchanged). -/
def ExtTable.refRen (t : ExtTable) (n : String) : String := (t.refs.lookup n).getD n

/-- **The function in module identities**: `userextnameJ` resolved through the table. -/
def Dump.raw (d : Dump) : Clif.Function := d.func.rename d.table.refRen

/-! ## Names -/

/-- The CLIF name of an object symbol: an anonymous data object `.Ldata<hex>` is `c_Ldata<hex>`
(its object-local name is no CLIF name; `pipeline.rs` `clif_name_of`), every other symbol
itself. -/
def clifName (sym : String) : String :=
  if sym.startsWith ".Ldata" then "c_Ldata" ++ String.ofList (sym.toList.drop 6) else sym

/-- Expressible as a CLIF name (`%name`, `Parse.lexLine`). -/
def validName (n : String) : Bool := !n.isEmpty && n.all Parse.isWordChar

/-- The unit's declarations: module identity or libcall ↦ the CLIF name of its symbol, from
every dump's table; an identity declared with two symbols, or a libcall with two, is an error. -/
def unitTable (ds : List Dump) : Except String (Std.HashMap String String) :=
  ds.foldlM (init := {}) fun m d => do
    let es := d.table.decls.filterMap (fun (k, dl) => dl.sym.map (k, clifName ·)) ++
      d.table.libcalls.filterMap fun (k, s) => s.map (k, clifName ·)
    es.foldlM (init := m) fun m (k, v) =>
      match m[k]? with
      | some w => if w == v then pure m else throw s!"{k}: two symbols in one unit ({w}, {v})"
      | none => pure (m.insert k v)

/-- Rename by the unit's declarations (an undeclared name unchanged). -/
def lookupRen (ρ : Std.HashMap String String) (n : String) : String := ρ.getD n n

/-- The declaration kinds the function's uses require: its own name and callees functions (or
libcalls), its `symbol` global values non-TLS and its `tls` ones TLS data. -/
def kindsOk (d : Dump) : Except String Unit := do
  let r := d.raw
  let kind (n : String) : Option Decl := d.table.decls.lookup n
  match kind r.name with
  | some dl => if dl.kind != "func" then throw s!"{r.name}: the function's own name is no function"
  | none => throw s!"{r.name}: the function's own name is not declared"
  if let (some s, some dl) := (d.symbol, kind r.name) then
    if dl.sym != some s then throw s!"{r.name}: declared as {repr dl.sym}, the dump's `; symbol` is {s}"
  for (_, e) in r.externs do
    match kind e.name with
    | some dl => if dl.kind != "func" then throw s!"{e.name}: a callee that is no function"
    | none => if (d.table.libcalls.lookup e.name).isNone then throw s!"{e.name}: an undeclared callee"
  for (_, g) in r.globals do
    match g with
    | .symbol n _ _ =>
      match kind n with
      | some dl => if dl.kind == "data" && dl.tls then throw s!"{n}: `symbol` of a TLS object"
      | none => throw s!"{n}: an undeclared global value"
    | .tlsSymbol n _ _ =>
      match kind n with
      | some dl => if !(dl.kind == "data" && dl.tls) then throw s!"{n}: `tls` of no TLS object"
      | none => throw s!"{n}: an undeclared global value"
    | _ => pure ()

/-- **Decode a dump** under the unit's declarations `ρ`: the function in module identities with
every name renamed by `ρ`; every name must be declared in `ρ`, of the right kind (`kindsOk`),
and its CLIF name expressible. -/
def decodeFn (ρ : Std.HashMap String String) (d : Dump) : Except String Clif.Function := do
  kindsOk d
  for n in d.raw.names do
    match ρ[n]? with
    | none => throw s!"{n}: no declaration (or its symbol needs escapes)"
    | some s => if !validName s then throw s!"{n}: its symbol {s} is no CLIF name"
  pure (d.raw.rename (lookupRen ρ))

theorem decodeFn_spec {ρ : Std.HashMap String String} {d : Dump} {g : Clif.Function}
    (h : decodeFn ρ d = .ok g) : g = d.raw.rename (lookupRen ρ) := by
  unfold decodeFn at h
  cases hk : kindsOk d with
  | error e => rw [hk] at h; cases h
  | ok u =>
    rw [hk] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · cases h; rfl

end Front

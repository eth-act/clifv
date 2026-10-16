import FV.Front.Perm
import FV.Front.Raw
import FV.Clif.Print
import FV.Clif.Parse
import FV.E2E.SrcScopeDefs
import FV.Link.Layout

/-!
# The frontend bundle and the Lean-built `LinkSpec` (T7b–T7d, docs/contracts/frontend.md)

**What enters** (`Bundle`, read from `cargo fv link-proof`'s `bundle.json` by `readBundle`,
which only reads files): per codegen unit (`Cgu`) the functions of the program part — each
**cg_clif's dump of it, as cg_clif wrote it** (one function in Cranelift's text syntax with its
external-name table and the module's declarations of the names it uses, `FV/Front/Raw.lean`),
with `lean-regalloc`'s output for it — the unit's data objects (`; data:` lines,
`clif-data-export`: every data object of the unit's object), the unit's **local** names (symbols
local to its object: two units' local symbols of one name are different symbols), and the linked
name the object merge gave each renamed symbol (`names`); for the executable, its symbols'
addresses, the Lean code's addresses (the merge's markers), the functions' sizes in the region
object, and the functions the reconstruction skipped.

**What is computed here**, by pure functions with explicit errors (no file is written by Rust
or Python for the compiler's input any more):

* `parseUnit`: each dump read (`readDump`) and **decoded** under the unit's declarations
  (`unitTable`, `decodeFn`: every external name replaced by the CLIF name of the symbol cg_clif
  declared for it; named as the bundle says), the data lines parsed, the unit's **data closure**
  (`reachSet`: the data objects reachable from the functions' names through relocations,
  checked closed: `closedB`); a reachable object whose line does not parse is an error;
* the **linked names** `finOf us i n` (the merge's name, or `n` itself), checked to be a
  **scoping** of the program (`scopingB`: a global name keeps its name, two local symbols get
  distinct names no global name has);
* `link us sc`: the program of the units under a scoping `sc` (every function renamed by
  `Function.rename (sc i)`), `linkData us sc` its data; `rawLink us sc'`: the units' functions
  **as cg_clif wrote them** (in module identities, `Dump.raw`) under a naming `sc'` of those;
* `assemble`: per function the `FnInput` of the renamed function (its printed text, which is
  checked to parse back to it: `FnInput.src = g`), the names the program uses, the outside
  part's addresses, the symbols of the CLIF image (`addrNamesOf` and the program functions whose
  address a reachable data object holds);
* `buildSpec`: the `Link.LinkSpec` of the bundle.

`FV/Front/BundleProof.lean`: the spec's source program is `link us (finOf us)`, its data
`linkData us (finOf us)` (`buildSpec_spec`); every data object reachable from the program is
in it (`data_complete`); any two scopings give alpha-equivalent programs (`link_alpha`); the
decoded units' program under a scoping is cg_clif's program under a naming that identifies two
module identities exactly when cg_clif declared them as one symbol (`rawLink_eq_link`).
-/

namespace Front

open Clif E2E.LinkCheck Link

/-! ## The bundle -/

/-- One function of the program part: its CLIF name (as the unit names it), cg_clif's dump of
it (the file's text, unchanged), `lean-regalloc`'s output for its decoding. -/
structure FnFile where
  name : String
  dump : String
  ra : String
  deriving Inhabited

/-- One codegen unit. -/
structure Cgu where
  /-- The unit's identity (its work directory's name, distinct across units). -/
  tag : String
  funcs : List FnFile
  /-- The unit's data objects: `clif-data-export`'s `; data:` lines. -/
  data : List String
  /-- The unit's local symbols: (CLIF name, symbol name in the unit's object). -/
  locals : List (String × String)
  /-- The linked name of each symbol the object merge renamed (CLIF name → linked name). -/
  names : List (String × String)
  /-- Addresses of the unit's local symbols in the executable (object symbol name → address,
  from the link map). -/
  localAddrs : List (String × Nat) := []
  deriving Inhabited

/-- **The input of the Lean-built `LinkSpec`.** -/
structure Bundle where
  units : List Cgu
  /-- The executable's symbols with their addresses (each defined once; a unit's local data
  object `.LdataN` as `.LdataN@<tag>`). -/
  symbols : List (String × Nat)
  /-- Linked name → address of its Lean code in the executable (the merge's marker). -/
  markers : List (String × Nat)
  /-- Linked name → its size in words in the region object. -/
  sizes : List (String × Nat)
  /-- Functions of the region the reconstruction could not include (name, reason). -/
  skipped : List (String × String) := []
  deriving Inhabited

/-! ## Parsing -/

/-- A parsed unit: its decoded functions with their dumps' header lines and regalloc outputs,
the same functions as cg_clif wrote them (in module identities, `Dump.raw`) and the renaming of
the unit's declarations (`lookupRen` of `unitTable`) that decodes them, its data closure, its
tag, locals and names. -/
structure PCgu where
  tag : String
  funcs : List (Clif.Function × List String × String)
  raw : List Clif.Function := []
  ren : String → String := id
  data : List DataObject
  locals : List (String × String)
  names : List (String × String)
  deriving Inhabited

/-- The name of a `; data: %name …` line (up to the first character that is no name
character). -/
def dataLineName (l : String) : String :=
  let t := (String.ofList (l.toList.dropWhile (fun c => c == ' ' || c == ';'))).trimAscii.toString
  let t := ((t.drop 5).toString.trimAscii.toString.drop 1).toString
  String.ofList (t.toList.takeWhile fun c => c.isAlphanum || c == '_' || c == '.' || c == '$')

/-- The names a set of objects reaches in one more step: `s` with every relocation target of an
object of `ds` named in `s`. -/
def reachStep (ds : List DataObject) (s : Std.HashSet String) : Std.HashSet String :=
  ds.foldl (fun s o => if s.contains o.name then o.refs.foldl (·.insert ·) s else s) s

/-- `fuel` steps of `reachStep` from `s`. -/
def reachIter (ds : List DataObject) : Nat → Std.HashSet String → Std.HashSet String
  | 0, s => s
  | k + 1, s => reachIter ds k (reachStep ds s)

/-- The names reachable from `roots` (one step per object suffices). -/
def reachSet (ds : List DataObject) (roots : List String) : Std.HashSet String :=
  reachIter ds (ds.length + 1) (roots.foldl (·.insert ·) {})

/-- `s` holds the roots and is closed under the relocations of the objects it names. -/
def closedB (ds : List DataObject) (roots : List String) (s : Std.HashSet String) : Bool :=
  roots.all s.contains && ds.all fun o => !s.contains o.name || o.refs.all s.contains

/-- Read one function's dump. -/
def readFile (fn : FnFile) : Except String Dump :=
  match readDump fn.dump with
  | .ok d => .ok d
  | .error e => .error s!"%{fn.name}: {e}"

/-- Decode one function's dump under the unit's declarations `ρ`: named as the bundle says. -/
def decodeFile (ρ : Std.HashMap String String) (fd : FnFile × Dump) :
    Except String (Clif.Function × List String × String) :=
  match decodeFn ρ fd.2 with
  | .error e => .error s!"%{fd.1.name}: {e}"
  | .ok g =>
    if g.name = fd.1.name then .ok (g, fd.2.header, fd.1.ra)
    else .error s!"%{fd.1.name}: its dump holds %{g.name}"

/-- The `; data:` lines with their names, parsed. -/
def dataParsed (ls : List String) : List (String × Except String DataObject) :=
  ls.filterMap fun l => (Clif.dataDirective l).map (dataLineName l, ·)

/-- The data objects that parse. -/
def okData (ps : List (String × Except String DataObject)) : List DataObject :=
  ps.filterMap fun p => match p.2 with | .ok o => some o | .error _ => none

/-- A line that does not parse whose name `s` holds. -/
def badLine (s : Std.HashSet String) (ps : List (String × Except String DataObject)) :
    Option (String × String) :=
  ps.findSome? fun p => match p.2 with
    | .error e => if s.contains p.1 then some (p.1, e) else none
    | .ok _ => none

/-- The names a unit's functions use: the roots of its data closure. -/
def rootsOf (fs : List (Clif.Function × List String × String)) : List String :=
  fs.flatMap (·.1.names)

/-- **Parse a unit**: its dumps read and decoded under its declarations, its data closure (the
objects of its `; data:` lines whose names its functions reach; every such line must parse, and
no object's name may be a declared external name, `lookupRen ρ` fixes them). -/
def parseUnit (u : Cgu) : Except String PCgu :=
  match u.funcs.mapM readFile with
  | .error e => .error e
  | .ok ds =>
  match unitTable ds with
  | .error e => .error s!"unit {u.tag}: {e}"
  | .ok ρ =>
  match (u.funcs.zip ds).mapM (decodeFile ρ) with
  | .error e => .error e
  | .ok fs =>
    let ps := dataParsed u.data
    let ds' := okData ps
    let s := reachSet ds' (rootsOf fs)
    if !closedB ds' (rootsOf fs) s then .error s!"unit {u.tag}: data closure not closed" else
    match badLine s ps with
    | some (n, e) => .error s!"unit {u.tag}: data object %{n}: {e}"
    | none =>
      let data := ds'.filter (s.contains ·.name)
      if (data.flatMap (·.names)).all (fun n => lookupRen ρ n == n) then
        .ok { tag := u.tag, funcs := fs, raw := ds.map Dump.raw, ren := lookupRen ρ, data,
              locals := u.locals, names := u.names }
      else .error s!"unit {u.tag}: a data object is named like a declared external name"

/-! ## Names -/

/-- The names unit `u` uses: those of its functions and of its data closure. -/
def PCgu.idents (u : PCgu) : List String :=
  u.funcs.flatMap (·.1.names) ++ u.data.flatMap (·.names)

/-- The CLIF names of the unit's local symbols. -/
def PCgu.localNames (u : PCgu) : List String := u.locals.map (·.1)

/-- **The linked name of `n` in unit `u`**: the merge's; else, for a local symbol the merge left
local, its object symbol qualified by the unit's tag (`sym@tag`, the name the binary checks look
up as `sym`: `BinCheck.symName`); else `n`. -/
def PCgu.fin (u : PCgu) (n : String) : String :=
  match u.names.lookup n with
  | some f => f
  | none => match u.locals.lookup n with
    | some o => o ++ "@" ++ u.tag
    | none => n

/-- The linked names of the units: unit `i`'s `fin`. -/
def finOf (us : List PCgu) (i : Nat) (n : String) : String :=
  match us[i]? with
  | some u => u.fin n
  | none => n

/-- **A scoping of the units**: per unit (by index) a naming of its names under which two names
of the units are named alike exactly when they are one symbol — the same name, and the same unit
or global in both (a name local to a unit is that unit's own symbol). -/
def ScopingOk (us : List PCgu) (sc : Nat → String → String) : Prop :=
  ∀ i j u v n m, us[i]? = some u → us[j]? = some v → n ∈ u.idents → m ∈ v.idents →
    (sc i n = sc j m ↔ n = m ∧ (i = j ∨ (n ∉ u.localNames ∧ m ∉ v.localNames)))

/-- The local symbols the units use: (unit index, name), without duplicates. -/
def localIds (us : List PCgu) : List (Nat × String) :=
  (us.zipIdx.flatMap fun (u, i) =>
    (u.idents.filter (· ∈ u.localNames)).map (i, ·)).eraseDups

/-- The global names the units use. -/
def globalNames (us : List PCgu) : List String :=
  us.flatMap fun u => u.idents.filter (· ∉ u.localNames)

/-- **`finOf us` is a scoping** (decided; `scopingB_sound`): every global name keeps its name;
the local symbols get distinct names, none a global name. -/
def scopingB (us : List PCgu) : Bool :=
  us.all (fun u => (u.idents.filter (· ∉ u.localNames)).all fun n => u.fin n == n) &&
  nodupB ((localIds us).map fun p => finOf us p.1 p.2) &&
  let g : Std.HashSet String := (globalNames us).foldl (·.insert ·) {}
  (localIds us).all fun p => !g.contains (finOf us p.1 p.2)

/-- **The program of the units under a scoping `sc`**: every function, unit by unit, renamed by
its unit's naming. -/
def link (us : List PCgu) (sc : Nat → String → String) : Clif.Program :=
  { funcs := us.zipIdx.flatMap fun (u, i) => u.funcs.map fun f => f.1.rename (sc i) }

/-- The data of the units under a scoping `sc`: every unit's closure, renamed. -/
def linkData (us : List PCgu) (sc : Nat → String → String) : List DataObject :=
  us.zipIdx.flatMap fun (u, i) => u.data.map (·.rename (sc i))

/-- **cg_clif's program of the units under a naming `sc`** of their functions' module
identities: every function as cg_clif wrote it (`PCgu.raw`: `uNS:IDX`, libcall names), renamed
by its unit's naming. -/
def rawLink (us : List PCgu) (sc : Nat → String → String) : Clif.Program :=
  { funcs := us.zipIdx.flatMap fun (u, i) => u.raw.map fun f => f.rename (sc i) }

/-! ## The `LinkSpec` -/

/-- The names a function's CLIF takes the address of (as `link-check`'s `addrNames`). -/
def addrNamesOf (f : Clif.Function) : List String :=
  f.globals.filterMap (fun g => match g.2 with | .symbol n _ _ => some n | _ => none) ++
  f.blocks.flatMap fun b => b.body.filterMap fun st => match st.inst with
    | .funcAddr _ fn => (f.extern? fn).map (·.name)
    | _ => none

/-- The input of one renamed function: its file's header and the printed function. -/
def fnInputOf (hdr : List String) (g : Clif.Function) (ra : String) : FnInput :=
  { clif := String.join (hdr.map (· ++ "\n")) ++ "\n" ++ g.print, ra }

/-- The input of one renamed function, checked to hold that function (`FnInput.src`). -/
def mkInput (hdr : List String) (g : Clif.Function) (ra : String) : Except String FnInput :=
  let fi := fnInputOf hdr g ra
  if fi.src = g then .ok fi else .error s!"%{g.name}: its printed CLIF does not parse back to it"

/-- `l` sorted, without duplicates. -/
def sortDedup (l : List String) : List String :=
  (l.mergeSort fun a b => decide (a ≤ b)).eraseDups

/-- `l` without the names of `s` and without duplicates, first occurrences kept (hash set:
linear). -/
def dedupGo : List String → Std.HashSet String → List String
  | [], _ => []
  | x :: xs, s => if s.contains x then dedupGo xs s else x :: dedupGo xs (s.insert x)

/-- `l` without duplicates, first occurrences kept. -/
def dedupFirst (l : List String) : List String := dedupGo l {}

/-- **The assembled program part**: the functions' inputs (renamed), their linked names, the
data, the names the program and its data use that are not its functions', the CLIF image's
symbols. -/
structure Assembled where
  units : List PCgu
  funcs : List FnInput
  names : List String
  data : List DataObject
  refs : List String
  symNames : List String

/-- The renamed functions of the units, with their files' headers and regalloc outputs. -/
def renamedOf (us : List PCgu) : List (List String × Clif.Function × String) :=
  us.zipIdx.flatMap fun (u, i) => u.funcs.map fun f => (f.2.1, f.1.rename (finOf us i), f.2.2)

/-- The program functions whose address a data object holds. -/
def dataFnsOf (names : List String) (D : List DataObject) : List String :=
  let nameSet : Std.HashSet String := names.foldl (·.insert ·) {}
  sortDedup ((D.flatMap (·.refs)).filter nameSet.contains)

/-- The assembled program part of parsed units and their functions' inputs. -/
def assembled (us : List PCgu) (fis : List FnInput) : Assembled :=
  let P := link us (finOf us)
  let names := P.funcs.map (·.name)
  let nameSet : Std.HashSet String := names.foldl (·.insert ·) {}
  let D := linkData us (finOf us)
  { units := us, funcs := fis, names, data := D
    refs := sortDedup ((P.funcs.flatMap (·.names) ++ D.flatMap (·.names)).filter
      (!nameSet.contains ·))
    symNames := dedupFirst (P.funcs.flatMap addrNamesOf ++ dataFnsOf names D) }

/-- **Assemble the program part of a bundle.** -/
def assemble (b : Bundle) : Except String Assembled :=
  match b.skipped with
  | (n, why) :: _ =>
    .error s!"link-proof skipped {b.skipped.length} function(s) of the region: {n}: {why}"
  | [] =>
    match b.units.mapM parseUnit with
    | .error e => .error e
    | .ok us =>
      if !scopingB us then .error "the linked names are not a scoping of the units" else
      match (renamedOf us).mapM (fun x => mkInput x.1 x.2.1 x.2.2) with
      | .error e => .error e
      | .ok fis => .ok (assembled us fis)

/-- **The symbol table**: the executable's symbols, then every unit's local symbols as
`sym@tag`. -/
def symTable (b : Bundle) : Std.HashMap String Nat :=
  let l := b.symbols ++ b.units.flatMap fun u => u.localAddrs.map fun (o, a) => (o ++ "@" ++ u.tag, a)
  l.foldl (fun m p => if m.contains p.1 then m else m.insert p.1 p.2) {}

/-- The address of `n`: its entry, else for `sym@tag` the executable's `sym` (a symbol defined
once in the executable). -/
def addrOf (t : Std.HashMap String Nat) (n : String) : Option Nat :=
  match t[n]? with
  | some a => some a
  | none => if n.contains '@' then t[(n.splitOn "@").headD n]? else none

/-- The link-map addresses of an assembled program part in the executable as rust-lld linked
it (`link-check`): its functions at their Lean code, then the names it uses. -/
def linkAddrs (b : Bundle) (A : Assembled) : List (String × Nat) :=
  let t := symTable b
  A.names.filterMap (fun n => (b.markers.lookup n).map (n, ·)) ++
    A.refs.filterMap fun n => (addrOf t n).map (n, ·)

/-- The sizes of the named functions. -/
def sizesFor (sz : List (String × Nat)) (names : List String) : Except String (List Nat) :=
  names.mapM fun n => match sz.lookup n with
    | some w => .ok w
    | none => .error s!"{n}: no size"

/-- **The `LinkSpec` of a bundle**: the assembled program part placed in the region from the
first function's Lean code address; the outside part's addresses those of the symbols the
program uses (a name without one is left out, as before: the linker's checks reject a use of
it). -/
def buildSpec (b : Bundle) : Except String LinkSpec :=
  match assemble b with
  | .error e => .error e
  | .ok A =>
    match sizesFor b.sizes A.names with
    | .error e => .error e
    | .ok sizes =>
      match A.names.head?.bind (fun n => b.markers.lookup n) with
      | none => .error "no function, or the first has no Lean code address"
      | some R =>
        .ok { funcs := A.funcs, names := A.names, sizes,
              outside := A.refs.filterMap fun n => (addrOf (symTable b) n).map (n, ·),
              data := A.data, symNames := A.symNames, R }

end Front

import FV.Link.Ld.Obj

/-! # Lean static linker: symbol resolution, archive members, COMDAT, `--gc-sections`

lld's semantics for a static link (docs/research/lean-linker.md §6):

* objects are loaded in command-line order; an archive's symbols become *lazy*: a member is
  extracted when a non-weak undefined reference to one of its symbols exists or appears later
  (the order of archives does not matter);
* a strong definition beats a weak one, two strong definitions are an error; a `COMDAT` group's
  first copy wins, the later copies' sections are discarded (their symbols are references);
* `--gc-sections`: the sections reachable through relocations from the entry, the `-u` symbols
  and the retained sections (`.init`, `.fini`, the init/fini arrays, notes, `SHF_GNU_RETAIN`,
  every section named `X` when `__start_X`/`__stop_X` is referenced) stay; an `.eh_frame` FDE
  is kept with its function and keeps its LSDA and its CIE's personality.
-/

namespace Link.Ld

/-- A global symbol's resolution state. -/
inductive Def where
  | undef (weak : Bool)
  | lazy (ar mem : Nat)
  | defd (file sym : Nat) (weak : Bool)
  | common (file sym : Nat)
  deriving Inhabited, Repr

/-- A section of the link: file index, section index. -/
abbrev SecId := Nat × Nat

/-- A record of an `.eh_frame` section: offset, size (with the length field), CIE or FDE, and
for an FDE the offset of its CIE in the same section. -/
structure EhPiece where
  off : Nat
  size : Nat
  cie : Bool
  cieOff : Nat
  deriving Inhabited, Repr

/-- The resolver's state. -/
structure St where
  files : Array Obj := #[]
  disc : Array (Std.HashSet Nat) := #[]
  syms : Std.HashMap String Def := {}
  comdats : Std.HashSet String := {}
  archives : Array Archive := #[]
  extracted : Std.HashSet (Nat × Nat) := {}
  queue : Array (Nat × Nat) := #[]
  deriving Inhabited

/-- `SHN_COMMON`, `SHN_ABS`. -/
def shnCommon : Nat := 0xfff2
def shnAbs : Nat := 0xfff1

/-- A symbol defined in a regular section of its file. -/
def Sym.inSec (s : Sym) : Bool := s.shndx != 0 && s.shndx < 0xff00

/-- Adds an object: COMDAT groups, then its global symbols. -/
def St.addObj (st : St) (o : Obj) : Except String St := do
  let fi := st.files.size
  let mut st := st
  let mut disc : Std.HashSet Nat := {}
  for i in [0:o.secs.size] do
    let s := o.secs[i]!
    if s.type == shtGroup then
      let sig := (o.syms[s.info]?.map (·.name)).getD ""
      if rdLE o.data s.off 4 &&& 1 != 0 then
        if st.comdats.contains sig then
          for k in [1:s.size / 4] do
            disc := disc.insert (rdLE o.data (s.off + 4 * k) 4)
        else st := { st with comdats := st.comdats.insert sig }
  for j in [o.firstGlobal:o.syms.size] do
    let sy := o.syms[j]!
    if sy.bind == 0 || sy.name.isEmpty then continue
    let weak := sy.bind == 2
    let cur := st.syms[sy.name]?
    if sy.shndx == 0 || (sy.inSec && disc.contains sy.shndx) then
      match cur with
      | none => st := { st with syms := st.syms.insert sy.name (.undef weak) }
      | some (.undef w) => st := { st with syms := st.syms.insert sy.name (.undef (w && weak)) }
      | some (.lazy a m) =>
        if !weak then
          st := { st with syms := st.syms.insert sy.name (.undef false), queue := st.queue.push (a, m) }
      | _ => pure ()
    else if sy.shndx == shnCommon then
      match cur with
      | some (.defd _ _ false) | some (.common _ _) => pure ()
      | _ => st := { st with syms := st.syms.insert sy.name (.common fi j) }
    else
      match cur with
      | some (.defd f k w) =>
        if w && !weak then st := { st with syms := st.syms.insert sy.name (.defd fi j weak) }
        else if !w && !weak then
          throw s!"duplicate symbol {sy.name}: {st.files[f]!.name} and {o.name} (index {k})"
      | _ => st := { st with syms := st.syms.insert sy.name (.defd fi j weak) }
  return { st with files := st.files.push o, disc := st.disc.push disc }

/-- Extracts the queued archive members. -/
partial def St.drain (st : St) : Except String St := do
  match st.queue.back? with
  | none => return st
  | some (a, m) =>
    let st := { st with queue := st.queue.pop }
    if st.extracted.contains (a, m) then st.drain
    else
      let st := { st with extracted := st.extracted.insert (a, m) }
      let ar := st.archives[a]!
      if !ar.isElf m then st.drain
      else
        let o ← Obj.parse s!"{ar.path}({ar.members[m]!.name})" ar.members[m]!.name (ar.memberBytes m)
        (← st.addObj o).drain

/-- Adds an archive: its symbols become lazy, undefined ones extract their members. -/
def St.addArchive (st : St) (ar : Archive) : Except String St := do
  let ai := st.archives.size
  let mut st := { st with archives := st.archives.push ar }
  for (n, m) in ar.symtab do
    match st.syms[n]? with
    | none | some (.undef true) => st := { st with syms := st.syms.insert n (.lazy ai m) }
    | some (.undef false) => st := { st with queue := st.queue.push (ai, m) }
    | _ => pure ()
  st.drain

/-- An input of the link. -/
inductive Input where
  | obj (path : String) (data : ByteArray)
  | archive (path : String) (data : ByteArray)

/-- **Resolution**: the roots `roots` (entry and `-u` symbols) as undefined references, then the
inputs in order. -/
def resolve (roots : List String) (ins : List Input) : Except String St := do
  let mut st : St := {}
  for r in roots do
    st := { st with syms := st.syms.insert r (.undef false) }
  for i in ins do
    match i with
    | .obj p d => st := ← (← st.addObj (← Obj.parse p (System.FilePath.mk p).fileName.get! d)).drain
    | .archive p d => st := ← st.addArchive (← Archive.parse p d)
  return st

/-! ## Symbol targets -/

/-- What a symbol of file `fi` refers to: a section and offset, an absolute value, a common
symbol, or nothing (undefined; `weak`). -/
inductive Target where
  | sec (s : SecId) (off : Nat) (tls : Bool)
  | abs (v : Nat)
  | common (file sym : Nat)
  | undef (name : String) (weak : Bool)
  deriving Inhabited, Repr

/-- The target of symbol `j` of file `fi`. -/
def St.target (st : St) (fi j : Nat) : Target :=
  let o := st.files[fi]!
  let sy := o.syms[j]!
  let local_ (f : Nat) (s : Sym) : Target :=
    if s.inSec then .sec (f, s.shndx) s.value (s.type == 6)
    else if s.shndx == shnAbs then .abs s.value
    else .undef s.name false
  if sy.bind == 0 || j < o.firstGlobal then local_ fi sy
  else match st.syms[sy.name]? with
    | some (.defd f k _) => local_ f st.files[f]!.syms[k]!
    | some (.common f k) => .common f k
    | some (.undef w) => .undef sy.name w
    | some (.lazy _ _) => .undef sy.name true
    | none => .undef sy.name (sy.bind == 2)

/-! ## `.eh_frame` records -/

/-- The records of an `.eh_frame` section's bytes (terminators dropped). -/
def ehPieces (b : ByteArray) : Except String (Array EhPiece) := do
  let mut o := 0
  let mut out : Array EhPiece := #[]
  let mut fuel := b.size
  while o + 4 ≤ b.size && fuel > 0 do
    fuel := fuel - 1
    let len := rdLE b o 4
    if len == 0 then o := o + 4; continue
    if len == 0xffffffff then throw "64-bit .eh_frame records are not supported"
    let id := rdLE b (o + 4) 4
    out := out.push { off := o, size := len + 4, cie := id == 0, cieOff := if id == 0 then 0 else o + 4 - id }
    o := o + len + 4
  return out

/-! ## `--gc-sections` -/

/-- A section kept whatever references it. -/
def retained (s : Sec) : Bool :=
  s.has shfAlloc &&
  (s.type == shtInitArray || s.type == shtFiniArray || s.type == shtPreinitArray ||
   s.type == shtNote || s.has shfRetain ||
   s.name == ".init" || s.name == ".fini" || s.name.startsWith ".init_array" ||
   s.name.startsWith ".fini_array" || s.name.startsWith ".preinit_array" ||
   s.name.startsWith ".ctors" || s.name.startsWith ".dtors")

/-- The section `s` is linked: allocated, not discarded, not an `.eh_frame` (synthesized),
not a group. -/
def St.linked (st : St) (s : SecId) : Bool :=
  match st.files[s.1]?.bind (·.secs[s.2]?) with
  | some sec => sec.has shfAlloc && sec.type != shtGroup && sec.name != ".eh_frame" &&
      !(st.disc[s.1]!.contains s.2)
  | none => false

/-- A C identifier (sections reachable through `__start_`/`__stop_`). -/
def isCIdent (n : String) : Bool :=
  !n.isEmpty && n.all fun c => c.isAlphanum || c == '_'

/-- The live sections and, per file, the `.eh_frame` section index and its records. -/
structure GcOut where
  live : Array (Array Bool)
  eh : Array (Option (Nat × Array EhPiece × Array Rela))
  deriving Inhabited

/-- The `.eh_frame` FDEs of each section: `(file, section)` → `(eh section, record)`s. -/
def fdeIndex (st : St) (eh : Array (Option (Nat × Array EhPiece × Array Rela))) :
    Std.HashMap SecId (Array (Nat × Nat)) := Id.run do
  let mut m : Std.HashMap SecId (Array (Nat × Nat)) := {}
  for fi in [0:st.files.size] do
    if let some (_, ps, rs) := eh[fi]! then
      let mut byOff : Std.HashMap Nat Nat := {}
      for k in [0:rs.size] do
        byOff := byOff.insert rs[k]!.off k
      for pi in [0:ps.size] do
        let p := ps[pi]!
        if !p.cie then
          if let some k := byOff[p.off + 8]? then
            if let .sec t _ _ := st.target fi rs[k]!.sym then
              m := m.insert t ((m.getD t #[]).push (fi, pi))
  return m

/-- **`--gc-sections`** (`gc = false`: every linked section is live). Roots: `roots` (symbol
names) and the retained sections. -/
def St.gc (st : St) (roots : List String) (gc : Bool) : Except String GcOut := do
  let mut eh : Array (Option (Nat × Array EhPiece × Array Rela)) := #[]
  for o in st.files do
    match (List.range o.secs.size).find? (fun i => o.secs[i]!.name == ".eh_frame" &&
        o.secs[i]!.has shfAlloc) with
    | some i => eh := eh.push (some (i, ← ehPieces (o.secBytes i), o.relas i))
    | none => eh := eh.push none
  let mut live : Array (Array Bool) :=
    st.files.mapIdx fun fi o => Array.ofFn (n := o.secs.size) fun i => !gc && st.linked (fi, i.1)
  if !gc then return { live, eh }
  -- sections by name (`__start_`/`__stop_`)
  let mut byName : Std.HashMap String (Array SecId) := {}
  for fi in [0:st.files.size] do
    let o := st.files[fi]!
    for i in [0:o.secs.size] do
      if isCIdent o.secs[i]!.name && st.linked (fi, i) then
        byName := byName.insert o.secs[i]!.name ((byName.getD o.secs[i]!.name #[]).push (fi, i))
  let fdes := fdeIndex st eh
  let mut work : Array SecId := #[]
  for r in roots do
    if let some (.defd f k _) := st.syms[r]? then
      let s := st.files[f]!.syms[k]!
      if s.inSec then work := work.push (f, s.shndx)
  for fi in [0:st.files.size] do
    let o := st.files[fi]!
    for i in [0:o.secs.size] do
      if retained o.secs[i]! && st.linked (fi, i) then work := work.push (fi, i)
  let mut fuel := 100000000
  while fuel > 0 do
    fuel := fuel - 1
    match work.back? with
    | none => break
    | some s =>
      work := work.pop
      if !st.linked s || live[s.1]![s.2]! then continue
      live := live.modify s.1 (·.set! s.2 true)
      -- the section's relocations
      let mark (fi : Nat) (r : Rela) (work : Array SecId) : Array SecId :=
        let sy := st.files[fi]!.syms[r.sym]!
        let w := match st.target fi r.sym with
          | .sec t _ _ => work.push t
          | _ => work
        if sy.name.startsWith "__start_" || sy.name.startsWith "__stop_" then
          let n := if sy.name.startsWith "__start_" then (sy.name.drop 8).toString
            else (sy.name.drop 7).toString
          w ++ byName.getD n #[]
        else w
      for r in st.files[s.1]!.relas s.2 do
        work := mark s.1 r work
      -- its FDEs: their LSDA and their CIE's personality
      for (fi, pi) in fdes.getD s #[] do
        if let some (_, ps, rs) := eh[fi]! then
          let p := ps[pi]!
          for r in rs do
            if (r.off > p.off + 8 && r.off < p.off + p.size) ||
                (r.off ≥ p.cieOff && r.off < p.cieOff + (ps.find? (·.off == p.cieOff)).elim 0 (·.size)) then
              work := mark fi r work
  return { live, eh }

end Link.Ld

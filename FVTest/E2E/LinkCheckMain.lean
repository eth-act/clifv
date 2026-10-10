import FV.E2E.DeadCleanupBinCheck
import FV.E2E.DeadCleanupStackBound
import FV.E2E.BinCheck
import FV.E2E.CodeMap
import FV.E2E.StackBound

/-!
# `lake exe link-check <dir> [--lean FILE --module NAME] [--entries a,b,…] [--prune]`

Evaluates the checker `E2E.LinkCheck.okB` (every premise of `LinkSys.Ok` about the program and
its layout, `FV/E2E/LinkCheck.lean`) on the input of a crate-level instance written by
`cargo fv link-proof` (docs/USAGE.md, "Proving a crate"): `<dir>/link.json` lists the functions
(`fns/<i>.clif`, the CLIF `lean-backend` compiled, with the link's symbol names, and
`fns/<i>.ra.json`, `lean-regalloc`'s output for it) and the link-map addresses (`addrs`).

It completes the input (the CLIF image's symbols `syms`: every `symbol` global value and
`func_addr` target of the functions, and the functions of the program in the data objects they
reach (vtables, `data_syms` of `link.json`), at its link-map address; `D`: the largest frame of a
function; `raStar = 8`) and prints the failing checks per function and premise (`diagR`, the
diagnostic version of `okB`), then a count per premise, then the stack bound
(`E2E.StackBound.budMap`, `FV/E2E/StackBound.lean`: the largest stack an activation of a function
of the program uses with its callees, and the bound of each entry, a function no other function
of the program calls; the functions whose calls reach a cycle of the call graph are `recursive`
and have none), the binary checks (`FV/E2E/BinCheck.lean`) and the code map (`codeMapB`,
`FV/E2E/CodeMap.lean`). With `--prune` it drops
the failing functions (they become externs of the base environment) until the rest passes. With `--lean` it
writes, when the checks pass, the Lean file that proves `LinkSys.Ok` of the crate by
`native_decide` on `okB` and states `backend_correct_program` for the entries (default: every
function), and decides the stack bound (`stack_ok` when the call graph has no cycle, else
`stack_entries`: the entries whose calls never reach one) and states
`backend_correct_program_stack` for those entries (`StackStmt`: at every fuel, with the fixed
bound): the proof does not trust this executable.

Exit status: 0 iff the (pruned) input passes.
-/

open E2E E2E.LinkCheck E2E.StackBound Lean Backend

/-- The names a function's CLIF takes the address of: its `symbol` global values and its
`func_addr` targets. -/
def addrNames (f : Clif.Function) : List String :=
  f.globals.filterMap (fun g => match g.2 with | .symbol n _ _ => some n | _ => none) ++
  f.blocks.flatMap fun b => b.body.filterMap fun st => match st.inst with
    | .funcAddr _ fn => (f.extern? fn).map (·.name)
    | _ => none

/-- A Lean string literal. -/
def leanStr (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\"
    else if c == '\n' then "\\n" else if c == '\t' then "\\t"
    else if c.toNat < 0x20 then s!"\\x{(Nat.toDigits 16 c.toNat).asString}" else c.toString) ++ "\""

/-- Why a check fails, in more detail (for the call-site and indirect-call checks). -/
def detail (I : LinkInput) (P : Clif.Program) (g : Clif.Function) (a : Art) (check : String) :
    List String :=
  let S := fun n => I.syms.lookup n
  let may := indToB S g
  if check == "callRegs/blrRegs" then
    a.vcp.blocks.toList.flatMap fun vb => vb.insts.toList.filterMap fun i => match i with
      | .call info | .tryCall info _ =>
        if siteOk P g may a.vcp info then none else some (match info.dest with
          | .sym n => s!"bl {n}: arguments/results not in the callee's ABI registers"
          | .reg r =>
            let nu := (decU info.uses).length
            let got := match r with
              | .vreg t .int => gotOf a.vcp t
              | _ => none
            let hs := P.funcs.filter fun h => may h && (got.all (· == h.name)) &&
              (regLocs h.sig).length == nu &&
              !(decide ((decU info.uses).map (·.2) = regLocs h.sig) &&
                decide (((decD info.defs).map (·.1)).take (sigRets h.sig).length =
                  (List.range (min (sigRets h.sig).length (decD info.defs).length)).map Reg.x))
            s!"blr with {nu} register argument(s), {info.defs.length} def(s): not the ABI registers of the program function(s) it may enter (BlrTo) with {nu} register parameter(s): {hs.map (·.name)}")
      | _ => none
  else if check == "indScope/indSig" then
    (P.funcs.filter (fun h => mayB S g h.name && indSigB g h &&
      (!indRetsB g h ||
      (match sigParamBytes h.sig with | .ok b => decide (b.length > 8) | .error _ => true)))).map
      (fun h => s!"indSig: program function {h.name} one of its indirect calls may enter (matching signature, or declared with matching parameter types) has a stack-passed parameter, or an sret pointer where an indirect call of its parameter types has none (or the reverse)")
  else []

/-! ## The binary checks (`FV/E2E/BinCheck.lean`) on the executable -/

open E2E.Elf E2E.BinCheck

/-- `0x…` -/
def hexN (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- The bytes of the image range `[a, a + n)` as file chunks (inside `p_filesz`). -/
def fileChunks (file : ByteArray) (phs : List Phdr) (a n : Nat) : Excerpt :=
  phs.filterMap fun p =>
    if p.type != 1 then none else
    let lo := max a p.vaddr
    let hi := min (a + n) (p.vaddr + p.filesz)
    if lo < hi then
      let off := p.offset + (lo - p.vaddr)
      some (off, file.extract off (off + (hi - lo)))
    else none

/-- The word at `x` of the loaded image of `r`. -/
def wordIn (r : Rd) (phs : List Phdr) (x : BitVec 64) : Option (BitVec 32) :=
  readN (memIn r phs) 4 x

/-- The image ranges `ArtOk`'s check of `a` reads: its code, and the GOT slots of its
`adrp`/`ldr` pairs. -/
def artRanges (r : Rd) (phs : List Phdr) (a : Art) : List (Nat × Nat) :=
  (a.base.toNat, 4 * a.fb.words.size) :: a.fb.relocs.filterMap fun rl =>
    if rl.type == .adrGotPage then
      match wordIn r phs (wAt a rl.offset), wordIn r phs (wAt a (rl.offset + 4)) with
      | some x0, some x1 =>
        if x0 != nopW && x1.toNat / 2 ^ 22 == 0x3e5 then
          some (gotOf (wAt a rl.offset).toNat x0 x1, 8)
        else none
      | _, _ => none
    else none

/-- What differs between the compiled function `a` and the executable (`artB`'s failures). -/
def artDiag (I : LinkInput) (r : Rd) (phs : List Phdr) (a : Art) : List String := Id.run do
  let m := memIn r phs
  let mut out : List String := []
  let w (x : Option (BitVec 32)) : String := match x with | some v => v.toHex | none => "(none)"
  for k in [0:a.fb.words.size] do
    if !(List.range 4).all (fun i => roB phs (wAt a (4 * k + i))) then
      out := out ++ [s!"word {k} at {hexN (wAt a (4 * k)).toNat}: not in a read-only segment"]
    if !a.fb.relocs.any (·.offset == 4 * k) then
      let x := wordIn r phs (wAt a (4 * k))
      if x != some (a.fb.words[k]?.getD 0) then
        out := out ++ [s!"word {k} at {hexN (wAt a (4 * k)).toNat}: executable {w x}, compiled {(a.fb.words[k]?.getD 0).toHex}"]
  for rl in a.fb.relocs do
    if !relocB I m phs a rl then
      let o := rl.offset
      let tgt := match rl.type with
        | .call26 => hexN (I.baseOf rl.sym)
        | .tlsDescAdrPage21 | .tlsDescLd64Lo12 | .tlsDescAddLo12 | .tlsDescCall =>
          s!"tp+{(tpOff phs (I.addrOf rl.sym)).map hexN}"
        | _ => hexN (I.symAddr rl.sym rl.addend).toNat
      out := out ++ [s!"{rl.type.elfName} {rl.sym}{if rl.addend == 0 then "" else s!"+{rl.addend}"} at word {o / 4} ({hexN (wAt a o).toNat}): executable {w (wordIn r phs (wAt a o))} {w (wordIn r phs (wAt a (o + 4)))}, compiled {(a.fb.words[o / 4]?.getD 0).toHex} {(a.fb.words[o / 4 + 1]?.getD 0).toHex}, target {tgt}"]
  return out

/-- What differs between a data object and the executable (`objB`'s failures). -/
def objDiag (I : LinkInput) (r : Rd) (phs : List Phdr) (o : Clif.DataObject) : List String := Id.run do
  if !(I.addrs.lookup o.name).isSome then return ["no link-map address"]
  let bs := objBytes I o
  let mut out : List String := []
  for i in [0:bs.length] do
    let x := objAt I o + BitVec.ofNat 64 i
    let e := loadIn r phs x.toNat
    if e != some (bs[i]?.getD 0) then
      out := out ++ [s!"byte {i} at {hexN x.toNat}: executable {e.map (·.toHex)}, CLIF {(bs[i]?.getD 0).toHex}"]
    if !(o.writable || roB phs x || relroB phs x) then
      out := out ++ [s!"byte {i} at {hexN x.toNat}: read-only object in a writable segment"]
  return out

/-- The defined symbols of a file: `(name, value) → (section, entry)`. -/
def symIndex (file : ByteArray) : Std.HashMap (String × Nat) (Nat × Nat) := Id.run do
  let r := fileRd file
  let some e := ehdr r | return {}
  let mut out : Std.HashMap (String × Nat) (Nat × Nat) := {}
  for s in [0:e.shnum] do
    let some sh := shdr r e s | continue
    if sh.type != 2 || sh.entsize != 24 then continue
    for i in [0:sh.size / 24] do
      let some (o, v) := symEntry r s i | continue
      let mut j := o
      while j < file.size && file[j]! != 0 do j := j + 1
      match String.fromUTF8? (file.extract o j) with
      | some n => if !out.contains (n, v) then out := out.insert (n, v) (s, i)
      | none => pure ()
  return out

/-- The excerpt `symsB` reads for the certificate `cert`: the symbol entries and their names. -/
def symChunks (file : ByteArray) (cert : List (String × Nat × Nat)) : Excerpt := Id.run do
  let r := fileRd file
  let some e := ehdr r | return []
  let mut out : Excerpt := []
  for (n, s, i) in cert do
    let some sh := shdr r e s | continue
    let off := sh.offset + 24 * i
    out := out ++ [(off, file.extract off (off + 24))]
    if let some (o, _) := symEntry r s i then
      let len := (symName n).utf8ByteSize + 1
      out := out ++ [(o, file.extract o (o + len))]
  return out

/-- A list literal of Lean terms, as `[…] ++ […] ++ …` of at most 200 items each (a single long
literal exceeds the elaborator's recursion depth). -/
def listLean (items : List String) : String :=
  if items.isEmpty then "[]" else
  " ++\n  ".intercalate ((List.range ((items.length + 199) / 200)).map fun k =>
    "[" ++ ",\n  ".intercalate ((items.drop (200 * k)).take 200) ++ "]")

/-- An excerpt as Lean source. -/
def exLean (ex : Excerpt) : String :=
  listLean (ex.map fun c => s!"({c.1}, Elf.ofHex \"{toHex c.2}\")")

/-- The ranges of an excerpt of `file`, sorted, with ranges at most 64 bytes apart merged. -/
def coalesce (file : ByteArray) (ex : Excerpt) : Excerpt := Id.run do
  let rs := (ex.map fun c => (c.1, c.1 + c.2.size)).mergeSort (fun a b => a.1 ≤ b.1)
  let mut out : List (Nat × Nat) := []
  for (lo, hi) in rs do
    match out with
    | (lo', hi') :: rest =>
      if lo ≤ hi' + 64 then out := (lo', max hi hi') :: rest else out := (lo, hi) :: out
    | [] => out := [(lo, hi)]
  return out.reverse.map fun (lo, hi) => (lo, file.extract lo hi)

/-- The excerpts and certificate of a crate's binary checks (`leanFiles`). -/
structure BinGen where
  hdr : Excerpt
  slices : List Excerpt
  data : Excerpt
  syms : Excerpt
  cert : List (String × Nat × Nat)
  dataLines : List String

def usage : String :=
  "usage: link-check <dir> [--lean FILE.lean --module NAME] [--entries a,b,…] [--prune] [--profile] [--dead-cleanup|--no-dead-cleanup]"

structure Opts where
  dir : String
  lean : Option String := none
  module : String := "Crate"
  entries : Option (List String) := none
  prune : Bool := false
  profile : Bool := false
  deadCleanup : Bool := true

def parseOpts : List String → Option Opts → Option Opts
  | [], o => o
  | "--lean" :: f :: rest, some o => parseOpts rest (some { o with lean := some f })
  | "--module" :: m :: rest, some o => parseOpts rest (some { o with module := m })
  | "--entries" :: e :: rest, some o =>
    parseOpts rest (some { o with entries := some ((e.splitOn ",").filter (· ≠ "")) })
  | "--prune" :: rest, some o => parseOpts rest (some { o with prune := true })
  | "--dead-cleanup" :: rest, some o => parseOpts rest (some { o with deadCleanup := true })
  | "--no-dead-cleanup" :: rest, some o => parseOpts rest (some { o with deadCleanup := false })
  | "--profile" :: rest, some o => parseOpts rest (some { o with profile := true })
  | d :: rest, none => parseOpts rest (some { dir := d })
  | _, _ => none

/-- The number of functions per slice of a crate's proof (`fnsB`, one `native_decide` each). -/
def sliceSize : Nat := 32

/-- `a ++ (b ++ (… ++ z))` -/
def nestApp : List String → String
  | [] => "[]"
  | [x] => x
  | x :: xs => s!"{x} ++ ({nestApp xs})"

/-- **The generated Lean files** `(path, text)` for `out` (`…/Crates/NAME.lean`, module
`Crates.NAME`): with at most `sliceSize` functions one file; otherwise the input
(`Crates.NAME.Input`, with the headers' excerpt, the data objects and the symbol
certificate), one module per slice of `sliceSize` functions deciding their checks and their
binary check on the slice's excerpt (`Crates.NAME.SliceK`; Lake builds them in parallel,
`native_decide` theorems of one file run one after the other), and `out`, which combines them. -/
def leanFiles (I : LinkInput) (names : List String) (entries : List String) (out module exe : String)
    (noTls : Bool) (stack : Option Nat) (stackEntries : List String) (bg : BinGen) :
    List (String × String) := Id.run do
  let ns := s!"Crates.{module}"
  let n := I.funcs.length
  let idx := List.range n
  let nSl := (n + sliceSize - 1) / sliceSize
  let sl := List.range (max nSl 1)
  let split := nSl > 1
  let slFns (k : Nat) := ", ".intercalate ((idx.drop (k * sliceSize)).take sliceSize |>.map (s!"fn{·}"))
  let pairs (l : List (String × Nat)) := ",\n    ".intercalate (l.map fun p => s!"({leanStr p.1}, {p.2})")
  let header (imports : String) := s!"{imports}

namespace {ns}

open E2E E2E.LinkCheck E2E.BinCheck

"
  -- the input: the functions, the slices, `input`
  let mut inp := ""
  for (fi, i) in I.funcs.zipIdx do
    inp := inp ++ s!"/-- `{names[i]!}` -/\ndef fn{i} : FnInput where\n  clif := {leanStr fi.clif}\n  ra := {leanStr fi.ra}\n\n"
  for k in sl do
    inp := inp ++ s!"/-- Slice {k} of the functions. -/\ndef slice{k} : List FnInput := [{slFns k}]\n\n"
  let funcs := " ++ ".intercalate (sl.map (s!"slice{·}"))
  let aliases := if I.aliases.isEmpty then "" else
    "\n  aliases := [" ++ ", ".intercalate (I.aliases.map fun p => s!"({leanStr p.1}, {leanStr p.2})") ++ "]"
  inp := inp ++ s!"/-- The crate's input. -/
def input : LinkInput where
  funcs := {funcs}
  addrs := [
    {pairs I.addrs}]
  syms := [
    {pairs I.syms}]
  raStar := {I.raStar}
  D := {I.D}{aliases}

/-- The data objects the program reaches (`cargo fv link-proof`'s `; data:` lines). -/
def dataObjs : List Clif.DataObject := parseData ({listLean (bg.dataLines.map leanStr)})

/-- The executable's ELF header, program headers and section headers. -/
def exHdr : Elf.Excerpt := {exLean bg.hdr}

/-- The executable's bytes of the data objects. -/
def exData : Elf.Excerpt := {exLean bg.data}

/-- The executable's symbol entries and names of the link map's names. -/
def exSyms : Elf.Excerpt := {exLean bg.syms}

/-- Where the link map's names are in the executable's symbol table (section, entry). -/
def symCert : List (String × Nat × Nat) :=
  {listLean (bg.cert.map fun c => s!"({leanStr c.1}, {c.2.1}, {c.2.2})")}

"
  let sliceThm (k : Nat) := s!"/-- The checks of the functions of slice {k} (`staticChks`, the validators, and `linkChks`). -/
theorem slice{k}_ok : fnsB input slice{k} = true := by native_decide

/-- The executable's bytes of the code of slice {k} (and of the GOT slots it loads). -/
def ex{k} : Elf.Excerpt := {exLean (bg.slices.getD k [])}

/-- The binary check of the functions of slice {k} (`ArtOk`: their code in the executable). -/
theorem slice{k}_bin : codeB input (exHdr ++ ex{k}) slice{k} = true := by native_decide

"
  let closedText := "/-- No function has a `tls_value`. -/
theorem noTls : (progOf input.results).funcs.all (fun g => !Backend.hasTls g) = true := by
  native_decide

/-- **The base premises are satisfiable**: the closed base environment (`closedBase`: nothing
outside the program has a semantics) satisfies them, so `link_ok` and the `correct_*` theorems
are not vacuous in their base premises. -/
theorem base_closed (F : BitVec 64 → Prop) : BaseOk (LinkSys.ofInput input closedBase F) :=
  baseOk_closed fun g hg => by simpa using List.all_eq_true.1 noTls g hg

"
  let doc := s!"/-! # Crate-level instance of `backend_correct_program` (generated)

Generated by `cargo fv link-proof` / `lake exe link-check` (docs/contracts/e2e.md,
\"Crate-level instance\") for the executable

  {exe}

The program `P` is the {n} functions of `input` (the CLIF `lean-backend` compiled, with the
link's symbol names, and `lean-regalloc`'s output), loaded at their addresses in the
executable's link map (`addrs`). `okB_input` decides every premise of `LinkSys.Ok` about the
program and its layout by `native_decide` (`okB_of`: the program's checks, `globalB_input`, and
the per-function checks by slices of {sliceSize} functions, `sliceK_ok`{if split then ", each in its own module" else ""}), run as compiled
code (the package `crate-proofs` loads the shared library of `FV.E2E.StackBound` and
`FV.E2E.BinCheck`); `link_ok` is
`LinkSys.Ok` of the crate's linked system for every base environment satisfying the base
premises (`BaseOk`: the contracts of std, other crates' code and the runtime, which stay
premises), and the `correct_*` theorems are `backend_correct_program` for the entries{if stack.isSome then ";
`stack_ok` decides the stack bound (`FV/E2E/StackBound.lean`: the call graph has no cycle), and
the `correct_stack_*` theorems are `backend_correct_program_stack` for the entries (at every
fuel)" else if !stackEntries.isEmpty then ";
`stack_entriesK` decide that the calls of the entries in `stackEntriesK` never reach a cycle of
the call graph (`FV/E2E/StackBound.lean`), and the `correct_stack_*` theorems are
`backend_correct_program_stack` for them (at every fuel)" else ""}.

**The executable** (docs/contracts/e2e.md, \"Binary level (M9)\"): `bin_ok` states `BinOk input
dataObjs file` for every file whose bytes agree with the excerpts `exAll` of this executable
(its headers, the code of the functions and the GOT slots they load, the {bg.dataLines.length} data objects the
program reaches, its symbol entries): a static AArch64 executable whose loaded image holds every
function's compiled words with its relocations resolved (`ArtOk`), the data objects with theirs
(`DataOk`), and whose symbol table is the link map (`SymsOk`); by `native_decide` on the
excerpts (`hdr_bin`, `sliceK_bin`, `data_bin`, `syms_bin`).
-/

"
  let mut main := s!"/-- The checks of the program (`globalChks`). -/
theorem globalB_input : globalB input = true := by native_decide

/-- Every premise of `LinkSys.Ok` about the program and its layout. -/
theorem okB_input : okB input = true :=
  okB_of globalB_input {if sl.length == 1 then "slice0_ok" else s!"(by
    show fnsB input ({funcs}) = true
    simp only [fnsB_append, {", ".intercalate (sl.map (s!"slice{·}_ok"))}, Bool.and_self])"}

/-- **`LinkSys.Ok` of the crate's linked system**, for every base environment satisfying the base
premises and every `F` containing the code. -/
theorem link_ok (B : BaseEnv) (F : BitVec 64 → Prop) (hB : BaseOk (LinkSys.ofInput input B F))
    (hF : ∀ a, (LinkSys.ofInput input B F).Img a → F a) : (LinkSys.ofInput input B F).Ok :=
  okB_sound okB_input hB hF

{if noTls then closedText else ""}/-- The entries are functions of the program. -/
theorem entries_present :
    [{", ".intercalate (entries.map leanStr)}].all
      (fun n => ((progOf input.results).func? n).isSome) = true := by native_decide

"
  let parts := ["exHdr"] ++ sl.map (s!"ex{·}") ++ ["exData", "exSyms"]
  let hs := ["hH"] ++ sl.map (s!"h{·}") ++ ["hD", "hS"]
  let codeOf (k : Nat) := s!"(codeB_sound slice{k}_bin (Elf.agrees_append.2 ⟨hH, h{k}⟩))"
  let code := (sl.drop 1).foldl (fun acc k => s!"(artsOk_append {acc}\n      {codeOf k})") (codeOf 0)
  main := main ++ s!"/-- The executable's headers: a static AArch64 executable. -/
theorem hdr_bin : hdrB exHdr = true := by native_decide

/-- The data objects in the executable (`DataOk`). -/
theorem data_bin : dataB input dataObjs (exHdr ++ exData) = true := by native_decide

/-- The link map is the executable's symbol table (`SymsOk`). -/
theorem syms_bin : symsB input (exHdr ++ exSyms) symCert = true := by native_decide

/-- The excerpts of the executable the binary checks read. -/
def exAll : Elf.Excerpt := {nestApp parts}

/-- **The executable is the crate's linked program**: every file whose bytes agree with the
excerpts is a static AArch64 executable holding the program's code with its relocations
resolved, the data objects, and the link map as its symbol table (`BinOk`). -/
theorem bin_ok (file : ByteArray) (h : Elf.Agrees file exAll) : BinOk input dataObjs file := by
  simp only [exAll, Elf.agrees_append] at h
  obtain ⟨{", ".intercalate hs}⟩ := h
  exact binOk_of (hdrB_sound hdr_bin hH)
    {code}
    (dataB_sound data_bin (Elf.agrees_append.2 ⟨hH, hD⟩))
    (symsB_sound syms_bin (Elf.agrees_append.2 ⟨hH, hS⟩))

"
  for (e, i) in entries.zipIdx do
    main := main ++ s!"/-- **`backend_correct_program` for `{e}`** -/\ntheorem correct_{i} : CrateStmt input {leanStr e} :=\n  crate_correct okB_input _\n\n"
  if let some S := stack then
    main := main ++ s!"/-- **The stack bound** (`FV/E2E/StackBound.lean`): the program's call graph has no cycle, and an
activation of any of its functions uses at most {S} bytes of stack with its callees
(`StackBound.stackFn_le`). -/
theorem stack_ok : StackBound.stackB input = some {S} := by native_decide

"
    for (e, i) in entries.zipIdx do
      main := main ++ s!"/-- **`backend_correct_program_stack` for `{e}`**: at every fuel, with the stack bound. -/\ntheorem correct_stack_{i} : StackBound.StackStmt input {leanStr e} :=\n  StackBound.crate_correct_stack okB_input stack_ok _\n\n"
  else if !stackEntries.isEmpty then
    -- in chunks of `sliceSize` (the generated proofs index them by `decide`)
    let nCh := (stackEntries.length + sliceSize - 1) / sliceSize
    for c in List.range nCh do
      let ch := (stackEntries.drop (c * sliceSize)).take sliceSize
      main := main ++ s!"/-- Entries whose calls never reach a cycle of the call graph (chunk {c}). -/
def stackEntries{c} : List String := [{", ".intercalate (ch.map leanStr)}]

/-- **The stack bound of the entries in `stackEntries{c}`** (`FV/E2E/StackBound.lean`): their calls
never reach a cycle of the call graph (the program has recursive functions). -/
theorem stack_entries{c} : StackBound.goodAll input stackEntries{c} = true := by native_decide

"
    for (e, i) in entries.zipIdx do
      if let some k := stackEntries.idxOf? e then
        main := main ++ s!"/-- **`backend_correct_program_stack` for `{e}`**: at every fuel, with its stack bound. -/\ntheorem correct_stack_{i} : StackBound.StackStmt input {leanStr e} :=\n  StackBound.crate_correct_stackN okB_input\n    (StackBound.goodN_of_idx stack_entries{k / sliceSize} {k % sliceSize} (by decide))\n\n"
  let footer := s!"end {ns}\n"
  if !split then
    return [(out, header ("import FV.E2E.BinCheck\nimport FV.E2E.StackBound\n\n" ++ doc.trimAsciiEnd.toString) ++ inp ++ sliceThm 0 ++ main ++ footer)]
  let dir := out.dropRight ".lean".length
  let mut files := [(s!"{dir}/Input.lean",
    header s!"import FV.E2E.BinCheck\n\n/-! The input of `{ns}` (generated; see there). -/" ++ inp ++ footer)]
  for k in sl do
    files := files ++ [(s!"{dir}/Slice{k}.lean",
      header s!"import {ns}.Input\n\n/-! Slice {k} of `{ns}`'s checks (generated; see there). -/" ++ sliceThm k ++ footer)]
  let imports := "\n".intercalate (sl.map (s!"import {ns}.Slice{·}")) ++ "\nimport FV.E2E.StackBound"
  return files ++ [(out, header (imports ++ "\n\n" ++ doc.trimAsciiEnd.toString) ++ main ++ footer)]

def leanFilesCleanup (I : LinkInput) (names : List String) (entries : List String) (out module exe : String)
    (noTls : Bool) (stack : Option Nat) (stackEntries : List String) (bg : BinGen) :
    List (String × String) := Id.run do
  let ns := s!"Crates.{module}"
  let n := I.funcs.length
  let idx := List.range n
  let nSl := (n + sliceSize - 1) / sliceSize
  let sl := List.range (max nSl 1)
  let split := nSl > 1
  let slFns (k : Nat) := ", ".intercalate ((idx.drop (k * sliceSize)).take sliceSize |>.map (s!"fn{·}"))
  let pairs (l : List (String × Nat)) := ",\n    ".intercalate (l.map fun p => s!"({leanStr p.1}, {p.2})")
  let header (imports : String) := s!"{imports}

namespace {ns}

open E2E E2E.LinkCheck E2E.BinCheck

"
  -- the input: the functions, the slices, `input`
  let mut inp := ""
  for (fi, i) in I.funcs.zipIdx do
    inp := inp ++ s!"/-- `{names[i]!}` -/\ndef fn{i} : FnInput where\n  clif := {leanStr fi.clif}\n  ra := {leanStr fi.ra}\n\n"
  for k in sl do
    inp := inp ++ s!"/-- Slice {k} of the functions. -/\ndef slice{k} : List FnInput := [{slFns k}]\n\n"
  let funcs := " ++ ".intercalate (sl.map (s!"slice{·}"))
  let aliases := if I.aliases.isEmpty then "" else
    "\n  aliases := [" ++ ", ".intercalate (I.aliases.map fun p => s!"({leanStr p.1}, {leanStr p.2})") ++ "]"
  inp := inp ++ s!"/-- The crate's input. -/
def input : LinkInput where
  funcs := {funcs}
  addrs := [
    {pairs I.addrs}]
  syms := [
    {pairs I.syms}]
  raStar := {I.raStar}
  D := {I.D}
  fallback := {I.fallback}{aliases}

/-- The data objects the program reaches (`cargo fv link-proof`'s `; data:` lines). -/
def dataObjs : List Clif.DataObject := parseData ({listLean (bg.dataLines.map leanStr)})

/-- The executable's ELF header, program headers and section headers. -/
def exHdr : Elf.Excerpt := {exLean bg.hdr}

/-- The executable's bytes of the data objects. -/
def exData : Elf.Excerpt := {exLean bg.data}

/-- The executable's symbol entries and names of the link map's names. -/
def exSyms : Elf.Excerpt := {exLean bg.syms}

/-- Where the link map's names are in the executable's symbol table (section, entry). -/
def symCert : List (String × Nat × Nat) :=
  {listLean (bg.cert.map fun c => s!"({leanStr c.1}, {c.2.1}, {c.2.2})")}

"
  let sliceThm (k : Nat) := s!"/-- The checks of the functions of slice {k} (`staticChks`, the validators, and `linkChks`). -/
theorem slice{k}_ok : fnsBCleanup input slice{k} = true := by native_decide

/-- The executable's bytes of the code of slice {k} (and of the GOT slots it loads). -/
def ex{k} : Elf.Excerpt := {exLean (bg.slices.getD k [])}

/-- The binary check of the functions of slice {k} (`ArtOk`: their code in the executable). -/
theorem slice{k}_bin : E2E.DeadCleanupBinCheck.codeB input (exHdr ++ ex{k}) slice{k} = true := by native_decide

"
  let closedText := "/-- No function has a `tls_value`. -/
theorem noTls : (progOf input.resultsCleanup).funcs.all (fun g => !Backend.hasTls g) = true := by
  native_decide

/-- **The base premises are satisfiable**: the closed base environment (`closedBase`: nothing
outside the program has a semantics) satisfies them, so `link_ok` and the `correct_*` theorems
are not vacuous in their base premises. -/
theorem base_closed (F : BitVec 64 → Prop) : BaseOk (LinkSys.ofInputCleanup input closedBase F) :=
  baseOk_closedCleanup fun g hg => by simpa using List.all_eq_true.1 noTls g hg

"
  let doc := s!"/-! # Crate-level instance of `backend_correct_program` (generated)

Generated by `cargo fv link-proof` / `lake exe link-check` (docs/contracts/e2e.md,
\"Crate-level instance\") for the executable

  {exe}

The program `P` is the {n} functions of `input` (the CLIF `lean-backend` compiled, with the
link's symbol names, and `lean-regalloc`'s output), loaded at their addresses in the
executable's link map (`addrs`). `okB_input` decides every premise of `LinkSys.Ok` about the
program and its layout by `native_decide` (`okBCleanup_of`: the program's checks, `globalB_input`, and
the per-function checks by slices of {sliceSize} functions, `sliceK_ok`{if split then ", each in its own module" else ""}), run as compiled
code (the package `crate-proofs` loads the shared library of `FV.E2E.DeadCleanupStackBound` and
`FV.E2E.DeadCleanupBinCheck`); `link_ok` is
`LinkSys.Ok` of the crate's linked system for every base environment satisfying the base
premises (`BaseOk`: the contracts of std, other crates' code and the runtime, which stay
premises), and the `correct_*` theorems are `backend_correct_program` for the entries{if stack.isSome then ";
`stack_ok` decides the stack bound (`FV/E2E/DeadCleanupStackBound.lean`: the call graph has no cycle), and
the `correct_stack_*` theorems are `backend_correct_program_stack` for the entries (at every
fuel)" else if !stackEntries.isEmpty then ";
`stack_entriesK` decide that the calls of the entries in `stackEntriesK` never reach a cycle of
the call graph (`FV/E2E/DeadCleanupStackBound.lean`), and the `correct_stack_*` theorems are
`backend_correct_program_stack` for them (at every fuel)" else ""}.

**The executable** (docs/contracts/e2e.md, \"Binary level (M9)\"): `bin_ok` states `E2E.DeadCleanupBinCheck.BinOk input
dataObjs file` for every file whose bytes agree with the excerpts `exAll` of this executable
(its headers, the code of the functions and the GOT slots they load, the {bg.dataLines.length} data objects the
program reaches, its symbol entries): a static AArch64 executable whose loaded image holds every
function's compiled words with its relocations resolved (`ArtOk`), the data objects with theirs
(`DataOk`), and whose symbol table is the link map (`SymsOk`); by `native_decide` on the
excerpts (`hdr_bin`, `sliceK_bin`, `data_bin`, `syms_bin`).
-/

"
  let mut main := s!"/-- The checks of the program (`globalChks`). -/
theorem globalB_input : globalBCleanup input = true := by native_decide

/-- Every premise of `LinkSys.Ok` about the program and its layout. -/
theorem okB_input : okBCleanup input = true :=
  okBCleanup_of globalB_input {if sl.length == 1 then "slice0_ok" else s!"(by
    show fnsBCleanup input ({funcs}) = true
    simp only [fnsBCleanup_append, {", ".intercalate (sl.map (s!"slice{·}_ok"))}, Bool.and_self])"}

/-- **`LinkSys.Ok` of the crate's linked system**, for every base environment satisfying the base
premises and every `F` containing the code. -/
theorem link_ok (B : BaseEnv) (F : BitVec 64 → Prop) (hB : BaseOk (LinkSys.ofInputCleanup input B F))
    (hF : ∀ a, (LinkSys.ofInputCleanup input B F).Img a → F a) : (LinkSys.ofInputCleanup input B F).Ok :=
  okBCleanup_sound okB_input hB hF

{if noTls then closedText else ""}/-- The entries are functions of the program. -/
theorem entries_present :
    [{", ".intercalate (entries.map leanStr)}].all
      (fun n => ((progOf input.resultsCleanup).func? n).isSome) = true := by native_decide

"
  let parts := ["exHdr"] ++ sl.map (s!"ex{·}") ++ ["exData", "exSyms"]
  let hs := ["hH"] ++ sl.map (s!"h{·}") ++ ["hD", "hS"]
  let codeOf (k : Nat) := s!"(E2E.DeadCleanupBinCheck.codeB_sound slice{k}_bin (Elf.agrees_append.2 ⟨hH, h{k}⟩))"
  let code := (sl.drop 1).foldl (fun acc k => s!"(E2E.DeadCleanupBinCheck.artsOk_append {acc}\n      {codeOf k})") (codeOf 0)
  main := main ++ s!"/-- The executable's headers: a static AArch64 executable. -/
theorem hdr_bin : hdrB exHdr = true := by native_decide

/-- The data objects in the executable (`DataOk`). -/
theorem data_bin : dataB input dataObjs (exHdr ++ exData) = true := by native_decide

/-- The link map is the executable's symbol table (`SymsOk`). -/
theorem syms_bin : symsB input (exHdr ++ exSyms) symCert = true := by native_decide

/-- The excerpts of the executable the binary checks read. -/
def exAll : Elf.Excerpt := {nestApp parts}

/-- **The executable is the crate's linked program**: every file whose bytes agree with the
excerpts is a static AArch64 executable holding the program's code with its relocations
resolved, the data objects, and the link map as its symbol table (`E2E.DeadCleanupBinCheck.BinOk`). -/
theorem bin_ok (file : ByteArray) (h : Elf.Agrees file exAll) : E2E.DeadCleanupBinCheck.BinOk input dataObjs file := by
  simp only [exAll, Elf.agrees_append] at h
  obtain ⟨{", ".intercalate hs}⟩ := h
  exact E2E.DeadCleanupBinCheck.binOk_of (hdrB_sound hdr_bin hH)
    {code}
    (dataB_sound data_bin (Elf.agrees_append.2 ⟨hH, hD⟩))
    (symsB_sound syms_bin (Elf.agrees_append.2 ⟨hH, hS⟩))

"
  for (e, i) in entries.zipIdx do
    main := main ++ s!"/-- **`backend_correct_program` for `{e}`** -/\ntheorem correct_{i} : CrateStmtCleanup input {leanStr e} :=\n  crate_correct_cleanup okB_input _\n\n"
  if let some S := stack then
    main := main ++ s!"/-- **The stack bound** (`FV/E2E/DeadCleanupStackBound.lean`): the program's call graph has no cycle, and an
activation of any of its functions uses at most {S} bytes of stack with its callees
(`DeadCleanupStackBound.stackFn_le`). -/
theorem stack_ok : DeadCleanupStackBound.stackB input = some {S} := by native_decide

"
    for (e, i) in entries.zipIdx do
      main := main ++ s!"/-- **`backend_correct_program_stack` for `{e}`**: at every fuel, with the stack bound. -/\ntheorem correct_stack_{i} : DeadCleanupStackBound.StackStmt input {leanStr e} :=\n  DeadCleanupStackBound.crate_correct_stack okB_input stack_ok _\n\n"
  else if !stackEntries.isEmpty then
    -- in chunks of `sliceSize` (the generated proofs index them by `decide`)
    let nCh := (stackEntries.length + sliceSize - 1) / sliceSize
    for c in List.range nCh do
      let ch := (stackEntries.drop (c * sliceSize)).take sliceSize
      main := main ++ s!"/-- Entries whose calls never reach a cycle of the call graph (chunk {c}). -/
def stackEntries{c} : List String := [{", ".intercalate (ch.map leanStr)}]

/-- **The stack bound of the entries in `stackEntries{c}`** (`FV/E2E/DeadCleanupStackBound.lean`): their calls
never reach a cycle of the call graph (the program has recursive functions). -/
theorem stack_entries{c} : DeadCleanupStackBound.goodAll input stackEntries{c} = true := by native_decide

"
    for (e, i) in entries.zipIdx do
      if let some k := stackEntries.idxOf? e then
        main := main ++ s!"/-- **`backend_correct_program_stack` for `{e}`**: at every fuel, with its stack bound. -/\ntheorem correct_stack_{i} : DeadCleanupStackBound.StackStmt input {leanStr e} :=\n  DeadCleanupStackBound.crate_correct_stackN okB_input\n    (DeadCleanupStackBound.goodN_of_idx stack_entries{k / sliceSize} {k % sliceSize} (by decide))\n\n"
  let footer := s!"end {ns}\n"
  if !split then
    return [(out, header ("import FV.E2E.DeadCleanupBinCheck\nimport FV.E2E.DeadCleanupStackBound\n\n" ++ doc.trimAsciiEnd.toString) ++ inp ++ sliceThm 0 ++ main ++ footer)]
  let dir := out.dropRight ".lean".length
  let mut files := [(s!"{dir}/Input.lean",
    header s!"import FV.E2E.DeadCleanupBinCheck\n\n/-! The input of `{ns}` (generated; see there). -/" ++ inp ++ footer)]
  for k in sl do
    files := files ++ [(s!"{dir}/Slice{k}.lean",
      header s!"import {ns}.Input\n\n/-! Slice {k} of `{ns}`'s checks (generated; see there). -/" ++ sliceThm k ++ footer)]
  let imports := "\n".intercalate (sl.map (s!"import {ns}.Slice{·}")) ++ "\nimport FV.E2E.DeadCleanupStackBound"
  return files ++ [(out, header (imports ++ "\n\n" ++ doc.trimAsciiEnd.toString) ++ main ++ footer)]

def main (args : List String) : IO UInt32 := do
  let some o := parseOpts args none | do IO.eprintln usage; return 2
  let dir : System.FilePath := o.dir
  let j ← match Json.parse (← IO.FS.readFile (dir / "link.json")) with
    | .ok j => pure j
    | .error e => do IO.eprintln s!"link-check: link.json: {e}"; return 2
  let exe := (j.getObjValAs? String "exe").toOption.getD "?"
  IO.println s!"link-check: {exe}"
  let fjs := ((j.getObjVal? "functions").bind (·.getArr?)).toOption.getD #[]
  let mut fis : Array FnInput := #[]
  for fj in fjs do
    let clif := (fj.getObjValAs? String "clif").toOption.getD ""
    let ra := (fj.getObjValAs? String "ra").toOption.getD ""
    fis := fis.push { clif := ← IO.FS.readFile (dir / clif), ra := ← IO.FS.readFile (dir / ra) }
  -- the executable and the data objects the functions reach (`; data:` lines, renamed to the
  -- linked symbols)
  let file ← IO.FS.readBinFile exe
  let dataLines : List String := (((j.getObjVal? "data").bind (·.getArr?)).toOption.getD #[]).toList.filterMap
    (·.getStr?.toOption)
  let ajs := ((j.getObjVal? "addrs").bind (·.getArr?)).toOption.getD #[]
  let addrs : List (String × Nat) := ajs.toList.filterMap fun a => do
    let arr ← a.getArr?.toOption
    let n ← (arr[0]?.bind (·.getStr?.toOption))
    let v ← (arr[1]?.bind (·.getNat?.toOption))
    pure (n, v)
  -- functions whose address is in a data object the program reaches (vtable methods)
  let dataSyms : List String := (((j.getObjVal? "data_syms").bind (·.getArr?)).toOption.getD #[]).toList.filterMap
    (·.getStr?.toOption)
  let I0 : LinkInput := { funcs := fis.toList, addrs, syms := [], raStar := 8, D := 0 }
  if o.profile then
    -- the slowest functions: the pipeline, the lowering validator, the allocation checker
    let mut tot : Array (Nat × String × Nat × Nat × Nat) := #[]
    for fi in fis do
      let t0 ← IO.monoMsNow
      let f := fi.func
      let r := (if o.deadCleanup then pipeCleanup else pipe) f fi.k 0 (raJ fi.ra fi.j)
      let ok := r.toBool
      let t1 ← IO.monoMsNow
      let a := getOk r
      let lc := Backend.Proof.Driver.lowerCheck f a.vc
      let t2 ← IO.monoMsNow
      let ca := (checkAlloc a.vcp a.rf).toBool
      let t3 ← IO.monoMsNow
      if !(ok && lc && ca) then IO.println s!"  profile: {f.name} fails the pipeline or a validator"
      tot := tot.push (t3 - t0, f.name, t1 - t0, t2 - t1, t3 - t2)
    for (t, n, a, b, c) in (tot.qsort (fun x y => x.1 > y.1)).toList.take 10 do
      IO.println s!"  profile: {t} ms {n} (pipeline {a}, lowerCheck {b}, checkAlloc {c})"
    IO.println s!"  profile: {(tot.map (·.1)).foldl (· + ·) 0} ms in total"
  let t0 ← IO.monoMsNow
  let R0 := if o.deadCleanup then I0.resultsCleanup else I0.results
  -- the CLIF image's symbols and the call-level stack
  -- the checks that do not depend on the rest of the program, once (`staticChks`: the
  -- validators); then `diagR` with them (`chks = staticChks ++ linkChks`)
  let D0 := (R0.map fun e => frameDrop (getOk e.2).af).foldl max 0
  let stat := R0.map fun e => (e.1.name, (if o.deadCleanup then staticChksWith Backend.DeadCleanup.prune else staticChks) { I0 with D := D0 } e.1 e.2)
  let nStat := (stat.filter fun e => !(bad e.2).isEmpty).length
  IO.println s!"  static checks (the validators): {nStat} function(s) fail"
  IO.println s!"  static checks done in {(← IO.monoMsNow) - t0} ms"
  let mut keep := R0
  let mut dropped : List (String × List String) := []
  let mut d : List (String × List String) := []
  let mut I := I0
  repeat
    let names := ((keep.flatMap fun e => addrNames e.1) ++
      dataSyms.filter (fun n => keep.any (·.1.name == n))).eraseDups
    let syms := names.filterMap fun n => (I0.addrs.lookup n).map (n, ·)
    let D := (keep.map fun e => frameDrop (getOk e.2).af).foldl max 0
    I := { I0 with syms, D }
    let P := progOf keep
    let T := tabOf keep
    let gl := bad (globalChks I P T)
    let fs := keep.filterMap fun e =>
      match bad ((stat.lookup e.1.name).getD [] ++ linkChks I P T e.1 e.2) with
      | [] => none
      | b => some (e.1.name, b ++ (match e.2 with | .error m => [m] | .ok _ => []))
    d := (if gl.isEmpty then [] else [("(program)", gl)]) ++ fs
    let bad := d.filter (·.1 != "(program)")
    if !o.prune || bad.isEmpty then break
    dropped := dropped ++ bad
    -- and their callers in the program, so that what is left is closed under calls (no function
    -- of the crate becomes an extern of the base environment)
    let mut gone := bad.map (·.1)
    repeat
      let callers := keep.filter fun e => !gone.contains e.1.name &&
        e.1.externs.any fun x => gone.contains x.2.name
      if callers.isEmpty then break
      for e in callers do
        dropped := dropped ++ [(e.1.name, ["(calls a dropped function)"])]
      gone := gone ++ callers.map (·.1.name)
    keep := keep.filter fun e => !gone.contains e.1.name
  let ms := (← IO.monoMsNow) - t0
  -- report
  IO.println s!"  {R0.length} functions, {I0.addrs.length} link-map addresses, {I.syms.length} CLIF image symbols, D = {I.D}; checked in {ms} ms"
  let failing := if o.prune then dropped ++ d else d
  let P0 := progOf R0
  for (n, bs) in failing do
    IO.println s!"  FAIL {n}:"
    for b in bs do
      IO.println s!"      {b}"
      if let some e := R0.find? (·.1.name == n) then
        for l in detail I P0 e.1 (getOk e.2) b do IO.println s!"        {l}"
  let mut counts : Std.HashMap String Nat := {}
  for (_, bs) in failing do
    for b in bs.eraseDups do counts := counts.insert b (counts.getD b 0 + 1)
  if !counts.isEmpty then
    IO.println "  failing premises (functions):"
    for (b, c) in counts.toList.mergeSort (fun a b => a.2 ≥ b.2) do
      IO.println s!"    {c}  {b}"
  if o.prune then
    IO.println s!"  --prune: {keep.length} of {R0.length} functions pass ({dropped.length} dropped)"
  let ok := d.isEmpty
  IO.println (if ok then "  okB: true" else "  okB: false")
  -- the (pruned) program
  let keepNames := keep.map (·.1.name)
  let funcs := (I0.funcs.zip (R0.map (·.1.name))).filter (keepNames.contains ·.2)
  let kAliases := I.aliases.filter fun p => keepNames.contains p.1
  let kAddrs := I.addrs.filter fun p => !(I0.aliases.any (·.1 == p.1)) || kAliases.any (·.1 == p.1)
  let I' : LinkInput := { I with funcs := funcs.map (·.1), aliases := kAliases, addrs := kAddrs }
  -- the binary checks (`FV/E2E/BinCheck.lean`) on the executable: its code, data objects and
  -- symbols against the program
  let tb ← IO.monoMsNow
  let r := fileRd file
  let phs := (phdrs r).getD []
  let hdrOk := match ehdr r with
    | some e => staticB e phs
    | none => false
  let arts := keep.map fun e => (e.1.name, getOk e.2)
  let mut codeBad := 0
  let mut words := 0
  for (n, a) in arts do
    words := words + a.fb.words.size
    if !artB I' r phs a then
      codeBad := codeBad + 1
      IO.println s!"  BIN code {n}:"
      for m in (artDiag I' r phs a).take 8 do IO.println s!"      {m}"
  -- the forms the linker left the relocated words in
  let mut nBl := 0
  let mut nNopAdr := 0
  let mut nAdrpAdd := 0
  let mut nGot := 0
  let mut nTls := 0
  for (_, a) in arts do
    for rl in a.fb.relocs do
      match rl.type with
      | .call26 => nBl := nBl + 1
      | .adrGotPage | .adrPrelPgHi21 =>
        match wordIn r phs (wAt a rl.offset), wordIn r phs (wAt a (rl.offset + 4)) with
        | some x0, some x1 =>
          if x0 == nopW then nNopAdr := nNopAdr + 1
          else if x1.toNat / 2 ^ 22 == 0x3e5 then nGot := nGot + 1
          else nAdrpAdd := nAdrpAdd + 1
        | _, _ => pure ()
      | .tlsDescAdrPage21 => nTls := nTls + 1
      | _ => pure ()
  IO.println s!"  relocations: {nBl} bl, address pairs {nNopAdr} nop+adr, {nAdrpAdd} adrp+add, {nGot} adrp+ldr (GOT), {nTls} TLSDESC sequences"
  -- the data objects the kept functions reach
  let allData := parseData dataLines
  let mut reach : List String := (keep.flatMap fun e => addrNames e.1).eraseDups
  let mut todo := reach
  repeat
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if let some o := allData.find? (·.name == n) then
        for it in o.items do
          if let .addr m _ := it then
            if !reach.contains m then
              reach := reach ++ [m]
              todo := todo ++ [m]
  let D := allData.filter (reach.contains ·.name)
  let mut dataBad := 0
  for o in D do
    if !objB I' r phs o then
      dataBad := dataBad + 1
      IO.println s!"  BIN data {o.name}:"
      for m in (objDiag I' r phs o).take 8 do IO.println s!"      {m}"
  -- the symbol table against the link map
  let idx := symIndex file
  let cert : List (String × Nat × Nat) := I'.addrs.filterMap fun p =>
    (idx.get? (symName p.1, p.2)).map (p.1, ·)
  let ex : Excerpt := [(0, file)]
  let symsBad := I'.addrs.filter fun p => !(I'.aliases.lookup p.1).isSome && !(cert.lookup p.1).isSome
  for p in symsBad do
    IO.println s!"  BIN symbol {p.1}: no defined symbol {symName p.1} = {hexN p.2} in the executable's symbol table"
  let symsOk := symsB I' ex cert
  let binOk := hdrOk && codeBad == 0 && dataBad == 0 && symsOk
  IO.println s!"  binary checks done in {(← IO.monoMsNow) - tb} ms"
  IO.println (if binOk then
      s!"  binary: ok ({arts.length} functions, {words} words, {D.length} data objects, {I'.addrs.length - I'.aliases.length} symbols)"
    else s!"  binary: FAIL code={codeBad} data={dataBad} syms={symsBad.length} hdr={if hdrOk then 0 else 1}")
  -- the code map of the executable machine (`codeMapB`, `FV/E2E/CodeMap.lean`: a premise of the
  -- theorem about the executable's own words, not of `okB`)
  IO.println (if codeMapB I' (tabOf keep) then "  code map: ok" else "  code map: FAIL (codeMapB)")
  -- the stack bound (`budMap`) of the (pruned) program: a function has a budget iff no call
  -- cycle is reachable from it (`StackBound.budC_isSome_iff`)
  let Pk := progOf keep
  let Sk := fun n => I.syms.lookup n
  let stackM := budMap I keep
  let stackOf (g : Clif.Function) : Option Nat :=
    (stackM.get? g.name).map (frameDrop (artOf keep g).af + ·)
  let bad := Pk.funcs.filter fun g => (stackOf g).isNone
  let s := Pk.funcs.foldl (fun x g => max x ((stackOf g).getD 0)) 0
  if bad.isEmpty then
    IO.println s!"  stack: {s} bytes at most (no call cycle)"
  else
    IO.println s!"  stack: recursive: the calls of {bad.length} function(s) reach a call cycle (their stack stays a premise): {(bad.map (·.name)).take 10}{if bad.length > 10 then " …" else ""}; the other {Pk.funcs.length - bad.length}: {s} bytes at most"
  let es := (Pk.funcs.filter fun h => !Pk.funcs.any fun g => edgeB Sk g h).map fun g =>
    (g.name, stackOf g)
  let es := es.mergeSort fun x y => x.2.getD (2 ^ 64) ≥ y.2.getD (2 ^ 64)
  IO.println s!"  stack: {es.length} entries (no caller in the program):"
  for (n, v) in es.take 10 do
    IO.println s!"      {match v with | some v => toString v | none => "recursive"}  {n}"
  if es.length > 10 then IO.println s!"      … {es.length - 10} more"
  -- the Lean file
  if let some out := o.lean then
    if !ok || !binOk then
      IO.eprintln "link-check: the checks fail; no Lean file written"
      return 1
    let entries := o.entries.getD keepNames
    let missing := entries.filter (!keepNames.contains ·)
    if !missing.isEmpty then
      IO.eprintln s!"link-check: entries not in the program: {missing}"
      return 1
    let noTls := keep.all fun e => !Backend.hasTls e.1
    -- the excerpts the binary checks read: the headers; per slice, the functions' code and GOT
    -- slots; the data objects; the symbol entries and names
    let some e := ehdr r | return 1
    let hdr : Excerpt := [(0, file.extract 0 64), (e.phoff, file.extract e.phoff (e.phoff + 56 * e.phnum)),
      (e.shoff, file.extract e.shoff (e.shoff + 64 * e.shnum))]
    let nSl := max ((funcs.length + sliceSize - 1) / sliceSize) 1
    let slices : List Excerpt := (List.range nSl).map fun k =>
      coalesce file (((funcs.drop (k * sliceSize)).take sliceSize).flatMap fun p =>
        let a := (arts.lookup p.2).getD default
        (artRanges r phs a).flatMap fun rg => fileChunks file phs rg.1 rg.2)
    let dataEx : Excerpt := coalesce file (D.flatMap fun o =>
      fileChunks file phs (objAt I' o).toNat (objBytes I' o).length)
    let dLines := dataLines.filter fun l => D.any fun o => parseData [l] == [o]
    let bg : BinGen := ⟨hdr, slices, dataEx, coalesce file (symChunks file cert), cert, dLines⟩
    -- the modules of an earlier split of this crate's proof (`leanFiles`)
    let dir : System.FilePath := out.dropRight ".lean".length
    if ← dir.isDir then
      for e in ← dir.readDir do
        if e.fileName == "Input.lean" || (e.fileName.startsWith "Slice" && e.fileName.endsWith ".lean") then
          IO.FS.removeFile e.path
    let stackGood := entries.filter fun e => match Pk.func? e with
      | some f => (stackOf f).isSome
      | none => false
    let stackAll := Pk.funcs.all fun g => (stackOf g).isSome
    let stackS := if stackAll then some (Pk.funcs.foldl (fun x g => max x ((stackOf g).getD 0)) 0)
      else none
    for (p, t) in (if o.deadCleanup then leanFilesCleanup else leanFiles) I' (funcs.map (·.2)) entries out o.module exe noTls stackS stackGood bg do
      if let some pd := (p : System.FilePath).parent then IO.FS.createDirAll pd
      IO.FS.writeFile p t
      IO.println s!"  wrote {p}"
    IO.println s!"  {funcs.length} functions, {entries.length} entries"
  return (if ok && binOk then 0 else 1)

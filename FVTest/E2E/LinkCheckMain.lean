import FV.E2E.LinkCheck

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
diagnostic version of `okB`), then a count per premise. With `--prune` it drops the failing
functions (they become externs of the base environment) until the rest passes. With `--lean` it
writes, when the checks pass, the Lean file that proves `LinkSys.Ok` of the crate by
`native_decide` on `okB` and states `backend_correct_program` for the entries (default: every
function): the proof does not trust this executable.

Exit status: 0 iff the (pruned) input passes.
-/

open E2E E2E.LinkCheck Lean Backend

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
  else if check == "indScope/indNoSym/indSig" then
    (if (indSigs g).all (fun s => !s.params.any (·.purpose == .sret)) then []
      else ["indSig: an indirect call passes an sret pointer"]) ++
    (P.funcs.filter (fun h => mayB S g h.name &&
      (indSigs g).any (fun s => decide (LinkSys.IndSigMatch s h)) &&
      (h.sig.params.any (·.purpose == .sret) ||
      (match sigParamBytes h.sig with | .ok b => decide (b.length > 8) | .error _ => true)))).map
      (fun h => s!"indSig: program function {h.name} it may call with the parameter types of one of its indirect calls has an sret or stack-passed parameter") ++
    (if S g.name == none then [] else ["indNoSym: the function's own address is taken"])
  else []

/-- The compiled words of `a` against the executable's bytes `b` at its address: equal outside
relocated fields; a `bl` (`call26`) reaches its symbol's link-map address. -/
def imageDiff (I : LinkInput) (a : Art) (b : ByteArray) : List String := Id.run do
  let ws := a.fb.words
  let mut out : List String := []
  if b.size != 4 * ws.size then
    out := out ++ [s!"{b.size} bytes in the executable, {4 * ws.size} compiled"]
  for k in [0:min ws.size (b.size / 4)] do
    let x : BitVec 32 := BitVec.ofNat 32 (b[4*k]!.toNat + 256 * b[4*k+1]!.toNat +
      65536 * b[4*k+2]!.toNat + 16777216 * b[4*k+3]!.toNat)
    match a.fb.relocs.find? (·.offset == 4 * k) with
    | none =>
      if x != ws[k]! then out := out ++ [s!"word {k}: executable {x.toHex}, compiled {ws[k]!.toHex}"]
    | some r =>
      if r.type == .call26 then
        let imm : Nat := x.toNat % (2 ^ 26 : Nat)
        let off : Int := if imm < 2 ^ 25 then (imm : Int) else (imm : Int) - (2 ^ 26 : Int)
        let tgt : Int := (a.base.toNat : Int) + 4 * (k : Int) + 4 * off
        match I.addrs.lookup ((I.aliases.lookup r.sym).getD r.sym) with
        | some t => if tgt != (t : Int) then out := out ++ [s!"word {k}: bl {r.sym} reaches {tgt}, its address is {t}"]
        | none => pure ()
  return out

def usage : String :=
  "usage: link-check <dir> [--lean FILE.lean --module NAME] [--entries a,b,…] [--prune] [--profile]"

structure Opts where
  dir : String
  lean : Option String := none
  module : String := "Crate"
  entries : Option (List String) := none
  prune : Bool := false
  profile : Bool := false

def parseOpts : List String → Option Opts → Option Opts
  | [], o => o
  | "--lean" :: f :: rest, some o => parseOpts rest (some { o with lean := some f })
  | "--module" :: m :: rest, some o => parseOpts rest (some { o with module := m })
  | "--entries" :: e :: rest, some o =>
    parseOpts rest (some { o with entries := some ((e.splitOn ",").filter (· ≠ "")) })
  | "--prune" :: rest, some o => parseOpts rest (some { o with prune := true })
  | "--profile" :: rest, some o => parseOpts rest (some { o with profile := true })
  | d :: rest, none => parseOpts rest (some { dir := d })
  | _, _ => none

/-- The number of functions per slice of a crate's proof (`fnsB`, one `native_decide` each). -/
def sliceSize : Nat := 32

/-- **The generated Lean files** `(path, text)` for `out` (`…/Crates/NAME.lean`, module
`Crates.NAME`): with at most `sliceSize` functions one file; otherwise the input
(`Crates.NAME.Input`), one module per slice of `sliceSize` functions deciding their checks
(`Crates.NAME.SliceK`; Lake builds them in parallel, `native_decide` theorems of one file run one
after the other), and `out`, which combines them. -/
def leanFiles (I : LinkInput) (names : List String) (entries : List String) (out module exe : String)
    (noTls : Bool) : List (String × String) := Id.run do
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

open E2E E2E.LinkCheck

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

"
  let sliceThm (k : Nat) := s!"/-- The checks of the functions of slice {k} (`staticChks`, the validators, and `linkChks`). -/
theorem slice{k}_ok : fnsB input slice{k} = true := by native_decide

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
code (the package `crate-proofs` loads the shared library of `FV.E2E.LinkCheck`); `link_ok` is
`LinkSys.Ok` of the crate's linked system for every base environment satisfying the base
premises (`BaseOk`: the contracts of std, other crates' code and the runtime, which stay
premises), and the `correct_*` theorems are `backend_correct_program` for the entries.
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
  for (e, i) in entries.zipIdx do
    main := main ++ s!"/-- **`backend_correct_program` for `{e}`** -/\ntheorem correct_{i} : CrateStmt input {leanStr e} :=\n  crate_correct okB_input _\n\n"
  let footer := s!"end {ns}\n"
  if !split then
    return [(out, header ("import FV.E2E.LinkCheck\n\n" ++ doc.trimAsciiEnd.toString) ++ inp ++ sliceThm 0 ++ main ++ footer)]
  let dir := out.dropRight ".lean".length
  let mut files := [(s!"{dir}/Input.lean",
    header s!"import FV.E2E.LinkCheck\n\n/-! The input of `{ns}` (generated; see there). -/" ++ inp ++ footer)]
  for k in sl do
    files := files ++ [(s!"{dir}/Slice{k}.lean",
      header s!"import {ns}.Input\n\n/-! Slice {k} of `{ns}`'s checks (generated; see there). -/" ++ sliceThm k ++ footer)]
  let imports := "\n".intercalate (sl.map (s!"import {ns}.Slice{·}"))
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
  let mut bins : Array (Option ByteArray) := #[]
  for fj in fjs do
    let clif := (fj.getObjValAs? String "clif").toOption.getD ""
    let ra := (fj.getObjValAs? String "ra").toOption.getD ""
    fis := fis.push { clif := ← IO.FS.readFile (dir / clif), ra := ← IO.FS.readFile (dir / ra) }
    bins := bins.push (← match (fj.getObjValAs? String "bin").toOption with
      | some b => do pure (some (← IO.FS.readBinFile (dir / b)))
      | none => pure none)
  let ajs := ((j.getObjVal? "addrs").bind (·.getArr?)).toOption.getD #[]
  let addrs0 : List (String × Nat) := ajs.toList.filterMap fun a => do
    let arr ← a.getArr?.toOption
    let n ← (arr[0]?.bind (·.getStr?.toOption))
    let v ← (arr[1]?.bind (·.getNat?.toOption))
    pure (n, v)
  -- `cargo fv`'s self-call aliases: a recursive `f` calls itself as `f__fvself`, which the
  -- linker resolves to `f`; the alias is a function of the program with `f`'s body, its
  -- self-call naming `f`, at `f`'s address (one copy of the code), and a fresh symbol address
  let top := (addrs0.map (·.2)).foldl max 0
  let mut aliases : List (String × String) := []
  let mut aliasAddrs : List (String × Nat) := []
  for fi in fis do
    let n := fi.func.name
    let a := n ++ "__fvself"
    if fi.func.externs.any (·.2.name == a) && !(addrs0.lookup a).isSome then
      let clif := (fi.clif.replace s!"%{a}(" s!"%{n}(").replace s!"function %{n}(" s!"function %{a}("
      fis := fis.push { fi with clif }
      bins := bins.push none
      aliases := aliases ++ [(a, n)]
      aliasAddrs := aliasAddrs ++ [(a, top + 16 * (aliases.length))]
  let addrs := addrs0 ++ aliasAddrs
  -- functions whose address is in a data object the program reaches (vtable methods)
  let dataSyms : List String := (((j.getObjVal? "data_syms").bind (·.getArr?)).toOption.getD #[]).toList.filterMap
    (·.getStr?.toOption)
  let I0 : LinkInput := { funcs := fis.toList, addrs, syms := [], raStar := 8, D := 0, aliases }
  if o.profile then
    -- the slowest functions: the pipeline, the lowering validator, the allocation checker
    let mut tot : Array (Nat × String × Nat × Nat × Nat) := #[]
    for fi in fis do
      let t0 ← IO.monoMsNow
      let f := fi.func
      let r := pipe f fi.k 0 (raJ fi.ra fi.j)
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
  let R0 := I0.results
  -- the CLIF image's symbols and the call-level stack
  -- the checks that do not depend on the rest of the program, once (`staticChks`: the
  -- validators); then `diagR` with them (`chks = staticChks ++ linkChks`)
  let D0 := (R0.map fun e => frameDrop (getOk e.2).af).foldl max 0
  let stat := R0.map fun e => (e.1.name, staticChks { I0 with D := D0 } e.1 e.2)
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
  -- the executable's bytes against the compiled words (not a premise: a check of the trusted
  -- object writer and linker)
  let mut imgBad := 0
  let mut imgWords := 0
  for (e, b) in R0.zip bins.toList do
    if let some b := b then
      let a := getOk e.2
      let msgs := imageDiff I0 a b
      imgWords := imgWords + a.fb.words.size
      if !msgs.isEmpty then
        imgBad := imgBad + 1
        IO.println s!"  IMAGE {e.1.name}:"
        for m in msgs.take 5 do IO.println s!"      {m}"
  IO.println s!"  image: {imgWords} words of {(bins.filter (·.isSome)).size} functions compared with the executable, {imgBad} function(s) differ"
  let ok := d.isEmpty
  IO.println (if ok then "  okB: true" else "  okB: false")
  -- the Lean file
  if let some out := o.lean then
    if !ok then
      IO.eprintln "link-check: the checks fail; no Lean file written"
      return 1
    let keepNames := keep.map (·.1.name)
    let funcs := (I0.funcs.zip (R0.map (·.1.name))).filter (keepNames.contains ·.2)
    let kAliases := I.aliases.filter fun p => keepNames.contains p.1
    let I' : LinkInput := { I with funcs := funcs.map (·.1), aliases := kAliases }
    let entries := o.entries.getD keepNames
    let missing := entries.filter (!keepNames.contains ·)
    if !missing.isEmpty then
      IO.eprintln s!"link-check: entries not in the program: {missing}"
      return 1
    let noTls := keep.all fun e => !Backend.hasTls e.1
    -- the modules of an earlier split of this crate's proof (`leanFiles`)
    let dir : System.FilePath := out.dropRight ".lean".length
    if ← dir.isDir then
      for e in ← dir.readDir do
        if e.fileName == "Input.lean" || (e.fileName.startsWith "Slice" && e.fileName.endsWith ".lean") then
          IO.FS.removeFile e.path
    for (p, t) in leanFiles I' (funcs.map (·.2)) entries out o.module exe noTls do
      if let some pd := (p : System.FilePath).parent then IO.FS.createDirAll pd
      IO.FS.writeFile p t
      IO.println s!"  wrote {p}"
    IO.println s!"  {funcs.length} functions, {entries.length} entries"
  return (if ok then 0 else 1)

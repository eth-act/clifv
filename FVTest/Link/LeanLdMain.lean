import FV.Link.Ld.Layout

/-! # `lake exe lean-ld ARGS…`: the Lean static linker (L2b stage 3, `Link.Ld.link`)

Takes the GNU ld arguments rustc gives `rust-lld -flavor gnu` for a static AArch64 musl
executable (docs/research/lean-linker.md §1, §6): objects, archives (rlibs, `-lc`, `-lunwind`
searched as `lib<name>.a` in every `-L` directory), `-o`, `-e`/`--entry`, `-u`/`--undefined`,
`--gc-sections`, `-Map`; options without effect on a static non-PIE link are accepted and
ignored (`--as-needed`, `-Bstatic`, `-Bdynamic`, `--eh-frame-hdr` (the header is always
written), `-z …`, `-static`, `-O1`, `--no-relax`, `-nostdlib`, …). `-pie`/`-shared` are errors.
-/

open Link.Ld

/-- Expands `@file` response files (whitespace-separated, double quotes). -/
partial def expand (args : List String) : IO (List String) := do
  let mut out : List String := []
  for a in args do
    if a.startsWith "@" then
      let t ← IO.FS.readFile (a.drop 1).toString
      out := out ++ (← expand (t.splitToList (fun c => c == '\n' || c == ' ' || c == '\t')
        |>.filter (!·.isEmpty) |>.map fun s => (s.replace "\"" "")))
    else out := out ++ [a]
  return out

def main (args0 : List String) : IO UInt32 := do
  let args ← expand args0
  let mut opts : Opts := { gc := false }
  let mut out := "a.out"
  let mut mapPath : Option String := none
  let mut libDirs : Array String := #[]
  -- the `-L` directories first (lld searches all of them for every `-l`)
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "-L" :: d :: r => libDirs := libDirs.push d; rest := r
    | a :: r =>
      if a.startsWith "-L" && a != "-L" then libDirs := libDirs.push (a.drop 2).toString
      rest := r
    | [] => rest := []
  let mut ins : Array Input := #[]
  let skip1 := ["-flavor", "-z", "-m", "--hash-style", "-plugin-opt", "--sysroot"]
  rest := args
  while !rest.isEmpty do
    match rest with
    | [] => pure ()
    | a :: r =>
      rest := r
      if a == "-o" then out := r.headD out; rest := r.drop 1
      else if a == "-L" then rest := r.drop 1
      else if a.startsWith "-L" then pure ()
      else if a == "-e" || a == "--entry" then opts := { opts with entry := r.headD opts.entry }; rest := r.drop 1
      else if a.startsWith "--entry=" then opts := { opts with entry := (a.drop 8).toString }
      else if a == "-u" || a == "--undefined" then opts := { opts with undefs := opts.undefs ++ [r.headD ""] }; rest := r.drop 1
      else if a.startsWith "--undefined=" then opts := { opts with undefs := opts.undefs ++ [(a.drop 12).toString] }
      else if a == "--gc-sections" then opts := { opts with gc := true }
      else if a == "--no-gc-sections" then opts := { opts with gc := false }
      else if a == "-Map" then mapPath := r.head?; rest := r.drop 1
      else if a.startsWith "-Map=" || a.startsWith "--Map=" then mapPath := some ((a.splitOn "=").drop 1 |> "=".intercalate)
      else if a == "-pie" || a == "-shared" || a == "--pie" || a == "-static-pie" then
        IO.eprintln s!"lean-ld: {a} is not supported (static non-PIE executables only)"; return 1
      else if skip1.contains a then rest := r.drop 1
      else if a.startsWith "-l" then
        let n := if a == "-l" then r.headD "" else (a.drop 2).toString
        if a == "-l" then rest := r.drop 1
        let name := if n.startsWith ":" then (n.drop 1).toString else s!"lib{n}.a"
        let mut found := none
        for d in libDirs do
          let p := System.FilePath.mk d / name
          if found.isNone && (← p.pathExists) then found := some p.toString
        match found with
        | some p => ins := ins.push (.archive p (← IO.FS.readBinFile p))
        | none => IO.eprintln s!"lean-ld: unable to find library -l{n}"; return 1
      else if a.startsWith "-" then pure ()
      else
        let d ← IO.FS.readBinFile a
        if d.size ≥ 8 && d.extract 0 8 == "!<arch>\n".toUTF8 then ins := ins.push (.archive a d)
        else ins := ins.push (.obj a d)
  match link opts ins.toList with
  | .error e => IO.eprintln s!"lean-ld: {e}"; return 1
  | .ok r =>
    IO.FS.writeBinFile out r.img.write
    IO.setAccessRights out { user := { read := true, write := true, execution := true },
                             group := { read := true, execution := true },
                             other := { read := true, execution := true } }
    if let some m := mapPath then IO.FS.writeFile m r.map
    return 0

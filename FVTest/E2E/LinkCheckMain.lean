import FVTest.E2E.LinkProof
import FVTest.E2E.ProductionLinkProof

open E2E E2E.LinkCheck E2E.StackBound Lean Backend E2E.Elf E2E.BinCheck

def main (args : List String) : IO UInt32 := do
  let some o := parseOpts args none | do IO.eprintln usage; return 2
  let dir : System.FilePath := o.dir
  let (b, exe) ← try Front.readBundle dir []
    catch e => do IO.eprintln s!"link-check: {e}"; return 2
  IO.println s!"link-check: {exe}"
  let A ← match Front.assemble b with
    | .ok A => pure A
    | .error e => do IO.eprintln s!"link-check: {exe}: {e}"; return 1
  let fis := A.funcs.toArray
  -- the executable and the data objects the functions reach (renamed to the linked symbols)
  let file ← IO.FS.readBinFile exe
  let dataLines : List String := A.data.map Clif.dataObject
  let addrs := Front.linkAddrs b A
  -- names whose address is in a data object the program reaches (vtable methods)
  let dataSyms : List String := A.data.flatMap (·.refs)
  let I0 : LinkInput := { funcs := fis.toList, addrs, syms := [], raStar := 8, D := 0 }
  if o.profile then
    -- the slowest functions: the pipeline, the lowering validator, the allocation checker
    let mut tot : Array (Nat × String × Nat × Nat × Nat) := #[]
    for fi in fis do
      let t0 ← IO.monoMsNow
      let f := fi.func
      let r := I0.pipeProduction o.deadCleanup fi
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
  let R0 := I0.resultsProduction o.deadCleanup
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
    for (p, t) in FVTest.E2E.ProductionLinkProof.leanFilesProduction I' (funcs.map (·.2)) entries out o.module exe o.deadCleanup noTls stackS stackGood bg do
      if let some pd := (p : System.FilePath).parent then IO.FS.createDirAll pd
      IO.FS.writeFile p t
      IO.println s!"  wrote {p}"
    IO.println s!"  {funcs.length} functions, {entries.length} entries"
  return (if ok && binOk then 0 else 1)

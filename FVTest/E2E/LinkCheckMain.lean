import FV.E2E.ProductionPipelineWith
import FV.Backend.Lowering.StockMemoryExtLoadNI
import FV.Front.Read
import FVTest.E2E.LinkProof
import FVTest.E2E.SemanticLinkProofWith
import FV.E2E.BinCheckFast
import FV.Link.Image
import FV.E2E.DeadCleanupLinkCheckT
import FV.E2E.SemanticPipelineCheckT

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
  -- Other supported compiler modes and whole-file retries can retain earlier
  -- artifacts. Recover their routing from actual bytes, then validate every
  -- selected artifact normally. These are data choices, not source assumptions.
  -- One task per function (`Link.parMap`, T3d: up to five pipelines per function).
  let choices : List (String × Nat) := match phdrs (fileRd file) with
    | none => []
    | some phs =>
      let rd := fileRd file
      let route (fi : FnInput) : Option (String × Nat) :=
        let f := fi.func
        if (Stock.Arithmetic.eligible f || Stock.Mixed.activationEligible f ||
            Stock.Logical.activationEligible f || Stock.Scalar.activationEligible f || (((Stock.MemoryExtending.eligible f || Stock.MemoryUnsigned.eligible f || Stock.MemoryCfg.eligible f || Stock.Memory.eligible f || Stock.ParameterCfg.eligible f || Stock.ConditionalForwardCfg.eligible f) || Stock.ConditionalCfg.eligible f) || Stock.ForwardCfg.eligible f || Stock.LinearCfg.eligible f || Stock.TwoBlock.Entry.eligible f)) &&
            !(Stock.D0.eligible f || Stock.ScalarAdd.activationEligible f) then
          -- Probe each complete route before its transactional retry. A retained
          -- logical/mixed artifact must not be skipped directly to legacy.
          let found := Stock.MemoryExtending.lowerRoutes.zipIdx.find? fun (lower, _) =>
            match I0.pipeOfWithLowering lower (productionStage o.deadCleanup) fi with
            | .error _ => false
            | .ok a => artB I0 rd phs a
          let idx := (found.map (·.2)).getD 4
          if idx != 0 || (((Stock.MemoryExtending.eligible f || Stock.MemoryUnsigned.eligible f || Stock.MemoryCfg.eligible f || Stock.Memory.eligible f || Stock.ParameterCfg.eligible f || Stock.ConditionalForwardCfg.eligible f) || Stock.ConditionalCfg.eligible f) || Stock.ForwardCfg.eligible f || Stock.LinearCfg.eligible f || Stock.TwoBlock.Entry.eligible f) then some (f.name, idx) else none
        else none
      (Link.parMap route I0.funcs).filterMap id
  let actualLower := Stock.MemoryExtending.lowerWithRoutes choices
  let lowerName := "(Backend.Stock.MemoryExtending.lowerWithRoutes [" ++
    ", ".intercalate (choices.map fun (name,idx) => "(" ++ leanStr name ++ ", " ++ toString idx ++ ")") ++ "])"
  if o.profile then
    -- the slowest functions: the pipeline, the lowering validator, the allocation checker
    let mut tot : Array (Nat × String × Nat × Nat × Nat) := #[]
    for fi in fis do
      let t0 ← IO.monoMsNow
      let f := fi.func
      let r := I0.pipeProductionWith actualLower o.deadCleanup fi
      let ok := r.toBool
      let t1 ← IO.monoMsNow
      let a := getOk r
      let lc := Backend.SemanticNI.check f a.vc
      let t2 ← IO.monoMsNow
      let ca := (checkAlloc a.vcp a.rf).toBool
      let t3 ← IO.monoMsNow
      if !(ok && lc && ca) then IO.println s!"  profile: {f.name} fails the pipeline or a validator"
      tot := tot.push (t3 - t0, f.name, t1 - t0, t2 - t1, t3 - t2)
    for (t, n, a, b, c) in (tot.qsort (fun x y => x.1 > y.1)).toList.take 10 do
      IO.println s!"  profile: {t} ms {n} (pipeline {a}, lowerCheck {b}, checkAlloc {c})"
    IO.println s!"  profile: {(tot.map (·.1)).foldl (· + ·) 0} ms in total"
  let t0 ← IO.monoMsNow
  -- `I0.resultsProductionWith actualLower o.deadCleanup`, one task per function (`Link.parMap_eq`)
  let R0I : Res := Link.parMap (fun fi => (fi.func, I0.pipeProductionWith actualLower o.deadCleanup fi)) I0.funcs
  -- the CLIF image's symbols and the call-level stack
  -- the checks that do not depend on the rest of the program, once (`staticChks`: the
  -- validators); then `diagR` with them (`chks = staticChks ++ linkChks`)
  let D0 := (R0I.map fun e => frameDrop (getOk e.2).af).foldl max 0
  let statI := Link.parMap (fun e => (e.1.name, staticChksSemanticNI (productionStage o.deadCleanup) { I0 with D := D0 } e.1 e.2)) R0I
  let failI := statI.filterMap fun e => if (bad e.2).isEmpty then none else some e.1
  -- the typed checks on the Stock route's results (#722, `Link.SemanticCompilerWith.attemptT`'s
  -- output, typed `--verified` when the units hold Stock code): the results `R0I` with
  -- `staticChksWithTS` (the checker `okRWithTS`: the Stock validator on an integer function, the
  -- typed validators on `lowerFunction`'s output); used when they accept every function the
  -- integer validators reject and the executable holds `R0I`'s code wherever it is not
  -- `lowerFunction`'s; theorem `E2E.SemanticExecBytes.binary_correct_exec_provenTS`
  let stockTS : Option (List (String × List (String × Bool))) :=
    if o.deadCleanup && !failI.isEmpty then
      let failSet : Std.HashSet String := failI.foldl (·.insert ·) {}
      let statS := Link.parMap (fun e => (e.1.name, staticChksWithTS (productionStage o.deadCleanup)
        { I0 with D := D0 } e.1 e.2)) R0I
      let fixedS := (statS.filter fun e => failSet.contains e.1 && (bad e.2).isEmpty).length
      let bytesS := match phdrs (fileRd file) with
        | none => false
        | some phs => (Link.parMap (fun e => match e.2 with
            | .ok a => artB I0 (fileRd file) phs a || lowersToB e.1 a.vc
            | .error _ => true) R0I).all id
      if fixedS == failI.length && bytesS then some statS else none
    else none
  -- the typed checker (S11e6, #615): when integer validators reject functions, the cleanup
  -- results `I.resultsCleanup` with the typed checks `chksWithT DeadCleanup.prune` (the checker
  -- `okBCleanupT`, which accepts integer functions too: `Link.DeadCleanup.compileExeT`'s output,
  -- typed `--verified`); used when the typed validators accept some of the rejected functions;
  -- theorem `E2E.DeadCleanupExecBytes.binary_correct_exec_provenT`. The integer results are
  -- dropped before the typed ones are computed (one result set at a time).
  let (typed, typedS, R0, stat, note) :
      Bool × Bool × Res × List (String × List (String × Bool)) × String :=
    match stockTS with
    | some statS =>
      (true, true, R0I, statS,
        s!"  typed checks: the {failI.length} function(s) failing the integer validators pass the typed ones on the Stock route's results (okRWithTS's); the typed Stock checker is used")
    | none => if o.deadCleanup && !failI.isEmpty then
      let failSet : Std.HashSet String := failI.foldl (·.insert ·) {}
      let probe := Link.parMap (fun (fi : FnInput) =>
        let r := I0.pipeCleanupOf fi
        (bad (staticChksWithT (fun _ => DeadCleanup.prune) { I0 with D := max D0 (frameDrop (getOk r).af) }
          fi.func r)).isEmpty) (I0.funcs.filter fun fi => failSet.contains fi.func.name)
      let fixed := (probe.filter id).length
      if fixed > 0 then
        let R0T : Res := Link.parMap (fun fi => (fi.func, I0.pipeCleanupOf fi)) I0.funcs
        let DT := (R0T.map fun e => frameDrop (getOk e.2).af).foldl max 0
        (true, false, R0T, Link.parMap (fun e => (e.1.name, staticChksWithT (fun _ => DeadCleanup.prune) { I0 with D := DT } e.1 e.2)) R0T,
          s!"  typed checks: {fixed} of the {failI.length} function(s) failing the integer validators pass the typed ones (okBCleanupT's); the typed checker is used")
      else (false, false, R0I, statI, s!"  typed checks: none of the {failI.length} function(s) failing the integer validators pass the typed ones")
    else (false, false, R0I, statI, "")
  let nStat := (stat.filter fun e => !(bad e.2).isEmpty).length
  if !note.isEmpty then IO.println note
  IO.println s!"  checker: {if typedS then "typed Stock (okRWithTS)" else if typed then "typed (okBCleanupT)" else "integer"}"
  IO.println s!"  static checks (the validators): {nStat} function(s) fail"
  IO.println s!"  static checks done in {(← IO.monoMsNow) - t0} ms"
  let mut keep := R0
  let mut dropped : List (String × List String) := []
  let mut d : List (String × List String) := []
  let mut I := I0
  -- hash maps instead of list scans per element (T3d: a 28k-function program); the checks are
  -- `globalChks`/`linkChks` evaluated through `LinkCtx.of` (`globalChksWith_of`, `linkChksWith_of`)
  let addrs0 := assocMap I0.addrs
  let statM := assocMap stat
  repeat
    let keepSet : Std.HashSet String := keep.foldl (fun s e => s.insert e.1.name) {}
    let names := Front.dedupFirst ((keep.flatMap fun e => addrNames e.1) ++
      dataSyms.filter keepSet.contains)
    let syms := names.filterMap fun n => addrs0[n]?.map (n, ·)
    let D := (keep.map fun e => frameDrop (getOk e.2).af).foldl max 0
    I := { I0 with syms, D }
    let P := progOf keep
    let T := tabOf keep
    let C := LinkCtx.of I P T
    let gl := bad (globalChksWith C I P T)
    -- typed: `chksWithT`'s call-site checks (`linkChksT`: a `blr` that enters no function of the
    -- program may have float uses/defs, `linkChksWithT_of`) and `calleeInt` with `C`'s declared
    -- names and indirect-call flag (`calleeWithB_eq`); typed Stock (`okRWithTS`, #742): the
    -- class-aware call-site checks `linkChksWithTS` (`linkChksWithTS_of`), no `calleeInt`
    let tyChk := fun (g : Clif.Function) => if typed && !typedS then
        [("calleeInt", !calleeWithB (fun n => C.callees.contains n) C.anyInd C.S g || g.sig.returns.all (·.ty.isInt))]
      else []
    let lc := fun (e : Clif.Function × Except String Art) =>
      if typedS then linkChksWithTS C P e.1 e.2
      else if typed then linkChksWithT C P e.1 e.2 else linkChksWith C P e.1 e.2
    let fs := (keep.zip (Link.parMap (fun e => bad ((statM[e.1.name]?).getD [] ++ lc e ++ tyChk e.1)) keep)).filterMap fun (e, b) =>
      match b with
      | [] => none
      | b => some (e.1.name, b ++ (match e.2 with | .error m => [m] | .ok _ => []))
    d := (if gl.isEmpty then [] else [("(program)", gl)]) ++ fs
    let bad := d.filter (·.1 != "(program)")
    if !o.prune || bad.isEmpty then break
    dropped := dropped ++ bad
    -- and their callers in the program, so that what is left is closed under calls (no function
    -- of the crate becomes an extern of the base environment)
    let mut gone : Std.HashSet String := bad.foldl (fun s b => s.insert b.1) {}
    repeat
      let callers := keep.filter fun e => !gone.contains e.1.name &&
        e.1.externs.any fun x => gone.contains x.2.name
      if callers.isEmpty then break
      dropped := dropped ++ callers.map fun e => (e.1.name, ["(calls a dropped function)"])
      gone := callers.foldl (fun s e => s.insert e.1.name) gone
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
  let keepSet : Std.HashSet String := keepNames.foldl (·.insert ·) {}
  let funcs := (I0.funcs.zip (R0.map (·.1.name))).filter (keepSet.contains ·.2)
  let kAliases := I.aliases.filter fun p => keepSet.contains p.1
  let aliases0 : Std.HashSet String := I0.aliases.foldl (fun s p => s.insert p.1) {}
  let kAliasSet : Std.HashSet String := kAliases.foldl (fun s p => s.insert p.1) {}
  let kAddrs := I.addrs.filter fun p => !aliases0.contains p.1 || kAliasSet.contains p.1
  let I' : LinkInput := { I with funcs := funcs.map (·.1), aliases := kAliases, addrs := kAddrs }
  -- `--input-only`: the input alone (no Lean proof), whatever the checks say
  if let some out := o.inputOnly then
    -- drop the functions outside `InScopeP`'s per-function conditions and, transitively, their
    -- callers (as `--prune`), so that the rest is in scope
    let mut I' := I'
    let mut outScope : List String := []
    repeat
      let P := I'.prog
      let S := fun n => I'.syms.lookup n
      let bad := P.funcs.filter fun g => !(fnScopeB g && declSigB P g && indB P S g &&
        callScopeB P S g && outScopeB P g)
      if bad.isEmpty then break
      let mut gone : Std.HashSet String := bad.foldl (fun s g => s.insert g.name) {}
      repeat
        let callers := P.funcs.filter fun g => !gone.contains g.name &&
          g.externs.any fun x => gone.contains x.2.name
        if callers.isEmpty then break
        gone := callers.foldl (fun s g => s.insert g.name) gone
      outScope := outScope ++ gone.toList
      I' := { I' with funcs := I'.funcs.filter fun fi => !gone.contains fi.func.name }
    if !outScope.isEmpty then
      IO.println s!"  --input-only: dropped {outScope.length} function(s) outside InScopeP (and their callers): {outScope}"
    let nSl := max ((I'.funcs.length + sliceSize - 1) / sliceSize) 1
    let pairs (l : List (String × Nat)) := ",\n    ".intercalate (l.map fun p => s!"({leanStr p.1}, {p.2})")
    let mut t := s!"import FV.E2E.LinkCheck\n\n/-! The input of `{exe}` (generated by `link-check --input-only`). -/\n\nnamespace Crates.{o.module}\n\nopen E2E E2E.LinkCheck\n\n"
    for (fi, i) in I'.funcs.zipIdx do
      let indices := (if fi.k == 0 then "" else s!"\n  k := {fi.k}") ++
        (if fi.j == 0 then "" else s!"\n  j := {fi.j}")
      t := t ++ s!"/-- `{fi.func.name}` -/\ndef fn{i} : FnInput where\n  clif := {leanStr fi.clif}\n  ra := {leanStr fi.ra}{indices}\n\n"
    for k in List.range nSl do
      let fns := ", ".intercalate (((List.range I'.funcs.length).drop (k * sliceSize)).take sliceSize |>.map (s!"fn{·}"))
      t := t ++ s!"/-- Slice {k} of the functions. -/\ndef slice{k} : List FnInput := [{fns}]\n\n"
    let aliases := if I'.aliases.isEmpty then "" else
      "\n  aliases := [" ++ ", ".intercalate (I'.aliases.map fun p => s!"({leanStr p.1}, {leanStr p.2})") ++ "]"
    t := t ++ s!"/-- The crate's input. -/\ndef input : LinkInput where\n  funcs := {" ++ ".intercalate ((List.range nSl).map (s!"slice{·}"))}\n  addrs := [\n    {pairs I'.addrs}]\n  syms := [\n    {pairs I'.syms}]\n  raStar := {I'.raStar}\n  D := {I'.D}{aliases}\n\nend Crates.{o.module}\n"
    if let some pd := (out : System.FilePath).parent then IO.FS.createDirAll pd
    IO.FS.writeFile out t
    IO.println s!"  wrote {out} ({I'.funcs.length} functions)"
    return 0
  -- the binary checks (`FV/E2E/BinCheck.lean`) on the executable: its code, data objects and
  -- symbols against the program
  let tb ← IO.monoMsNow
  let r := fileRd file
  let phs := (phdrs r).getD []
  let hdrOk := match ehdr r with
    | some e => staticB e phs
    | none => false
  let arts := keep.map fun e => (e.1.name, getOk e.2)
  -- the link map and the aliases in hash maps, built once (`artWithB_assocMap`, `objWithB_assocMap`)
  let addrM := assocMap I'.addrs
  let aliasM := assocMap I'.aliases
  let ad := fun n => (addrM[n]?).getD 0
  let al := fun n => aliasM[n]?
  let mut codeBad := 0
  let mut words := 0
  for (n, a) in arts do
    words := words + a.fb.words.size
    if !artWithB ad al r phs a then
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
  -- the first object of each name (`find?`'s answer)
  let dataM : Std.HashMap String Clif.DataObject :=
    allData.foldl (fun m o => if m.contains o.name then m else m.insert o.name o) {}
  let roots := Front.dedupFirst (keep.flatMap fun e => addrNames e.1)
  let mut reach : Std.HashSet String := roots.foldl (·.insert ·) {}
  let mut todo := roots
  repeat
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if let some o := dataM[n]? then
        for it in o.items do
          if let .addr m _ := it then
            if !reach.contains m then
              reach := reach.insert m
              todo := m :: todo
  let D := allData.filter (reach.contains ·.name)
  let mut dataBad := 0
  for o in D do
    if !objWithB (fun n => addrM[n]?) r phs o then
      dataBad := dataBad + 1
      IO.println s!"  BIN data {o.name}:"
      for m in (objDiag I' r phs o).take 8 do IO.println s!"      {m}"
  -- the symbol table against the link map
  let idx := symIndex file
  let cert : List (String × Nat × Nat) := I'.addrs.filterMap fun p =>
    (idx.get? (symName p.1, p.2)).map (p.1, ·)
  let ex : Excerpt := [(0, file)]
  let certM := assocMap cert
  let symsBad := I'.addrs.filter fun p => !(aliasM[p.1]?).isSome && !(certM[p.1]?).isSome
  for p in symsBad do
    IO.println s!"  BIN symbol {p.1}: no defined symbol {symName p.1} = {hexN p.2} in the executable's symbol table"
  let symsOk := symsWithB (fun n => aliasM[n]?) (fun n => certM[n]?) I' ex
  let binOk := hdrOk && codeBad == 0 && dataBad == 0 && symsOk
  IO.println s!"  binary checks done in {(← IO.monoMsNow) - tb} ms"
  IO.println (if binOk then
      s!"  binary: ok ({arts.length} functions, {words} words, {D.length} data objects, {I'.addrs.length - I'.aliases.length} symbols)"
    else s!"  binary: FAIL code={codeBad} data={dataBad} syms={symsBad.length} hdr={if hdrOk then 0 else 1}")
  -- the code map of the executable machine (`codeMapB`, `FV/E2E/CodeMap.lean`: a premise of the
  -- theorem about the executable's own words, not of `okB`)
  IO.println (if codeMapFastB (fun n => (assocMap I'.addrs)[n]?) (fun n => (assocMap I'.syms)[n]?) (tabOf keep)
    then "  code map: ok" else "  code map: FAIL (codeMapB)")
  -- the stack bound (`budMap`) of the (pruned) program: a function has a budget iff no call
  -- cycle is reachable from it (`StackBound.budC_isSome_iff`)
  let Pk := progOf keep
  let sk := assocMap I.syms
  let stackM := budMapFast I keep
  let artM := artMap keep
  let stackOf (g : Clif.Function) : Option Nat :=
    (stackM.get? g.name).map (frameDrop ((artM[g.name]?).getD default).af + ·)
  let bad := Pk.funcs.filter fun g => (stackOf g).isNone
  let s := Pk.funcs.foldl (fun x g => max x ((stackOf g).getD 0)) 0
  if bad.isEmpty then
    IO.println s!"  stack: {s} bytes at most (no call cycle)"
  else
    IO.println s!"  stack: recursive: the calls of {bad.length} function(s) reach a call cycle (their stack stays a premise): {(bad.map (·.name)).take 10}{if bad.length > 10 then " …" else ""}; the other {Pk.funcs.length - bad.length}: {s} bytes at most"
  -- no caller: no function declares it, and no indirect call can enter it (`edgeB`)
  let cs := calleeSet Pk
  let iSigs := (Pk.funcs.filter (!indFreeB ·)).flatMap indSigs
  let es := (Pk.funcs.filter fun h => !(cs.contains h.name ||
      ((sk[h.name]?).isSome && iSigs.any fun s => decide (LinkSys.IndSigMatch s h)))).map fun g =>
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
    for (p, t) in FVTest.E2E.SemanticLinkProofWith.leanFilesSemanticWith lowerName I' (funcs.map (·.2)) entries out o.module exe o.deadCleanup noTls stackS stackGood bg (lowerImport := "FV.Backend.Lowering.StockMemoryExtLoadNI") do
      if let some pd := (p : System.FilePath).parent then IO.FS.createDirAll pd
      IO.FS.writeFile p t
      IO.println s!"  wrote {p}"
    IO.println s!"  {funcs.length} functions, {entries.length} entries"
  return (if ok && binOk then 0 else 1)

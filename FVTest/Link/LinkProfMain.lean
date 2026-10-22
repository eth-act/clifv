import FV.Backend.Lowering.StockScalarNI
import FV.Link.Compile
import FV.Link.DeadCleanupCompile
import FV.Link.TailCompile
import FV.Link.OptCompile
import FV.Link.Placed
import FV.E2E.SrcScopeDefs
import FV.Front.Read
import FV.E2E.LinkScopeInputDefs
import FV.Link.Ld.Spec
import FVTest.Link.LdArgs
import FV.Link.ExeUCompile
import FV.Link.SemanticCompileDefs

/-! Temporary profiling harness (T3d; not committed): times the stages of `lean-link --verified`.
Per-function checks against the whole program are timed on `K` evenly spaced functions and
extrapolated. -/

open Lean E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Link Backend

def timeW {α} (sh : α → String) (label : String) (f : Unit → α) : IO α := do
  let t0 ← IO.monoMsNow
  let v ← IO.lazyPure f
  let str := sh v
  IO.println s!"prof: {label}: {(← IO.monoMsNow) - t0} ms ({str.take 80})"
  return v

def timeIt {α} [ToString α] (label : String) (f : Unit → α) : IO α := timeW toString label f

def sampleOf {α} (xs : List α) (k : Nat) : List α :=
  let n := xs.length
  if n ≤ k then xs else (List.range k).filterMap fun i => xs[i * n / k]?

def parStr (p : Clif.AbiParam) : String := toString (repr p.ty) ++ " " ++ toString (repr p.purpose)

def sigStr (s : Clif.Signature) : String :=
  "(" ++ ", ".intercalate (s.params.map parStr) ++ ") -> (" ++ ", ".intercalate (s.returns.map parStr) ++ ")"

/-- The program-level failures of every function, with witnesses. -/
def failsMain (d : String) : IO UInt32 := do
  let (b0, _) ← Front.readBundle d []
  let .ok S := Front.buildSpec { b0 with sizes := b0.markers.map fun (n, _) => (n, 0) } | return 1
  let P := S.input0.prog
  let sy := assocMap S.input0.syms
  let Sy := fun nm => sy[nm]?
  let ind := P.funcs.filter (!indFreeB ·)
  IO.println s!"fails: {P.funcs.length} functions, {ind.length} with indirect calls"
  for g in ind do
    let bad1 := P.funcs.filter fun h => mayB Sy g h.name && indSigB g h &&
        (match sigParamBytes h.sig with | .ok b => decide (b.length > 8) | .error _ => true)
    let bad2 := P.funcs.filter fun h => mayB Sy g h.name && indSigB g h && !indRetsB g h
    let sites := g.blocks.flatMap fun B =>
      (B.body.filterMap fun st => match st.inst with
        | .callIndirect sg _ args => (g.sigDecls.lookup sg).map (·, args)
        | _ => none) ++
      match B.term with
      | .tryCallIndirect _ args et => ((g.sigDecls.lookup et.sig).map (·, args)).toList
      | _ => []
    let bad3 := sites.filterMap fun (s, args) =>
      let hs := P.funcs.filter fun h => indToB Sy g h &&
        decide ((regLocs h.sig).length = (callRegs s args).length) && decide (regLocs h.sig ≠ callRegs s args)
      if hs.isEmpty then none else some (s, args, hs)
    if bad1.isEmpty && bad2.isEmpty && bad3.isEmpty then continue
    IO.println s!"FAIL {g.name}: indSigs {(indSigs g).map sigStr}"
    for h in bad1.take 3 do IO.println s!"  calleeStack: {h.name} {sigStr h.sig} decl {declB g h.name} sym {(Sy h.name).isSome}"
    for h in bad2.take 3 do IO.println s!"  sretRets: {h.name} {sigStr h.sig} decl {declB g h.name} sym {(Sy h.name).isSome}"
    for (s, args, hs) in bad3.take 3 do
      IO.println s!"  blrRegs: site {sigStr s} args {args.length} callRegs {repr (callRegs s args)}"
      for h in hs.take 3 do IO.println s!"    → {h.name} {sigStr h.sig} regLocs {repr (regLocs h.sig)} decl {declB g h.name} got {gotDeclB g h.name} match {indMatchB g h}"
  return 0

def main (args : List String) : IO UInt32 := do
  if let ["fails", d] := args then return ← failsMain d
  let [d, ks] := args | do IO.eprintln "usage: link-prof DIR K"; return 2
  let K := ks.toNat!
  let t0 ← IO.monoMsNow
  let (b0, exe) ← Front.readBundle d []
  IO.println s!"prof: readBundle: {(← IO.monoMsNow) - t0} ms"
  let S ← match ← timeW (fun r => match r with | .ok (S : LinkSpec) => s!"{S.funcs.length}" | .error e => e) "buildSpec" (fun _ => Front.buildSpec { b0 with sizes := b0.markers.map fun (n, _) => (n, 0) }) with
    | .ok S => pure S
    | .error e => do IO.eprintln e; return 1
  let n := S.funcs.length
  IO.println s!"prof: {n} functions, {S.input0.syms.length} syms, {S.input0.addrs.length} addrs"
  let SC ← timeW (fun (S : LinkSpec) => s!"{S.sizes.foldl (· + ·) 0}") "placedPar" (fun _ => Link.DeadCleanup.placedPar S)
  let I := S.input0
  let srcP ← timeW (fun (P : Clif.Program) => s!"{P.funcs.length}") "srcProg" (fun _ => I.srcProg)
  let _ ← timeIt "src legalOkB" (fun _ => srcP.funcs.all Opt.Legalize128.legalOkB)
  let _ ← timeIt "src linkFreeB" (fun _ => srcP.funcs.all linkFreeB)
  let sm := sampleOf srcP.funcs K
  let _ ← timeIt s!"src declSigB ×{sm.length} (×{n}/{sm.length} to extrapolate)" (fun _ => sm.all (declSigB srcP))
  let _ ← timeIt "helperFreeB" (fun _ => helperFreeB srcP)
  let P := SC.input0.prog
  let syms := fun nm => SC.input0.syms.lookup nm
  let _ ← timeIt "addrSlotsInputB" (fun _ => addrSlotsInputB P syms)
  let _ ← timeIt "fnScopeInFails all (par)" (fun _ => (parMap fnScopeInFails P.funcs).all List.isEmpty)
  let _ ← timeIt "names Nodup" (fun _ => decide (P.funcs.map (·.name)).Nodup)
  let gs := sampleOf P.funcs K
  let _ ← timeIt s!"declSigB ×{gs.length}" (fun _ => gs.all (declSigB P))
  let _ ← timeIt s!"indB ×{gs.length} (indirect: {gs.filter (!indFreeB ·) |>.length})" (fun _ => gs.all (indB P syms))
  let _ ← timeIt s!"callScopeB ×{gs.length}" (fun _ => gs.all (callScopeB P syms))
  let _ ← timeIt s!"outScopeB ×{gs.length}" (fun _ => gs.all (outScopeB P))
  let _ ← timeIt "indirect callers in P" (fun _ => (P.funcs.filter (!indFreeB ·)).length)
  let _ ← timeIt "fnScopeB all (par)" (fun _ => (parMap fnScopeB P.funcs).all id)
  let _ ← timeIt "addrSlotsInB" (fun _ => addrSlotsInB P syms)
  -- leanLink's stages
  let file0 ← IO.FS.readBinFile exe
  let some phs := phdrs (fileRd file0) | do IO.eprintln "no phdrs"; return 1
  let I0 := SC.input0
  let Rs ← timeIt "parResultsCleanupT" (fun _ => let r := Link.DeadCleanup.parResultsCleanupT I0; r.length)
  let _ := Rs
  let Rs := Link.DeadCleanup.parResultsCleanupT I0
  let I := I0.withDepth Rs
  let T := tabOf Rs
  let tp := tpOff phs
  let _ ← timeIt "placeOkB" (fun _ => SC.placeOkB)
  let _ ← timeIt "pipeline ok" (fun _ => Rs.all (·.2.toBool))
  let _ ← timeIt "namesOkB" (fun _ => SC.namesOkB T)
  let _ ← timeIt "sizesOkB" (fun _ => SC.sizesOkB T)
  let Ts := sampleOf T K
  let _ ← timeIt s!"relocsOkB ×{Ts.length}" (fun _ => Ts.all fun e => relocsOkB I tp e.2)
  let _ ← timeIt "codeMapB" (fun _ => codeMapB I T)
  let B ← timeW (fun (B : ByteArray) => s!"{B.size}") "regionBytes" (fun _ => ByteArray.mk (regionBytes I tp ((T.take SC.funcs.length).map (·.2))).toArray)
  let off := offsetOf phs SC.R
  let _ ← timeIt "regionOkB" (fun _ => regionOkB file0 SC.R B.size off)
  let file := patch file0 off B
  let _ ← timeIt "outsideOkB" (fun _ => outsideOkB I SC.data file)
  let _ ← timeIt "ehOkR" (fun _ => EhCheck.ehOkR Rs file)
  let _ ← timeIt "unwFnsB" (fun _ => EhCheck.unwFnsB Rs)
  return 0

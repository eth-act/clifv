import FV.Backend.Lowering.StockParameterCfgNI
import FV.Link.Compile
import FV.Link.DeadCleanupCompile
import FV.Link.DeadCleanupCompileT3
import FV.Link.TailCompile
import FV.Link.OptCompile
import FV.Link.Placed
import FV.E2E.SrcScopeDefs
import FV.Front.Read
import FV.E2E.LinkScopeInputDefs
import FV.E2E.LinkScopeInputDefsT
import FV.E2E.LinkScopeInputDefsTC
import FV.Link.Ld.Spec
import FV.Link.ReachCheck
import FV.Link.Ld.SpecTotal
import FV.Link.Ld.RelsFast
import FVTest.Link.LdArgs
import FV.Link.ExeUCompile
import FV.Link.SemanticCompileDefs
import FV.Link.UnwReport
import FV.Link.SemanticCompileT

/-! # `lake exe lean-link DIR [--dead-cleanup|--no-dead-cleanup] [--opt] [--verified] [--ld FILE]`:
the executable compiler on an executable (L1, L2b)

`--ld FILE` (`cargo fv` passes it when `lean-ld` linked the executable; `FILE`: `lean-ld`'s
arguments): after the compiler succeeds, `ldCheck` links again with `Link.Ld.link`, checks that
the output is the executable read, and decides `Plan.specOkB` of the plan against the link spec:
the premise of `Link.Ld.file0OkB_ld` and the totality theorems `…compileExe{,Opt}_total_ld`
(no check of the linker's output); reported, and added to the `--verified` totality note.

`DIR` is `cargo fv link-proof --cgus … --no-check`'s output for an executable linked by
`cargo fv --lean-link` (docs/research/lean-linker.md): the frontend bundle `bundle.json`
(docs/contracts/frontend.md; read by `Front.readBundle`: per codegen unit the program's
functions in placement order — their CLIF as the frontend wrote it and `lean-regalloc`'s
output — its data objects, local symbols and the merge's names; the executable's symbols and
the functions' Lean code addresses). The `Link.LinkSpec` is built in Lean by `Front.buildSpec`
(the renaming to linked names, the data closure, the CLIF image's symbols; `FV/Front/BundleProof.lean`:
its source program is the units' program under the linked names, a scoping, alpha-equivalent to
the units' program under any scoping; the region's base `R`: the first function's address) and
given the Lean compiler's layout (`Link.LinkSpec.placedPar`/`Link.DeadCleanup.placedPar`,
`FV/Link/Placed.lean`: the CLIF functions' names and the sizes of their compiled code, `=
placed`), the layout the totality theorems are about, by construction; no size is read from
outside (rust-lld's placement of the region object is checked against it, `symsOkB`). The
tool then runs the executable
compiler — `Link.DeadCleanup.compileExe` (default, `--dead-cleanup`; the input conditions
`InScopeP`) or `Link.compileExe` (`--no-dead-cleanup`; the input conditions `InScopeIn`, decided
on the CLIF alone), then the Lean linker (placement, the
compiler's pipeline, the linker's checks, the checks of rust-lld's output — among them that
rust-lld put every function at its placement, `symsOkB`) — and writes the result over the
executable. It prints the theorems covering the written executable (`coverage:`): the
compiler's `compileExe_correct` (entries without a reachable call cycle) and
`compileExe_correct_peak` (any entry), and, for an input in the source domain (`SrcScopeB`),
`compileExe_correct_source` and `compileExe_correct_source_peak` about the original
(pre-`i128`-legalisation) program. No per-crate proof needed.

Outside the compiler's input conditions, without `--verified`, the cleanup compiler (no `--opt`,
no self tail calls) tries the typed scope (S11): first `Link.DeadCleanup.compileExeT3` (the
decided input conditions `InScopeInT3`, no run-time decider; then `leanLink` and the output checks
`OutOkTCleanup`; coverage `compileExeT3_correct`), else `Link.DeadCleanup.compileExeT` (`InScopePT`,
then `leanLink`, then `OutOkTCleanup`; coverage `compileExeT_correct`); returned values by class.
Otherwise the tool links with the bare Lean linker (`leanLink`, no
compiler theorem; reported as such). When `lean-backend` compiled some function with the Stock
lowering (`stockDiffersB`, #734), the typed compilers and `leanLink` (`lowerFunction` throughout)
are not tried: the bare linker links on the Stock placement (`Link.leanLinkProductionWith`, the
routes of `compileWithRoutes` in order; no compiler theorem). **`--verified`** fails closed: an input outside `SrcScopeB`, outside
the per-function input conditions decided on the CLIF alone (`fnScopeInB`, V7) or outside
`InScopeP` is an error and the executable is not written, so every executable it writes is
covered by the four theorems above and its input is in `InScopeIn` (`InScopeP`'s program-level
conditions with `fnScopeInB`), on which the compiler is proven total
(`Link.DeadCleanup.compileExe_total_reach_input`, `Link.compileExe_total_reach`, given the
layout, reach and `file0` conditions). **Typed `--verified`** (S11e6, #419; the cleanup compiler
without `--opt` and self tail calls): an input whose functions all meet the typed per-function
conditions `fnScopeInTB` (`InScopeInT`'s; float data movement, float parameters and returns)
— or, for functions with direct `try_call`s taking `f32`/`f64` parameters or returning
`f32`/`f64` and (S11f, #35) functions with the proven float arithmetic, rounding, conversions and
scalar comparisons, the conditions `fnScopeInTCB` (the structural conjuncts of `fnScopeInTB`
with `Compile.functionETCF` and the decided output check `lowersTCB`: `lowerCheckTCF` on
`lowerFunction`'s output; a function passes under either list) — but not all
`fnScopeInB` is compiled by `Link.DeadCleanup.compileExeT` (the typed branches: on `InScopePT`
`InScopePT`/`leanLink`/`OutOkTCleanup`, else the third branch `leanLink`/`okBCleanupT`), and the
written executable is covered by the typed theorems
`compileExeT_correct`, `compileExeT_correct_peak`, `compileExeT_correct_source`,
`compileExeT_correct_source_peak` (returned values by class) and, through the frontend,
`Front.bundle_correct_rawT{,_peak}`; totality is proven on `InScopeIn` only. `compileExeT`
lowers every function with `lowerFunction`, while the units hold the Stock routes' code
(Cranelift's) where `lean-backend` took them; when some function differs (`stockDiffersB`, #691),
the typed compiler on the Stock route (#722) `Link.SemanticCompilerWith.attemptT` (the Stock
route's pipeline and link `leanLinkProductionWith` on its placement `placedProductionWith`, i.e.
the units' code, accepted by the typed checks `okRWithTS`: the Stock validator on an integer
function, the typed validators on `lowerFunction`'s output) is tried instead; coverage
`attemptT_correct`, `attemptT_correct_depth`, `attemptT_correct_peak` (returned values by
class). When it fails, the smaller set of those functions or of the typed ones (outside
`fnScopeInB`; the executable then takes the integer route) is left out of the region (the
`exclude:` line below). On such an error it
also prints the functions failing a per-function condition (`exclusions`, the line
`--verified: exclude: …`; the typed conditions `fnScopeInTB`, and on a typed input the functions
failing `fnScopeTB` or the output checks `outChksT`): `cargo fv` then links
the executable again with those functions' cg_clif code (left out of the region, outside code
like a fallback) and runs `lean-link` again (T3c).

**`--opt`**: the optimising executable compiler — `Link.DeadCleanup.compileExeOpt` (default) or
`Link.compileExeOpt` (`--no-dead-cleanup`): `compileExe` on the input whose functions the
mid-end optimised (`Link.LinkSpec.opt`: `Opt.optimizeExe` with the proven rule sets, each
optimised function printed to CLIF and used only when it parses back to itself; the functions
where it does not keep their input and are listed, `optFallbacks:`). The input conditions are
decided on the optimised input, the source domain on the original one; coverage:
`compileExeOpt_correct`, `compileExeOpt_correct_peak`, `compileExeOpt_correct_source`,
`compileExeOpt_correct_source_peak`, totality `compileExeOpt_total_reach_input`. The layout is
then the optimised functions' (`placedPar S.opt`, the theorem's `S.withSizes (sizesOf S.opt)`
after `withSizes_opt`; `cargo fv --lean-link --opt-proven-only`, whose units `lean-backend
--opt-proven-only` compiles with the same mid-end).

**Unwinding** (S10f): with the cleanup compiler the tool then decides `Link.DeadCleanup.unwOkB`
on the written executable — the unwind tables rust-lld wrote for the region, found as
libunwind finds them (`.eh_frame_hdr`'s search), are the compiled functions'
(`Link.EhCheck.ehOkR`), and the compiled functions pass the unwinding checks
(`Link.EhCheck.unwFnsB`) — so `compileExeU` succeeds and the coverage adds
`compileExe_correct_unwind`/`_peak` (the exceptional edges; under `--opt`, `compileExeOptU`
succeeds: `compileExeOpt_correct_unwind`/`_peak`, the latter through the mid-end, S10g #404);
otherwise the executable is still written (the theorems above do not depend on unwinding) and
the first failing reason is printed.

**Self tail calls** (S8, #32): with the cleanup compiler and without `--opt`, when a function
`return_call`s itself (`Opt.TailLoop.eligB`), the compiler is `Link.DeadCleanup.compileExeTail`
(`compileExe` on `Link.LinkSpec.tail`: the self tail calls as loops, each transformed function
printed to CLIF and used only when it parses back to itself; the functions where it does not
keep their input, `tailFallbacks:`); coverage: `compileExeTail_correct`,
`compileExeTail_correct_peak` (about the input's program, self `return_call`s included),
totality `compileExeTail_total_reach_input`. Such an input is outside `SrcScopeB` (`linkFreeB`),
so `--verified` rejects it.
-/

open Lean E2E E2E.LinkCheck E2E.Elf Link

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

open Backend in
/-- The program-level per-function input conditions `g` fails (`progScopeB`'s conjuncts, the
indirect-call scope `indB` and the call sites `callScopeB` split by cause); `F`: `P.func?` (a hash
map, `funcMap`). -/
def scopeFails (F : String → Option Clif.Function) (P : Clif.Program) (S : String → Option Nat)
    (g : Clif.Function) : List String :=
  let ind := !indFreeB g
  -- `g`'s facts once (`mayWithB`, `indSigWithB`, `indRetsWithB`, `indToWithB`: T3d)
  let Ds := declSet g
  let D := fun n => Ds.contains n
  let sigs := indSigs g
  let to := indToWithB S (!ind) D sigs g
  let site (s : Clif.Signature) (args : List Nat) : List String :=
    if indSiteWithB P to s args then [] else ["callScopeB:blrRegs"]
  let sites := g.blocks.flatMap fun B =>
    (B.body.flatMap fun st => match st.inst with
      | .call fn args => match g.extern? fn with
        | some e => if dirSiteWithB F e args then [] else ["callScopeB:dirSite"]
        | none => []
      | .callIndirect sg _ args => match g.sigDecls.lookup sg with
        | some s => site s args
        | none => []
      | _ => []) ++
    match B.term with
    | .tryCall fn args _ => match g.extern? fn with
      | some e => if dirSiteWithB F e args then [] else ["callScopeB:dirSite"]
      | none => []
    | .tryCallIndirect _ args et => match g.sigDecls.lookup et.sig with
      | some s => site s args
      | none => []
    | _ => []
  ((if declSigWithB F g then [] else ["declSigB"]) ++
    (if ind && P.funcs.any (fun h => mayWithB S (!ind) D h.name && indSigWithB D sigs h &&
        (match sigParamBytes h.sig with | .ok b => decide (b.length > 8) | .error _ => true))
      then ["indB:calleeStack"] else []) ++
    (if ind && P.funcs.any (fun h => mayWithB S (!ind) D h.name && indSigWithB D sigs h &&
        !indRetsWithB sigs h)
      then ["indB:sretRets"] else []) ++
    sites ++ (if outScopeWithB F g then [] else ["outScopeB"])).eraseDups

/-- The source-domain conditions (`SrcScopeB`'s per-function conjuncts) a parsed function `g` of
the source program fails (`F`: its `func?`, a hash map, `funcMap`). -/
def srcFails (F : String → Option Clif.Function) (g : Clif.Function) : List String :=
  (if Opt.Legalize128.legalOkB g then [] else ["legalOkB"]) ++
    (if linkFreeB g then [] else ["linkFreeB"]) ++ (if declSigWithB F g then [] else ["declSigB"])

/-- **`--verified`: the functions to leave out of the region** (T3c): those failing a
per-function condition of the source domain (`srcFails`), of the input conditions decided on the
CLIF alone (`fnScopeInB`; with `typed`, the typed `fnScopeInTB` — a function passes if it meets
`fnScopeInTB` or the typed-try_call `fnScopeInTCB`, the causes reported are `fnScopeInFailsT`'s
— which holds of every function meeting `fnScopeInB`, `fnScopeInTB_of_fnScopeInB`) or of the
program-level conditions
(`scopeFails`), and `extra` (on a typed input, the functions failing `fnScopeTB` or the output
checks: `typedFails`), when the program-wide conditions hold (`helperFreeB`, distinct names,
`addrSlotsInputB`); `none` otherwise. `cargo fv` links the executable again with their cg_clif
code (outside code, as a fallback's) and runs `lean-link` on it: leaving a function out of the
program only drops conjuncts of the other functions' per-function conditions (each quantifies
over the program's functions), and every condition is decided again on the relinked
executable. `only`: just `extra` (with the program-wide conditions): the typed Stock route's
failures (`typedStockFails`), whose theorem `attemptT_correct` has none of the per-function
conditions above as premises (#754). -/
def exclusions (S SC : LinkSpec) (typed : Bool) (extra : List String := []) (only : Bool := false) :
    Option (List String) :=
  let srcP := S.input0.srcProg
  let P := SC.input0.prog
  let sy := assocMap SC.input0.syms
  let syms := fun n => sy[n]?
  let fm := funcMap P
  let fmS := funcMap srcP
  -- `typed`: a function passes if it meets the typed conditions `fnScopeInTB` or the
  -- typed-try_call ones `fnScopeInTCB`; the reported causes are the T list's
  let fnFails := if typed then
      fun g => if fnScopeInFailsT g = [] || fnScopeInFailsTC g = [] then [] else fnScopeInFailsT g
    else fnScopeInFails
  if !helperFreeB srcP || !Link.nodupB (P.funcs.map (·.name)) || !addrSlotsInputB P syms then none
  else if only then some (Front.dedupFirst extra)
  else
    let src := srcP.funcs.filter fun g => !(srcFails (fun n => fmS[n]?) g).isEmpty
    let fns := (P.funcs.zip (parMap (fun g => fnFails g ++ scopeFails (fun n => fm[n]?) P syms g)
      P.funcs)).filter (!·.2.isEmpty)
    some (Front.dedupFirst (src.map (·.name) ++ fns.map (·.1.name) ++ extra))

/-- On a typed input (`--verified`) whose `compileExeT` fails: the functions failing the typed
per-function conditions of `InScopePT` (`fnScopeTB`), and those whose compiled code fails the
output checks (`OutOkTCleanup`; only when `InScopePT` holds), or, on the third branch (`tc`: the
typed-try_call scope, outside `InScopePT`), the per-function checks of `okBCleanupT` on
`resultsCleanup` (`chksWithT`, with the widened call-site checks `linkChksT`), with the failing
conditions; in `compileExeT`'s std-sized forms (`inScopePTPar`, `outChksTWith`,
`linkChksWithT`: hash maps, the pipeline once in parallel). -/
def typedFails (SC : LinkSpec) (tc : Bool) : List (String × List String) :=
  let I0 := SC.input0
  let fs := if tc then [] else (I0.prog.funcs.zip (parMap fnScopeTB I0.prog.funcs)).filterMap fun (g, b) =>
    if b then none else some (g.name, ["fnScopeTB"])
  if !fs.isEmpty || (!tc && !inScopePTPar I0) then fs
  else if tc then
    -- `okBCleanupTFast`'s per-function checks
    let I := SC.inputCleanup
    let R : Res := parMap (fun fi => (fi.func, I.pipeCleanupOf fi)) I.funcs
    let P := progOf R
    let T := tabOf R
    let C := LinkCtx.of I P T
    let rs := parMap (fun e => (e.1.name, ((staticChksWithT (fun _ => Backend.DeadCleanup.prune) I e.1 e.2 ++
      linkChksWithT C P e.1 e.2 ++
      [("calleeInt", !calleeWithB (fun n => C.callees.contains n) C.anyInd C.S e.1 ||
        e.1.sig.returns.all (·.ty.isInt))]).filter (!·.2)).map (·.1))) R
    rs.filter (!·.2.isEmpty)
  else
    let Rs := Link.DeadCleanup.parResultsCleanupT I0
    let I := I0.withDepth Rs
    let P := progOf Rs
    let m := funcMap P
    let sy := assocMap I.syms
    let cs := calleeSet P
    let anyInd := P.funcs.any (!indFreeB ·)
    let rs := parMap (fun e => (e.1.name, ((outChksTWith (fun n => m[n]?) (fun n => sy[n]?)
      (fun n => cs.contains n) anyInd P e.1 e.2).filter (!·.2)).map (·.1))) Rs
    rs.filter (!·.2.isEmpty)

/-- Whether `lean-backend` compiled `g` with a Stock lowering other than `lowerFunction` (#691):
as it does, `lower` (the Stock routes, `lowerCheckedParameterCfgNI`'s chain) on a function
without `try_call` (`compileFileParameterCfgNIWhen`), and a different `VCode` from
`lowerFunction`'s (`Stock.D0.defaultLower`, `pipeCleanupT`'s); a function on which `lower`
fails takes `lowerFunction` in both. -/
def stockDiffersB (lower : Clif.Function → Except String Backend.VCode) (g : Clif.Function) : Bool :=
  !(g.blocks.any fun b => b.term.isTry) &&
    match lower g with
    | .error _ => false
    | .ok vc => match Backend.Stock.D0.defaultLower g with
      | .ok vl => !decide (vc = vl)
      | .error _ => true

/-- On a typed input whose `Link.SemanticCompilerWith.attemptT lower SP` fails (#722): the
functions failing the per-function checks of `okRWithTS` on the Stock route's results
(`chksWithTS` in `okRWithTSFast`'s std-sized form: `staticChksWithTS` and the class-aware
`linkChksWithTS`, #742), with the failing conditions, and the failing global checks (as
`<global>`). -/
def typedStockFails (lower : Clif.Function → Except String Backend.VCode) (SP : LinkSpec) :
    List (String × List String) :=
  let I := SP.inputProductionWith lower true
  let R : Res := parMap (fun fi => (fi.func, I.pipeProductionWith lower true fi)) I.funcs
  let P := progOf R
  let T := tabOf R
  let C := LinkCtx.of I P T
  let gl := ((globalChksWith C I P T).filter (!·.2)).map (·.1)
  let rs := parMap (fun e => (e.1.name, ((staticChksWithTS (productionStage true) I e.1 e.2 ++
      linkChksWithTS C P e.1 e.2).filter (!·.2)).map (·.1))) R
  (if gl.isEmpty then [] else [("<global>", gl)]) ++ rs.filter (!·.2.isEmpty)

/-- Print `exclusions` (the line `cargo fv` reads). -/
def printExclusions (exe : String) (S SC : LinkSpec) (typed : Bool) (extra : List String := [])
    (only : Bool := false) : IO Unit :=
  match exclusions S SC typed extra only with
  | some (n :: ns) => IO.eprintln s!"lean-link: {exe}: --verified: exclude: {" ".intercalate (n :: ns)}"
  | _ => pure ()

/-- `--key VALUE` taken out of an argument list. -/
def takeOpt (key : String) : List String → Option String × List String
  | k :: v :: rest =>
    if k == key then (some v, rest) else let (o, r) := takeOpt key (v :: rest); (o, k :: r)
  | l => (none, l)

/-- **`lean-ld`'s plan against the link spec** (`--ld FILE`, `FILE`: `lean-ld`'s arguments, one
per line): links again (`Link.Ld.link`, deterministic), checks that its output is `file0` and
decides `Plan.specOkB`, the premise of `Link.Ld.file0OkB_ld` and the `…_total_ld` theorems;
on failure, the failing conjuncts. -/
def ldCheck (P : LinkSpec) (file0 : ByteArray) (f : String) : IO (Except String Unit) := do
  let args := ((← IO.FS.readFile f).splitOn "\n").filter (!·.isEmpty)
  match ← Link.Ld.parseLdArgs args with
  | .error e => return .error s!"lean-ld's arguments: {e}"
  | .ok c => match Link.Ld.link c.opts c.ins with
    | .error e => return .error s!"lean-ld: {e}"
    | .ok r =>
      if r.img.write.data != file0.data then return .error "lean-ld's output is not the executable read"
      let pl := r.plan
      if pl.specOkB P then return .ok ()
      let pa := pl.pieces.toArray
      let am := addrMap P.input0.addrs
      let bad := P.data.filter fun o =>
        !Link.Ld.objPlanB am pl pa (Link.Ld.pieceHint pa) (offsetOf pl.phdrs P.R) P.size o
      let fails := (if pl.regionInB P.R P.size then [] else ["regionInB"]) ++
        (if Link.Ld.symsPlanB P.input0 pl then [] else ["symsPlanB"]) ++
        (if Link.Ld.tlsBoundB P pl then [] else ["tlsBoundB"]) ++
        (if bad.isEmpty then [] else [s!"dataPlanB ({bad.length} object(s): {(bad.take 3).map (·.name)})"])
      return .error s!"Plan.specOkB fails: {fails}"

/-- **`compileExe_total_ldIn`'s premises on `lean-ld`'s inputs** (`--ld FILE`; the cleanup
compiler on `S0`, before the layout): resolution and `--gc-sections`, `layRefsB`, `relsInB`,
`fitsB`, `specPreB`, the compiler's input conditions on the link spec at the placement's symbols
(`Link.DeadCleanup.ldSpec`), decided on the inputs without linking; and whether that link spec's
addresses are `S0`'s (`LinkSpec.atSyms`), so that it is the spec compiled, `SC` (`ldSpec_self`)
and the executable compiled is the theorem's (`relsInB` by `relsInFastB`, `reachOkB` by
`reachOkMap`: equal, `relsInFastB_eq`, `reachOkMap_eq`). On failure, the failing conditions; on
success, each condition's time. -/
def ldInCheck (S0 SC : LinkSpec) (f : String) : IO (Except String String) := do
  let args := ((← IO.FS.readFile f).splitOn "\n").filter (!·.isEmpty)
  match ← Link.Ld.parseLdArgs args with
  | .error e => return .error s!"lean-ld's arguments: {e}"
  | .ok c =>
    let o := c.opts
    let roots := o.entry :: o.undefs
    match Link.Ld.resolve roots c.ins with
    | .error e => return .error s!"resolve: {e}"
    | .ok st => match st.gc roots o.gc with
      | .error e => return .error s!"gc: {e}"
      | .ok g =>
        let t0 ← IO.monoMsNow
        let S1 := S0.atSyms ((Link.Ld.layPre o st g).syms o st g).1
        let same ← IO.lazyPure fun _ => decide (S1.R = S0.R) && decide (S1.outside = S0.outside)
        -- `SC` is `placed S0` (`Link.DeadCleanup.placedPar_eq`), so with `S0`'s own addresses `ldSpec S0 o st g = SC`
        -- (`Link.DeadCleanup.ldSpec_self`): the premises are decided on the spec compiled
        let P := if same then SC else Link.DeadCleanup.placedPar S1
        let checks : List (String × (Unit → Bool)) := [("layRefsB", fun _ => Link.Ld.layRefsB o st g),
          ("relsInB", fun _ => Link.Ld.relsInFastB o st g), ("fitsB", fun _ => Link.Ld.fitsB o st g),
          ("specPreB", fun _ => Link.Ld.specPreB P o st g), ("InScopeIn", fun _ => inScopeInPar P.input0),
          ("layoutOkB", fun _ => P.layoutOkB), ("reachOkB", fun _ => P.reachOkMap),
          ("atSyms (the compiled spec's addresses)", fun _ => same)]
        let mut fails : List String := []
        let mut times : List String := [s!"resolve, gc, atSyms {(← IO.monoMsNow) - t0} ms"]
        for (n, c) in checks do
          let t0 ← IO.monoMsNow
          let b ← IO.lazyPure c
          times := times ++ [s!"{n} {(← IO.monoMsNow) - t0} ms"]
          if !b then fails := fails ++ [n]
        if fails.isEmpty then return .ok s!"{", ".intercalate times}"
        else return .error s!"failing: {fails}"

def main (args0 : List String) : IO UInt32 := do
  let usage := "usage: lean-link DIR [--dead-cleanup|--no-dead-cleanup] [--opt] [--verified] [--ld FILE]"
  let (ldFile, args) := takeOpt "--ld" args0
  let flags := args.filter (·.startsWith "--")
  if flags.any (fun a => !["--dead-cleanup", "--no-dead-cleanup", "--opt", "--verified"].contains a) ||
      (flags.contains "--dead-cleanup" && flags.contains "--no-dead-cleanup") then
    IO.eprintln usage; return 2
  let deadCleanup := !flags.contains "--no-dead-cleanup"
  let verified := flags.contains "--verified"
  let opt := flags.contains "--opt"
  let [d] := args.filter (!·.startsWith "--") | do IO.eprintln usage; return 2
  let dir : System.FilePath := d
  let (b0, exe) ← try Front.readBundle dir []
    catch e => do IO.eprintln s!"lean-link: {e}"; return 2
  -- `buildSpec` takes a size per function (every region function has a marker); the layout below
  -- replaces them by the compiled code's
  let S ← match Front.buildSpec { b0 with sizes := b0.markers.map fun (n, _) => (n, 0) } with
    | .ok S => pure S
    | .error e => do IO.eprintln s!"lean-link: {exe}: {e}"; return 1
  -- the compiler's input: the optimised one under `--opt` (`compileExeOpt S = compileExe S.opt`),
  -- the self tail calls as loops when a function has one (`compileExeTail S = compileExe S.tail`),
  -- with the Lean compiler's layout (`placedPar = placed`: the totality theorems' layout)
  let tailOn := deadCleanup && !opt && S.funcs.any (fun fi => Opt.TailLoop.eligB fi.func)
  let SC0 := if opt then S.opt else if tailOn then S.tail else S
  let SC := if deadCleanup then Link.DeadCleanup.placedPar SC0 else SC0.placedPar
  let names := SC.names
  let R := SC.R
  let file0 ← IO.FS.readBinFile exe
  let summary := s!"{names.length} function(s), {SC.data.length} data object(s), region {hex R}..{hex (R + SC.size)} ({SC.size} bytes)"
  let compile := if deadCleanup then Link.DeadCleanup.compileExe else Link.compileExe
  let link := if deadCleanup then Link.DeadCleanup.leanLink else Link.leanLink
  let thm (s : String) := (if deadCleanup then "Link.DeadCleanup." else "Link.") ++ s
  let exeName := if opt then "compileExeOpt" else if tailOn then "compileExeTail" else "compileExe"
  let theoremName := thm s!"{exeName}_correct"
  let compilerName := thm exeName
  let linkerName := if deadCleanup then "Link.DeadCleanup.leanLink" else "Link.leanLink"
  if opt then
    let fb := Link.optFallbacksWith S.funcs SC0.funcs
    IO.println s!"lean-link: {exe}: --opt: optFallbacks: {fb.length} of {S.funcs.length} function(s) {fb.take 5}"
  if tailOn then
    let fb := S.tailFallbacks
    IO.println s!"lean-link: {exe}: self tail calls as loops: {S.tailLoops.length} function(s) {S.tailLoops.take 5}, tailFallbacks: {fb.length} {fb.take 5}"
  -- the source domain (`SrcScopeB` reads the parsed functions only, so `S.input0`'s is the
  -- compiler's input's)
  let I := S.input0
  let srcOk := SrcScopeB I
  -- the typed scope under `--verified` (S11e6): the cleanup compiler `compileExeT`
  let typedOk := deadCleanup && !opt && !tailOn
  if verified && !srcOk then
    let P := I.srcProg
    let fmS := funcMap P
    let bad := P.funcs.filterMap fun g => match srcFails (fun n => fmS[n]?) g with
      | [] => none
      | fs => some (g.name, fs)
    IO.eprintln s!"lean-link: {exe}: --verified: outside the source domain (SrcScopeB): {bad.length} function(s) failing legalOkB/linkFreeB/declSigB {(bad.take 3).map (·.1)}, helperFreeB {helperFreeB P}; not written"
    for (n, fs) in bad do
      IO.eprintln s!"lean-link:   {n}: {fs}"
    printExclusions exe S SC typedOk
    return 1
  -- the input conditions decided on the CLIF alone (`fnScopeInB`, `addrSlotsInputB`); with
  -- `InScopeP`'s other program conditions, which `compile` checks, `InScopeIn`; with the cleanup
  -- compiler, an input outside `fnScopeInB` whose functions all meet the typed `fnScopeInTB`
  -- (`InScopeInT`'s) is compiled by `compileExeT` (`typedV`)
  let mut typedV := false
  let mut typedN := 0
  if verified then
    let P := SC.input0.prog
    let sy := assocMap SC.input0.syms
    let syms := fun n => sy[n]?
    if !addrSlotsInputB P syms then
      IO.eprintln s!"lean-link: {exe}: --verified: outside the input conditions (InScopeIn): addrSlotsInputB fails (an indirect call, a function with an address and stack slots, no program callee with slots); not written"
      return 1
    let bad := P.funcs.filterMap fun g => match fnScopeInFails g with
      | [] => none
      | fs => some (g.name, fs)
    let badT := if typedOk && !bad.isEmpty then
        (P.funcs.zip (parMap (fun g => match fnScopeInFailsT g with
            | [] => []
            | fs => if fnScopeInFailsTC g = [] then [] else fs) P.funcs)).filterMap fun (g, fs) =>
          match fs with
          | [] => none
          | fs => some (g.name, fs)
      else bad
    if !bad.isEmpty && typedOk && badT.isEmpty then
      typedV := true
      typedN := bad.length
      IO.println s!"lean-link: {exe}: --verified: typed scope (InScopeInT): {bad.length} function(s) outside fnScopeInB meet fnScopeInTB/fnScopeInTCB {(bad.take 3).map (·.1)}"
    else if !badT.isEmpty then
      let scopeN := if typedOk then "fnScopeInTB/fnScopeInTCB" else "fnScopeInB"
      let causes := (badT.flatMap (·.2)).eraseDups.map fun c => s!"{c} {(badT.filter (·.2.contains c)).length}"
      IO.eprintln s!"lean-link: {exe}: --verified: outside the input conditions (InScopeIn{if typedOk then "T" else ""}): {badT.length} function(s) failing {scopeN} (by cause: {causes}) {(badT.take 3).map (·.1)}; not written"
      for (n, fs) in badT do
        IO.eprintln s!"lean-link:   {n}: {fs}"
      printExclusions exe S SC typedOk
      return 1
  -- The checked semantic provider handles a CFG function alongside retained
  -- try-call functions. Recompiling that mixed program only through the old
  -- provider can require a different region size from the emitted objects.
  -- Other exception, optimizer and tail-call variants retain their routes;
  -- typed `--verified` (S11e6) keeps its own route below.
  let hasCfg := SC0.funcs.any (fun fi => (((Backend.Stock.ParameterCfg.eligible fi.func || Backend.Stock.ConditionalForwardCfg.eligible fi.func) || Backend.Stock.ConditionalCfg.eligible fi.func) || Backend.Stock.ForwardCfg.eligible fi.func || Backend.Stock.LinearCfg.eligible fi.func || Backend.Stock.TwoBlock.Entry.eligible fi.func))
  let stockEnabled := !typedV && !opt && !tailOn && SC0.funcs.any (fun fi => (((Backend.Stock.ParameterCfg.eligible fi.func || Backend.Stock.ConditionalForwardCfg.eligible fi.func) || Backend.Stock.ConditionalCfg.eligible fi.func) || Backend.Stock.ForwardCfg.eligible fi.func || Backend.Stock.LinearCfg.eligible fi.func || Backend.Stock.TwoBlock.Entry.eligible fi.func) || Backend.Stock.Scalar.activationEligible fi.func || Backend.Stock.Logical.activationEligible fi.func || Backend.Stock.Mixed.activationEligible fi.func || Backend.Stock.Arithmetic.eligible fi.func || Backend.Stock.ScalarAdd.activationEligible fi.func) &&
    (hasCfg || !(SC0.funcs.any fun fi => fi.func.blocks.any fun b => b.term.isTry)) &&
    -- #739: every route's `attempt` first checks `inScopePar` (`inScopeInPar` without the
    -- cleanup) of its placed spec, whose per-function conjunct `fnScopeB` (`fnScopeInB`) does not
    -- read the placement; when it fails, all routes fail and `compileWithRoutes` is `compile SC`,
    -- so skip the routes' placements (each one the full pipeline)
    (parMap (if deadCleanup then fnScopeB else fnScopeInB) SC0.input0.prog.funcs).all id
  let routes := [Backend.Stock.ParameterCfg.lowerValidated,Backend.Stock.ConditionalForwardCfg.lowerValidated,Backend.Stock.ConditionalCfg.lowerValidated,Backend.Stock.ForwardCfg.lowerValidated,Backend.Stock.LinearCfg.lowerValidated,Backend.Stock.TwoBlock.Entry.lowerValidated,Backend.Stock.TwoBlock.lowerValidated,Backend.Stock.Scalar.lowerValidated,Backend.Stock.Logical.lowerValidated,Backend.Stock.Mixed.lowerValidated,
    Backend.Stock.Arithmetic.lowerValidated]
  -- typed `--verified`: `compileExeT` (S11e6, #419)
  if typedV then
    -- #691: the region object rust-lld placed holds the units' code as `lean-backend` compiled
    -- it: the Stock routes (Cranelift's code; `routes`' first, falling back to `lowerFunction`)
    -- on a function without `try_call`, `lowerFunction` on the others. `compileExeT` lowers
    -- every function with `lowerFunction` (`pipeCleanupT`), so on a function where the two
    -- lowerings differ its layout is not the one reserved (`placeOkB`, `regionOkB`) and its
    -- code not the units'. Leave out of the region the smaller of the two sets, then link again
    -- (`cargo fv`): those functions (they keep cg_clif's code, as outside code), or the typed
    -- functions (outside `fnScopeInB`; the executable then takes the integer route below).
    let stockFns := (SC.funcs.zip (parMap (fun fi => stockDiffersB routes[0]! fi.func) SC.funcs)).filterMap
      fun (fi, b) => if b then some fi.func.name else none
    if !stockFns.isEmpty then
      -- #722: the typed compiler on the Stock route: the units' code (the Stock route's pipeline
      -- and placement), the typed checks per function
      let SP := SC0.placedProductionWith routes[0]! true
      let att := SemanticCompilerWith.attemptT routes[0]! SP file0
      if let .ok file := att then
        IO.FS.writeBinFile exe file
        IO.println s!"lean-link: {exe}: {summary} written by Link.SemanticCompilerWith.attemptT (Link.SemanticCompilerWith.attemptT_correct); {stockFns.length} function(s) Stock-lowered, {typedN} typed function(s) in the region"
        if let some f := ldFile then
          match ← ldCheck SP file0 f with
          | .ok () => IO.println s!"lean-link: {exe}: lean-ld's plan meets the link spec (Plan.specOkB)"
          | .error e => IO.eprintln s!"lean-link: {exe}: lean-ld's plan: {e}"
        IO.println s!"lean-link: {exe}: coverage: Link.SemanticCompilerWith.attemptT_correct, Link.SemanticCompilerWith.attemptT_correct_depth, Link.SemanticCompilerWith.attemptT_correct_peak (returned values by class); about the legalised program; input in InScopeInT (typed scope; totality proven on InScopeIn only) (--verified)"
        return 0
      if let .error e := att then
        let bad := typedStockFails routes[0]! SP
        let causes := (bad.flatMap (·.2)).eraseDups.map fun c => s!"{c} {(bad.filter (·.2.contains c)).length}"
        IO.eprintln s!"lean-link: {exe}: --verified: typed Stock route (attemptT): {e}: {bad.length} function(s) failing (by cause: {causes}) {(bad.take 3).map (·.1)}"
        for (n, fs) in bad.take 50 do
          IO.eprintln s!"lean-link:   {n}: {fs}"
        -- leave out only the functions failing the typed checks when that set is the smallest
        -- (only those: `attemptT_correct` has no per-function input premise, #754)
        let badFns := (bad.filter (·.1 != "<global>")).map (·.1)
        if !badFns.isEmpty && badFns.length < min typedN stockFns.length then
          IO.eprintln s!"lean-link: {exe}: --verified: typed Stock route: leaving out the {badFns.length} function(s) failing the typed checks; not written"
          printExclusions exe S SC true badFns (only := true)
          return 1
      let typedSmaller := typedN ≤ stockFns.length
      IO.eprintln s!"lean-link: {exe}: --verified: typed scope: {stockFns.length} function(s) compiled by the Stock lowering, which compileExeT does not reproduce (lowerFunction) {stockFns.take 3}; leaving out {if typedSmaller then s!"the {typedN} typed function(s)" else s!"those {stockFns.length}"}; not written"
      if typedSmaller then printExclusions exe S SC false
      else printExclusions exe S SC true stockFns
      return 1
    match Link.DeadCleanup.compileExeT SC file0 with
    | .ok file =>
      IO.FS.writeBinFile exe file
      IO.println s!"lean-link: {exe}: {summary} written by Link.DeadCleanup.compileExeT (Link.DeadCleanup.compileExeT_correct)"
      IO.println s!"lean-link: {exe}: coverage: Link.DeadCleanup.compileExeT_correct, Link.DeadCleanup.compileExeT_correct_peak (returned values by class); the original (pre-i128-legalisation) program, in SrcScopeB: Link.DeadCleanup.compileExeT_correct_source, Link.DeadCleanup.compileExeT_correct_source_peak; cg_clif's program: Front.bundle_correct_rawT, Front.bundle_correct_raw_peakT; input in InScopeInT (typed scope; totality proven on InScopeIn only) (--verified)"
      IO.println s!"lean-link: {exe}: exceptional edges not covered (typed scope: compileExeU is integer-only)"
      IO.println s!"lean-link: {exe}: unwinding conditions: {Link.DeadCleanup.unwReport SC file}"
      return 0
    | .error e =>
      if e != Link.DeadCleanup.outOkTMsg && e != Link.DeadCleanup.outOfScopeTMsg &&
          e != Link.DeadCleanup.outOkTCMsg then
        IO.eprintln s!"lean-link: {exe}: {e}"
        return 1
      let bad := typedFails SC (e == Link.DeadCleanup.outOkTCMsg)
      let causes := (bad.flatMap (·.2)).eraseDups.map fun c => s!"{c} {(bad.filter (·.2.contains c)).length}"
      IO.eprintln s!"lean-link: {exe}: --verified: typed scope: {e}: {bad.length} function(s) failing (by cause: {causes}) {(bad.take 3).map (·.1)}; not written"
      for (n, fs) in bad do
        IO.eprintln s!"lean-link:   {n}: {fs}"
      printExclusions exe S SC true (bad.map (·.1))
      return 1
  let compiled := if stockEnabled then SemanticCompilerWith.compileWithRoutes routes SC0 file0 deadCleanup
    else (compile SC file0).map fun file => (⟨file,none⟩ : SemanticCompilerWith.RoutedOutput)
  match compiled with
  | .ok out =>
    let file := out.file
    if out.route.isSome then
      let actualLower := (routes[out.route.getD 0]?).getD Backend.Stock.Arithmetic.lowerValidated
      let SP := SC0.placedProductionWith actualLower deadCleanup
      IO.FS.writeBinFile exe file
      IO.println s!"lean-link: {exe}: {summary} written by Link.SemanticCompilerWith.compileWithRoutes (Link.SemanticCompilerWith.compileWithRoutes_spec, Link.SemanticCompilerWith.attempt_correct)"
      if let some f := ldFile then
        match ← ldCheck SP file0 f with
        | .ok () => IO.println s!"lean-link: {exe}: lean-ld's plan meets the link spec (Plan.specOkB); retained legacy acceptance: Link.SemanticCompilerWith.compileWithRoutes_accepts_legacy"
        | .error e => IO.eprintln s!"lean-link: {exe}: lean-ld's plan: {e}"
      let src := if srcOk then
          "; the original (pre-i128-legalisation) program, in SrcScopeB: Link.SemanticCompilerWith.attempt_correct_source, Link.SemanticCompilerWith.attempt_correct_source_peak"
        else "; outside SrcScopeB: about the legalised program only"
      let scope := if verified then "; input in InScopeIn (--verified)" else ""
      IO.println s!"lean-link: {exe}: coverage: Link.SemanticCompilerWith.attempt_correct, Link.SemanticCompilerWith.attempt_correct_depth, Link.SemanticCompilerWith.attempt_correct_peak{src}{scope}"
      return 0
    -- the unwind tables (S10f): with the cleanup compiler, `compileExeU SC file0 = .ok file`
    let unwOk := deadCleanup && Link.DeadCleanup.unwOkB SC file
    IO.FS.writeBinFile exe file
    IO.println s!"lean-link: {exe}: {summary} written by {compilerName} ({theoremName})"
    let src := if srcOk then
        s!"; the original (pre-i128-legalisation) program, in SrcScopeB: {thm s!"{exeName}_correct_source"}, {thm s!"{exeName}_correct_source_peak"}"
      else "; outside SrcScopeB: about the legalised program only"
    let total := if deadCleanup || opt then thm s!"{exeName}_total_reach_input" else "Link.compileExe_total_reach"
    -- `file0` linked by `lean-ld`: its plan against the link spec (`file0OkB_ld`)
    let totalLd := thm s!"{exeName}_total_ld"
    let ldOk ← match ldFile with
      | none => pure false
      | some f => do
        let t0 ← IO.monoMsNow
        match ← ldCheck SC file0 f with
        | .ok () =>
          IO.println s!"lean-link: {exe}: lean-ld's plan meets the link spec (Plan.specOkB, {(← IO.monoMsNow) - t0} ms): file0OkB by Link.Ld.file0OkB_ld; totality without checks of the linker's output: {totalLd}"
          -- the plain cleanup compiler: the premises of `compileExe_total_ldIn` on the inputs
          if deadCleanup && !opt && !tailOn then
            let t1 ← IO.monoMsNow
            match ← ldInCheck SC0 SC f with
            | .ok times => IO.println s!"lean-link: {exe}: lean-ld's inputs meet the input conditions ({(← IO.monoMsNow) - t1} ms: {times}): totality decided on the inputs, without linking: Link.DeadCleanup.compileExe_total_ldIn"
            | .error e => IO.eprintln s!"lean-link: {exe}: lean-ld's inputs: compileExe_total_ldIn's premises: {e}"
          pure true
        | .error e =>
          IO.eprintln s!"lean-link: {exe}: lean-ld's plan: {e} (totality only with the checks of file0, {total})"
          pure false
    let totalAll := if ldOk then s!"{total}; on lean-ld's output {totalLd}" else total
    let scope := if verified then s!"; input in InScopeIn (totality: {totalAll}) (--verified)" else ""
    -- the exceptional edges: `compileExeU SC0 file0 = .ok file` (`compileExeOptU S` under `--opt`)
    let unw := if unwOk && !tailOn then
        if opt then
          s!"; exceptional edges: {thm "compileExeOpt_correct_unwind"}, {thm "compileExeOpt_correct_unwind_peak"}"
        else s!"; exceptional edges: {thm "compileExe_correct_unwind"}, {thm "compileExe_correct_unwind_peak"}"
      else ""
    IO.println s!"lean-link: {exe}: coverage: {thm s!"{exeName}_correct"}, {thm s!"{exeName}_correct_peak"}{src}{scope}{unw}"
    if deadCleanup && !unwOk then
      IO.println s!"lean-link: {exe}: exceptional edges not covered (unwOkB: {Link.DeadCleanup.unwFail SC file})"
    -- report only (S10g, #404): the unwinding conditions of the totality argument, measured
    if deadCleanup && !tailOn then
      IO.println s!"lean-link: {exe}: unwinding conditions: {Link.DeadCleanup.unwReport SC file}"
    return 0
  | .error e =>
    if e != outOfScopeMsg && e != outOfScopeInMsg then
      IO.eprintln s!"lean-link: {exe}: {e}"
      return 1
    -- outside `compileExe`'s input conditions: the executable is not covered by
    -- `compileExe_correct`; `Link.leanLink` still links it (its checks, the per-crate proof),
    -- except under `--verified`
    let P := SC.input0.prog
    let sy := assocMap SC.input0.syms
    let syms := fun n => sy[n]?
    let fm := funcMap P
    let bad := P.funcs.filterMap fun g => match scopeFails (fun n => fm[n]?) P syms g with
      | [] => none
      | fs => some (g.name, fs)
    let causes := (bad.flatMap (·.2)).eraseDups.map fun c => s!"{c} {(bad.filter (·.2.contains c)).length}"
    let scopeName := if e == outOfScopeInMsg then "InScopeIn" else "InScopeP"
    let fnScope := if e == outOfScopeInMsg then "fnScopeInB" else "fnScopeB"
    let what := if verified then "--verified: not written" else s!"linking with {linkerName} (outside {theoremName} scope)"
    IO.eprintln s!"lean-link: {exe}: outside compileExe's input conditions ({scopeName}): {bad.length} function(s) failing the program-level per-function conditions (by cause: {causes}) {(bad.take 3).map (·.1)}, distinct names {decide (P.funcs.map (·.name)).Nodup}, {if e == outOfScopeInMsg then s!"addrSlotsInputB {addrSlotsInputB P syms}" else s!"addrSlotsInB {addrSlotsInB P syms}"} (else {fnScope}); {what}"
    for (n, fs) in bad do
      IO.eprintln s!"lean-link:   {n}: {fs}"
    if verified then
      printExclusions exe S SC typedOk
      return 1
    -- #734 (#691 without `--verified`): where `lean-backend` compiled a function with the Stock
    -- lowering (`stockDiffersB`), the typed compilers and `link SC` (`lowerFunction` on every
    -- function) reproduce neither the units' code nor the layout rust-lld reserved for it; the
    -- bare Lean linker then links on the Stock placement (`compileWithRoutes`' routes in order)
    let stockFns := if !opt && !tailOn then
        (SC.funcs.zip (parMap (fun fi => stockDiffersB routes[0]! fi.func) SC.funcs)).filterMap
          fun (fi, b) => if b then some fi.func.name else none
      else []
    -- the typed scope (S11, #35; under `--verified` taken above when every function meets
    -- `fnScopeInTB`): first `compileExeT3 SC file0 = .ok file` on the decided input conditions
    -- `InScopeInT3` (no run-time decider), else `compileExeT` on `InScopePT`; both with the
    -- output checks `OutOkTCleanup`
    if deadCleanup && !opt && !tailOn && stockFns.isEmpty then
      match Link.DeadCleanup.compileExeT3 SC file0 with
      | .ok file =>
        IO.FS.writeBinFile exe file
        IO.println s!"lean-link: {exe}: {summary} written by Link.DeadCleanup.compileExeT3 (Link.DeadCleanup.compileExeT3_correct)"
        IO.println s!"lean-link: {exe}: coverage: Link.DeadCleanup.compileExeT3_correct (typed scope InScopeInT3, OutOkTCleanup; returned values by class)"
        return 0
      | .error e3 =>
        IO.eprintln s!"lean-link: {exe}: decider-free typed scope: {e3}"
        match Link.DeadCleanup.compileExeT SC file0 with
        | .ok file =>
          IO.FS.writeBinFile exe file
          IO.println s!"lean-link: {exe}: {summary} written by Link.DeadCleanup.compileExeT (Link.DeadCleanup.compileExeT_correct)"
          IO.println s!"lean-link: {exe}: coverage: Link.DeadCleanup.compileExeT_correct (typed scope InScopePT, OutOkTCleanup; returned values by class)"
          return 0
        | .error e => IO.eprintln s!"lean-link: {exe}: typed scope: {e}"
    if !stockFns.isEmpty then
      IO.eprintln s!"lean-link: {exe}: {stockFns.length} function(s) compiled by the Stock lowering, which the typed compilers and {linkerName} do not reproduce (lowerFunction) {stockFns.take 3}; linking on the Stock placement"
      for (lower, i) in routes.zipIdx do
        match Link.leanLinkProductionWith lower (SC0.placedProductionWith lower deadCleanup) file0 deadCleanup with
        | .ok file =>
          IO.FS.writeBinFile exe file
          IO.println s!"lean-link: {exe}: {summary} written by Link.leanLinkProductionWith (Stock route {i})"
          IO.println s!"lean-link: {exe}: coverage: none (outside {scopeName}; Link.leanLinkProductionWith, no compiler theorem)"
          return 0
        | .error e => IO.eprintln s!"lean-link: {exe}: Stock route {i}: {e}"
      return 1
    match link SC file0 with
    | .error e => do IO.eprintln s!"lean-link: {exe}: {e}"; return 1
    | .ok file =>
      IO.FS.writeBinFile exe file
      IO.println s!"lean-link: {exe}: {summary} written by {linkerName}"
      IO.println s!"lean-link: {exe}: coverage: none (outside {scopeName}; {linkerName}, no compiler theorem)"
      return 0

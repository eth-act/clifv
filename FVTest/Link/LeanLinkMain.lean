import FV.Link.TypedCompileSourceModes
import FV.E2E.LinkIdxSig
import FV.Link.ReturnPinExeSourceWith
import FV.Backend.Lowering.StockMemorySinkExtNI
import FV.Link.Compile
import FV.Link.DeadCleanupCompile
import FV.Link.DeadCleanupCompileT3
import FV.Link.TailCompile
import FV.Link.OptCompile
import FV.Link.ConstPhiCompile
import FV.Link.Placed
import FV.E2E.SrcScopeDefs
import FV.E2E.SrcScopeFastT
import FV.Front.Read
import FV.E2E.LinkScopeInputDefs
import FV.E2E.LinkScopeInputDefsT
import FV.E2E.LinkScopeInputDefsTC
import FV.Link.Ld.Spec
import FV.Link.Ld.DataFast
import FV.Link.ReachCheck
import FV.Link.Ld.SpecTotal
import FV.Link.Ld.RelsFast
import FVTest.Link.LdArgs
import FV.Link.ExeUCompile
import FV.Link.SemanticCompileDefs
import FV.Link.UnwReport
import FV.Link.SemanticCompileT
import FV.E2E.SrcScopeFast
import FV.Link.TypedStockShared
import FV.Front.BundleFast
import FV.Link.MidPair

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
`compileExe_correct_sourceCp` and `compileExe_correct_source_peakCp` about the bundle's program
(before the `i128` legalisation and constant-phi removal). No per-crate proof needed.

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
`InScopeP` is an error and the executable is not written. Every executable it writes is covered
by the theorems its `coverage:` line names for the route that wrote it (#1096): the ReturnPin
route `Link.ReturnPinCompilerWith.attempt_correct{,_depth}`, the Stock routes
`Link.SemanticCompilerWith.attempt_correct{,_depth,_peak}`, the typed Stock route
`…attemptT_correct{,_depth,_peak}`, the typed fallback `Link.TypedCompilerWith.attempt_correct…`,
the plain compiler the four theorems above (each with its `…Cp` source theorems where
printed); only the plain compiler's input is claimed in `InScopeIn` with a totality theorem
(`Link.DeadCleanup.compileExe_total_reach_input`, `Link.compileExe_total_reach`, given the
layout, reach and `file0` conditions): the routes have none. **Typed `--verified`** (S11e6, #419; the cleanup compiler
without `--opt` and self tail calls): an input whose functions all meet the typed per-function
conditions `fnScopeInTB` (`InScopeInT`'s; float data movement, float parameters and returns)
— or, for functions with direct `try_call`s taking `f32`/`f64` parameters or returning
`f32`/`f64` and (S11f, #35) functions with the proven float arithmetic, rounding, conversions and
scalar comparisons, the conditions `fnScopeInTCB` (the structural conjuncts of `fnScopeInTB`
with `Compile.functionETCF` and the decided output checks `lowersTCB`: `lowerCheckTCF` on
`lowerFunction`'s output, and `sizeOutB` where the input-side size bound `sizeOkB` fails, #1057;
a function passes under either list) — but not all
`fnScopeInB` is compiled by `Link.DeadCleanup.compileExeT` (the typed branches: on `InScopePT`
`InScopePT`/`leanLink`/`OutOkTCleanup`, else the third branch `leanLink`/`okBCleanupT`), and the
written executable is covered by the typed theorems
`compileExeT_correct`, `compileExeT_correct_peak`, `compileExeT_correct_sourceCp`,
`compileExeT_correct_source_peakCp` (returned values by class) and, through the frontend,
`Front.bundle_correct_rawTCp`, `Front.bundle_correct_raw_peakTCp` (#1088: about cg_clif's
program, at `buildSpec`'s spec `S0` of the bundle read and the compiled spec, whose functions are
`S0`'s constant-phi removals, `Front.placedFrom_cp_funcs`; `Front.bundle_correct_rawT{…}` take
`compileExeT` of `S0` itself, which is not what runs when constant-phi removal changes a function);
totality is proven on `InScopeIn` only. `compileExeT`
lowers every function with `lowerFunction`, while the units hold the Stock routes' code
(Cranelift's) where `lean-backend` took them; when some function differs (`stockDiffersB`, #691),
the typed compiler on the Stock route (#722) `Link.SemanticCompilerWith.attemptT` (the Stock
route's pipeline and link `leanLinkProductionWith` on its placement `placedProductionWith`, i.e.
the units' code, accepted by the typed checks `okRWithTS`: the Stock validator on an integer
function, the typed validators on `lowerFunction`'s output) is tried instead; coverage
`attemptT_correct`, `attemptT_correct_depth`, `attemptT_correct_peak` (returned values by
class), and for a bundle in `SrcScopeB` `attemptT_correct_sourceCp`, `attemptT_correct_source_peakCp`
(#1100; `hcp` by `TypedStockShared.stockSteps_placed` and `rfl`). When it fails, the smallest of: the functions failing its typed checks, the functions
whose placed code is not the units' (their span to the next function is not rust-lld's,
`spanFails`, #1075; its link checks name the failing check and objects, `linkFails`), those
Stock-lowered functions, or the typed ones (outside `fnScopeInB`; the executable then takes the
integer route) is left out of the region (the `exclude:` line below). On such an error it
also prints the functions failing a per-function condition (`exclusions`, the line
`--verified: exclude: …`; the typed conditions `fnScopeInTB`, and on a typed input the functions
failing `fnScopeTB` or the output checks `outChksT`): `cargo fv` then links
the executable again with those functions' cg_clif code (left out of the region, outside code
like a fallback) and runs `lean-link` again (T3c).

**Constant-phi removal** (#990): the compiler's input is `Link.LinkSpec.cp` of the bundle's spec,
each function after `Opt.ConstPhi.run` when `Opt.ConstPhi.keeps` holds (`FnInput.cp`: the function
`lean-backend` compiled, so its register allocations apply); every route theorem named below is
about that input; the source theorems named (`…_sourceCp`, `Front.bundle_correct_raw{,_peak}TCp`)
are about the bundle's program through it (`Link.cpSource`; `constant-phi removal:` line).
The source domain `SrcScopeB` that `--verified` requires is decided on the bundle's program (as
parsed, before the `i128` legalisation), and the source theorems named below are about that
program: the `…_sourceCp` theorems (#1052) compose the legalisation's refinement, constant-phi
removal's (`Link.cpSource`, `cpSource_depth`) and the route's theorem at the compiled input,
instantiated at `I0 = S0.input0` and the route's placement of `S0.cp` (`hcp`: its functions are
`I0`'s constant-phi removals, by `rfl`). The `_source` theorems instantiated at the compiled input
itself would need `SrcScopeB` of its source program, which holds each changed function as printed
after the legalisation and fails `declSigB` where such a function meets an unchanged one at an
`i128` signature (#1042); they are not named. The typed Stock route (`attemptT`) also takes a
bundle whose program is only in `SrcScopeTB` (#1076: `legalOkTB` instead of `legalOkB`, an `i128`
function with a `try_call_indirect` at an `i128`-free signature, as Rust's
`Box<dyn Any>::downcast`), whose legalisation refines it there (`legalProg_refinesT`; at the
route's input in `SrcScopeTB`, `attemptT_correct_sourceTB`); every other route then leaves out
the functions failing `legalOkB` and links again.

**`--opt`**: the optimising executable compiler — `Link.DeadCleanup.compileExeOpt` (default) or
`Link.compileExeOpt` (`--no-dead-cleanup`): `compileExe` on the input whose functions the
mid-end optimised (`Link.LinkSpec.opt`: `Opt.optimizeExe` with the proven rule sets, each
optimised function printed to CLIF and used only when it parses back to itself; the functions
where it does not keep their input and are listed, `optFallbacks:`). The input conditions are
decided on the optimised input, the source domain on the original one; coverage:
`compileExeOpt_correct`, `compileExeOpt_correct_peak`, `compileExeOpt_correct_sourceCp`,
`compileExeOpt_correct_source_peakCp`, totality `compileExeOpt_total_reach_input`. The layout is
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
/-- More than 8 bytes of stack-passed parameters (or none computable): `indB`'s bound fails. -/
def bigParamsB (t : Clif.Signature) : Bool :=
  match sigParamBytes t with | .ok b => decide (b.length > 8) | .error _ => true

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
        bigParamsB h.sig)
      then ["indB:calleeStack"] else []) ++
    (if ind && P.funcs.any (fun h => mayWithB S (!ind) D h.name && indSigWithB D sigs h &&
        !indRetsWithB sigs h)
      then ["indB:sretRets"] else []) ++
    sites ++ (if outScopeWithB F g then [] else ["outScopeB"])).eraseDups

open Backend in
/-- **`scopeFails` with the functions `g` may enter indexed** (`scopeFailsFast_eq`, #1108): the
indirect-call sites (`callScopeB:blrRegs`) and the indirect-call scope (`indB:*`) test the
functions `g` declares (`X.byName`) and the distinct signatures of the others it may enter
(`SI`, `sigIdx`), instead of every function of `P` per site (ruint: 1,347 s). -/
def scopeFailsFast (F : String → Option Clif.Function) (S : String → Option Nat) (X : LinkIdx)
    (SI : Std.HashMap (List Clif.Ty) (List Clif.Signature)) (g : Clif.Function) : List String :=
  let ind := !indFreeB g
  let Ds := declSet g
  let D := fun n => Ds.contains n
  let sigs := indSigs g
  let to := indToWithB S (indFreeB g) D sigs g
  let M1 := g.externs.flatMap fun e => X.byName.getD e.2.name []
  let cs := if indFreeB g then [] else sigCands SI sigs
  let S2 := cs.filter (indMatchSig sigs)
  let S3 := cs.filter (indSigMatchSig sigs)
  let mi := fun h => mayWithB S (indFreeB g) D h.name && indSigWithB D sigs h
  let site (s : Clif.Signature) (args : List Nat) : List String :=
    let Q := fun (t : Clif.Signature) => decide ((regLocs t).length ≠ (callRegs s args).length) ||
      decide (regLocs t = callRegs s args)
    if M1.all (fun h => !to h || Q h.sig) && S2.all Q then [] else ["callScopeB:blrRegs"]
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
    (if ind && (M1.any (fun h => mi h && bigParamsB h.sig) || S3.any bigParamsB)
      then ["indB:calleeStack"] else []) ++
    (if ind && (M1.any (fun h => mi h && !indRetsSig sigs h.sig) || S3.any (fun t => !indRetsSig sigs t))
      then ["indB:sretRets"] else []) ++
    sites ++ (if outScopeWithB F g then [] else ["outScopeB"])).eraseDups

open Backend in
theorem scopeFailsFast_eq (F : String → Option Clif.Function) (P : Clif.Program)
    (S : String → Option Nat) (g : Clif.Function) :
    scopeFailsFast F S (LinkIdx.of P []) (sigIdx P S) g = scopeFails F P S g := by
  obtain ⟨hM1, hD, hS1, hS2, hS3, hS4⟩ := candFacts P [] S g _ _ _ _ _ rfl rfl rfl rfl rfl
  have hsite : ∀ (s : Clif.Signature) (args : List Nat),
      ((g.externs.flatMap fun e => (LinkIdx.of P []).byName.getD e.2.name []).all
          (fun h => !indToWithB S (indFreeB g) (fun n => (declSet g).contains n) (indSigs g) g h ||
            (decide ((regLocs h.sig).length ≠ (callRegs s args).length) ||
              decide (regLocs h.sig = callRegs s args))) &&
        ((if indFreeB g = true then [] else sigCands (sigIdx P S) (indSigs g)).filter
          (indMatchSig (indSigs g))).all (fun t =>
            decide ((regLocs t).length ≠ (callRegs s args).length) ||
              decide (regLocs t = callRegs s args))) =
        indSiteWithB P (indToWithB S (indFreeB g) (fun n => (declSet g).contains n) (indSigs g) g)
          s args := by
    intro s args
    rw [indSiteWithB]
    simp only [Bool.or_assoc]
    exact (allMay_eq _ hM1 hD hS1 hS2 _).symm
  have hbig : ((g.externs.flatMap fun e => (LinkIdx.of P []).byName.getD e.2.name []).any
        (fun h => (mayWithB S (indFreeB g) (fun n => (declSet g).contains n) h.name &&
          indSigWithB (fun n => (declSet g).contains n) (indSigs g) h) && bigParamsB h.sig) ||
      ((if indFreeB g = true then [] else sigCands (sigIdx P S) (indSigs g)).filter
        (indSigMatchSig (indSigs g))).any bigParamsB) =
      P.funcs.any (fun h => (mayWithB S (indFreeB g) (fun n => (declSet g).contains n) h.name &&
          indSigWithB (fun n => (declSet g).contains n) (indSigs g) h) && bigParamsB h.sig) :=
    (anyMay_eq _ hM1 hD hS3 hS4 bigParamsB).symm
  have hrets : ((g.externs.flatMap fun e => (LinkIdx.of P []).byName.getD e.2.name []).any
        (fun h => (mayWithB S (indFreeB g) (fun n => (declSet g).contains n) h.name &&
          indSigWithB (fun n => (declSet g).contains n) (indSigs g) h) &&
            !indRetsSig (indSigs g) h.sig) ||
      ((if indFreeB g = true then [] else sigCands (sigIdx P S) (indSigs g)).filter
        (indSigMatchSig (indSigs g))).any (fun t => !indRetsSig (indSigs g) t)) =
      P.funcs.any (fun h => (mayWithB S (indFreeB g) (fun n => (declSet g).contains n) h.name &&
          indSigWithB (fun n => (declSet g).contains n) (indSigs g) h) &&
            !indRetsSig (indSigs g) h.sig) :=
    (anyMay_eq _ hM1 hD hS3 hS4 (fun t => !indRetsSig (indSigs g) t)).symm
  unfold scopeFailsFast scopeFails
  simp only [Bool.not_not, indRetsWithB_sig, hsite, hbig, hrets]

/-- The source-domain conditions (`SrcScopeB`'s per-function conjuncts; with `tb`,
`SrcScopeTB`'s: `legalOkTB` instead of `legalOkB`, #1076) a parsed function `g` of the source
program fails (`F`: its `func?`, a hash map, `funcMap`). -/
def srcFails (F : String → Option Clif.Function) (g : Clif.Function) (tb : Bool := false) :
    List String :=
  (if tb then (if Opt.Legalize128.legalOkTB g then [] else ["legalOkTB"])
    else if Opt.Legalize128.legalOkB g then [] else ["legalOkB"]) ++
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
failures (`TypedStockShared.stockFails`), whose theorem `attemptT_correct` has none of the per-function
conditions above as premises (#754). `S` is the bundle's spec `S0`: the source-domain conditions
are `SrcScopeB`'s on the bundle's program, which is what `--verified` and the `…_sourceCp`
theorems require (#1089); on `S0.cp` a function constant-phi removal changed is printed after
the `i128` legalisation, so `declSigB` would fail where it meets an unchanged one (#1123).

`typedNext` (the exits before the route is chosen: the source domain and the admission, #1076):
the program-level conditions (`scopeFails`) are premises of the integer route only (`compile`,
`InScopeIn`), not of the typed routes (`attemptT_correct` has no per-function premise, #754;
`compileExeT`'s failures are listed on its own exit). So when the executable linked again takes
the typed scope — `typed`, and a function left in fails `fnScopeInB` (it meets
`fnScopeInTB`/`fnScopeInTCB`) — only the functions failing a per-function condition are left
out, and of those failing `scopeFails` only the ones failing a call-site condition
(`callScopeB:*`): the typed Stock route checks those call sites again on the compiled code
(`callRegs/blrRegs`, `TypedStockShared.stockFails`), so leaving them in usually costs one more link (k256:
all 56 functions failing `callScopeB:blrRegs` failed it there; crypto-bigint: 0 of 5).
Otherwise, as before, every function failing `scopeFails` (one link fewer).

`srcT` (#1076): the source-domain conditions are `SrcScopeTB`'s (the executable linked again may
take the typed Stock route `attemptT`, which accepts an input in `SrcScopeTB`; an `i128` function
with a `try_call_indirect` stays in). -/
def exclusions (S SC : LinkSpec) (typed : Bool) (extra : List String := []) (only : Bool := false)
    (typedNext : Bool := false) (srcT : Bool := false) : Option (List String) :=
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
    let src := (srcP.funcs.filter fun g =>
      !(srcFails (fun n => fmS[n]?) g (tb := srcT)).isEmpty).map (·.name)
    let fs := P.funcs.zip (parMap (fun g => (fnFails g, fnScopeInFails g)) P.funcs)
    let out : Std.HashSet String := .ofList (src ++ (fs.filter (!·.2.1.isEmpty)).map (·.1.name))
    let typedScope := typedNext && typed &&
      fs.any fun (g, _, i) => !i.isEmpty && !out.contains g.name
    -- `scopeFailsFast_eq` (#1108)
    let X := LinkIdx.of P []
    let SI := sigIdx P syms
    let scope := (P.funcs.zip (parMap (fun g => scopeFailsFast (fun n => fm[n]?) syms X SI g)
      P.funcs)).filterMap fun (g, s) =>
        if s.isEmpty || (typedScope && !s.any (·.startsWith "callScopeB")) then none
        else some g.name
    some (Front.dedupFirst (src ++ (fs.filter (!·.2.1.isEmpty)).map (·.1.name) ++ scope ++ extra))

/-- The number of functions of `SC`'s compiled program failing a program-level input condition
(`scopeFails`): with one, the input is outside `InScopeIn`/`InScopeInT` (their `progScopeInB`). -/
def progScopeFailsN (SC : LinkSpec) : Nat :=
  let P := SC.input0.prog
  let sy := assocMap SC.input0.syms
  let fm := funcMap P
  let X := LinkIdx.of P []
  let SI := sigIdx P (fun n => sy[n]?)
  -- `scopeFailsFast_eq` (#1108)
  (parMap (fun g => !(scopeFailsFast (fun n => fm[n]?) (fun n => sy[n]?) X SI g).isEmpty)
    P.funcs).count true

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
    let X := LinkIdx.of P C.ents
    let rs := parMap (fun e => (e.1.name, ((staticChksWithT (fun _ => Backend.DeadCleanup.prune) I e.1 e.2 ++
      linkChksWithTI C X P e.1 e.2 ++
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

/-- The error of the linkers when `outsideOkB` fails (`Link.leanLink`, `Link.leanLinkWithResults`). -/
def outsideOkMsg : String :=
  "rust-lld's output fails the checks: static headers, data objects, symbols (outsideOkB)"

/-- On a link failing `outsideOkB` (`outsideOkMsg`): which of its parts fail and on what (at
most `k` entries per part, with the number failing). Decided on rust-lld's output `file0` before
the region is written, with the link map of `I`: `hdrB` and `symsOkB` read no byte of the region
(`regionOkB`: the headers lie before it; the symbol table is in no `PT_LOAD` segment), and a data
object with a byte in the region `[R, R + n)` is named as such (its bytes there are the
region's, not checked here). -/
def outsideFails (I : LinkInput) (D : List Clif.DataObject) (file0 : ByteArray) (R n : Nat)
    (k : Nat := 10) : List String :=
  let ex : Excerpt := [(0, file0)]
  let r := exRd ex
  let hdr := if BinCheck.hdrB ex then [] else ["hdrB: not a static AArch64 executable (Static)"]
  let data := match phdrs r with
    | none => ["dataFastB: no program headers"]
    | some phs =>
      let am := addrMap I.addrs
      let bad := D.filter fun o => !objFastB am I r phs o
      let one (o : Clif.DataObject) : String :=
        match am[o.name]? with
        | none => s!"dataFastB: data object {o.name}: not in the link map"
        | some a =>
          let bs := (BinCheck.objBytes I o).toArray
          let inR := decide (a < R + n) && decide (R < a + bs.size)
          let at0 := BitVec.ofNat 64 a
          let byteAt := (List.range bs.size).find? fun i =>
            loadIn r phs (at0 + BitVec.ofNat 64 i).toNat != some (bs[i]?.getD 0)
          let roAt := (List.range bs.size).find? fun i =>
            let x := at0 + BitVec.ofNat 64 i
            !(o.writable || BinCheck.roB phs x || BinCheck.relroB phs x)
          let bytes := match byteAt with
            | some i =>
              let got : Option (BitVec 8) := loadIn r phs (at0 + BitVec.ofNat 64 i).toNat
              let want : BitVec 8 := bs[i]?.getD 0
              s!"byte {i} (at {hex (a + i)}) is {got.map BitVec.toNat} in the file, {want.toNat} resolved"
            | none => "bytes as resolved"
          let ro := match roAt with
            | some i => s!"; read-only object, byte {i} in no read-only segment"
            | none => ""
          s!"dataFastB: data object {o.name} at {hex a}, {bs.size} byte(s){if inR then " (inside the region)" else ""}: {bytes}{ro}"
      (if bad.isEmpty then [] else [s!"dataFastB: {bad.length} of {D.length} data object(s) fail"]) ++
        (bad.take k).map one
  let idx := symIndex file0
  let fr := fileRd file0
  let symBad := I.addrs.filter fun p => !((I.aliases.lookup p.1).isSome ||
    match idx[(BinCheck.symName p.1, p.2)]? with
    | some (s, i) => match symEntry fr s i with
      | some (o, v) => v == p.2 && cstrB fr o (BinCheck.symName p.1)
      | none => false
    | none => false)
  let symOne (p : String × Nat) : String :=
    match idx[(BinCheck.symName p.1, p.2)]? with
    | some _ => s!"symsOkB: {p.1} at {hex p.2}: the symbol entry does not read back"
    | none =>
      let other := idx.fold (fun acc (nm, v) _ => if nm == BinCheck.symName p.1 then v :: acc else acc) []
      s!"symsOkB: {p.1} at {hex p.2}: no symbol of that name at that address (that name at: {other.map hex})"
  let syms := (if symBad.isEmpty then [] else [s!"symsOkB: {symBad.length} of {I.addrs.length} link-map name(s) fail"]) ++
    (symBad.take k).map symOne
  hdr ++ data ++ syms

/-- A failing check's line (`tag: N of n fail`) and its first `k` objects. -/
def failLines {α : Type} (k : Nat) (tag : String) (n : Nat) (bad : List α) (one : α → String) :
    List String :=
  if bad.isEmpty then [] else s!"{tag}: {bad.length} of {n} fail" :: (bad.take k).map one

/-- `regionOkB file R n off`'s conditions that fail, each with its numbers (`linkFails`). -/
def regionFails (file : ByteArray) (phs : List Phdr) (R n off : Nat) : List String :=
  match ehdr (fileRd file) with
  | none => ["regionOkB: no ELF header"]
  | some e =>
    let hdr := (if 64 ≤ off then [] else [s!"regionOkB: file offset {off} is inside the ELF header"]) ++
      (if e.phoff + 56 * e.phnum ≤ off then [] else
        [s!"regionOkB: the program headers end at {hex (e.phoff + 56 * e.phnum)}, after the region's file offset"]) ++
      (if off + n ≤ file.size then [] else
        [s!"regionOkB: the region's file bytes end {off + n - file.size} byte(s) past the end of the file"])
    let seg := match segIn phs R with
      | none => [s!"regionOkB: no PT_LOAD segment contains {hex R}"]
      | some p =>
        let others := phs.filter fun q => !(q == p || q.type != 1 || decide (q.vaddr + q.memsz ≤ R) ||
          decide (R + n ≤ q.vaddr))
        s!"regionOkB: segment {hex p.vaddr}..{hex (p.vaddr + p.filesz)} (memsz {hex p.memsz}, offset {hex p.offset}, flags {p.flags})" ::
          ((if notW p then [] else ["regionOkB: the segment is writable"]) ++
          (if R + n ≤ p.vaddr + p.filesz then [] else
            [s!"regionOkB: the region ends {R + n - (p.vaddr + p.filesz)} byte(s) past the segment's file bytes"]) ++
          (if p.filesz ≤ p.memsz then [] else ["regionOkB: the segment's filesz exceeds its memsz"]) ++
          (if off = p.offset + (R - p.vaddr) then [] else
            [s!"regionOkB: file offset {hex off}, the segment maps {hex R} at {hex (p.offset + (R - p.vaddr))}"]) ++
          others.map fun q => s!"regionOkB: PT_LOAD segment {hex q.vaddr}..{hex (q.vaddr + q.memsz)} meets the region")
    hdr ++ seg

/-- The placed functions of `S` whose span to the next placed function (code, gap word, the
next one's alignment) is not the one in rust-lld's output (`marks`: the bundle's markers, the
functions' addresses there), with both spans: where the placement's code is not the units'
(`lean-backend`'s), which rust-lld laid out (#1075). -/
def spanFails (S : LinkSpec) (marks : List (String × Nat)) : List (String × Nat × Nat) :=
  let mk := assocMap marks
  let pa := S.progAddrs
  (pa.zip pa.tail).filterMap fun (e, e') => match mk[e.1]?, mk[e'.1]? with
    | some m, some m' => if m' - m == e'.2 - e.2 then none else some (e.1, e'.2 - e.2, m' - m)
    | _, _ => none

/-- On a link by `Link.leanLinkWithResults S file0 results` (`Link.leanLinkProductionWith`: the
Stock routes and the typed Stock route `attemptT`) that fails: every region-level check of the
linker that fails, each with what fails it (at most `k` entries per check, with the number
failing), in the linker's order (#1075). The checks of one placed program: `placeOkB` (which
condition), the pipeline (the functions it rejects, with the reason), `namesOkB`/`sizesOkB` (the
functions whose compiled name or size is not the placement's), `relocsOkB` (the functions and
the first failing relocation), `codeMapB` (the functions whose code-map conditions fail); the
checks of rust-lld's output: `regionOkB` (the region `[R, R + n)`, the segment containing `R`
and which condition fails), then, on the written file, `outsideOkB` (`outsideFails`). Where the
checks of rust-lld's output fail, the placement against rust-lld's layout of the units' code
(`marks`: the functions' addresses in rust-lld's output, the bundle's markers): the functions
whose span to the next placed function is not rust-lld's (the functions whose compiled code or
alignment is not the units'; each moves every later function), and the functions placed
elsewhere. -/
def linkFails (S : LinkSpec) (file0 : ByteArray) (results : LinkInput → Res)
    (marks : List (String × Nat) := []) (k : Nat := 10) : List String :=
  match phdrs (fileRd file0) with
  | none => ["phdrs: rust-lld's output has no program headers"]
  | some phs =>
    let I0 := S.input0
    let Rs := results I0
    let I := I0.withDepth Rs
    let T := tabOf Rs
    let P := T.take S.funcs.length
    let tp := tpOff phs
    let place :=
      (if nodupB S.names then [] else ["placeOkB: two placed functions have one name"]) ++
      (if S.names.length = S.funcs.length ∧ S.sizes.length = S.funcs.length then [] else
        [s!"placeOkB: {S.funcs.length} function(s), {S.names.length} name(s), {S.sizes.length} size(s)"]) ++
      failLines k "placeOkB: positive sizes" S.sizes.length ((S.names.zip S.sizes).filter (·.2 == 0))
        (fun e => s!"placeOkB: {e.1}: size 0") ++
      (if 0 < S.R ∧ S.R % 4 = 0 ∧ S.R + S.size < 2 ^ 64 then [] else
        [s!"placeOkB: region {hex S.R} of {S.size} bytes: not nonzero, word-aligned and in the address space"]) ++
      failLines k "placeOkB: outside symbols clear of the region" S.outside.length
        (S.outside.filter fun e => !clearOfB S.R S.size [e]) (fun e => s!"placeOkB: {e.1} at {hex e.2}")
    let why (r : Except String Art) : String := match r with
      | .error m => m
      | .ok _ => ""
    let pipe := failLines k "pipeline" Rs.length (Rs.filter (!·.2.toBool)) fun e =>
      s!"pipeline: {e.1.name}: {why e.2}"
    let rows := (P.zip (S.names.zip S.sizes)).zipIdx
    let names := failLines k "namesOkB" S.names.length (rows.filter fun r => r.1.1.1.name != r.1.2.1)
      (fun r => s!"namesOkB: function {r.2} is {r.1.1.1.name}, placed as {r.1.2.1}") ++
      (if P.length = S.names.length then [] else
        [s!"namesOkB: {P.length} compiled function(s) for {S.names.length} placed"])
    let sizes := failLines k "sizesOkB" S.sizes.length
      (rows.filter fun r => r.1.1.2.fb.words.size != r.1.2.2) fun r =>
        s!"sizesOkB: {r.1.1.1.name}: {r.1.1.2.fb.words.size} word(s) compiled, {r.1.2.2} placed"
    let relocAt (a : Art) : String := match a.fb.relocs.find? (fun r => !relocOkB I tp a r) with
      | some r => s!"relocation at offset {r.offset}"
      | none => "two relocations at one offset"
    let relocs := failLines k "relocsOkB" T.length (T.filter fun e => !relocsOkB I tp e.2) fun e =>
      s!"relocsOkB: {e.1.name}: {relocAt e.2}"
    let codeMap := if codeMapB I T then [] else
      let byBase := (T.toArray.qsort fun a b => decide (a.2.base.toNat < b.2.base.toNat)).toList
      failLines k "codeMapB: link-map addresses" T.length
          (T.filter fun e => !(I.symAddr e.1.name 0 == e.2.base || noBlrB I T e.1.name))
          (fun e => s!"codeMapB: {e.1.name}: code at {hex e.2.base.toNat}, link map {hex (I.symAddr e.1.name 0).toNat}") ++
        failLines k "codeMapB: disjoint code (address order)" T.length
          ((byBase.zip byBase.tail).filter fun p =>
            decide (p.2.2.base.toNat < p.1.2.base.toNat + 4 * p.1.2.fb.words.size))
          (fun p => s!"codeMapB: {p.1.1.name} ({hex p.1.2.base.toNat}, {p.1.2.fb.words.size} words) meets {p.2.1.name} ({hex p.2.2.base.toNat})")
    let B := regionBytesA I tp S.aligns (P.map (·.2))
    let n := B.length
    let off := offsetOf phs S.R
    let mk := assocMap marks
    let pa := S.progAddrs
    let words := assocMap (S.names.zip S.sizes)
    let moved :=
      failLines k "placed spans as rust-lld's (markers)" pa.length (spanFails S marks)
        (fun e => s!"placement: {e.1} ({words[e.1]?.getD 0} words): {e.2.1} bytes to the next function, rust-lld's {e.2.2}") ++
      failLines k "placed at rust-lld's addresses (markers)" pa.length
        (pa.filterMap fun e => match mk[e.1]? with
          | some m => if m == e.2 then none else some (e.1, e.2, m)
          | none => none)
        (fun e => s!"placement: {e.1} at {hex e.2.1}, rust-lld's at {hex e.2.2}")
    let region := if regionOkB file0 S.R n off then [] else
      s!"regionOkB: region {hex S.R}..{hex (S.R + n)} ({n} bytes, placement {S.size}) at file offset {hex off} of {file0.size}" ::
        regionFails file0 phs S.R n off ++ moved
    let outside := if !region.isEmpty then [] else
      if outsideOkB I S.data (patch file0 off ⟨B.toArray⟩) then [] else
        outsideFails I S.data file0 S.R n k ++ moved
    place ++ pipe ++ names ++ sizes ++ relocs ++ codeMap ++ region ++ outside

/-- Print `exclusions` (the line `cargo fv` reads). -/
def printExclusions (exe : String) (S SC : LinkSpec) (typed : Bool) (extra : List String := [])
    (only : Bool := false) (typedNext : Bool := false) (srcT : Bool := false) : IO Unit :=
  match exclusions S SC typed extra only typedNext srcT with
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
  -- #1108: the bundle holds every function's dump (8.4 GB of text on ruint's test executable);
  -- only its markers are read after `buildSpec`, which consumes it (`Front.buildSpecF`)
  let markers := b0.markers
  -- `buildSpec` takes a size per function (every region function has a marker); the layout below
  -- replaces them by the compiled code's
  let S ← match Front.buildSpec { b0 with sizes := markers.map fun (n, _) => (n, 0) } with
    | .ok S => pure S
    | .error e => do IO.eprintln s!"lean-link: {exe}: {e}"; return 1
  -- constant-phi removal (#990): the input `lean-backend` compiled (`FnInput.cp`, its decision
  -- `Opt.ConstPhi.keeps`); the route theorems below are about `S0.cp`, the source ones about
  -- `S0`'s program through it (`Link.cpSource`)
  let S0 := S
  let S := S0.cp
  let cpN := S0.cpChanged
  IO.println s!"lean-link: {exe}: constant-phi removal: {cpN.length} of {S0.funcs.length} function(s) {cpN.take 5}, cpFallbacks: {S0.cpFallbacks.length}; the route theorems below are about the compiled input Link.LinkSpec.cp (lean-backend's input), the source ones (…Cp, Front.…TCp) about the bundle's program through constant-phi removal (Link.cpSource)"
  -- the compiler's input: the optimised one under `--opt` (`compileExeOpt S = compileExe S.opt`),
  -- the self tail calls as loops when a function has one (`compileExeTail S = compileExe S.tail`),
  -- with the Lean compiler's layout (`placedPar = placed`: the totality theorems' layout)
  let tailOn := deadCleanup && !opt && S.funcs.any (fun fi => Opt.TailLoop.eligB fi.func)
  let SC0 := if opt then S.opt else if tailOn then S.tail else S
  -- the cleanup layout from the cleanup pipeline's results, kept for the typed Stock route below
  -- (`TypedStockShared.cleanupArts_placed`: `DeadCleanup.placedPar SC0`)
  let Ac := if deadCleanup then parMap TypedStockShared.cleanupArt SC0.funcs else []
  let SC := if deadCleanup then TypedStockShared.placedFrom SC0 Ac else SC0.placedPar
  let names := SC.names
  let R := SC.R
  let file0 ← IO.FS.readBinFile exe
  let summary := s!"{names.length} function(s), {SC.data.length} data object(s), region {hex R}..{hex (R + SC.size)} ({SC.size} bytes), {(SC.aligns.filter (· > 4)).length} function(s) aligned beyond a word"
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
  -- the source domain `--verified` requires: the bundle's program (`S0`; `SrcScopeB` reads the
  -- parsed functions only). The source theorems named below are about it: the `…_sourceCp`
  -- theorems, through the `i128` legalisation and constant-phi removal (`Link.cpSource`, #1052),
  -- instantiated at `I0 = S0.input0` and the route's placement of `S0.cp` (`hcp` by `rfl`)
  let srcOk := SrcScopeB S0.input0
  -- the typed scope under `--verified` (S11e6): the cleanup compiler `compileExeT`
  let typedOk := deadCleanup && !opt && !tailOn
  -- #1076: the typed Stock route (`attemptT`, chosen below) also takes a bundle whose program is
  -- only in `SrcScopeTB` (an `i128` function with a `try_call_indirect` at an `i128`-free
  -- signature: `legalOkTB`, not `legalOkB`); the legalisation refines it there
  -- (`legalProg_refinesT`, `attemptT_correct_sourceTB`). The other routes exit below (`srcT`).
  let srcT := verified && !srcOk && typedOk && SrcScopeTB S0.input0
  if verified && !srcOk && !srcT then
    let P := S0.input0.srcProg
    let fmS := funcMap P
    let bad := P.funcs.filterMap fun g => match srcFails (fun n => fmS[n]?) g (tb := typedOk) with
      | [] => none
      | fs => some (g.name, fs)
    IO.eprintln s!"lean-link: {exe}: --verified: outside the source domain ({if typedOk then "SrcScopeTB" else "SrcScopeB"}): {bad.length} function(s) failing {if typedOk then "legalOkTB" else "legalOkB"}/linkFreeB/declSigB {(bad.take 3).map (·.1)}, helperFreeB {helperFreeB P}; not written"
    for (n, fs) in bad do
      IO.eprintln s!"lean-link:   {n}: {fs}"
    -- only the failing functions when the executable linked again takes the typed scope
    -- (`exclusions`' `typedNext`, #1076), there `SrcScopeTB`'s (`srcT`)
    printExclusions exe S0 SC typedOk (typedNext := true) (srcT := typedOk)
    return 1
  -- #1119 (`cargo fv --midval`): the functions compiled from Cranelift's optimised dumps
  -- (`dump`) carry their unoptimised dumps (`src_dump`). Each pair is re-decided here on the
  -- bundle's own texts (`Link.midPairB`; nothing cargo fv or lean-backend said is trusted): a
  -- failing one is left out of the region (`--verified: exclude:`). When all hold
  -- (`Link.midValidatedB_sound`: `Opt.MidVal.Validated I0.srcProg.funcs S0.input0.srcProg.funcs`,
  -- `I0` the bundle with the source dumps), the source theorems named are the `…Mid` ones, about
  -- the bundle's source program (the unoptimised dumps), on `SrcScopeB S0.input0` (`srcOk`); on a
  -- bundle only in `SrcScopeTB` (`srcT`, the typed Stock route alone) the `…TBMid` ones
  -- (`FV/Link/MidSourceTB.lean`), decided on that route's input below (`midFis0`: the source
  -- dumps' inputs).
  let midSrc ← try Front.readSrcBundle dir
    catch e => do IO.eprintln s!"lean-link: {e}"; return 2
  let (midN, midFis0) : Nat × List FnInput ← match midSrc with
    | none => pure (0, [])
    | some (bs, srcNames) => do
      if !verified then
        IO.eprintln s!"lean-link: {exe}: {srcNames.length} function(s) compiled from optimised dumps (src_dump, #1119): only with --verified; not written"
        return 1
      let A0 ← match Front.assemble bs with
        | .ok A0 => pure A0
        | .error e => do IO.eprintln s!"lean-link: {exe}: the source dumps (src_dump): {e}"; return 1
      let fs0 := A0.funcs.map FnInput.src
      let fs1 := S0.input0.srcProg.funcs
      if fs0.map (·.name) != fs1.map (·.name) then
        IO.eprintln s!"lean-link: {exe}: the source dumps (src_dump) assemble to other function names than the dumps; not written"
        return 1
      let pairs := fs0.zip fs1
      let oks := parMap (fun (p : Clif.Function × Clif.Function) => Link.midPairB p.1 p.2) pairs
      let bad := (pairs.zip oks).filterMap fun (p, b) => if b then none else some p.2.name
      if !bad.isEmpty then
        IO.eprintln s!"lean-link: {exe}: --verified: the mid-end validator's pair fails (Link.midPairB, re-decided on the bundle's dumps): {bad.length} function(s) {bad.take 3}; not written"
        printExclusions exe S0 SC typedOk bad (only := true)
        return 1
      if srcOk then
        IO.println s!"lean-link: {exe}: mid-end validator: {srcNames.length} function(s) compiled from Cranelift's optimised dumps; Link.midValidatedB holds against the source dumps (src_dump): the source theorems below are the …Mid ones, about the bundle's source program (unoptimised dumps)"
      else
        IO.println s!"lean-link: {exe}: mid-end validator: {srcNames.length} function(s) compiled from Cranelift's optimised dumps; Link.midPairB holds on every pair of the bundle's dumps; the bundle's program is in SrcScopeTB only: the typed Stock route decides Link.midValidatedB on its input (the …TBMid source theorems)"
      pure (srcNames.length, A0.funcs)
  -- a coverage line through the validator: the `…Cp` source theorems by their `…Mid`
  -- compositions (`FV/Link/MidSourceRoutes.lean`), about the unoptimised dumps; `Front.…TCp`
  -- (about the dumps compiled) not named
  let midCov (s : String) : String := if midN == 0 then s else
    let s := (s.replace "_sourceCp" "_sourceMid").replace "_source_peakCp" "_source_peakMid"
    let s := s.replace "; cg_clif's program: Front.bundle_correct_rawTCp, Front.bundle_correct_raw_peakTCp" ""
    let s := s.replace "the bundle's program (before the i128 legalisation and constant-phi removal), in SrcScopeB:"
      "the bundle's source program (the unoptimised dumps, src_dump, before the i128 legalisation and constant-phi removal; through the mid-end validator: Link.midValidatedB decided against the dumps compiled, whose program is in SrcScopeB):"
    s ++ (if (s.splitOn "Mid").length > 1 then
        s!"; mid-end validator (#1119): {midN} function(s) compiled from Cranelift's optimised dumps"
      else s!"; mid-end validator (#1119): {midN} function(s) compiled from Cranelift's optimised dumps, and no theorem named here is about their unoptimised dumps")
  -- the input conditions decided on the CLIF alone (`fnScopeInB`, `addrSlotsInputB`); with
  -- `InScopeP`'s other program conditions, which `compile` checks, `InScopeIn`; with the cleanup
  -- compiler, an input outside `fnScopeInB` whose functions all meet the typed `fnScopeInTB`
  -- (`InScopeInT`'s) is compiled by `compileExeT` (`typedV`)
  let mut typedV := false
  let mut typedN := 0
  -- the functions admitted only through the admission predicate `fnScopeInTCB` (outside
  -- `fnScopeInTB`): under no totality theorem (#1048)
  let mut tcbN := 0
  if verified then
    let P := SC.input0.prog
    let sy := assocMap SC.input0.syms
    let syms := fun n => sy[n]?
    if !addrSlotsInputB P syms then
      IO.eprintln s!"lean-link: {exe}: --verified: outside the input conditions (InScopeIn): addrSlotsInputB fails (an indirect call, a function with an address and stack slots, no program callee with slots); not written"
      return 1
    let bad := (P.funcs.zip (parMap fnScopeInFails P.funcs)).filterMap fun (g, fs) => match fs with
      | [] => none
      | fs => some (g.name, fs)
    -- per function: the `fnScopeInTB` causes it fails when it fails `fnScopeInTCB` too, and
    -- whether it is admitted only through `fnScopeInTCB`
    let tFails := if typedOk && !bad.isEmpty then
        P.funcs.zip (parMap (fun g => match fnScopeInFailsT g with
            | [] => ([], false)
            | fs => if fnScopeInFailsTC g = [] then ([], true) else (fs, false)) P.funcs)
      else []
    let badT := if typedOk && !bad.isEmpty then
        tFails.filterMap fun (g, fs, _) =>
          match fs with
          | [] => none
          | fs => some (g.name, fs)
      else bad
    tcbN := (tFails.filter (·.2.2)).length
    if !bad.isEmpty && typedOk && badT.isEmpty then
      typedV := true
      typedN := bad.length
      IO.println s!"lean-link: {exe}: --verified: typed scope (InScopeInT): {bad.length} function(s) outside fnScopeInB meet fnScopeInTB/fnScopeInTCB, {tcbN} of them only fnScopeInTCB {(bad.take 3).map (·.1)}"
    else if !badT.isEmpty then
      let scopeN := if typedOk then "fnScopeInTB/fnScopeInTCB" else "fnScopeInB"
      let causes := (badT.flatMap (·.2)).eraseDups.map fun c => s!"{c} {(badT.filter (·.2.contains c)).length}"
      IO.eprintln s!"lean-link: {exe}: --verified: outside the input conditions (InScopeIn{if typedOk then "T" else ""}): {badT.length} function(s) failing {scopeN} (by cause: {causes}) {(badT.take 3).map (·.1)}; not written"
      for (n, fs) in badT do
        IO.eprintln s!"lean-link:   {n}: {fs}"
      printExclusions exe S0 SC typedOk (typedNext := true) (srcT := srcT)
      return 1
  -- #1108: the input conditions every Stock route's `attempt` (and the return-pin attempt) checks
  -- first, `inScopePar` (`inScopeInPar` without the cleanup) of its placed spec, do not read the
  -- placement (`Link.inScopePar_withSizes`, `Link.inScopeInPar_withSizes`): decided at most
  -- once, on the placement with zero sizes
  let scope0 : Thunk Bool := Thunk.mk fun _ =>
    let SZ := SC0.withSizes (SC0.funcs.map fun _ => 0)
    if deadCleanup then inScopePar SZ.input0 else inScopeInPar SZ.input0
  -- The checked semantic provider handles a CFG function alongside retained
  -- try-call functions. Recompiling that mixed program only through the old
  -- provider can require a different region size from the emitted objects.
  -- Other exception, optimizer and tail-call variants retain their routes;
  -- typed `--verified` (S11e6) keeps its own route below.
  let hasCfg := SC0.funcs.any (fun fi => (((((((Backend.Stock.MemorySinkExt.eligible fi.func || Backend.Stock.MemoryCapturedCopy.eligible fi.func || Backend.Stock.MemoryLoadStore.eligible fi.func) || Backend.Stock.MemoryStoreCfg.eligible fi.func) || Backend.Stock.MemoryStore.eligible fi.func) || Backend.Stock.MemoryExtending.eligible fi.func) || Backend.Stock.MemoryUnsigned.eligible fi.func || Backend.Stock.MemoryCfg.eligible fi.func || Backend.Stock.Memory.eligible fi.func || Backend.Stock.ParameterCfg.eligible fi.func || Backend.Stock.ConditionalForwardCfg.eligible fi.func) || Backend.Stock.ConditionalCfg.eligible fi.func) || Backend.Stock.ForwardCfg.eligible fi.func || Backend.Stock.LinearCfg.eligible fi.func || Backend.Stock.TwoBlock.Entry.eligible fi.func))
  let stockEnabled := !typedV && !opt && !tailOn && SC0.funcs.any (fun fi => (((((((Backend.Stock.MemorySinkExt.eligible fi.func || Backend.Stock.MemoryCapturedCopy.eligible fi.func || Backend.Stock.MemoryLoadStore.eligible fi.func) || Backend.Stock.MemoryStoreCfg.eligible fi.func) || Backend.Stock.MemoryStore.eligible fi.func) || Backend.Stock.MemoryExtending.eligible fi.func) || Backend.Stock.MemoryUnsigned.eligible fi.func || Backend.Stock.MemoryCfg.eligible fi.func || Backend.Stock.Memory.eligible fi.func || Backend.Stock.ParameterCfg.eligible fi.func || Backend.Stock.ConditionalForwardCfg.eligible fi.func) || Backend.Stock.ConditionalCfg.eligible fi.func) || Backend.Stock.ForwardCfg.eligible fi.func || Backend.Stock.LinearCfg.eligible fi.func || Backend.Stock.TwoBlock.Entry.eligible fi.func) || Backend.Stock.Scalar.activationEligible fi.func || Backend.Stock.Logical.activationEligible fi.func || Backend.Stock.Mixed.activationEligible fi.func || Backend.Stock.Arithmetic.eligible fi.func || Backend.Stock.ScalarAdd.activationEligible fi.func) &&
    (hasCfg || !(SC0.funcs.any fun fi => fi.func.blocks.any fun b => b.term.isTry)) &&
    -- #739, #1108: when the input conditions fail (`scope0`), all routes fail and
    -- `compileWithRoutes` is `compile SC`, so skip the routes' placements (each one the full
    -- pipeline)
    scope0.get
  let routes := [Backend.Stock.MemorySinkExt.lowerValidated,Backend.Stock.MemoryCapturedCopy.lowerValidated,Backend.Stock.MemoryLoadStore.lowerValidated,Backend.Stock.MemoryStoreCfg.lowerValidated,Backend.Stock.MemoryUnsigned.lowerValidated,Backend.Stock.MemoryCfg.lowerValidated,Backend.Stock.Memory.lowerValidated,Backend.Stock.ParameterCfg.lowerValidated,Backend.Stock.ConditionalForwardCfg.lowerValidated,Backend.Stock.ConditionalCfg.lowerValidated,Backend.Stock.ForwardCfg.lowerValidated,Backend.Stock.LinearCfg.lowerValidated,Backend.Stock.TwoBlock.Entry.lowerValidated,Backend.Stock.TwoBlock.lowerValidated,Backend.Stock.Scalar.lowerValidated,Backend.Stock.Logical.lowerValidated,Backend.Stock.Mixed.lowerValidated,
    Backend.Stock.Arithmetic.lowerValidated]
  -- #691: on a typed input, the functions `lean-backend` compiled with the Stock lowering
  -- (`stockDiffersB`, computed with the Stock route's result per function: `stockSteps_fst`);
  -- when there are some, the typed Stock route `attemptT` below
  let steps := if typedV then
      parMap (fun (p : FnInput × Except String Art) => TypedStockShared.stockStep routes[0]! p.1 p.2)
        (SC0.funcs.zip Ac)
    else []
  let stockFnsT := steps.filterMap fun s => if s.1 then some s.2.1.name else none
  -- #1076: a bundle only in `SrcScopeTB` is taken by the typed Stock route `attemptT` alone;
  -- every other route names `_source` theorems on `SrcScopeB`: leave out the functions failing
  -- it (`legalOkB`) and link again
  if srcT && !(typedV && !stockFnsT.isEmpty) then
    let P := S0.input0.srcProg
    let fmS := funcMap P
    let bad := P.funcs.filterMap fun g => match srcFails (fun n => fmS[n]?) g with
      | [] => none
      | fs => some (g.name, fs)
    IO.eprintln s!"lean-link: {exe}: --verified: outside the source domain (SrcScopeB) of the routes other than the typed Stock route (the bundle's program is in SrcScopeTB, which only attemptT takes): {bad.length} function(s) failing legalOkB/linkFreeB/declSigB {(bad.take 3).map (·.1)}; not written"
    for (n, fs) in bad do
      IO.eprintln s!"lean-link:   {n}: {fs}"
    printExclusions exe S0 SC typedOk (typedNext := true)
    return 1
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
    let stockFns := stockFnsT
    if !stockFns.isEmpty then
      -- #722: the typed compiler on the Stock route: the units' code (the Stock route's pipeline
      -- and placement), the typed checks per function
      -- (`TypedStockShared.stockSteps_placed`: `SC0.placedProductionWith routes[0]! true`;
      -- `TypedStockShared.attemptTFrom_eq`: `attemptT routes[0]! SP file0`); the checks evaluated
      -- once, with their failures (#1108, `TypedStockShared.attemptTFrom_stockFails`)
      let SP := TypedStockShared.placedStock SC0 steps
      let RS := TypedStockShared.stockRes SP steps
      let bad := TypedStockShared.stockFails SP RS
      let att := if bad.isEmpty then leanLinkWithResults SP file0 (fun _ => RS)
        else .error SemanticCompilerWith.outOkTSMsg
      -- #1119: a bundle only in `SrcScopeTB` with functions compiled from optimised dumps: the
      -- theorems through the validator on this route (`attemptT_correct_source{,_peak}TBMid`,
      -- `FV/Link/MidSourceTB.lean`) take `Opt.MidVal.Validated P0.funcs Q.funcs`, `Q` the route
      -- input's source program, `P0` the source dumps' inputs taken as the route takes the dumps
      -- (`FnInput.cp`, then parsed), by name; decided here (`Link.midValidatedB_sound`) before the
      -- executable is written, a failing pair left out (`--verified: exclude:`)
      let midTB : Bool := midN != 0 && srcT && SrcScopeTB SP.input0
      if midTB then
        let Q := (SemanticCompilerWith.input routes[0]! SP true).toLinkInput.srcProg.funcs
        let m0 : Std.HashMap String Clif.Function :=
          midFis0.foldl (fun m fi => let f := (FnInput.cp fi).src; m.insert f.name f) {}
        let P0 := Q.map fun q => (m0[q.name]?).getD default
        if !Link.midValidatedB P0 Q then
          let badQ := (P0.zip Q).filterMap fun (f, g) => if Link.midPairB f g then none else some g.name
          IO.eprintln s!"lean-link: {exe}: --verified: the mid-end validator's pair fails on the typed Stock route's input (Link.midPairB, the source dumps taken as the route takes the dumps): {badQ.length} function(s) {badQ.take 3}; not written"
          printExclusions exe S0 SC typedOk badQ (only := true)
          return 1
      if let .ok file := att then
        IO.FS.writeBinFile exe file
        IO.println s!"lean-link: {exe}: {summary} written by Link.SemanticCompilerWith.attemptT (Link.SemanticCompilerWith.attemptT_correct); {stockFns.length} function(s) Stock-lowered, {typedN} typed function(s) in the region"
        if let some f := ldFile then
          match ← ldCheck SP file0 f with
          | .ok () => IO.println s!"lean-link: {exe}: lean-ld's plan meets the link spec (Plan.specOkB)"
          | .error e => IO.eprintln s!"lean-link: {exe}: lean-ld's plan: {e}"
        -- the functions failing a program-level input condition (`scopeFails`; `attemptT` does not
        -- need them, `exclusions`' `typedNext`): the executable is then outside `InScopeInT`
        let progN := if verified then progScopeFailsN SC else 0
        let progTot := if progN = 0 then "" else
          s!"; {progN} function(s) fail a program-level input condition (scopeFails: declSigB/indB/callScopeB/outScopeB), so the executable is outside InScopeInT: no totality claim for it"
        -- #1076: name `attemptT_correct_sourceTB` only where its premise `SrcScopeTB` holds of the
        -- route's input (the compiled input's source program; `SrcScopeTB` does not read the
        -- route input's call-level stack, `SrcScopeTB_withDepth`: decided on `SP.input0`)
        let srcTB := if !srcT then "" else
          let thmTB := if SrcScopeTB SP.input0 then
            if midTB then
              ", Link.SemanticCompilerWith.attemptT_correct_sourceTBMid, Link.SemanticCompilerWith.attemptT_correct_source_peakTBMid: about the bundle's unoptimised dumps (src_dump) taken as the route's input takes the dumps (constant-phi removal), through the mid-end validator (Link.midValidatedB decided on the route's input)"
            else ", Link.SemanticCompilerWith.attemptT_correct_sourceTB, Link.SemanticCompilerWith.attemptT_correct_source_peakTB"
            else ""
          s!"; the bundle's program is in SrcScopeTB, not SrcScopeB (#1076: i128 functions with a try_call_indirect at an i128-free signature): its legalisation refines it (E2E.LegalProgram.legalProg_refinesT{thmTB})"
        -- #1100: the bundle's program through the legalisation and constant-phi removal, at
        -- `I0 = S0.input0` (`hsrc = srcOk`, decided above) and `SP` (`hcp`:
        -- `TypedStockShared.stockSteps_placed`, `SP = SC0.placedProductionWith routes[0]! true`
        -- with `SC0 = S0.cp` on this route, then `rfl`)
        let srcCp := if srcOk then
            "; the bundle's program (before the i128 legalisation and constant-phi removal), in SrcScopeB: Link.SemanticCompilerWith.attemptT_correct_sourceCp, Link.SemanticCompilerWith.attemptT_correct_source_peakCp"
          else ""
        IO.println <| midCov s!"lean-link: {exe}: coverage: Link.SemanticCompilerWith.attemptT_correct, Link.SemanticCompilerWith.attemptT_correct_depth, Link.SemanticCompilerWith.attemptT_correct_peak (returned values by class; per function the typed checks okRWithTS); about the legalised program{srcCp}; admission (--verified): every function meets fnScopeInTB (InScopeInT) or the admission predicate fnScopeInTCB; totality: no theorem for attemptT (the totality theorems are about compileExe/compileExeT/compileExeT3 on InScopeIn); {tcbN} function(s) admitted only through fnScopeInTCB{progTot}{srcTB}"
        return 0
      if let .error e := att then
        let causes := (bad.flatMap (·.2)).eraseDups.map fun c => s!"{c} {(bad.filter (·.2.contains c)).length}"
        IO.eprintln s!"lean-link: {exe}: --verified: typed Stock route (attemptT): {e}: {bad.length} function(s) failing (by cause: {causes}) {(bad.take 3).map (·.1)}"
        for (n, fs) in bad.take 50 do
          IO.eprintln s!"lean-link:   {n}: {fs}"
        -- the link's own checks (`leanLinkProductionWith`): name the failing check and its
        -- objects, also where no function fails the typed checks (#1075)
        if e != SemanticCompilerWith.outOkTSMsg then
          for l in linkFails SP file0 (fun I => parResultsProductionWith routes[0]! I true) markers do
            IO.eprintln s!"lean-link:   {l}"
        -- leave out only the functions failing the typed checks when that set is the smallest
        -- (only those: `attemptT_correct` has no per-function input premise, #754)
        let badFns := (bad.filter (·.1 != "<global>")).map (·.1)
        if !badFns.isEmpty && badFns.length < min typedN stockFns.length then
          IO.eprintln s!"lean-link: {exe}: --verified: typed Stock route: leaving out the {badFns.length} function(s) failing the typed checks; not written"
          printExclusions exe S0 SC true badFns (only := true)
          return 1
        -- #1075: where the route's code is not the units' (`lean-backend` compiles a unit with
        -- an `sret` copy or a void call with the return-pin lowering `Stock.VoidCall.NI`; on
        -- such an `sret` copy `routes[0]` falls back to `lowerFunction`, and `attemptT` with the
        -- return-pin lowering fails the typed checks `okRWithTS`: itertools' specializations),
        -- the placement is not rust-lld's layout and the link's checks of rust-lld's output fail
        -- (`regionOkB`, `outsideOkB`) with no failing function: leave out the functions whose
        -- placed span is not rust-lld's when that set is the smallest (they keep cg_clif's code,
        -- as outside code; `attemptT_correct` has no per-function input premise)
        let moved := if e == SemanticCompilerWith.outOkTSMsg then [] else (spanFails SP markers).map (·.1)
        if badFns.isEmpty && !moved.isEmpty && moved.length < min typedN stockFns.length then
          IO.eprintln s!"lean-link: {exe}: --verified: typed Stock route: leaving out the {moved.length} function(s) whose placed code is not the units' (span to the next function not rust-lld's) {moved.take 3}; not written"
          printExclusions exe S0 SC true moved (only := true)
          return 1
      let typedSmaller := typedN ≤ stockFns.length
      IO.eprintln s!"lean-link: {exe}: --verified: typed scope: {stockFns.length} function(s) compiled by the Stock lowering, which compileExeT does not reproduce (lowerFunction) {stockFns.take 3}; leaving out {if typedSmaller then s!"the {typedN} typed function(s)" else s!"those {stockFns.length}"}; not written"
      if typedSmaller then printExclusions exe S0 SC false
      else printExclusions exe S0 SC true stockFns
      return 1
    match Link.DeadCleanup.compileExeT SC file0 with
    | .ok file =>
      IO.FS.writeBinFile exe file
      IO.println s!"lean-link: {exe}: {summary} written by Link.DeadCleanup.compileExeT (Link.DeadCleanup.compileExeT_correct)"
      -- #1088: through the frontend, `Front.bundle_correct_rawTCp`/`…raw_peakTCp` at `S0` (`hb`:
      -- `buildSpec` of the bundle read gave `S0` above), `SC` (`hcp`: `Front.placedFrom_cp_funcs`,
      -- `rfl`: `SC0 = S0.cp` on this route) and `hsrc = srcOk` (decided above)
      IO.println <| midCov s!"lean-link: {exe}: coverage: Link.DeadCleanup.compileExeT_correct, Link.DeadCleanup.compileExeT_correct_peak (returned values by class); the bundle's program (before the i128 legalisation and constant-phi removal), in SrcScopeB: Link.DeadCleanup.compileExeT_correct_sourceCp, Link.DeadCleanup.compileExeT_correct_source_peakCp; cg_clif's program: Front.bundle_correct_rawTCp, Front.bundle_correct_raw_peakTCp; admission (--verified): every function meets fnScopeInTB (InScopeInT) or the admission predicate fnScopeInTCB; totality: no theorem covers this executable (Link.DeadCleanup.compileExeT_total_reach_input needs InScopeIn; {typedN} function(s) are outside fnScopeInB); {tcbN} function(s) admitted only through fnScopeInTCB"
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
      printExclusions exe S0 SC true (bad.map (·.1))
      return 1
  -- This complete-file attempt leaves every previous mode and retry action below intact.
  let returnPinEnabled := !opt && !tailOn && SC0.funcs.any (fun fi =>
    Backend.Stock.MemorySretCopy.eligible fi.func || (Backend.Stock.VoidCall.sourceData? fi.func).isSome) &&
    -- #1108: `ReturnPinCompilerWith.attempt` fails when the input conditions do (`scope0`)
    scope0.get
  if returnPinEnabled then
    let lower := Backend.Stock.VoidCall.NI.lowerValidated
    let SP := SC0.placedProductionWith lower deadCleanup
    match Link.ReturnPinCompilerWith.attempt lower SP file0 deadCleanup with
    | .ok file =>
      IO.FS.writeBinFile exe file
      IO.println s!"lean-link: {exe}: {summary} written by Link.ReturnPinCompilerWith.attempt (Link.ReturnPinCompilerWith.attempt_correct, Link.ReturnPinCompilerWith.attempt_correct_depth)"
      if let some f := ldFile then
        match ← ldCheck SP file0 f with
        | .ok () => IO.println s!"lean-link: {exe}: lean-ld's plan meets the link spec (Plan.specOkB)"
        | .error e => IO.eprintln s!"lean-link: {exe}: lean-ld's plan: {e}"
      let src := if srcOk then
          "; the bundle's program (before the i128 legalisation and constant-phi removal), in SrcScopeB: Link.ReturnPinCompilerWith.attempt_correct_sourceCp, Link.ReturnPinCompilerWith.attempt_correct_source_peakCp"
        else "; outside SrcScopeB: about the legalised program only"
      IO.println <| midCov s!"lean-link: {exe}: coverage: Link.ReturnPinCompilerWith.attempt_correct, Link.ReturnPinCompilerWith.attempt_correct_depth{src}"
      return 0
    | .error _ => pure ()
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
          "; the bundle's program (before the i128 legalisation and constant-phi removal), in SrcScopeB: Link.SemanticCompilerWith.attempt_correct_sourceCp, Link.SemanticCompilerWith.attempt_correct_source_peakCp"
        else "; outside SrcScopeB: about the legalised program only"
      let scope := if verified then "; input conditions InScopeIn decided (--verified; no totality theorem for this route)" else ""
      IO.println <| midCov s!"lean-link: {exe}: coverage: Link.SemanticCompilerWith.attempt_correct, Link.SemanticCompilerWith.attempt_correct_depth, Link.SemanticCompilerWith.attempt_correct_peak{src}{scope}"
      return 0
    -- the unwind tables (S10f): with the cleanup compiler, `compileExeU SC file0 = .ok file`
    let unwOk := deadCleanup && Link.DeadCleanup.unwOkB SC file
    IO.FS.writeBinFile exe file
    IO.println s!"lean-link: {exe}: {summary} written by {compilerName} ({theoremName})"
    let src := if srcOk then
        s!"; the bundle's program (before the i128 legalisation and constant-phi removal), in SrcScopeB: {thm s!"{exeName}_correct_sourceCp"}, {thm s!"{exeName}_correct_source_peakCp"}"
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
    let scope := if verified then s!"; input in InScopeIn (--verified); totality: {totalAll}{if ldOk then "" else " (its layout, reach and file0 premises decided only with --ld)"}" else ""
    -- the exceptional edges: `compileExeU SC0 file0 = .ok file` (`compileExeOptU S` under `--opt`)
    let unw := if unwOk && !tailOn then
        if opt then
          s!"; exceptional edges: {thm "compileExeOpt_correct_unwind"}, {thm "compileExeOpt_correct_unwind_peak"}"
        else s!"; exceptional edges: {thm "compileExe_correct_unwind"}, {thm "compileExe_correct_unwind_peak"}"
      else ""
    IO.println <| midCov s!"lean-link: {exe}: coverage: {thm s!"{exeName}_correct"}, {thm s!"{exeName}_correct_peak"}{src}{scope}{unw}"
    if deadCleanup && !unwOk then
      IO.println s!"lean-link: {exe}: exceptional edges not covered (unwOkB: {Link.DeadCleanup.unwFail SC file})"
    -- report only (S10g, #404): the unwinding conditions of the totality argument, measured
    if deadCleanup && !tailOn then
      IO.println s!"lean-link: {exe}: unwinding conditions: {Link.DeadCleanup.unwReport SC file}"
    return 0
  | .error e =>
    -- Recover a typed file with its actual complete route and production stage.
    if !opt && !tailOn then
      for typedLower in routes do
        let TP := SC0.placedProductionWith typedLower deadCleanup
        match Link.TypedCompilerWith.attempt typedLower TP file0 deadCleanup with
        | .ok file =>
          IO.FS.writeBinFile exe file
          IO.println s!"lean-link: {exe}: {summary} written by Link.TypedCompilerWith.attempt (Link.TypedCompilerWith.attempt_correct)"
          if let some f := ldFile then
            match ← ldCheck TP file0 f with
            | .ok () => IO.println s!"lean-link: {exe}: lean-ld's plan meets the link spec (Plan.specOkB)"
            | .error why => IO.eprintln s!"lean-link: {exe}: lean-ld's plan: {why}"
          let src := if srcOk then
              "; the bundle's program (before the i128 legalisation and constant-phi removal), in SrcScopeB: Link.TypedCompilerWith.attempt_correct_sourceCp, Link.TypedCompilerWith.attempt_correct_source_peakCp"
            else "; outside SrcScopeB: about the legalised program only"
          IO.println <| midCov s!"lean-link: {exe}: coverage: Link.TypedCompilerWith.attempt_correct, Link.TypedCompilerWith.attempt_correct_depth, Link.TypedCompilerWith.attempt_correct_peak{src}"
          return 0
        | .error _ => pure ()
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
    -- `scopeFailsFast_eq`, in parallel (#1108)
    let X := LinkIdx.of P []
    let SI := sigIdx P syms
    let bad := (P.funcs.zip (parMap (fun g => scopeFailsFast (fun n => fm[n]?) syms X SI g)
      P.funcs)).filterMap fun (g, fs) => match fs with
      | [] => none
      | fs => some (g.name, fs)
    let causes := (bad.flatMap (·.2)).eraseDups.map fun c => s!"{c} {(bad.filter (·.2.contains c)).length}"
    let scopeName := if e == outOfScopeInMsg then "InScopeIn" else "InScopeP"
    let fnScope := if e == outOfScopeInMsg then "fnScopeInB" else "fnScopeB"
    let what := if verified then "--verified: not written" else s!"linking with {linkerName} (outside {theoremName} scope)"
    IO.eprintln s!"lean-link: {exe}: outside compileExe's input conditions ({scopeName}): {bad.length} function(s) failing the program-level per-function conditions (by cause: {causes}) {(bad.take 3).map (·.1)}, distinct names {namesNodupB (P.funcs.map (·.name))}, {if e == outOfScopeInMsg then s!"addrSlotsInputB {addrSlotsInputB P syms}" else s!"addrSlotsInB {addrSlotsInB P syms}"} (else {fnScope}); {what}"
    for (n, fs) in bad do
      IO.eprintln s!"lean-link:   {n}: {fs}"
    if verified then
      printExclusions exe S0 SC typedOk
      return 1
    -- #734 (#691 without `--verified`): where `lean-backend` compiled a function with the Stock
    -- lowering (`stockDiffersB`), the typed compilers and `link SC` (`lowerFunction` on every
    -- function) reproduce neither the units' code nor the layout rust-lld reserved for it; the
    -- bare Lean linker then links on the Stock placement (`compileWithRoutes`' routes in order)
    let stockFns := if !opt && !tailOn then
        (SC.funcs.zip (parMap (fun fi => TypedStockShared.stockDiffersB routes[0]! fi.func) SC.funcs)).filterMap
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
        IO.println <| midCov s!"lean-link: {exe}: coverage: Link.DeadCleanup.compileExeT3_correct (typed scope InScopeInT3, OutOkTCleanup; returned values by class)"
        return 0
      | .error e3 =>
        IO.eprintln s!"lean-link: {exe}: decider-free typed scope: {e3}"
        match Link.DeadCleanup.compileExeT SC file0 with
        | .ok file =>
          IO.FS.writeBinFile exe file
          IO.println s!"lean-link: {exe}: {summary} written by Link.DeadCleanup.compileExeT (Link.DeadCleanup.compileExeT_correct)"
          IO.println <| midCov s!"lean-link: {exe}: coverage: Link.DeadCleanup.compileExeT_correct (typed scope InScopePT, OutOkTCleanup; returned values by class)"
          return 0
        | .error e => IO.eprintln s!"lean-link: {exe}: typed scope: {e}"
    if !stockFns.isEmpty then
      IO.eprintln s!"lean-link: {exe}: {stockFns.length} function(s) compiled by the Stock lowering, which the typed compilers and {linkerName} do not reproduce (lowerFunction) {stockFns.take 3}; linking on the Stock placement"
      for (lower, i) in routes.zipIdx do
        match Link.leanLinkProductionWith lower (SC0.placedProductionWith lower deadCleanup) file0 deadCleanup with
        | .ok file =>
          IO.FS.writeBinFile exe file
          IO.println s!"lean-link: {exe}: {summary} written by Link.leanLinkProductionWith (Stock route {i})"
          IO.println <| midCov s!"lean-link: {exe}: coverage: none (outside {scopeName}; Link.leanLinkProductionWith, no compiler theorem)"
          return 0
        | .error e => IO.eprintln s!"lean-link: {exe}: Stock route {i}: {e}"
      return 1
    match link SC file0 with
    | .error e => do IO.eprintln s!"lean-link: {exe}: {e}"; return 1
    | .ok file =>
      IO.FS.writeBinFile exe file
      IO.println s!"lean-link: {exe}: {summary} written by {linkerName}"
      IO.println <| midCov s!"lean-link: {exe}: coverage: none (outside {scopeName}; {linkerName}, no compiler theorem)"
      return 0

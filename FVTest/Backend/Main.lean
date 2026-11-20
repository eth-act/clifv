import FV.Backend
import FV.Backend.ReturnPinProduction
import FV.Opt.Legalize128Pass
import FV.Opt.LegalExn
import FV.Opt.ConstPhiSelect
import FVTest.Opt.Common
import FVTest.Backend.StockConfig
import FVTest.Backend.I128Native
import FVTest.Backend.AllocChoice
import FVTest.Backend.CraneliftInput
import FV.Backend.Proof.LowerSimUCheck
import FV.Backend.Proof.LowerSimUCheckTC
import FV.Compile.SubsetTC
import FV.E2E.RegLevelFrameSaved
import FV.E2E.RegLevelUTry
import FV.E2E.RegLevelLeafKeep
import FV.E2E.DeadCleanupPipeline
import FVTest.Backend.FnVerdict
import FV.Opt.MidValCond
import FV.Link.ConstPhiCompile
import FV.Link.MidPair
import FV.E2E.SrcScopeDefs

/-!
`lake exe lean-backend <in.clif> <out.o|out.s> [--traps <out.json>] [--rules <out.txt>]
[--dump <dir>] [--regalloc lean|regalloc2|spill|stack|regalloc2-small] [--personality <sym>]
[--opt [--opt-* options]]`: compile every function of a `.clif` file with the
Lean backend (`FV/Backend.lean`). Register allocation: `regalloc2` (default, as Cranelift: the
external `lean-regalloc` oracle, `$LEAN_REGALLOC` or `rust/target/release/lean-regalloc`, given
the code in the form Cranelift's lowering hands to regalloc2 (vreg numbering, `args`, calls to
`sret` callees: `FVTest/Backend/CraneliftInput.lean`); every allocation validated by the Lean checker `checkAlloc`
with the spill allocation as fallback, `docs/contracts/regalloc.md`; with `$FV_RA_OUT` set, the
answers are written there; with `$FV_RA_DIAG` set, one line per function is appended there: the
code regalloc2 was given and the allocation lowered), `lean` (the Lean allocator `leanAlloc`,
`FV/Backend/LinearScan.lean`, validated the same way, `FVTest/Backend/AllocChoice.lean`),
`spill` (the fallback for every function), `stack` (the
stack-slot baseline), or `regalloc2-small` (regalloc2 with the 10-register stress environment
`smallEnv`, for testing spill code). If the output path ends in `.o`, write an ELF relocatable object encoded
by the Lean encoder (`FV/Backend/{Encode,Obj}.lean`, no assembler); otherwise write assembly
text (for `llvm-mc`, the encoder's test oracle). Optionally write the function/trap table that
`clif-native --functions-obj` reads (`--traps`), the names of the ISLE rules that fired
(`--rules`, one per line), and per function `name.bin`/`name.relocs.json`/`name.traps.json`
into `dir` (`--dump`, the schema of `clif2obj`'s dumps). Functions the backend does not
support are listed on stderr (and in the table), as is every fired rule outside the
emitter-subset closure (`Isle.Aarch64.Closure.rules`). Exit status 0 unless the arguments are
wrong, the input cannot be read, or encoding fails (an encoder or backend bug; the message
names the function and instruction). With `--opt`, every function is first optimised by the
Lean mid-end (`Opt.optimizeExe`, the executable compiler's mid-end, `docs/contracts/midend.md`;
options in `FVTest/Opt/Common.lean`).
With `--personality <sym>` (`cargo fv`: `rust_eh_personality`), functions with landing pads
(`try_call`) get cg_clif's LSDA and a `zLPR` CIE with that personality routine
(`FV/Backend/Obj.lean`); without it their landing pads have no LSDA (as Cranelift's own
objects, which leave the LSDA to the embedder).

Every function that mentions `i128` is first legalised by `Opt.Legalize128` (rewritten to
plain `i8..i64` CLIF before the mid-end and the backend). A legalised function the validator
`Opt.Legal.checkW` accepts is covered by `E2E.backend_correct_legal_wide` and treated like any other
function (`InSubset` and `lowerCheck` decided on the legalised form); a rejected one is
reported unverified ("i128 legalized (outside backend_correct: …)"). Under `--opt` with the
proven rule sets (`--opt-proven-only`) a legalised function is covered by
`E2E.backend_correct_legal_opt_wide` (the legalisation composed with the mid-end), every other by
`E2E.backend_correct_opt_exe` (`call_indirect`, `try_call`, `try_call_indirect` included); with
unproven rules every legalised function is reported unverified. The unwinding of a legalised
function with a `try_call` is covered by `E2E.backend_correct_legal_unwind_any` when the
handler-edge check `Opt.Legal.exnOk` and the unwinding theorem's checks pass (dead cleanup,
no `--opt`). Under `--opt` with the proven rule sets, the unwinding of a function that is not
legalised is covered by `E2E.backend_correct_opt_exe_cleanup_unwind_any` (without dead cleanup
`E2E.backend_correct_opt_exe_unwind_any`) when its compiled form is the mid-end's output on its
source function and the unwinding theorem's checks pass on the optimised function; a legalised
one by `E2E.backend_correct_legal_opt_unwind_any` (dead cleanup) when its compiled form is the
mid-end's output on the source function's legalisation, which `Opt.Legal.check` and
`Opt.Legal.exnOk` accept, and the checks pass.

Constant-phi removal (#990): after the `i128` legalisation and before the mid-end and the
backend, every function goes through `Opt.ConstPhi.run` (Cranelift's `eliminate_unreachable_code`
and `remove_constant_phis`, which Cranelift runs at every optimisation level) when the pass changes
it and its output, printed after the file's header, parses back to itself
(`Opt.ConstPhi.select`, the decision `link-check` and `lean-link` take, `FnInput.cp`). A
function the pass changed is covered by the theorems above composed with the pass
(`FV/E2E/PassX.lean` at `T := Opt.ConstPhi.run`, with `--opt` at `T := Opt.ConstPhi.runOpt cfg`):
`E2E.backend_correct_pass{,_cleanup}`, `backend_correct_pass_finalTCF`,
`backend_correct_legal_pass_wide{,_cleanup}`, `backend_correct_pass{,_cleanup}_unwind_any`,
`backend_correct_legal_pass_unwind_any`, and in general `E2E.pass_lift`. On the Stock path
(`compileFileReturnPinWhen` enabled) the Stock theorem `backend_correct_world_niX_semantic_return_pins`
is composed with them (#1100, `FV/E2E/SemanticReturnPinsPass.lean`):
`E2E.backend_correct_legal_wide_semantic_return_pins`, `backend_correct_pass_semantic_return_pins`
and `backend_correct_legal_pass_wide_semantic_return_pins` (`FVTest.Backend.FnVerdict`).

With `--settings <request.json> --settings-receipt <receipt.json>` (the proved settings mode),
the settings of a Cranelift filetest (the `--stock-config` request schema) are compiler input:
settings the proved compiler does not implement reject the request (exit 3) or, per function,
the function's output (`StockConfig.admit`; "compiled, not for these settings: …"). No
stock-configured step runs: the functions are compiled exactly as without the option. The
receipt lists, per function, whether `backend_correct` covers it. Without `preserve_frame_pointers`
a leaf that needs no frame is compiled without one (`Backend.frameless`); it is covered by
`E2E.backend_correct_final_cleanup_leaf` (normal-return form: the leaf makes no call) when its
code passes `FnAsm.leafChk` and its arguments are in registers (`E2E.regArgsB`), which stderr and
the receipt (`theorem`, `frameless_leaf`) state. `scripts/stock-compiler-compare.py`
counts the outputs of this mode that are identical to stock and covered (the honest metric).

A function inside the theorem's scope whose size is over the validation budget
(`Backend.validationBudget`, blocks × values) is compiled without running the lowering
validator and listed as `compiled, unverified (validation budget)`; an `i128`-legalised function
whose legalisation is over the same budget is not checked by the legalisation validator
(`Opt.Legalize128.overCheckBudget?`) and is listed unverified with that reason. A function
whose instructions × blocks exceed the compile budget (`compileBudget`) is not compiled
(`unsupported: compile budget: …`). With `--skip-unverified` (`cargo fv` under `--lean-link`,
which keeps cg_clif's code for every unverified function), a function whose verdict is
unverified before it is compiled (the legalisation's reason, or over the validation budget) is
not compiled and is listed `not compiled (--skip-unverified), unverified (…)` with the reason it
would get compiled.

With `--midval-opt <g.opt.clif>` (#1119; `cargo fv` passes Cranelift's optimised dump of a function
whose dump header says `opt_level` is not `none`): for the input's one function `f` and the
same-named function `g` of that file, `lean-backend` runs `Opt.MidVal.emitC (Opt.ConstPhi.run f) g`
and decides `Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints` itself, and `Link.midPairB`
on the two functions after constant-phi removal and the `i128` legalisation (`FnInput.cp`: the
pair `link-check` re-decides for its binary theorem `…_mid`). When both hold, `g` is
compiled in place of `f`, and when `g`'s verdict is a theorem that composes with the validator
(`FVTest.Backend.FnVerdict.midvalVerdict`; with a `try_call`, also its unwinding theorem) the
function is reported verified by the theorem through the validator
(`E2E.backend_correct_midval_*`, `FV/E2E/MidValPass.lean`, `MidValPassLegacy.lean`), about the
source function (`.unopt.clif`). Otherwise `f` is compiled exactly as without the option (same
objects, same lines). One more line says which: `%name: midval: validated (…)`, or
`%name: midval: rejected (…)` / `validated, not composed (…)`, `…; compiled from the .unopt.clif as
without --midval-opt`. Only in the default mode (dead cleanup; no `--opt`, `--stock-config`,
`--settings` or `--pipeline-t`). The effects of a compilation are deferred (`Act`) so that the one
not kept leaves no trace.
-/

open Backend

def usage : String :=
  "usage: lean-backend <in.clif> <out.o|out.s> [--traps <out.json>] [--rules <out.txt>] [--dump <dir>] [--regalloc lean|regalloc2|spill|stack|regalloc2-small] [--personality <sym>] [--opt] [--dead-cleanup|--no-dead-cleanup] [--pipeline-t] [--skip-unverified] [--midval-opt <g.opt.clif>] [--stock-config <request.json> --config-receipt <receipt.json>] [--settings <request.json> --settings-receipt <receipt.json>]"

/-- The rules the end-to-end theorem covers: the emitter-subset closure, and the `try_call`
rules of `lower_branch` (ids 1034 `bl`, 1035 GOT + `blr`: `Backend.Proof.tryRootRule`, proven by
`tryRulesCorrect`; 1036 `try_call_indirect`: `Backend.Proof.tryIndRootRule`, proven by
`tryIndRulesCorrect`), which are outside the generated closure (its opcodes have no
`try_call`). -/
def closureIds : Std.HashSet Isle.RuleId :=
  Isle.Aarch64.Closure.rules.foldl (fun s r => s.insert r.rule) ({} : Std.HashSet Isle.RuleId)
    |>.insert 1034 |>.insert 1035 |>.insert 1036

structure Opts where
  traps : Option String := none
  rules : Option String := none
  dump : Option String := none
  /-- `--regalloc`; default `regalloc2`. -/
  regalloc : Option String := none
  opt : Option Opt.Config := none
  personality : Option String := none
  stockConfig : Option String := none
  configReceipt : Option String := none
  /-- `--settings <request.json>` (with `--settings-receipt <receipt.json>`): the proved settings
  mode. The request has `--stock-config`'s schema. The proved compiler compiles every function
  unchanged (no stock-configured step); a function's output is for these settings only where it
  implements them (`StockConfig.admit`), and the receipt says per function whether
  `backend_correct` covers it. -/
  settings : Option String := none
  settingsReceipt : Option String := none
  deadCleanup : Bool := true
  /-- `--pipeline-t` (or `FV_PIPELINE_T=1`): compile with `E2E.LinkCheck.pipeT`'s pipeline (the
  D0 lowering, no dead cleanup, no Stock routes), the compiler `crate_correct_inScope` covers.
  Only for regenerating `crate-proofs/Crates/InScopeInputs` (`scripts/regen-crate-proofs.sh`). -/
  pipelineT : Bool := false
  /-- `--skip-unverified` (#1074): in the default mode (no `--opt`, `--stock-config`,
  `--settings` or `--pipeline-t`), a function whose verdict is unverified before it is compiled
  is not compiled (`preUnverifiedOf`). `cargo fv` passes it under `--lean-link`, where an
  unverified function's code is never used. -/
  skipUnverified : Bool := false
  /-- `--midval-opt <g.opt.clif>` (#1119): Cranelift's optimised dump of the function of the
  input (cg_clif's `.unopt.clif`, one function). `lean-backend` decides
  `Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints` itself (the certificate and hints from
  `Opt.MidVal.emitC`) and, when it holds and the theorem of the compiled `g` composes with the
  validator (`FVTest.Backend.FnVerdict.midvalVerdict`), compiles `g` and names the theorem through
  the validator, about the source function `f`; otherwise it compiles `f` exactly as without the
  option. Only in the default mode (dead cleanup; no `--opt`, `--stock-config`, `--settings` or
  `--pipeline-t`). -/
  midvalOpt : Option String := none

/-- A deferred effect of a compilation (`runCore`): `run` replays the effects of the compilation
it keeps, in order, and drops those of a compilation of `g` it does not keep (`--midval-opt`). -/
inductive Act where
  | err (s : String)
  | file (p : System.FilePath) (c : String)
  | bin (p : System.FilePath) (b : ByteArray)
  | mkdir (p : System.FilePath)

def Act.run : Act → IO Unit
  | .err s => IO.eprintln s
  | .file p c => IO.FS.writeFile p c
  | .bin p b => IO.FS.writeBinFile p b
  | .mkdir p => IO.FS.createDirAll p

/-- The compile budget's size measure of a function (#1074): instructions (statements and
terminators) × blocks. After #1074's fixes (`Backend.repAt_eq_chain`, `Opt.Legal.checkW_eq_F`)
the super-linear parts of compiling a function are the emission check's queries (one per branch,
handler and alias) times the forwarding chains and label runs each walks, `MachBuffer`'s
erasures (one per removed branch) times the lines, and the relaxation rounds times the lines. -/
def compileCost (f : Clif.Function) : Nat :=
  (f.blocks.length + (f.blocks.map (·.body.length)).sum) * f.blocks.length

/-- The compile budget: a function whose `compileCost` exceeds it is not compiled (`cargo fv`
keeps cg_clif's code). The largest function measured, ruint's
`bits::tests::test_primitive_shifts` (2,242,370,287), compiles in about 18 min. -/
def compileBudget : Nat := 20000000000

/-- The reason `f` is not compiled: over the compile budget. -/
def overCompileBudget? (f : Clif.Function) : Option String :=
  let c := compileCost f
  if c > compileBudget then
    some s!"compile budget: {c} instructions × blocks > {compileBudget}"
  else none

/-- The verdict `compileFileWithLowering` gives a function before compiling it, when that verdict
is unverified: its kind (as `run` prints it) and reason, with `compileFileWithLowering`'s
precedence. `pre` is the function's reason from the legalisation (`preUnverified`); a function
over the validation budget (`overBudget?`) gets the scope reason (`unverifiedReason?`) if any,
else the budget's. Every other unverified reason is decided on the compiled code. -/
def preUnverifiedOf (pre : Option String) (f : Clif.Function) : Option (String × String) :=
  match pre, overBudget? f with
  | some r, _ => some ("outside backend_correct", r)
  | none, some b => some ((unverifiedReason? f).elim ("validation budget", b) ("outside backend_correct", ·))
  | none, none => none

/-- One function's allocation as the backend lowered it: the prepared VCode `vcp`, the
allocation `rf` with `lowerRFunc vcp rf = .ok af` (`lowerAllocReady_eq`, `lowerAlloc_eq`), `af`,
and whether `checkAlloc vcp rf` accepted `rf` while allocating (`false` for the spill fallback,
which `allocResult` lowers without the checker); `none` without an `RFunc` (the stack allocator)
or when `prepare` failed. -/
abbrev AllocRecord := Option (VCode × RFunc × AFunc × Bool)

/-- `allocResult vcp ra` (the same choice, by its definition), with whether `checkAlloc` accepted
the allocation it returns. -/
def allocChecked (vcp : VCode) (ra : Except String RFunc) : RFunc × Bool :=
  match ra with
  | .ok rf =>
    if (checkAlloc vcp rf).isOk then
      match lowerRFunc vcp rf with
      | .ok _ => (rf, true)
      | .error _ => (spillAlloc vcp, false)
    else (spillAlloc vcp, false)
  | .error _ => (spillAlloc vcp, false)

theorem allocChecked_fst (vcp : VCode) (ra : Except String RFunc) :
    (allocChecked vcp ra).1 = allocResult vcp ra := by
  cases ra with
  | error e => rfl
  | ok rf =>
    unfold allocChecked allocResult
    by_cases hc : (checkAlloc vcp rf).isOk = true
    · simp only [hc, ↓reduceIte]
      cases lowerRFunc vcp rf <;> rfl
    · simp only [hc, ↓reduceIte, Bool.false_eq_true]

/-- The flag is `checkAlloc`'s acceptance of the allocation returned. -/
theorem allocChecked_snd {vcp : VCode} {ra : Except String RFunc}
    (h : (allocChecked vcp ra).2 = true) : (checkAlloc vcp (allocChecked vcp ra).1).isOk = true := by
  cases ra with
  | error e => simp [allocChecked] at h
  | ok rf =>
    unfold allocChecked at h ⊢
    by_cases hc : (checkAlloc vcp rf).isOk = true
    · simp only [hc, ↓reduceIte] at h ⊢
      cases hl : lowerRFunc vcp rf with
      | ok af => simpa [hl] using hc
      | error e => simp [hl] at h
    · simp [hc] at h

/-- Which allocation `lowerAllocReady vcp ra` lowers, and why (`FV_RA_DIAG`). -/
def allocVerdict (vcp : VCode) (ra : Except String RFunc) : String :=
  match ra with
  | .error e => s!"no answer: {e}"
  | .ok rf =>
    match checkAlloc vcp rf with
    | .error e => s!"checkAlloc: {e}"
    | .ok _ =>
      match lowerRFunc vcp rf with
      | .error e => s!"lowerRFunc: {e}"
      | .ok af => if emitReady af then "regalloc2" else "not emitReady"

/-- `Allocator.run`, also returning each function's `AllocRecord` (the objects the unwinding
theorems name). The `regalloc2` case is `allocateRegalloc2` with the allocation it lowers
(`allocResult vcp (readyAnswer vcp ra)`) kept; `lean-regalloc` is given `(shapeOf vcp).code`
(`CraneliftInput.shape`: regalloc2's input as Cranelift builds it, #551), its answer read back
and rebuilt against `vcp`. -/
def allocRecording (a : Allocator) (vcs : Array VCode)
    (shapeOf : VCode → CraneliftInput.Shape := fun vcp => .same vcp "") :
    IO (Array (Except String AFunc) × Array AllocRecord) := do
  match a with
  | .stack => pure (vcs.map allocate, vcs.map fun _ => none)
  | .spill =>
    let ps := vcs.map prepareChecked
    let afs := ps.map (·.bind fun vcp => lowerRFunc vcp (spillAlloc vcp))
    pure (afs, (ps.zip afs).map fun (p, af) => match p, af with
      | .ok vcp, .ok af => some (vcp, spillAlloc vcp, af, false)
      | _, _ => none)
  | .regalloc2 bin env =>
    let prepared := vcs.map prepareChecked
    let ok := prepared.filterMap (·.toOption)
    let shapes := ok.map shapeOf
    let rs : Array (Except String RFunc) ← do
      try
        match ← CraneliftInput.runLeanRegallocVia bin env shapes ok with
        | .error e => pure (ok.map fun _ => .error e)
        | .ok rs => pure (rs.map (·.bind RAResult.oracle))
      catch e => pure (ok.map fun _ => .error (toString e))
    let mut out : Array (Except String AFunc) := #[]
    let mut recs : Array AllocRecord := #[]
    let mut ans : Array String := #[]
    let diagOn := (← IO.getEnv "FV_RA_DIAG").isSome
    let mut diag : Array String := #[]
    let mut j := 0
    for p in prepared do
      match p with
      | .error e =>
        out := out.push (.error e)
        recs := recs.push none
      | .ok vcp =>
        let ra := rs[j]?.getD (.error "lean-regalloc: missing result")
        let af := lowerAllocReady vcp ra
        out := out.push af
        recs := recs.push (af.toOption.map fun a =>
          let (rf, chk) := allocChecked vcp (readyAnswer vcp ra)
          (vcp, rf, a, chk))
        ans := ans.push <| match ra with
          | .ok rf =>
            if raAnswerRoundTrip vcp rf then raAnswerJson vcp rf
            else raFailJson vcp.name "the answer does not rebuild the allocation"
          | .error e => raFailJson vcp.name e
        if diagOn then
          diag := diag.push s!"{vcp.name}\t{(shapes[j]?.map (·.why)).getD ""}\t{allocVerdict vcp ra}"
        j := j + 1
    -- `cargo fv --keep-temps`: regalloc2's answers, for `cargo fv link-proof` and `lean-link`
    -- (which rebuild the allocations from them, as for the Lean allocator's)
    if let some p ← IO.getEnv "FV_RA_OUT" then
      IO.FS.writeFile p ("{\"functions\":[" ++ ",".intercalate ans.toList ++ "]}\n")
    -- debugging aid (#551): per function, the code regalloc2 was given and the path taken
    if let some p ← IO.getEnv "FV_RA_DIAG" then
      let h ← IO.FS.Handle.mk p .append
      for l in diag do h.putStrLn l
    pure (out, recs)

/-- `allocRunOfName? n` with the `AllocRecord`s: the Lean allocator (`n = "lean"`:
`allocateLeanAnswers`, writing the answers to `$FV_RA_OUT` when set) records its allocation as
the `regalloc2` case does (`allocResult vcp (readyAnswer vcp ra)` with `ra = leanAlloc vcp`);
other names run `allocRecording a`. -/
def allocRecordingNamed (n : String) (a : Allocator) (vcs : Array VCode)
    (shapeOf : VCode → CraneliftInput.Shape := fun vcp => .same vcp "") :
    IO (Array (Except String AFunc) × Array AllocRecord) := do
  if n != "lean" then return ← allocRecording a vcs shapeOf
  let (afs, ans) := allocateLeanAnswers vcs
  if let some p ← IO.getEnv "FV_RA_OUT" then
    IO.FS.writeFile p ("{\"functions\":[" ++ ",".intercalate ans.toList ++ "]}\n")
  let recs := (vcs.zip afs).map fun (vc, af) => match prepareChecked vc, af with
    | .ok vcp, .ok af =>
      let (rf, chk) := allocChecked vcp (readyAnswer vcp (leanAlloc vcp))
      some (vcp, rf, af, chk)
    | _, _ => none
  pure (afs, recs)

/-- The first check of the unwinding theorem (`E2E.backend_correct_final_cleanup_unwind_any`, or
`E2E.backend_correct_final_unwind_any` without dead cleanup) that fails for a compiled function
`f` with a `try_call`, on the objects the theorem names: the lowering `vc` of `f` (`unwCheck`, the
exceptional-edge half of `lowerCheckU`; `lowerCheck` ran during compilation), the prepared
VCode and the allocation (`savedCheck vcp rf`), the allocated function and its final code
(`padsNonzeroB af fa`). `callSites`/`unwindRows` succeed for every compiled function
(compilation fails otherwise). The `_any` theorems have no premise on the calls of the last
block (#622: the call-site bridge `siteAt_any` holds for every block since #553), so the former
check `lastCallsOk` is not run; it is a pure check on the compiled objects, so dropping it
changes no generated code. With `tc` (a function with typed `try_call`s,
`Compile.functionETC`; #585): the same checks with the class-aware validator `unwCheckTC` over
`lowerCheckTC`'s recording (`loweringUTC_of_check`) in place of `unwCheck`; no unwinding theorem
covers typed `try_call`s yet. -/
def unwindCheckFailure? (f : Clif.Function) (rec : AllocRecord) (fa? : Option FnAsm)
    (tc : Bool := false) : Option String :=
  match lowerFunction f with
  | .error _ => some "lowerFunction"
  | .ok vc =>
    if tc && !(Compile.functionETC f && Proof.Driver.unwCheckTC f vc) then some "unwCheckTC"
    else if !tc && !Proof.Driver.unwCheck f vc then some "unwCheck"
    else match rec, fa? with
      | some (vcp, rf, af, _), some fa =>
        if !savedCheck vcp rf then some "savedCheck"
        else if !Proof.padsNonzeroB af fa then some "padsNonzeroB"
        else none
      | _, _ => some "no lowerRFunc allocation (allocator)"

/-- The typed theorems' premises on the objects `lean-backend` emitted for a function `f` outside
subset E (`FVTest.Backend.FnVerdict`, typed path): `lowerFunction f = .ok vc`, the typed validator
`lowerCheckFor f vc` (`lowerCheckT`/`TC`/`TCF`), `prepare` of the cleanup stage with `prepCheck`
(`prepareChecked`; outside subset E `cleanupStage f vc = DeadCleanup.prune vc`), `checkAlloc` of
the function's allocation `rf` on that prepared code, `lowerRFunc`, and `emitFunc` at the
function's index, whose code must be the emitted one (`FnAsm.text`): `none` when all hold, else
the first that fails. The Stock routes' providers may lower a function of the typed scope too;
this re-run makes the typed theorem's `lowerFunction` premise a decided fact, whatever the route. -/
def typedRecheck (f : Clif.Function) (cleanup : Bool) (rec : AllocRecord) (fa : FnAsm) :
    Option String :=
  match lowerFunction f with
  | .error e => some s!"lowerFunction fails ({e})"
  | .ok vc =>
    if !lowerCheckFor f vc then some "lowerCheckFor rejects lowerFunction's output"
    else match prepareChecked (if cleanup then cleanupStage f vc else vc), rec with
      | .error e, _ => some s!"prepare of lowerFunction's output ({e})"
      | _, none => some "no allocation record"
      | .ok vcp, some (_, rf, _, _) =>
        if !(checkAlloc vcp rf).isOk then
          some "checkAlloc rejects the allocation on lowerFunction's prepared code"
        else match lowerRFunc vcp rf with
          | .error e => some s!"lowerRFunc on lowerFunction's prepared code ({e})"
          | .ok af => match emitFunc fa.k af with
            | .error e => some s!"emitFunc ({e})"
            | .ok fa' =>
              if fa'.text == fa.text then none
              else some "lowerFunction's pipeline does not reproduce the emitted code (a Stock route lowered it)"

/-- One compilation of the input `src` (`run`), its effects deferred to `acts`. `mid = some (n, g)`
(`--midval-opt`, `n` the file's one function, `checkCertC` decided): `g` is compiled in place of the
source function `n`; the second component is `none` when `g`'s verdict is a theorem through the
validator (`FVTest.Backend.FnVerdict.midvalVerdict`, and the unwinding theorem through it for a
`try_call` function), else why not (`run` then drops this compilation and compiles `f`). Without
`mid` the compilation is `lean-backend`'s as before the option (#1119). -/
def runCore (input output : String) (o : Opts) (src : String)
    (mid : Option (String × Clif.Function)) (acts : IO.Ref (Array Act)) :
    IO (UInt32 × Option String) := do
  let say (s : String) : IO Unit := acts.modify (·.push (.err s))
  let wfile (p : System.FilePath) (c : String) : IO Unit := acts.modify (·.push (.file p c))
  let fin (rc : UInt32) : UInt32 × Option String :=
    (rc, mid.map fun _ => s!"lean-backend exits with {rc} on the optimised function")
  let pipelineT := o.pipelineT || (← IO.getEnv "FV_PIPELINE_T") == some "1"
  let o := if pipelineT then { o with deadCleanup := false } else o
  if o.configReceipt.isSome != o.stockConfig.isSome then
    say "lean-backend: --stock-config and --config-receipt must be supplied together"
    return fin 2
  if o.stockConfig.isSome && (o.opt.isSome || o.regalloc.any (· != "regalloc2") || o.personality.isSome) then
    say "lean-backend: stock configuration forbids independent opt/regalloc/personality overrides"
    return fin 2
  if o.settingsReceipt.isSome != o.settings.isSome then
    say "lean-backend: --settings and --settings-receipt must be supplied together"
    return fin 2
  if o.settings.isSome && (o.stockConfig.isSome || o.opt.isSome || o.regalloc.any (· != "regalloc2") ||
      o.personality.isSome || pipelineT) then
    say "lean-backend: --settings (the proved compiler) forbids --stock-config, --opt, --regalloc, --personality and --pipeline-t"
    return fin 2
  let mut stock : Option StockConfig.Config := none
  if let some path := o.stockConfig then
    let request ← match Lean.Json.parse (← IO.FS.readFile path) with
      | .ok j => pure j
      | .error e => do say s!"lean-backend: invalid configuration JSON: {e}"; return fin 2
    let checked := StockConfig.parse request
    let error := match checked with | .ok _ => none | .error e => some e
    if let some receipt := o.configReceipt then
      wfile receipt ((StockConfig.receipt request error none o.deadCleanup).pretty ++ "\n")
    match checked with
    | .error e => say s!"lean-backend: unsupported stock configuration: {e}"; return fin 3
    | .ok c => stock := some c
  -- the proved settings mode: the same request schema, the proved compiler unchanged
  let mut proved : Option StockConfig.Config := none
  if let (some path, some receipt) := (o.settings, o.settingsReceipt) then
    let request ← match Lean.Json.parse (← IO.FS.readFile path) with
      | .ok j => pure j
      | .error e => do say s!"lean-backend: invalid settings JSON: {e}"; return fin 2
    match StockConfig.parse request with
    | .error e =>
      wfile receipt ((StockConfig.settingsReceipt request (some e) [] o.deadCleanup).pretty ++ "\n")
      say s!"lean-backend: settings the proved compiler does not implement: {e}"
      return fin 3
    | .ok c => proved := some c
  let ra := o.regalloc.getD "regalloc2"
  let some runAlloc ← allocRunOfName? ra
    | do say s!"lean-backend: unknown allocator {ra}"; return fin 2
  -- the stock configuration requires regalloc2 (checked above)
  let alloc := (← Allocator.ofName? ra).getD .spill
  -- `--midval-opt`: the validated optimised function `g` in place of the source function
  let source0 := Clif.parseFile src
  let source : Clif.ParsedFile := match mid with
    | some (n, g) => { source0 with funcs := source0.funcs.map fun p =>
        if p.name == n then { p with func := .ok g } else p }
    | none => source0
  let lg := Opt.Legalize128.parsedFile128 source
  -- constant-phi removal after the legalisation, before the mid-end (#990)
  let header := Link.clifHeader src
  let lgc := Opt.ConstPhi.selectFile header lg.file
  let pf := match o.opt with | some c => Opt.optimizeParsedFile c lgc | none => lgc
  -- the compile budget (#1074): functions over it are not compiled (unsupported)
  let overCompile : List (String × String) := pf.funcs.filterMap fun p =>
    p.func.toOption.bind fun f => (overCompileBudget? f).map (p.name, ·)
  let pfc : Clif.ParsedFile :=
    { pf with funcs := pf.funcs.filter fun p => !overCompile.any (·.1 == p.name) }
  -- the mid-end theorems (`E2E.backend_correct_opt_exe`, `E2E.backend_correct_legal_opt`) cover
  -- every function, legalised ones included, for the proven rule sets
  let unv128 := match o.opt with
    | some c => if c.rules == .cranelift && c.ruleAllow == .proven then lg.unverified
      else lg.unverified ++ lg.accepted.map
        (·, "i128 legalized and optimised with unproven rules (outside backend_correct_legal_opt: --opt)")
    | none => lg.unverified
  let unvTry : List (String × String) := []
  -- `--skip-unverified` (#1074): a function unverified before it is compiled is not compiled
  let skipped : List (String × String × String) :=
    if o.skipUnverified && o.opt.isNone && stock.isNone && proved.isNone && !pipelineT then
      pfc.funcs.filterMap fun p => p.func.toOption.bind fun f =>
        (preUnverifiedOf ((unv128 ++ unvTry).lookup p.name) f).map fun (k, r) => (p.name, k, r)
    else []
  let pfc : Clif.ParsedFile :=
    { pfc with funcs := pfc.funcs.filter fun p => !skipped.any (·.1 == p.name) }
  -- The settings checks see each function before and after `i128` legalisation.
  let clif (name : String) : List Clif.Function :=
    (source.funcs ++ pf.funcs).filterMap fun p => if p.name == name then p.func.toOption else none
  let rejected ← IO.mkRef (#[] : Array (String × String))
  -- the allocation of each function as lowered (by VCode name), for the unwinding checks
  let records ← IO.mkRef (#[] : Array (String × AllocRecord))
  let allocNone : Array VCode → IO (Array (Except String AFunc)) := fun vcs => do
    -- regalloc2 sees the code as Cranelift's lowering gives it (`CraneliftInput.shape`, #551)
    let byName (n : String) : Option Clif.Function :=
      (pf.funcs.find? (·.name == n)).bind (·.func.toOption)
    let shapeOf := fun (vcp : VCode) => CraneliftInput.shape (byName vcp.name) o.deadCleanup vcp
    let (afs, recs) ← allocRecordingNamed ra alloc vcs shapeOf
    records.set ((vcs.map (·.name)).zip recs)
    pure afs
  -- the proved settings mode: `preserve_frame_pointers` as compiler input (`Backend.frameless`),
  -- and the settings checks (`StockConfig.admit`)
  let noFrame ← IO.mkRef (#[] : Array (String × String))
  let allocDefault : Array VCode → IO (Array (Except String AFunc)) := match proved with
    | some c => fun vcs => do
      rejected.set #[]; noFrame.set #[]
      StockConfig.admitWith c clif rejected noFrame allocNone vcs
    | none => allocNone
  let fa ← match stock with
    | none => (if pipelineT then compileFileWith allocNone pfc (unv128 ++ unvTry) false
        else compileFileReturnPinWhen (!o.opt.isSome &&
          !(pfc.funcs.any fun p => p.func.toOption.any fun f => f.blocks.any (·.term.isTry)))
          allocDefault pfc (unv128 ++ unvTry) o.deadCleanup)
    | some c => do
      -- native `i128` lowering for the functions `I128Native.nativeSet` admits (#554)
      let native := if pipelineT then [] else I128Native.nativeSet source pfc o.deadCleanup
      let configuredAlloc : Array VCode → IO (Array (Except String AFunc)) := fun vcs => do
        -- A whole-file retry replaces the previous attempt's configuration receipt.
        rejected.set #[]
        StockConfig.allocateWith c clif rejected allocNone (I128Native.replace native vcs)
      -- The functions are lowered as in the default mode (validated where their theorem
      -- applies, so the validated cleanup also skips dead code, #968, #969). The native `i128`
      -- functions stay unvalidated: `I128Native.replace` replaces their VCode.
      let why := "experimental stock-configured driver (outside backend_correct)"
      let fa ← compileFileReturnPinWhen (!pipelineT && !o.opt.isSome &&
          !(pfc.funcs.any fun p => p.func.toOption.any fun f => f.blocks.any (·.term.isTry)))
        configuredAlloc pfc
        (unv128 ++ unvTry ++ native.map (fun (n, _) => (n, why))) o.deadCleanup
      -- Every compiled function stays outside `backend_correct` in this mode: the configured
      -- allocation and the native `i128` code are unverified.
      pure { fa with
        unverified := fa.funcs.map fun a => (a.name, ((unv128 ++ unvTry).lookup a.name).getD why)
        unvalidated := [] }
  let fa := { fa with unsupported := fa.unsupported ++ overCompile }
  -- Frameless leaves (`--settings`, `preserve_frame_pointers=false`, #1028) are inside
  -- `E2E.backend_correct_final_cleanup_leaf` when its premises on the compiled function hold:
  -- the compiled code passes `FnAsm.leafChk` (no line but `ret` names x29/x30, so it makes no
  -- call: `bl`/`blr` write x30, and so do the TLS descriptor call and `try_call`'s call) and every
  -- argument is in a register (`E2E.regArgsB`). A function without calls is unwound through by
  -- no exception, so the theorem's normal-return form covers it. Only with dead cleanup (the
  -- theorem's pipeline), and not for an `i128`-legalised function (`backend_correct_legal_wide`
  -- has no frameless form). (`--opt` is refused in this mode.) A function
  -- constant-phi removal changed is covered by the theorem composed with the pass (`E2E.pass_lift`).
  -- With the spill fallback allocation (`AllocChecked` in place of `checkAlloc`), the theorem's
  -- `CompiledCleanupAL` form `E2E.backend_correct_final_cleanup_exL` covers it.
  let nf ← noFrame.get
  let leafMiss? (name : String) : Option String :=
    if !o.deadCleanup then some "no dead cleanup (backend_correct_final_cleanup_leaf's pipeline)"
    else if lg.accepted.contains name then some "i128-legalised"
    else if !(fa.funcs.find? (·.name == name)).any (·.leafChk) then
      some "FnAsm.leafChk: a line other than ret names x29/x30"
    else if !((pf.funcs.find? (·.name == name)).bind (·.func.toOption)).any (E2E.regArgsB ·.sig) then
      some "E2E.regArgsB: an argument on the stack"
    else none
  let rs0 ← rejected.get
  let leaves := nf.toList.filter fun p => fa.funcs.any (·.name == p.1) &&
    !fa.unverified.any (·.1 == p.1) && !fa.unvalidated.any (·.1 == p.1) && !rs0.any (·.1 == p.1)
  let outside := leaves.filterMap fun (n, why) => (leafMiss? n).map fun m =>
    (n, s!"{why} outside backend_correct_final_cleanup_leaf: {m}")
  let fa := { fa with unverified := fa.unverified ++ outside }
  let coveredLeaves := (leaves.filter fun p => (leafMiss? p.1).isNone).map (·.1)
  for n in coveredLeaves do
    say (s!"lean-backend: {input}: %{n}: frameless leaf, backend_correct_final_cleanup_leaf " ++
      "(normal-return form: FnAsm.leafChk admits no call, so no exception unwinds through it)")
  -- The per-function verdict (#1096): a compiled function inside the theorems' scope is reported
  -- verified only by the theorem whose checkable premises `lean-backend` decided on the objects it
  -- emitted (`FVTest.Backend.FnVerdict`: the path, the theorem, the checks); a failing premise
  -- (`formsCoveredB`, `checkAlloc` of the spill fallback, the typed re-run) makes it unverified.
  -- The Stock routes run when `compileFileReturnPinWhen` is enabled (no `--opt`, no `try_call` in
  -- the file the driver compiles, `pfc`, not `--pipeline-t`, not the stock-configured driver; #1107:
  -- the same condition as the driver's). Their `SemanticABI.checkCalls` premise is
  -- `Backend.compileFileReturnPinWhen_checkCalls` (#1101).
  let passT := if o.opt.isSome then "Opt.ConstPhi.runOpt cfg" else "Opt.ConstPhi.run"
  -- the pass changed the (legalised) source function
  let cpOn (name : String) : Bool :=
    ((lg.file.funcs.find? (·.name == name)).bind (·.func.toOption)).any (Opt.ConstPhi.keeps header)
  let provenOpt : Bool := match o.opt with
    | some c => c.rules == .cranelift && c.ruleAllow == .proven
    | none => false
  let recs ← records.get
  let stockOn := !pipelineT && !o.opt.isSome && stock.isNone &&
    !(pfc.funcs.any fun p => p.func.toOption.any fun f => f.blocks.any (·.term.isTry))
  let facts : List (String × FVTest.Backend.FnVerdict.Facts) := pf.funcs.filterMap fun p =>
    match p.func, fa.funcs.find? (·.name == p.name) with
    | .ok f, some a =>
      if fa.unverified.any (·.1 == p.name) || fa.unvalidated.any (·.1 == p.name) ||
          coveredLeaves.contains p.name || rs0.any (·.1 == p.name) then none
      else
        let rec? := (recs.find? (·.1 == p.name)).bind (·.2)
        let scope : FVTest.Backend.FnVerdict.Scope :=
          if Compile.functionE f then .integer else if Compile.functionET f then .typedT
          else if Compile.functionETC f then .typedTC else .typedTCF
        let (record, alloc, covered) : Bool × Bool × Bool := match rec? with
          | some (vcp, rf, af, chk) =>
            (true, chk || (checkAlloc vcp rf).isOk, Proof.formsCoveredB ⟨a.k, af.slotBase⟩ vcp)
          | none => (false, false, false)
        let typed := if scope == .integer || !record then none
          else typedRecheck f o.deadCleanup rec? a
        let src? := (lg.file.funcs.find? (·.name == p.name)).bind (·.func.toOption)
        let cpSrc := src?.any fun g => (unverifiedReason? g).isNone
        -- the Stock compositions' `InSubset` of the source before constant-phi removal (#1100)
        let cpSrcE := src?.any Backend.verifiable
        some (p.name,
          { scope, path := if stockOn then .stock else .legacy, cleanup := o.deadCleanup,
            opt := o.opt.isSome, optProven := provenOpt, legal := lg.accepted.contains p.name,
            cp := cpOn p.name, cpSrc, cpSrcE, cpT := passT, d0 := Stock.D0.eligible f, record, alloc,
            covered, typed })
    | _, _ => none
  -- `--midval-opt` (#1119): the compiled `g`'s verdict through the validator, or why none applies
  let midRes : Option (Except String FVTest.Backend.FnVerdict.Verdict) := mid.map fun (n, _) =>
    let why (p : List (String × String)) := p.lookup n
    match facts.lookup n with
    | some x => FVTest.Backend.FnVerdict.midvalVerdict x
    | none =>
      if let some r := why fa.unsupported then .error s!"the optimised function is not compiled ({r})"
      else if let some (_, _, r) := skipped.find? (·.1 == n) then
        .error s!"the optimised function is unverified before it is compiled ({r})"
      else if let some r := why fa.unverified then .error s!"the compiled g is unverified ({r})"
      else if let some r := why fa.unvalidated then .error s!"the compiled g is not validated ({r})"
      else if coveredLeaves.contains n then .error "frameless leaf: no theorem through the validator"
      else .error "the optimised function is not compiled"
  let verdicts : List (String × FVTest.Backend.FnVerdict.Verdict) := facts.map fun (n, x) =>
    match mid, midRes with
    | some (m, _), some (.ok v) => if n == m then (n, v) else (n, FVTest.Backend.FnVerdict.verdict x)
    | _, _ => (n, FVTest.Backend.FnVerdict.verdict x)
  let fails : List (String × String) :=
    verdicts.filterMap fun (e : String × FVTest.Backend.FnVerdict.Verdict) => e.2.fail.map (e.1, ·)
  let fa := { fa with unverified := fa.unverified ++ fails }
  if let (some request, some receipt) := (stock.map (·.request), o.configReceipt) then
    wfile receipt
      ((StockConfig.receipt request none (some (← rejected.get).toList) o.deadCleanup).pretty ++ "\n")
  if let (some c, some receipt) := (proved, o.settingsReceipt) then
    let rs ← rejected.get
    let verdict (name : String) : Lean.Json :=
      let why (p : List (String × String)) := p.lookup name
      if let some r := rs.toList.lookup name then
        Lean.Json.mkObj [("compiled", Lean.toJson (fa.funcs.any (·.name == name))),
          ("backend_correct", Lean.toJson false), ("setting_rejection", Lean.toJson r)]
      else if let some r := why fa.unsupported then
        Lean.Json.mkObj [("compiled", Lean.toJson false), ("unsupported", Lean.toJson r)]
      else if let some r := why fa.unverified then
        Lean.Json.mkObj [("compiled", Lean.toJson true), ("backend_correct", Lean.toJson false), ("unverified", Lean.toJson r)]
      else if let some r := why fa.unvalidated then
        Lean.Json.mkObj [("compiled", Lean.toJson true), ("backend_correct", Lean.toJson false), ("unvalidated", Lean.toJson r)]
      else if coveredLeaves.contains name then
        Lean.Json.mkObj [("compiled", Lean.toJson true), ("backend_correct", Lean.toJson true),
          ("theorem", Lean.toJson "backend_correct_final_cleanup_leaf"),
          ("frameless_leaf", Lean.toJson "no call (FnAsm.leafChk): the normal-return form covers it")]
      else if fa.funcs.any (·.name == name) then
        Lean.Json.mkObj [("compiled", Lean.toJson true), ("backend_correct", Lean.toJson true)]
      else Lean.Json.mkObj [("compiled", Lean.toJson false)]
    for (n, why) in rs do
      say s!"lean-backend: {input}: %{n}: compiled, not for these settings: {why}"
    wfile receipt ((StockConfig.settingsReceipt c.request none
      (pf.funcs.map fun p => (p.name, verdict p.name)) o.deadCleanup).pretty ++ "\n")
  let fa := match stock <|> proved with
    | some c => if c.unwind then fa else { fa with unwind := [] }
    | none => fa
  if output.endsWith ".o" || o.dump.isSome then
    match fa.layout with
    | .error e =>
      say s!"lean-backend: {input}: encoding failed: {e}"
      return fin 1
    | .ok fbs =>
      if output.endsWith ".o" then acts.modify (·.push (.bin output (elfObject fbs fa.unwind fa.lsda o.personality)))
      if let some d := o.dump then
        acts.modify (·.push (.mkdir d))
        for (_, fb) in fbs do
          acts.modify (·.push (.bin (System.FilePath.mk d / s!"{fb.name}.bin") (wordsBytes fb.words)))
          wfile (System.FilePath.mk d / s!"{fb.name}.relocs.json") fb.relocsJson
          wfile (System.FilePath.mk d / s!"{fb.name}.traps.json") fb.trapsJson
          if let some c := stock <|> proved then
            let metadata := Lean.Json.mkObj [
              ("name", Lean.toJson fb.name), ("alignment", Lean.toJson (4 : Nat)),
              ("unwind_disabled", Lean.toJson (!c.unwind)),
              ("stack_maps", Lean.toJson ([] : List String)),
              ("exception_metadata_comparison_supported", Lean.toJson false)]
            wfile (System.FilePath.mk d / s!"{fb.name}.metadata.json") (metadata.pretty ++ "\n")
  if !output.endsWith ".o" then wfile output fa.text
  if let some t := o.traps then wfile t fa.tableJson
  let names := Isle.Aarch64.program.ruleNames fa.rules
  if let some r := o.rules then wfile r (String.join (names.map (· ++ "\n")))
  for (id, n) in fa.rules.zip names do
    if !closureIds.contains id then
      say s!"lean-backend: {input}: rule {n} fired outside the emitter-subset closure"
  for (n, why) in fa.unsupported do
    say s!"lean-backend: {input}: %{n}: unsupported: {why}"
  for (n, why) in fa.unverified do
    say s!"lean-backend: {input}: %{n}: compiled, unverified (outside backend_correct): {why}"
  for (n, why) in fa.unvalidated do
    say s!"lean-backend: {input}: %{n}: compiled, unverified (validation budget): {why}"
  for (n, k, why) in skipped do
    say s!"lean-backend: {input}: %{n}: not compiled (--skip-unverified), unverified ({k}): {why}"
  -- A function with a `try_call` is inside `backend_correct_final` for the runs in which every
  -- callee of a `try_call` returns normally (callee contract `CalleeTryOk`: the results only; the
  -- exception payload registers are havocked on the normal return). Its unwinding (landing
  -- pads, the LSDA, the frame unwound by the CFI) is inside the unwinding theorem
  -- (`E2E.backend_correct_final_cleanup_unwind_any`, without dead cleanup
  -- `E2E.backend_correct_final_unwind_any`) when that theorem's checks pass on its compiled
  -- objects (`unwindCheckFailure?`). An `i128`-legalised function is inside
  -- `E2E.backend_correct_legal_unwind_any` (dead cleanup only) when, in addition, its legalisation
  -- is recomputed from the source function with the same result, and `Opt.Legal.check` and the
  -- handler-edge check `Opt.Legal.exnOk` accept it (`legalUnwOk`). Under `--opt` with the proven
  -- rule sets, a function that is not legalised is inside
  -- `E2E.backend_correct_opt_exe_cleanup_unwind_any` (without dead cleanup
  -- `E2E.backend_correct_opt_exe_unwind_any`) when its compiled form is `Opt.optimizeExe` of its
  -- source function, recomputed (`optUnwOk`), and the checks pass on the optimised function; a
  -- legalised one is inside `E2E.backend_correct_legal_opt_unwind_any` (dead cleanup only) when
  -- its compiled form is `Opt.optimizeExe` of the source function's legalisation, recomputed,
  -- which `Opt.Legal.check` and `Opt.Legal.exnOk` accept (`legalOptUnwOk`). No unwinding theorem
  -- composes unproven rule sets. A function the constant-phi removal changed (`cpOn`: its
  -- compiled form is `Opt.ConstPhi.select` of its (legalised) source function, before the
  -- mid-end) is covered by the same theorems composed with the pass (`FV/E2E/PassX.lean`:
  -- `backend_correct_pass{,_cleanup}_unwind_any`, `backend_correct_legal_pass_unwind_any`, at
  -- `T := Opt.ConstPhi.run`, with `--opt` at `T := Opt.ConstPhi.runOpt cfg`).
  let legalUnwOk (name : String) (g : Clif.Function) : Bool :=
    match (source.funcs.find? (·.name == name)).bind (·.func.toOption) with
    | some f => match Opt.Legalize128.function128Cert f with
      | .ok (g', cert) => Opt.ConstPhi.select header g' == g && Opt.Legal.check f g' cert &&
        Opt.Legal.exnOk f g' cert
      | .error _ => false
    | none => false
  let optUnwOk (name : String) (g : Clif.Function) : Bool :=
    match o.opt, (source.funcs.find? (·.name == name)).bind (·.func.toOption) with
    | some c, some f => provenOpt && Opt.optimizeExe (Opt.ConstPhi.select header f) c == g
    | _, _ => false
  let legalOptUnwOk (name : String) (g : Clif.Function) : Bool :=
    match o.opt, (source.funcs.find? (·.name == name)).bind (·.func.toOption) with
    | some c, some f => match Opt.Legalize128.function128Cert f with
      | .ok (g', cert) => provenOpt && Opt.optimizeExe (Opt.ConstPhi.select header g') c == g &&
        Opt.Legal.check f g' cert &&
        Opt.Legal.exnOk f g' cert
      | .error _ => false
    | _, _ => false
  let cpSrcOf (name : String) : Bool :=
    ((lg.file.funcs.find? (·.name == name)).bind (·.func.toOption)).any
      fun g => (unverifiedReason? g).isNone
  -- `--midval-opt`: why the compiled `g` gets no theorem through the validator (`none`: it does)
  let mut midFail : Option String := match midRes with
    | some (.error e) => some e
    | _ => none
  for (name, v) in verdicts do
    if v.thm.isNone then continue
    let some f := (pf.funcs.find? (·.name == name)).bind (·.func.toOption) | continue
    if !hasTryCall f then
      say s!"lean-backend: {input}: %{name}: {FVTest.Backend.FnVerdict.line v}"
      continue
    let legal := lg.accepted.contains name
    let why? : Option String :=
      if o.opt.isSome && !provenOpt then
        some "--opt with unproven rule sets: no unwinding theorem composes them (--opt-proven-only)"
      else if legal && !o.deadCleanup then
        some "i128 legalized: no unwinding theorem composes the legalisation without dead cleanup"
      else if o.opt.isSome && legal && !legalOptUnwOk name f then
        some "--opt, i128 legalized: not Opt.optimizeExe of the constant-phi removal of the source function's legalisation accepted by Opt.Legal.check and Opt.Legal.exnOk"
      else if o.opt.isSome && !legal && !optUnwOk name f then
        some "--opt: the compiled function is not Opt.optimizeExe of the constant-phi removal of its source function"
      else if o.opt.isNone && legal && !legalUnwOk name f then
        some "i128 legalized: Opt.Legal.check (no try_call_indirect, no call_indirect at an i128 signature) or Opt.Legal.exnOk (the handler edges) rejects"
      else if cpOn name && !cpSrcOf name then
        some "constant-phi removal: the source function is outside the scope, so no unwinding theorem composes the pass"
      else (unwindCheckFailure? f ((recs.find? (·.1 == name)).bind (·.2))
        (fa.funcs.find? (·.name == name))).map (s!"unwinding check failed: {·}")
    let unwThm := FVTest.Backend.FnVerdict.unwindThm o.deadCleanup o.opt.isSome legal (cpOn name)
      passT
    let unw0 : Except String String := match why? with
      | none =>
        if Compile.functionE f then .ok unwThm
        else .error "outside subset E: the unwinding theorems are about the integer lowering (lowerCheck), no unwinding theorem covers typed try_calls yet"
      | some why =>
        let rec? := (recs.find? (·.1 == name)).bind (·.2)
        let fa? := fa.funcs.find? (·.name == name)
        if why == "unwinding check failed: unwCheck" && Compile.functionETC f &&
            (unwindCheckFailure? f rec? fa? (tc := true)).isNone then
          .error "try_call with float values: the exceptional-edge conditions hold on the typed lowering (unwCheckTC, loweringUTC_of_check), no unwinding theorem covers typed try_calls yet"
        else .error why
    -- through the validator: the unwinding theorem through it, or `f` is compiled (#1119)
    let isMid := mid.any (·.1 == name)
    let unw : Except String String := match unw0 with
      | .ok _ => if isMid then .ok (FVTest.Backend.FnVerdict.unwindMidThm legal (cpOn name) passT)
        else unw0
      | .error why => .error why
    if isMid then
      if let .error why := unw0 then
        midFail := midFail <|> some s!"try_call: no unwinding theorem for the compiled g ({why})"
    say s!"lean-backend: {input}: %{name}: {FVTest.Backend.FnVerdict.line v true unw}"
  return (0, midFail)

/-- The decision of `--midval-opt` for the source text `src` and the optimised text `srcOpt`:
the function's name and `g` when `Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints` holds
for the certificate and branch-condition hints `Opt.MidVal.emitC` gives, and `Link.midPairB` holds
on the pair as `link-check` re-decides it on the bundle (each function's input after constant-phi
removal and the `i128` legalisation, `FnInput.cp`/`FnInput.func`: the program its binary theorem
is about), else why not (the function's name when there is one). -/
def midvalDecide (src srcOpt : String) : Except (Option String × String) (String × Clif.Function) := do
  let fs := (Clif.parseFile src).funcs
  let some p := fs.head? | throw (none, "the input has no function")
  if fs.length != 1 then throw (none, s!"the input has {fs.length} functions (only single-function files)")
  let f ← match p.func with
    | .ok f => pure f
    | .error _ => throw (some p.name, "the source function does not parse")
  let gs := (Clif.parseFile srcOpt).funcs
  let some k := gs.findIdx? (·.name == p.name)
    | throw (some p.name, "the optimised dump has no function of that name")
  let some q := gs[k]? | throw (some p.name, "the optimised dump has no function of that name")
  let g ← match q.func with
    | .ok g => pure g
    | .error _ => throw (some p.name, "the optimised function does not parse")
  let f' := Opt.ConstPhi.run f
  let (cert, hints) ← match Opt.MidVal.emitC f' g with
    | .ok c => pure c
    | .error e => throw (some p.name, s!"Opt.MidVal.check rejects: {e}")
  if !Opt.MidVal.checkCertC f' g cert hints then
    throw (some p.name, "Opt.MidVal.checkCertC rejects the emitted certificate")
  -- #1119 layer 2: the pair `link-check` decides for the binary theorem (`…_mid`), and `g`'s
  -- printed CLIF parsing back to it (`Front.mkInput`: else `link-check` cannot assemble the bundle)
  let fi0 : E2E.LinkCheck.FnInput := { clif := src, ra := "" }
  let fi1 : E2E.LinkCheck.FnInput := { clif := srcOpt, ra := "", k }
  if !Link.midPairB fi0.cp.func fi1.cp.func then
    throw (some p.name, "Link.midPairB rejects the pair after constant-phi removal and the i128 legalisation (link-check's pair)")
  let fiP : E2E.LinkCheck.FnInput := { clif := Link.clifHeader srcOpt ++ g.print, ra := "" }
  if !decide (fiP.src = g) then
    throw (some p.name, "the optimised function's printed CLIF does not parse back to it (link-check's bundle, Front.mkInput)")
  pure (p.name, g)

/-- `lean-backend`: one compilation (`runCore`), its effects replayed. With `--midval-opt` (#1119)
in the default mode: the optimised function `g` when `checkCertC` holds and its theorem composes
with the validator, else the source function `f`, compiled exactly as without the option; an
info line `midval: …` says which and why. -/
def run (input output : String) (o : Opts) : IO UInt32 := do
  let src ← IO.FS.readFile input
  let once (mid : Option (String × Clif.Function)) : IO (UInt32 × Option String × Array Act) := do
    let acts ← IO.mkRef #[]
    let (rc, why) ← runCore input output o src mid acts
    pure (rc, why, ← acts.get)
  let replay (acts : Array Act) : IO Unit := acts.forM Act.run
  let some optPath := o.midvalOpt | do
    let (rc, _, acts) ← once none
    replay acts
    return rc
  let note (n : Option String) (s : String) : IO Unit :=
    IO.eprintln s!"lean-backend: {input}: {(n.map (s!"%{·}: ")).getD ""}midval: {s}"
  let plain (n : Option String) (s : String) : IO UInt32 := do
    let (rc, _, acts) ← once none
    replay acts
    note n s!"{s}; compiled from the .unopt.clif as without --midval-opt"
    return rc
  let pipelineT := o.pipelineT || (← IO.getEnv "FV_PIPELINE_T") == some "1"
  if o.opt.isSome || o.stockConfig.isSome || o.settings.isSome || pipelineT || !o.deadCleanup then
    return ← plain none "not attempted (only in the default mode: dead cleanup, no --opt, --stock-config, --settings or --pipeline-t)"
  match midvalDecide src (← IO.FS.readFile optPath) with
  | .error (n, why) => plain n s!"rejected ({why})"
  | .ok (n, g) =>
    let (rc, why, acts) ← once (some (n, g))
    match rc, why with
    | 0, none =>
      replay acts
      note (some n) s!"validated (Opt.MidVal.checkCertC decided), compiled from the optimised dump {optPath}"
      return 0
    | _, some why => plain (some n) s!"validated, not composed ({why})"
    | rc, none => plain (some n) s!"validated, not composed (lean-backend exits with {rc} on the optimised function)"

def main (args : List String) : IO UInt32 := do
  let rec opts (o : Opts) : List String → Option Opts
    | [] => some o
    | "--traps" :: t :: rest => opts { o with traps := some t } rest
    | "--rules" :: r :: rest => opts { o with rules := some r } rest
    | "--dump" :: d :: rest => opts { o with dump := some d } rest
    | "--regalloc" :: a :: rest => opts { o with regalloc := some a } rest
    | "--personality" :: p :: rest => opts { o with personality := some p } rest
    | "--stock-config" :: c :: rest => opts { o with stockConfig := some c } rest
    | "--config-receipt" :: c :: rest => opts { o with configReceipt := some c } rest
    | "--settings" :: c :: rest => opts { o with settings := some c } rest
    | "--settings-receipt" :: c :: rest => opts { o with settingsReceipt := some c } rest
    | "--dead-cleanup" :: rest => opts { o with deadCleanup := true } rest
    | "--no-dead-cleanup" :: rest => opts { o with deadCleanup := false } rest
    | "--pipeline-t" :: rest => opts { o with pipelineT := true } rest
    | "--skip-unverified" :: rest => opts { o with skipUnverified := true } rest
    | "--midval-opt" :: g :: rest => opts { o with midvalOpt := some g } rest
    | _ => none
  let (optCfg, args) ← match Opt.parseOptArgs args with
    | .ok r => pure r
    | .error e => do IO.eprintln s!"lean-backend: {e}"; return 2
  match args with
  | i :: out :: rest =>
    match opts { opt := optCfg } rest with
    | some o => run i out o
    | none => do IO.eprintln usage; return 2
  | _ => do IO.eprintln usage; return 2

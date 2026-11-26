/-!
# The per-function verdict of `lean-backend` (#1096 part 2)

The one place where `lean-backend` pairs the path a function took with the theorem it names and
the checks it decided (as `FVTest/E2E/BinVerdict.lean` does for `link-check`). A function is
"verified" only when every checkable premise of the named theorem was decided on the objects
`lean-backend` emitted; a failing one names no theorem and the function is reported unverified.
The run and environment hypotheses of the theorems (the callee and `try_call` contracts, the
external and indirect-call contracts, the TLS resolver contract, the linked symbol addresses, the
ABI entry state and stack, `TrapsExplicit`) are not the tool's to decide and stay premises.

Paths (`lean-backend`'s driver, `FVTest/Backend/Main.lean`):

* **Stock** (`compileFileReturnPinWhen` enabled: no `--opt`, no `try_call` in the file): an
  integer function's lowering is one of the Stock routes' (`Backend.lowerCheckedVoidCallABI` and
  the providers below it) or the legacy one, each validated by a check that implies
  `SemanticABI.checkCalls` (`SemanticNI.check`, `lowerCheck`): proved for the driver's own run by
  `Backend.compileFileReturnPinWhen_checkCalls` (`FV/Backend/StockCheckCalls.lean`, #1101); the
  theorem is `E2E.backend_correct_world_niX_semantic_return_pins` with the artifact
  `CompiledSemanticReturnPins.of_checks_calls`, composed with the `i128` legalisation
  (`legal_wide_semantic_return_pins`) and constant-phi removal (`pass_semantic_return_pins`,
  `legal_pass_wide_semantic_return_pins`, `FV/E2E/SemanticReturnPinsPass.lean`, #1100) where
  those changed it and their checks hold (constant-phi removal: the source function before it is
  `Backend.verifiable`); otherwise about the compiled function.
* **legacy** (the Stock routes disabled): the lowering is `Stock.D0.defaultLower`, i.e.
  `lowerFunction` unless `Stock.D0.eligible`; an integer function gets `backend_correct_final`'s
  family (`_cleanup` with dead cleanup), composed with the `i128` legalisation (`legal_wide`),
  the mid-end (`opt_exe`, `legal_opt_wide`) and constant-phi removal (`pass`, `legal_pass_wide`)
  where those changed it and their checks hold; a `Stock.D0`-eligible one the path-independent
  theorem of the Stock path (composed as there, without `--opt`).
* **typed** (outside subset E): `lean-backend` re-runs `lowerFunction`, the typed validator
  (`lowerCheckFor`: `lowerCheckT`/`TC`/`TCF`), `prepare`, `checkAlloc`, `lowerRFunc` and the
  emission with the function's allocation and checks that they reproduce the emitted code; the
  theorem is the typed scope's (`backend_correct_final_cleanupT`, `backend_correct_world_cleanupTC`,
  `backend_correct_world_cleanupTCF`; without dead cleanup `finalT`/`finalTC`/`finalTCF`), composed
  with the `i128` legalisation and constant-phi removal where those changed the function and their
  checks hold (#1112, `FV/E2E/PassTypedCleanup.lean`: `pass_*`, `legal_wide_*`,
  `legal_pass_wide_*`; without dead cleanup only constant-phi removal in `typedTCF`,
  `backend_correct_pass_finalTCF`); otherwise about the compiled function. A function with
  `fcopysign` or `fma` at `f32`/`f64` (#35:
  `Compile.functionETCF`'s `instETFLO`, no `fma` with an `fneg`-defined second operand,
  `fmaNegYFree`) is in the scope `typedTCF`: `backend_correct_world_cleanupTCF` (without dead
  cleanup `backend_correct_finalTCF`), whose statement covers it through `functionETCF` and
  `lowerCheckTCF` (the `fcopysign`/`fma` roots `lowerRulesCorrectCS_program`,
  `lowerRulesCorrectFM_program` inside the proof).

On every path `lean-backend` decides `formsCoveredB` of the prepared code (the premise `FormsCovered`
of every theorem here) and `checkAlloc` of the allocation it lowered (the spill fallback's too).
-/

namespace FVTest.Backend.FnVerdict

/-- The validator branch of `Backend.lowerCheckFor`. -/
inductive Scope where
  | integer | typedT | typedTC | typedTCF
  deriving DecidableEq, Repr

/-- Whether the Stock routes were enabled for the function's file. -/
inductive Path where
  | stock | legacy
  deriving DecidableEq, Repr

/-- What `lean-backend` decided about one compiled function inside the theorems' scope
(`unverifiedReason?` none, within the validation budget). -/
structure Facts where
  scope : Scope
  path : Path
  /-- dead cleanup (`--dead-cleanup`, the default) -/
  cleanup : Bool := true
  /-- `--opt` (the Lean mid-end ran) -/
  opt : Bool := false
  /-- with the proven rule sets (`--opt-proven-only`) -/
  optProven : Bool := true
  /-- `i128`-legalised (`Opt.Legal.checkW` accepted) -/
  legal : Bool := false
  /-- constant-phi removal changed it (`Opt.ConstPhi.keeps`) -/
  cp : Bool := false
  /-- the source function before constant-phi removal is in the scope too (`unverifiedReason?`) -/
  cpSrc : Bool := true
  /-- the source function before constant-phi removal (after the `i128` legalisation) is
  `Backend.verifiable`: the Stock compositions' `InSubset` of it (`InSubset.of_verifiable`) -/
  cpSrcE : Bool := true
  /-- the pass constant-phi removal composes with (`Opt.ConstPhi.run`; with `--opt`
  `Opt.ConstPhi.runOpt cfg`) -/
  cpT : String := "Opt.ConstPhi.run"
  /-- `Stock.D0.eligible` of the compiled function -/
  d0 : Bool := false
  /-- an allocation record (`lowerRFunc`'s allocation) exists -/
  record : Bool := true
  /-- `checkAlloc` accepts the allocation lowered (regalloc2's, or the spill fallback re-checked) -/
  alloc : Bool := true
  /-- `formsCoveredB ⟨fa.k, af.slotBase⟩ vcp` -/
  covered : Bool := true
  /-- typed scope: `lowerFunction`'s output re-validated and reproducing the emitted code (`none`:
  it does; `some why`: it does not) -/
  typed : Option String := none
  deriving Repr

/-- The verdict: the theorem (fully qualified) and what it is about, or the failing premise. -/
structure Verdict where
  thm : Option String
  /-- `the source function`, or the compiled function when a transformation is not composed -/
  about : String := ""
  /-- the decided checks, in order -/
  checks : List String := []
  fail : Option String := none
  deriving Repr, DecidableEq

/-- The Stock path's theorem: every route's validator implies `SemanticABI.checkCalls`. -/
def stockThm : String := "E2E.backend_correct_world_niX_semantic_return_pins"

/-- The theorem that gives the Stock path's `SemanticABI.checkCalls` premise from the driver's
run (#1101). -/
def stockCallsThm : String := "Backend.compileFileReturnPinWhen_checkCalls"

/-- The transformations that ran compose with the legacy theorem: constant-phi removal only when
the source function before it is in the scope, the mid-end only with the proven rule sets. -/
def composable (x : Facts) : Bool := !(x.cp && !x.cpSrc) && !(x.opt && !x.optProven)

/-- The legacy integer theorem for the facts (with dead cleanup the `_cleanup` names), composed
with the transformations that ran (constant-phi removal at `T := x.cpT`); when they do not compose
(`composable`), the plain theorem about the compiled function. -/
def legacyThm (x : Facts) : String :=
  let c := if x.cleanup then "_cleanup" else ""
  if !composable x then s!"E2E.backend_correct_final{c}"
  else if x.cp then
    if x.legal then s!"E2E.backend_correct_legal_pass_wide{c} (T := {x.cpT})"
    else s!"E2E.backend_correct_pass{c} (T := {x.cpT})"
  else if x.opt then
    if x.legal then s!"E2E.backend_correct_legal_opt_wide{c}" else s!"E2E.backend_correct_opt_exe{c}"
  else if x.legal then s!"E2E.backend_correct_legal_wide{c}"
  else s!"E2E.backend_correct_final{c}"

/-- The typed scope's theorem (`typedTCF`: the float operations, float calls, the literal pool,
and since #35 `fcopysign` and `fma`). -/
def typedThm (x : Facts) : String :=
  match x.scope, x.cleanup with
  | .typedT, true => "E2E.backend_correct_final_cleanupT"
  | .typedT, false => "E2E.backend_correct_finalT"
  | .typedTC, true => "E2E.backend_correct_world_cleanupTC"
  | .typedTC, false => "E2E.backend_correct_finalTC"
  | _, true => "E2E.backend_correct_world_cleanupTCF"
  | _, false => "E2E.backend_correct_finalTCF"

/-- The typed theorem composed with the transformations that changed the function (#1112,
`FV/E2E/PassTypedCleanup.lean`): the `i128` legalisation, constant-phi removal at `T := x.cpT`, or
both, for the typed scope's theorem with dead cleanup; without dead cleanup constant-phi removal
alone in the scope `typedTCF` (`backend_correct_pass_finalTCF`, `FV/E2E/PassX.lean`). Their subset
and artifact premises are the typed theorem's, of the compiled function. `none` (the typed theorem
about the compiled function): the mid-end ran, or no composed theorem exists for the scope and
pipeline. -/
def typedComposedThm (x : Facts) : Option String :=
  if x.opt || !(x.legal || x.cp) then none
  else if !x.cleanup then
    if x.scope == .typedTCF && x.cp && !x.legal then
      some s!"E2E.backend_correct_pass_finalTCF (T := {x.cpT})"
    else none
  else
    let t := match x.scope with
      | .typedT => "final_cleanupT"
      | .typedTC => "world_cleanupTC"
      | _ => "world_cleanupTCF"
    if x.cp then
      if x.legal then some s!"E2E.backend_correct_legal_pass_wide_{t} (T := {x.cpT})"
      else some s!"E2E.backend_correct_pass_{t} (T := {x.cpT})"
    else some s!"E2E.backend_correct_legal_wide_{t}"

/-- The checks the typed composition adds (`typedComposedThm`). -/
def typedComposedChecks (x : Facts) : List String :=
  (if x.legal then ["Opt.Legal.checkW"] else []) ++ (if x.cp then ["Opt.ConstPhi.keeps"] else [])

/-- What the theorem is about when it is not composed with the transformations that ran. -/
def compiledAbout (x : Facts) : String :=
  let ts := (if x.legal then ["the i128 legalisation"] else []) ++
    (if x.cp then ["constant-phi removal"] else []) ++ (if x.opt then ["the mid-end"] else [])
  if ts.isEmpty then "the source function"
  else s!"the compiled function, after {" and ".intercalate ts} (not composed on this path)"

/-- The Stock path's theorem composed with the transformations that changed the function (#1100,
`FV/E2E/SemanticReturnPinsPass.lean`): the `i128` legalisation, constant-phi removal at
`T := x.cpT`, or both. `none` (the Stock theorem about the compiled function): the mid-end ran, or
constant-phi removal changed a function whose source before it is not `Backend.verifiable`. -/
def stockComposedThm (x : Facts) : Option String :=
  if x.opt || !(x.legal || x.cp) || (x.cp && !x.cpSrcE) then none
  else if x.cp then
    if x.legal then some s!"E2E.backend_correct_legal_pass_wide_semantic_return_pins (T := {x.cpT})"
    else some s!"E2E.backend_correct_pass_semantic_return_pins (T := {x.cpT})"
  else some "E2E.backend_correct_legal_wide_semantic_return_pins"

/-- The checks the composition adds (`stockComposedThm`). -/
def stockComposedChecks (x : Facts) : List String :=
  (if x.legal then ["Opt.Legal.checkW"] else []) ++
  (if x.cp then ["Opt.ConstPhi.keeps", "Backend.verifiable of the source function"] else [])

/-- The Stock theorem's verdict with the decided checks `base`: composed when it can be. -/
def stockVerdict (x : Facts) (base : List String) : Verdict :=
  match stockComposedThm x with
  | some t => { thm := some t, about := "the source function", checks := base ++ stockComposedChecks x }
  | none => { thm := some stockThm, about := compiledAbout x, checks := base }

/-- **The verdict.** -/
def verdict (x : Facts) : Verdict :=
  let common := ["formsCoveredB", "checkAlloc"]
  let fail? : Option String :=
    if !x.record then some "no allocation record (an allocator without lowerRFunc's allocation): no theorem names its code"
    else if !x.alloc then some "checkAlloc rejects the allocation lowered (the spill fallback)"
    else if !x.covered then some "formsCoveredB fails on the prepared code"
    else if x.scope != .integer then x.typed.map (s!"typed: {·}")
    else none
  match fail? with
  | some f => { thm := none, fail := some f }
  | none =>
    match x.scope, x.path with
    | .integer, .legacy =>
      if x.d0 then
        stockVerdict x (["unverifiedReason? (InSubset)", "lowerCheck (Stock.D0)", "prepCheck"] ++ common)
      else
        { thm := some (legacyThm x),
          about := if composable x then "the source function" else compiledAbout x,
          checks := ["unverifiedReason? (InSubset)", "lowerFunction", "lowerCheck", "prepCheck"] ++ common ++
            (if !composable x then [] else
              (if x.legal then ["Opt.Legal.checkW"] else []) ++
              (if x.cp then ["Opt.ConstPhi.keeps", "unverifiedReason? of the source function"] else []) ++
              (if x.opt then ["Opt.optimizeExe with the proven rule sets"] else [])) }
    | .integer, .stock =>
      stockVerdict x (["unverifiedReason? (InSubset)",
        s!"SemanticABI.checkCalls (the route's validator: {stockCallsThm})", "prepCheck"] ++ common)
    | _, _ =>
      let base := ["unverifiedReason? (the typed scope)", "lowerFunction", "lowerCheckFor (re-run)",
        "prepCheck", "the emitted code reproduced"] ++ common
      match typedComposedThm x with
      | some t => { thm := some t, about := "the source function", checks := base ++ typedComposedChecks x }
      | none => { thm := some (typedThm x), about := compiledAbout x, checks := base }

/-- The line `lean-backend` prints (after `%name: `). `normal`: a function with a `try_call` whose
unwinding is not covered; `unw`: the unwinding theorem, or why none applies. -/
def line (v : Verdict) (tryCall : Bool := false) (unw : Except String String := .error "") : String :=
  match v.thm with
  | none => s!"compiled, unverified (outside backend_correct): {v.fail.getD "?"}"
  | some t =>
    let body := s!"{t} (about {v.about}; decided: {", ".intercalate v.checks})"
    if !tryCall then s!"compiled, verified by {body}"
    else match unw with
      | .ok u => s!"compiled, verified by {body}; unwinding by {u} (the unwinder/personality model and the decoding of the emitted tables trusted)"
      | .error why => s!"compiled, verified for normal returns by {body}; try_call: unwinding, landing pads and the LSDA trusted ({why})"

/-- The unwinding theorem of a `try_call` function on the legacy path (`lean-backend` names it when
its checks pass, `unwindCheckFailure?` and the transformations' checks): composed with the
transformations as the normal-return theorem. -/
def unwindThm (cleanup opt legal cp : Bool) (cpT : String) : String :=
  let c := if cleanup then "_cleanup" else ""
  if cp then
    (if legal then "E2E.backend_correct_legal_pass_unwind_any"
      else s!"E2E.backend_correct_pass{c}_unwind_any") ++ s!" (T := {cpT})"
  else if legal && opt then "E2E.backend_correct_legal_opt_unwind_any"
  else if legal then "E2E.backend_correct_legal_unwind_any"
  else if opt then s!"E2E.backend_correct_opt_exe{c}_unwind_any"
  else s!"E2E.backend_correct_final{c}_unwind_any"

/-! ## Through the mid-end validator (#1119, `lean-backend --midval-opt`)

`lean-backend <f.unopt.clif> --midval-opt <g.opt.clif>` decides `Opt.MidVal.checkCertC
(Opt.ConstPhi.run f) g cert hints` (the certificate and branch-condition hints from
`Opt.MidVal.emitC`) and, when it holds, compiles
Cranelift's optimised function `g` in place of cg_clif's source function `f`. The facts below are
then those of the compiled `g`; the theorem named is the one of `FV/E2E/MidValPass.lean` /
`MidValPassLegacy.lean` composed with what ran on `g`, about the source function `f`. When `g`'s
verdict names no theorem, or no theorem through the validator composes what ran (`--opt`, no dead
cleanup, the typed scope after the `i128` legalisation or constant-phi removal, constant-phi
removal whose source is outside the scope), `midvalVerdict` says why and `lean-backend` compiles `f`
exactly as without the option. -/

/-- What a theorem through the mid-end validator is about. -/
def midAbout : String :=
  "the source function (.unopt.clif), compiled from cg_clif's optimised dump validated by Opt.MidVal"

/-- The premise `lean-backend --midval-opt` decides for every theorem through the validator. -/
def midCheck : String :=
  "Opt.MidVal.checkCertC (Opt.ConstPhi.run f) g cert hints (cert, hints: Opt.MidVal.emitC)"

/-- The Stock path's theorem through the validator for the facts of the compiled `g`. -/
def stockMidThm (x : Facts) : Except String String :=
  if x.cp && !x.cpSrcE then
    .error "constant-phi removal changed g and g is not Backend.verifiable: no Stock theorem composes the pass"
  else if x.cp then
    if x.legal then .ok s!"E2E.backend_correct_midval_legal_pass_wide_semantic_return_pins (T := {x.cpT})"
    else .ok s!"E2E.backend_correct_midval_pass_semantic_return_pins (T := {x.cpT})"
  else if x.legal then .ok "E2E.backend_correct_midval_legal_wide_semantic_return_pins"
  else .ok "E2E.backend_correct_midval_semantic_return_pins"

/-- The theorem through the validator for the facts of the compiled `g`, or why none composes. -/
def midvalThm (x : Facts) : Except String String :=
  if x.opt then .error "--opt: no theorem composes the Lean mid-end with the validator"
  else if !x.cleanup then
    .error "no dead cleanup: the theorems through the validator are about the dead-cleanup pipeline"
  else match x.scope, x.path with
    | .integer, .stock => stockMidThm x
    | .integer, .legacy =>
      if x.d0 then stockMidThm x
      else if x.cp && !x.cpSrc then
        .error "constant-phi removal changed g and g is outside the scope: no theorem composes the pass"
      else if x.cp then
        if x.legal then .ok s!"E2E.backend_correct_midval_legal_pass_wide_cleanup (T := {x.cpT})"
        else .ok s!"E2E.backend_correct_midval_pass_cleanup (T := {x.cpT})"
      else if x.legal then .ok "E2E.backend_correct_midval_legal_wide_cleanup"
      else .ok "E2E.backend_correct_midval_final_cleanup"
    | scope, _ =>
      if x.legal || x.cp then
        .error "typed scope after the i128 legalisation or constant-phi removal of g: no typed theorem composes them"
      else match scope with
        | .typedT => .ok "E2E.backend_correct_midval_final_cleanupT"
        | .typedTC => .ok "E2E.backend_correct_midval_world_cleanupTC"
        | _ => .ok "E2E.backend_correct_midval_world_cleanupTCF"

/-- **The verdict of a function compiled from the validated `g`** (module section above): the
theorem through the validator with today's decided checks of `g` and `midCheck`, about the source
function; `.error why` when `g`'s verdict names no theorem or none composes. -/
def midvalVerdict (x : Facts) : Except String Verdict :=
  let v := verdict x
  match v.thm with
  | none => .error s!"the compiled g is unverified ({v.fail.getD "?"})"
  | some _ => (midvalThm x).map fun t => { thm := some t, about := midAbout, checks := v.checks ++ [midCheck] }

/-- The unwinding theorem through the validator of a `try_call` function compiled from `g` (dead
cleanup, no `--opt`), composed as `unwindThm`. -/
def unwindMidThm (legal cp : Bool) (cpT : String) : String :=
  if cp then
    (if legal then "E2E.backend_correct_midval_legal_pass_unwind_any"
      else "E2E.backend_correct_midval_pass_cleanup_unwind_any") ++ s!" (T := {cpT})"
  else if legal then "E2E.backend_correct_midval_legal_unwind_any"
  else "E2E.backend_correct_midval_final_cleanup_unwind_any"

/-! ## Through the mid-end validator's hoisting mode (#1119, `symbol_value` hoisting)

When `checkCertC` rejects the pair but the hoisting mode accepts it (`Link.hoistCopy f g`, the
pair link-check and lean-link re-decide; Cranelift hoisted a `symbol_value` out of a loop),
`lean-backend` compiles `g` too. The simulation then holds only at a symbol table where the
compared copy's global values resolve, which `lean-backend` does not know: the theorem it names is
`g`'s own (about the optimised function, `midSymsAbout`), with `Link.hoistCopy` among the decided
checks; `link-check` (`…_midS`) and `lean-link` (`…MidS`) carry it to the source function at the
executable's symbol table, per function `E2E.midval_entrySyms`. -/

/-- What the theorem of a function validated by the hoisting mode is about. -/
def midSymsAbout : String :=
  "Cranelift's optimised function (.opt.clif); about the source function (.unopt.clif) only at link level, where link-check (…_midS) and lean-link (…MidS) decide the hoisting mode's premise at the executable's symbol table (E2E.midval_entrySyms)"

/-- The check `lean-backend --midval-opt` decides for the hoisting mode. -/
def midSymsCheck : String :=
  "Link.hoistCopy f g (Opt.MidVal.symsCopy on Opt.MidVal.emitC (hoist := true); the premise globalsResolve at the executable's symbol table is decided at link level)"

/-- **The verdict of a function compiled from a `g` the hoisting mode accepts**: `g`'s own
theorem, about the optimised function (`midSymsAbout`), with `midSymsCheck`; `.error why` when
`g`'s verdict names no theorem. -/
def midvalSymsVerdict (x : Facts) : Except String Verdict :=
  let v := verdict x
  match v.thm with
  | none => .error s!"the compiled g is unverified ({v.fail.getD "?"})"
  | some _ => .ok { v with about := midSymsAbout, checks := v.checks ++ [midSymsCheck] }

end FVTest.Backend.FnVerdict

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
  `backend_correct_world_cleanupTCF`; without dead cleanup `finalT`/`finalTC`/`finalTCF`), about
  the compiled function.

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

/-- The typed scope's theorem. -/
def typedThm (x : Facts) : String :=
  match x.scope, x.cleanup with
  | .typedT, true => "E2E.backend_correct_final_cleanupT"
  | .typedT, false => "E2E.backend_correct_finalT"
  | .typedTC, true => "E2E.backend_correct_world_cleanupTC"
  | .typedTC, false => "E2E.backend_correct_finalTC"
  | _, true => "E2E.backend_correct_world_cleanupTCF"
  | _, false => "E2E.backend_correct_finalTCF"

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
      { thm := some (typedThm x), about := compiledAbout x,
        checks := ["unverifiedReason? (the typed scope)", "lowerFunction", "lowerCheckFor (re-run)",
          "prepCheck", "the emitted code reproduced"] ++ common }

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

end FVTest.Backend.FnVerdict

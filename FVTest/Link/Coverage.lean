/-! # The theorems `lean-link` names (#1104, part 2(c) of the coverage audit #1096)

The one place where `lean-link` (`FVTest/Link/LeanLinkMain.lean`) gets a theorem name, as
`FVTest/E2E/BinVerdict.lean` is for `link-check` (#1095) and `FVTest/Backend/FnVerdict.lean` for
`lean-backend` (#1098). A printed claim is a `Claim`: the theorems, in the order printed, and the
premises the tool decided for them on this run, each with its evaluated value; its names are
printed only when every premise holds (`Claim.text`, `Claim.pick`). The route table below is the
only source of theorem-name literals in `lean-link` (`scripts/check-coverage-literals.py` rejects
any other); `FVTest/Link/CoverageTest.lean` checks that every name it can produce is a theorem and
that a false premise names none.

What a route's `coverage:` line claims holds by construction where `lean-link` runs exactly the
compiler the theorem is about; the equalities that tie the run to the theorem's object are
theorems, cited where the claims are printed: `TypedStockShared.attemptTFrom_eq` and
`TypedStockShared.stockSteps_placed` (the typed Stock route), `SemanticCompilerWith.compileWithRoutes_spec`
(the Stock routes), `withSizes_opt` (the `--opt` layout), `Front.placedFrom_cp_funcs` (the typed
compiler's source theorems through the frontend).
-/

namespace FVTest.Link.Coverage

/-- One printed claim: the theorems, fully qualified and in the order printed, and each premise
the tool decided for them on this run, with its evaluated value. -/
structure Claim where
  thms : List String
  premises : List (String × Bool) := []
  deriving Repr, DecidableEq

/-- Every premise holds. -/
def Claim.holds (c : Claim) : Bool := c.premises.all (·.2)

/-- The theorem names as printed (`, `-separated). -/
def Claim.names (c : Claim) : String := ", ".intercalate c.thms

/-- The names when every premise holds, else no name and the first failing premise. -/
def Claim.text (c : Claim) : String :=
  match c.premises.find? (!·.2) with
  | none => c.names
  | some (p, _) => s!"no theorem is named ({p} fails)"

/-- The printed fragment of `c`: its names in the frame `form` when every premise holds, else
`otherwise` (the route's text for that case, naming none of `c`'s theorems). -/
def Claim.pick (c : Claim) (form : String → String) (otherwise : String := "") : String :=
  if c.holds then form c.names else otherwise

/-- A claim with its premises. -/
def Claim.given (c : Claim) (ps : List (String × Bool)) : Claim := { c with premises := c.premises ++ ps }

/-! ## The route table -/

/-- The executable compilers of the plain path: `compileExe`, under `--opt` `compileExeOpt`,
with self tail calls `compileExeTail`. -/
inductive ExeKind where
  | plain | opt | tail
  deriving DecidableEq, Repr

/-- The compiler's name in `Link` (`Link.DeadCleanup` with the dead cleanup). -/
def ExeKind.name : ExeKind → String
  | .plain => "compileExe"
  | .opt => "compileExeOpt"
  | .tail => "compileExeTail"

/-- The routes that write an executable. -/
inductive Route where
  /-- `Link.ReturnPinCompilerWith.attempt` -/
  | returnPin
  /-- `Link.SemanticCompilerWith.compileWithRoutes` (the Stock routes' `attempt`) -/
  | stock
  /-- `Link.SemanticCompilerWith.attemptT` (the typed Stock route, typed `--verified`) -/
  | stockT
  /-- `Link.TypedCompilerWith.attempt` (the typed fallback on a Stock route) -/
  | typed
  /-- `Link.DeadCleanup.compileExeT` under typed `--verified` (`InScopeInT`) -/
  | exeTV
  /-- `Link.DeadCleanup.compileExeT` outside the input conditions (`InScopePT`) -/
  | exeT
  /-- `Link.DeadCleanup.compileExeT3` (`InScopeInT3`) -/
  | exeT3
  /-- the plain compiler (`cleanup`: `Link.DeadCleanup`'s) -/
  | exe (cleanup : Bool) (kind : ExeKind)
  deriving DecidableEq, Repr

/-- The namespace of the plain compilers. -/
def exeNs (cleanup : Bool) : String := if cleanup then "Link.DeadCleanup." else "Link."

/-- **The route's theorems** (the `coverage:` line's head). -/
def Route.claim : Route → Claim
  | .returnPin => ⟨["Link.ReturnPinCompilerWith.attempt_correct",
      "Link.ReturnPinCompilerWith.attempt_correct_depth"], []⟩
  | .stock => ⟨["Link.SemanticCompilerWith.attempt_correct",
      "Link.SemanticCompilerWith.attempt_correct_depth",
      "Link.SemanticCompilerWith.attempt_correct_peak"], []⟩
  | .stockT => ⟨["Link.SemanticCompilerWith.attemptT_correct",
      "Link.SemanticCompilerWith.attemptT_correct_depth",
      "Link.SemanticCompilerWith.attemptT_correct_peak"], []⟩
  | .typed => ⟨["Link.TypedCompilerWith.attempt_correct",
      "Link.TypedCompilerWith.attempt_correct_depth",
      "Link.TypedCompilerWith.attempt_correct_peak"], []⟩
  | .exeTV => ⟨["Link.DeadCleanup.compileExeT_correct", "Link.DeadCleanup.compileExeT_correct_peak"], []⟩
  | .exeT => ⟨["Link.DeadCleanup.compileExeT_correct"], []⟩
  | .exeT3 => ⟨["Link.DeadCleanup.compileExeT3_correct"], []⟩
  | .exe c k => ⟨[s!"{exeNs c}{k.name}_correct", s!"{exeNs c}{k.name}_correct_peak"], []⟩

/-- The theorems the `written by` line names next to the compiler. -/
def Route.writtenClaim : Route → Claim
  | .returnPin => ⟨["Link.ReturnPinCompilerWith.attempt_correct",
      "Link.ReturnPinCompilerWith.attempt_correct_depth"], []⟩
  | .stock => ⟨["Link.SemanticCompilerWith.compileWithRoutes_spec",
      "Link.SemanticCompilerWith.attempt_correct"], []⟩
  | .stockT => ⟨["Link.SemanticCompilerWith.attemptT_correct"], []⟩
  | .typed => ⟨["Link.TypedCompilerWith.attempt_correct"], []⟩
  | .exeTV | .exeT => ⟨["Link.DeadCleanup.compileExeT_correct"], []⟩
  | .exeT3 => ⟨["Link.DeadCleanup.compileExeT3_correct"], []⟩
  | .exe c k => ⟨[s!"{exeNs c}{k.name}_correct"], []⟩

/-- **The route's source theorems** about the bundle's program, through the `i128` legalisation
and constant-phi removal (`…_sourceCp`, #1052/#1100); their premise is `SrcScopeB` of the
bundle's program (`hsrc`; `hcp` by construction). None for `compileExeTail` (its inputs fail
`linkFreeB`, so `SrcScopeB`) and the typed fallbacks outside the input conditions. -/
def Route.sourceThms : Route → List String
  | .returnPin => ["Link.ReturnPinCompilerWith.attempt_correct_sourceCp",
      "Link.ReturnPinCompilerWith.attempt_correct_source_peakCp"]
  | .stock => ["Link.SemanticCompilerWith.attempt_correct_sourceCp",
      "Link.SemanticCompilerWith.attempt_correct_source_peakCp"]
  | .stockT => ["Link.SemanticCompilerWith.attemptT_correct_sourceCp",
      "Link.SemanticCompilerWith.attemptT_correct_source_peakCp"]
  | .typed => ["Link.TypedCompilerWith.attempt_correct_sourceCp",
      "Link.TypedCompilerWith.attempt_correct_source_peakCp"]
  | .exeTV => ["Link.DeadCleanup.compileExeT_correct_sourceCp",
      "Link.DeadCleanup.compileExeT_correct_source_peakCp"]
  | .exeT | .exeT3 | .exe _ .tail => []
  | .exe c k => [s!"{exeNs c}{k.name}_correct_sourceCp", s!"{exeNs c}{k.name}_correct_source_peakCp"]

/-- The source claim with its decided premise `SrcScopeB` of the bundle's program; a route
without source theorems names none (`no source theorem for this route` fails). -/
def Route.source (r : Route) (srcOk : Bool) : Claim :=
  ⟨r.sourceThms, [("SrcScopeB of the bundle's program", srcOk),
    ("a source theorem for this route", !r.sourceThms.isEmpty)]⟩

/-- Through the mid-end validator (#1119, `FV/Link/MidSourceRoutes.lean`): the `…Mid`
composition of a `…Cp` source theorem, about the unoptimised dumps. -/
def midName (n : String) : String :=
  (n.replace "_sourceCp" "_sourceMid").replace "_source_peakCp" "_source_peakMid"

/-- The typed compiler's theorems through the frontend, about cg_clif's program (#1088). -/
def frontClaim : Claim := ⟨["Front.bundle_correct_rawTCp", "Front.bundle_correct_raw_peakTCp"], []⟩

/-- The totality theorem `compileExeT` would need (`InScopeIn`): named as not covering. -/
def exeTTotal : String := "Link.DeadCleanup.compileExeT_total_reach_input"

/-- The plain compilers' totality on `InScopeIn` (the layout, reach and `file0` premises). -/
def Route.totalClaim (cleanup : Bool) (k : ExeKind) : Claim :=
  ⟨[if cleanup || k == .opt then s!"{exeNs cleanup}{k.name}_total_reach_input"
    else "Link.compileExe_total_reach"], []⟩

/-- The source fragment of a `coverage:` line: the route's source theorems when `SrcScopeB` of the
bundle's program holds, else what the route's theorems are about. -/
def srcText (r : Route) (srcOk : Bool) : String :=
  (r.source srcOk).pick
    (fun n => s!"; the bundle's program (before the i128 legalisation and constant-phi removal), in SrcScopeB: {n}")
    (if srcOk then "; in SrcScopeB, but no source theorem is named for this compiler"
      else "; outside SrcScopeB: about the legalised program only")

/-- A theorem's name without its namespace. -/
def shortName (n : String) : String := (n.splitOn ".").getLastD n

/-- The plain compilers' totality without checks of the linker's output (`lean-ld`'s plan). -/
def totalLdClaim (cleanup : Bool) (k : ExeKind) (ldOk : Bool) : Claim :=
  ⟨[s!"{exeNs cleanup}{k.name}_total_ld"], [("Plan.specOkB of lean-ld's plan", ldOk)]⟩

/-- `file0OkB` from `lean-ld`'s plan. -/
def file0LdThm : String := "Link.Ld.file0OkB_ld"

/-- Totality decided on `lean-ld`'s inputs, without linking. -/
def totalLdInThm : String := "Link.DeadCleanup.compileExe_total_ldIn"

/-- The Stock routes' retained legacy acceptance. -/
def stockLegacyThm : String := "Link.SemanticCompilerWith.compileWithRoutes_accepts_legacy"

/-- The exceptional edges (S10f): `compileExeU` (`compileExeOptU` under `--opt`) succeeds. -/
def unwindClaim (opt : Bool) (unwOk : Bool) : Claim :=
  let k := if opt then "compileExeOpt" else "compileExe"
  ⟨[s!"Link.DeadCleanup.{k}_correct_unwind", s!"Link.DeadCleanup.{k}_correct_unwind_peak"],
    [("Link.DeadCleanup.unwOkB", unwOk)]⟩

/-- #1076: the legalisation refines a bundle's program in `SrcScopeTB`. -/
def legalTBThm : String := "E2E.LegalProgram.legalProg_refinesT"

/-- The typed Stock route's source theorems on a bundle only in `SrcScopeTB` (premise:
`SrcScopeTB` of the route's input); through the mid-end validator the `…TBMid` ones (premise:
`Link.midValidatedB`, decided on the route's input before writing). -/
def sourceTBClaim (scopeTB mid : Bool) : Claim :=
  if mid then ⟨["Link.SemanticCompilerWith.attemptT_correct_sourceTBMid",
      "Link.SemanticCompilerWith.attemptT_correct_source_peakTBMid"],
      [("SrcScopeTB of the route's input", scopeTB)]⟩
  else ⟨["Link.SemanticCompilerWith.attemptT_correct_sourceTB",
      "Link.SemanticCompilerWith.attemptT_correct_source_peakTB"],
      [("SrcScopeTB of the route's input", scopeTB)]⟩

/-- Every route. -/
def allRoutes : List Route :=
  [.returnPin, .stock, .stockT, .typed, .exeTV, .exeT, .exeT3] ++
    ([true, false].flatMap fun c => [ExeKind.plain, .opt, .tail].filterMap fun k =>
      -- self tail calls only with the dead cleanup (`tailOn`)
      if !c && k == .tail then none else some (Route.exe c k))

/-- **The route table**: every theorem name `lean-link` can print, by what it is printed for.
`FVTest.Link.CoverageTest` checks that each is a theorem. -/
def routeClaims : List (String × List String) :=
  allRoutes.flatMap (fun r =>
    [(s!"{repr r} coverage", r.claim.thms), (s!"{repr r} written", r.writtenClaim.thms),
      (s!"{repr r} source", r.sourceThms),
      -- through the mid-end validator (`midCov`)
      (s!"{repr r} source (mid-end validator)", r.sourceThms.map midName)]) ++
  ([true, false].flatMap fun c => [ExeKind.plain, .opt, .tail].filterMap fun k =>
    if !c && k == .tail then none else
      some (s!"{exeNs c}{k.name} totality", (Route.totalClaim c k).thms ++
        (totalLdClaim c k true).thms)) ++
  [("unwinding", (unwindClaim false true).thms), ("unwinding --opt", (unwindClaim true true).thms),
    ("frontend", frontClaim.thms), ("compileExeT totality (not covering)", [exeTTotal]),
    ("lean-ld", [file0LdThm, totalLdInThm]), ("Stock legacy acceptance", [stockLegacyThm]),
    ("SrcScopeTB", [legalTBThm] ++ (sourceTBClaim true false).thms ++ (sourceTBClaim true true).thms)]

end FVTest.Link.Coverage

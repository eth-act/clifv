module

public import FV.Backend
public import FV.E2E.DeadCleanupLinkCheck

@[expose] public section

namespace FVTest.StockD0Runtime
open Backend Backend.Stock.D0

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def input : String := String.intercalate "\n" (
  ([ ("i32", ""), ("i32", " system_v"), ("i32", " fast"),
     ("i64", ""), ("i64", " system_v"), ("i64", " fast") ].zipIdx.map fun ((ty, conv), i) =>
    "function %parsed_d0_" ++ toString i ++ "(" ++ ty ++ ") -> " ++ ty ++ conv ++ " {\n" ++
    "block0(v0: " ++ ty ++ "):\n    return v0\n}\n") ++
  ["function %legacy_constant(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 5\n    return v1\n}\n"])

/-- Exercise actual parsing, routing, malformed-oracle spill fallback and mixed
file metadata through production entry points; no source-name allowlist is used. -/
def check : IO Unit := do
  let file := Clif.parseFile input
  require (file.funcs.length == 7) "D0 regression: parser did not return seven functions"
  for (parsed, i) in file.funcs.zipIdx do
    let f ← match parsed.func with
      | .ok f => pure f
      | .error _ => throw (IO.userError s!"D0 regression: parse failure for {parsed.name}")
    let expected := if i < 6 then Origin.stockD0 else Origin.legacy
    match selectWith Stock.lower f with
    | .ok (origin, _) =>
      if origin ≠ expected then throw (IO.userError s!"D0 regression: wrong route for {f.name}")
    | .error e => throw (IO.userError s!"D0 regression: route rejected {f.name}: {e}")
    match selectWith (fun _ => .error "forced Stock failure") f with
    | .ok (.legacy, _) => pure ()
    | _ => throw (IO.userError "D0 regression: forced failure did not reach successful legacy")
    if i < 6 then
      let result ← match Stock.lower f with
        | .ok result => pure result
        | .error e => throw (IO.userError s!"D0 regression: actual Stock failure: {e}")
      match selectWith (fun _ => .ok {result with edgeArgs := #[#[#[.vreg 0 .int]]]}) f with
      | .ok (.legacy, _) => pure ()
      | _ => throw (IO.userError "D0 regression: nonempty edge payload was not rejected")
    for cleanup in [false, true] do
      let answer := if cleanup then E2E.LinkCheck.pipeCleanupT f i 4096 .null
        else E2E.LinkCheck.pipeT f i 4096 .null
      match answer with
      | .ok _ => pure ()
      | .error e => throw (IO.userError s!"D0 regression: malformed allocator answer did not fall back: {e}")
  for cleanup in [false, true] do
    let output := Backend.compileFile file cleanup
    require (output.funcs.length == 7 && output.unsupported.isEmpty &&
      output.unverified.isEmpty && output.unvalidated.isEmpty)
      "D0 regression: mixed file lost compilation or verified metadata"
  IO.println "D0 runtime: six Stock routes, one legacy route, forced fallbacks, both cleanup modes and mixed-file metadata passed"

end FVTest.StockD0Runtime

def main : IO Unit := FVTest.StockD0Runtime.check

import FVTest.Backend.Main

open Backend
namespace TwoLoadCurrentSourceCapture

def originalFunction : Clif.Function := {
  name := "two_deferred_acquires"
  sig := {
    params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]
    returns := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]
    callConv := some .systemV }
  blocks := [{id := 0,params := [(7,.i64),(31,.i64)],body := [
    ⟨[63],.atomicLoad .i8 {} 7⟩,
    ⟨[64],.atomicLoad .i8 {} 31⟩,
    ⟨[100],.extend .uextend .i64 63⟩,
    ⟨[101],.extend .uextend .i64 64⟩],term := .ret [100,101]}]}

def takeExcept {α : Type} (label : String) (value : Except String α) : IO α :=
  match value with
  | .ok out => pure out
  | .error message => throw (IO.userError (label++": "++message))

def requiredEnv (name : String) : IO String := do
  let some value ← IO.getEnv name | throw (IO.userError ("missing "++name))
  pure value

/-- Source-only draft. No command compiled or executed this adapter. -/
def capture : IO Unit := do
  if (← requiredEnv "FV_TWO_LOAD_SOURCE_APPROVED") != "1" then
    throw (IO.userError "current source capture lacks the reviewed release")
  let out := System.FilePath.mk (← requiredEnv "FV_TWO_LOAD_SOURCE_OUTPUT")
  if ← out.pathExists then throw (IO.userError "output directory already exists")
  let mode ← requiredEnv "FV_TWO_LOAD_SOURCE_MODE"
  let cleanup ← if mode == "raw" then pure false else if mode == "cleanup" then pure true
    else throw (IO.userError "mode must be raw or cleanup")
  let phase ← requiredEnv "FV_TWO_LOAD_SOURCE_PHASE"
  if phase != "export" && phase != "capture" then throw (IO.userError "phase must be export or capture")
  let some allocator ← Allocator.ofName? "regalloc2" | throw (IO.userError "default regalloc2 is unavailable")
  let .regalloc2 _ machineEnv := allocator | throw (IO.userError "allocator is not default regalloc2")
  let result ← takeExcept "Stock.lower" (Stock.lower originalFunction)
  let stage := Stock.Arithmetic.stage cleanup result.code
  let prepared ← takeExcept "prepareChecked" (prepareChecked stage)
  let shape := CraneliftInput.shape (some originalFunction) cleanup prepared
  let stockJson ← takeExcept "stock JSON" (vcodeJson result.code)
  let stageJson ← takeExcept "stage JSON" (vcodeJson stage)
  let preparedJson ← takeExcept "prepared JSON" (vcodeJson prepared)
  let shapeJson ← takeExcept "oracle input JSON" (match shape.edges with
    | some edges => vcodeJsonAt shape.code edges
    | none => vcodeJson shape.code)
  -- This is the exact payload expression in current runLeanRegallocVia, for one function.
  let payload := "{\"env\":"++envJson machineEnv++",\"functions\":["++shapeJson++"]}\n"
  if phase == "capture" then
    let expected ← IO.FS.readFile (System.FilePath.mk (← requiredEnv "FV_TWO_LOAD_EXPECTED_ORACLE_INPUT"))
    if expected != payload then throw (IO.userError "current prepared oracle input differs from reviewed export")
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "stock.vcode.json") stockJson
  IO.FS.writeFile (out / "stage.vcode.json") stageJson
  IO.FS.writeFile (out / "prepared.vcode.json") preparedJson
  IO.FS.writeFile (out / "oracle.input.json") payload
  IO.FS.writeFile (out / "shape-reason.txt") shape.why
  if phase == "export" then return
  -- Use the same recording callback and shape function as the real default CLI.
  let (physical,records) ← allocRecordingNamed "regalloc2" allocator #[stage]
    (fun vcp => CraneliftInput.shape (some originalFunction) cleanup vcp)
  let some record := records[0]?.join | throw (IO.userError "default callback returned no allocation record")
  let (actualPrepared,rf,af) := record
  let actualPreparedJson ← takeExcept "actual prepared JSON" (vcodeJson actualPrepared)
  if actualPreparedJson != preparedJson then throw (IO.userError "callback prepared code differs from reviewed input")
  let some result := physical[0]? | throw (IO.userError "default callback returned no physical result")
  let _ ← takeExcept "default callback physical code" result
  let _ ← takeExcept "actual allocation checker" (checkAlloc actualPrepared rf)
  let _ ← takeExcept "actual lowering" (lowerRFunc actualPrepared rf)
  IO.FS.writeFile (out / "callback.actual-answer.json") (raAnswerJson actualPrepared rf)
  let assembly ← takeExcept "emitFunc" (emitFunc 0 af)
  let binary ← takeExcept "layout" assembly.layout
  IO.FS.writeFile (out / "physical.repr") (reprStr af)
  IO.FS.writeFile (out / "assembly.repr") (reprStr assembly)
  IO.FS.writeFile (out / "binary.repr") (reprStr binary)

end TwoLoadCurrentSourceCapture


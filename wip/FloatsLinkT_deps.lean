import FV.E2E.ExecProven
import FV.E2E.DeadCleanupExecProven
import FV.Link.Exe
import FV.Link.DeadCleanupExe
open Lean Meta

def mods : List Name := [
  `FV.E2E.LinkArm, `FV.E2E.LinkGood, `FV.E2E.LinkCheck, `FV.E2E.PipelineCheck,
  `FV.E2E.DeadCleanupLinkCheck, `FV.E2E.StackBound, `FV.E2E.DeadCleanupStackBound,
  `FV.E2E.BinCheck, `FV.E2E.DeadCleanupBinCheck, `FV.E2E.Binary, `FV.E2E.DeadCleanupBinary,
  `FV.E2E.BinaryGood, `FV.E2E.DeadCleanupBinaryGood, `FV.E2E.ExecWords, `FV.E2E.ExecBytes,
  `FV.E2E.DeadCleanupExecBytes, `FV.E2E.CodeMap, `FV.E2E.ExecStatic, `FV.E2E.DeadCleanupExecStatic,
  `FV.E2E.ExecFrameSim, `FV.E2E.DeadCleanupExecFrameSim, `FV.E2E.ExecRunN,
  `FV.E2E.DeadCleanupExecRunN, `FV.E2E.ExecGoodRun, `FV.E2E.DeadCleanupExecGoodRun,
  `FV.E2E.ExecGoodReads, `FV.E2E.DeadCleanupExecGoodReads, `FV.E2E.ExecGot,
  `FV.E2E.DeadCleanupExecGot, `FV.E2E.ExecProven, `FV.E2E.DeadCleanupExecProven]

#eval show MetaM Unit from do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless mods.contains m do continue
    if n.isInternal then
      -- keep auxiliary (match_, proof_) under their parent
      pure ()
    let used := ci.getUsedConstantsAsSet
    let mut us : Array String := #[]
    for u in used.toList do
      if let some _ := env.getModuleIdxFor? u then
        us := us.push u.toString
    out := out.push (n.toString ++ "\t" ++ m.toString ++ "\t" ++ String.intercalate " " us.toList)
  IO.FS.writeFile "/tmp/FloatsLinkT_deps.tsv" (String.intercalate "\n" out.toList)

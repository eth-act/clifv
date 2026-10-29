import Lean
open Lean

/-! Index of the definitions of the given modules: `module<TAB>name<TAB>line<TAB>kind` for every
user-written definition (def/abbrev/instance/opaque bodies; no auxiliary or generated names).
usage: lean --run declidx.lean MODULE... (LEAN_PATH: a build of those modules) -/

def skip (n : Name) : Bool :=
  n.isInternal || n.isInternalDetail ||
  (match n with
   | .str _ s => s.startsWith "match_" || s.startsWith "proof_" || s == "_unsafe_rec" ||
       s.startsWith "eq_" || s == "eq_def" || s.startsWith "_" || s == "sizeOf_spec"
       || s == "noConfusion" || s == "noConfusionType" || s == "casesOn" || s == "recOn"
       || s == "brecOn" || s == "below" || s == "binductionOn" || s == "ibelow" || s == "ctorIdx"
       || s.endsWith "_def"
   | _ => false)

unsafe def main (args : List String) : IO Unit := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let mods := args.map String.toName
  let env ← importModules (mods.toArray.map ({module := ·})) {} (loadExts := true) (level := .server)
  let ctx : Core.Context := { fileName := "", fileMap := default }
  for m in mods do
    let some idx := env.getModuleIdx? m | continue
    for c in env.header.moduleData[idx.toNat]!.constNames do
      if skip c then continue
      let some ci := env.find? c | continue
      let .defnInfo _ := ci | continue
      if (env.find? (c.str "_cstage1")).isSome && false then continue
      let r ← (findDeclarationRanges? c : CoreM _).toIO' ctx { env }
      match r with
      | some rg =>
        let inst := (Meta.instanceExtension.getState env).instanceNames.contains c
        IO.println s!"{m}\t{c}\t{rg.range.pos.line}\t{if inst then "instance" else "def"}"
      | _ => pure ()

import FV.Backend
import FV.Backend.RegallocPerEdgePrepare
import FV.Backend.RegallocPerEdgePrepareCheck
import FV.Backend.RegallocPerEdge
import FV.Backend.RegallocPerEdgeSpill

/-! Actual allocator adapter for per-successor VCode. Every allocation selected
for lowering, including the spill fallback, passes the indexed checker. Existing
runtime/theorem variants remain unchanged. Production cutover still requires
preparation/source/completeness proofs and the original full-goal gates. -/
namespace Backend
open Lean

def vcodeJsonAt (vc : VCode) (edges : Array (Array (Array Reg))) : Except String String := do
  let (succs, preds) ← vc.cfg
  if edges.size != vc.blocks.size then throw "per-successor block count differs"
  for (row, bi) in edges.zipIdx do
    if row.size != succs[bi]!.size then throw s!"block {bi}: per-successor vector count differs"
  let classes := String.ofList (vc.classes.toList.map fun | .int => 'i' | .float => 'f')
  let mut start := 0
  let mut blocks : Array String := #[]
  let mut insts : Array String := #[]
  for (b, bi) in vc.blocks.zipIdx do
    let params ← b.params.toList.mapM vregNum
    blocks := blocks.push <| s!"\{\"insts\":[{start},{start + b.insts.size}]," ++
      s!"\"succs\":{jlist (succs[bi]!.toList.map toString)}," ++
      s!"\"preds\":{jlist (preds[bi]!.toList.map toString)}," ++
      s!"\"params\":{jlist (params.map toString)}}"
    start := start + b.insts.size
    for (i, k) in b.insts.zipIdx do
      let ops ← i.operands
      let last := k + 1 == b.insts.size
      -- a `tryCall` is a regalloc2 branch (`MachTerminator::Branch`) with operands
      let branch := i.isTerminator && !i.isRet
      let kind := if i.isRet then "ret" else if branch then "branch" else "other"
      if last != i.isTerminator then
        throw s!"block {b.label}: terminator not at the end of the block"
      let args ← if branch then do
          let xs ← edges[bi]!.mapM fun args => args.mapM vregNum
          let per := xs.toList.map fun args => jlist (args.toList.map toString)
          pure s!",\"args\":{jlist per}"
        else pure ""
      let clob := jlist (i.clobbers.map fun r => jstr r.pregName)
      insts := insts.push <| s!"\{\"ops\":{jlist (ops.toList.map Operand.json)}," ++
        s!"\"clobbers\":{clob},\"kind\":\"{kind}\"{args}}"
  pure <| s!"\{\"name\":{jstr vc.name},\"entry\":0,\"vregs\":\"{classes}\"," ++
    s!"\"blocks\":{jlist blocks.toList},\"insts\":{jlist insts.toList}}"

def runLeanRegallocAt (bin : String) (env : MachineEnv) (vcs : Array EdgeVCode) : IO (Except String (Array (Except String RAResult))) := do
  if vcs.isEmpty then return .ok #[]
  let mut funcs : Array String := #[]
  for vc in vcs do
    match vcodeJsonAt vc.code vc.edges with
    | .ok j => funcs := funcs.push j
    | .error e => return .error s!"%{vc.code.name}: {e}"
  let input := s!"\{\"env\":{envJson env},\"functions\":[" ++ ",".intercalate funcs.toList ++ "]}\n"
  let (h, path) ← IO.FS.createTempFile
  h.putStr input
  h.flush
  -- debugging aid: keep a copy of the allocator input
  if let some keep ← IO.getEnv "LEAN_REGALLOC_KEEP" then IO.FS.writeFile keep input
  let out ← IO.Process.output { cmd := bin, args := #[path.toString] }
  IO.FS.removeFile path
  if out.exitCode != 0 then
    return .error s!"lean-regalloc ({bin}) failed with status {out.exitCode}: {out.stderr}"
  match Json.parse out.stdout with
  | .error e => return .error s!"lean-regalloc output: {e}"
  | .ok j =>
    let arr := ((j.getObjVal? "functions").bind (·.getArr?)).toOption.getD #[]
    if arr.size != vcs.size then return .error "lean-regalloc: function count differs"
    return .ok <| (vcs.zip arr).map fun (vc, fj) => do
      let o ← parseRAOut fj
      let rf ← buildRFunc vc.code o
      pure { prepared := vc.code, rf, rustChecker := o.checker }


/-- The fallback is checked just like the external oracle. -/
def checkedSpillAt (vc : VCode) (edges : Array (Array (Array Reg))) : Except String RFunc := do
  let fallback := spillAllocAt vc edges
  checkAllocAt vc edges fallback
  pure fallback

/-- Choose a checked allocation. Oracle failure/rejection/unlowerability or
emission unreadiness uses the indexed spill fallback, which is checked too. -/
def allocResultAt (vc : VCode) (edges : Array (Array (Array Reg))) (ra : Except String RFunc) : Except String RFunc :=
  match ra with
  | .error _ => checkedSpillAt vc edges
  | .ok rf =>
    if (checkAllocAt vc edges rf).isOk then
      match lowerRFunc vc rf with
      | .ok af => if emitReady af then .ok rf else checkedSpillAt vc edges
      | .error _ => checkedSpillAt vc edges
    else checkedSpillAt vc edges

def lowerAllocAt (vc : VCode) (edges : Array (Array (Array Reg))) (ra : Except String RFunc) : Except String AFunc := do
  lowerRFunc vc (← allocResultAt vc edges ra)

def allocateSpillAt (vcs : Array EdgeVCode) : Array (Except String AFunc) :=
  vcs.map fun input => do
    let prepared ← prepareCheckedAt input.code input.edges
    lowerAllocAt prepared.code prepared.edges (.error "indexed spill allocation requested")

/-- Prepare code and vectors together, serialize actual vectors, parse the
untrusted oracle, then validate/select/lower through the indexed checker. -/
def allocateRegalloc2At (bin : String) (env : MachineEnv) (vcs : Array EdgeVCode) : IO (Array (Except String AFunc)) := do
  let prepared := vcs.map fun input => prepareCheckedAt input.code input.edges
  let ok := prepared.filterMap (·.toOption)
  let rs : Array (Except String RFunc) ← do
    try
      match ← runLeanRegallocAt bin env ok with
      | .error e => pure (ok.map fun _ => .error e)
      | .ok rs => pure (rs.map (·.bind RAResult.oracle))
    catch e => pure (ok.map fun _ => .error (toString e))
  let mut out : Array (Except String AFunc) := #[]
  let mut j := 0
  for p in prepared do
    match p with
    | .error e => out := out.push (.error e)
    | .ok prepared =>
      out := out.push (lowerAllocAt prepared.code prepared.edges (rs[j]?.getD (.error "lean-regalloc: missing result")))
      j := j + 1
  pure out

def Allocator.runAt : Allocator → Array EdgeVCode → IO (Array (Except String AFunc))
  | .regalloc2 bin env,vcs => allocateRegalloc2At bin env vcs
  | .stack,vcs | .spill,vcs => pure (allocateSpillAt vcs)

end Backend

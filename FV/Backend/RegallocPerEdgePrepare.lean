module

public import FV.Backend.RegallocOps

public section

/-! Preparation carries actual outgoing vectors with their blocks through
reachability, critical-edge splitting and reverse postorder. The legacy prepare
and VCode representation remain unchanged. -/
namespace Backend

structure EdgeVCode where
  code : VCode
  edges : Array (Array (Array Reg))
  deriving Inhabited

/-- Prepare per-successor VCode. A split edge copies no parameters into its new
empty block; the old outgoing vector moves to that block's single jump. -/
def prepareAt (vc : VCode) (outgoing : Array (Array (Array Reg))) : Except String EdgeVCode := do
  let (succs, _) ← vc.cfg
  if outgoing.size != vc.blocks.size then throw "per-successor block count differs"
  for (args, bi) in outgoing.zipIdx do
    if args.size != succs[bi]!.size then throw s!"block {bi}: per-successor vector count differs"
  let live := reachable succs
  let kept := ((vc.blocks.zip outgoing).zip live).filterMap fun ((b, args), l) =>
    if l then some (b, args) else none
  let vc := { vc with blocks := kept.map Prod.fst }
  let outgoing := kept.map Prod.snd
  let (succs, preds) ← vc.cfg
  if !(preds[0]?.getD #[]).isEmpty then throw "the entry block is a branch target"
  if !(vc.blocks[0]?.map (fun (b : VBlock) => b.params.isEmpty)).getD true then throw "entry block has parameters"
  let mut next := (vc.blocks.foldl (fun m (b : VBlock) => max m b.label) 0) + 1
  let mut blocks : Array VBlock := #[]
  let mut rows : Array (Array (Array Reg)) := #[]
  let mut edgeBlocks : Array VBlock := #[]
  let mut edgeRows : Array (Array (Array Reg)) := #[]
  for (b, bi) in vc.blocks.zipIdx do
    let ss := succs[bi]!
    let mut row := outgoing[bi]!
    if ss.size < 2 then
      blocks := blocks.push b
      rows := rows.push row
      continue
    let some t := b.insts.back? | throw "empty block"
    let mut labels : Array Label := #[]
    for ((s, label), j) in (ss.zip t.targets.toArray).zipIdx do
      if preds[s]!.size > 1 then
        let args := row[j]!
        edgeBlocks := edgeBlocks.push {label := next,insts := #[.jump label],branchArgs := args}
        edgeRows := edgeRows.push #[args]
        row := row.set! j #[]
        labels := labels.push next
        next := next + 1
      else labels := labels.push label
    let some t' := t.setTargets labels.toList | throw "setTargets"
    blocks := blocks.push {b with insts := b.insts.pop.push t'}
    rows := rows.push row
  let vc := {vc with blocks := blocks ++ edgeBlocks}
  let outgoing := rows ++ edgeRows
  let (succs, _) ← vc.cfg
  let order := rpo succs
  let ordered := {vc with blocks := order.map (fun i => vc.blocks[i]!)}
  pure ⟨ordered,order.map (fun i => outgoing[i]!)⟩

end Backend

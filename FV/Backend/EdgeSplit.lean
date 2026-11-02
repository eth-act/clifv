import FV.Backend.RegallocPerEdgePrepareCheck

/-! Edge splitting turns per-successor VCode into legacy single-vector VCode. Every edge of a
multi-successor block that carries arguments goes through a new edge block: one `jump` to the
old target, with the old vector as its `branchArgs`. The original blocks keep their positions;
the edge blocks follow them. The result is checked against the indexed preparation relation and
against legacy compatibility, so a successful split has the proved per-edge-to-legacy transport. -/
namespace Backend

/-- Split every multi-successor edge that carries arguments into an edge block. -/
def splitEdges (vc : VCode) (outgoing : Array (Array (Array Reg))) : Except String EdgeVCode := do
  let (succs, _) ← vc.cfg
  if outgoing.size != vc.blocks.size then throw "per-successor block count differs"
  let mut next := (vc.blocks.foldl (fun m (b : VBlock) => max m b.label) 0) + 1
  let mut blocks : Array VBlock := #[]
  let mut rows : Array (Array (Array Reg)) := #[]
  let mut edgeBlocks : Array VBlock := #[]
  let mut edgeRows : Array (Array (Array Reg)) := #[]
  for (b, bi) in vc.blocks.zipIdx do
    let mut row := outgoing[bi]!
    if succs[bi]!.size < 2 || row.all (·.isEmpty) then
      blocks := blocks.push b
      rows := rows.push row
      continue
    let some t := b.insts.back? | throw "empty block"
    let mut labels : Array Label := #[]
    for (label, j) in t.targets.toArray.zipIdx do
      let args := row[j]!
      if args.isEmpty then
        labels := labels.push label
      else
        edgeBlocks := edgeBlocks.push {label := next, insts := #[.jump label], branchArgs := args}
        edgeRows := edgeRows.push #[args]
        row := row.set! j #[]
        labels := labels.push next
        next := next + 1
    let some t' := t.setTargets labels.toList | throw "setTargets"
    blocks := blocks.push {b with insts := b.insts.pop.push t'}
    rows := rows.push row
  pure ⟨{vc with blocks := blocks ++ edgeBlocks}, rows ++ edgeRows⟩

/-- Every actual CFG edge selects the legacy `branchArgs` of its block. -/
def edgeLegacyCompatibleB (vc : VCode) (edges : Array (Array (Array Reg))) : Bool :=
  match vc.cfg with
  | .ok (ss, _) => (List.range ss.size).all fun b =>
    match ss[b]?, vc.blocks[b]? with
    | some sb, some vb => (List.range sb.size).all fun j =>
      decide (edges[b]?.bind (·[j]?) = some vb.branchArgs)
    | some _, none => false
    | none, _ => true
  | .error _ => false

/-- Edge splitting with its internal checks: the indexed preparation relation to the input,
and legacy compatibility of the output. -/
def splitEdgesChecked (vc : VCode) (edges : Array (Array (Array Reg))) : Except String EdgeVCode := do
  let split ← splitEdges vc edges
  if !(Proof.PerEdgePrep.prepCheckAt vc edges split && edgeLegacyCompatibleB split.code split.edges) then
    throw "edge splitting relation rejected"
  pure split

end Backend

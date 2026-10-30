import FV.Backend.RegallocPerEdgeSpill
import FV.Backend.Proof.SpillStep4Cfg

namespace Backend.Proof.PerEdgeSpill
open Backend Backend.Proof.Spill
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- The actual shared-target argument moves before a single-successor jump. -/
def jumpCopies (vc : VCode) (edges : Array (Array (Array Reg)))
    (succs preds : Array (Array Nat)) (b : Nat) : List RItem :=
  match succs[b]? with
  | some #[target] =>
    if (preds[target]?.getD #[]).size > 1 then
      match vc.blocks[target]? with
      | some tb => spillArgMovesAt (spillHomesAt vc edges) (edges[b]?.bind (·[0]?) |>.getD #[]) tb.params
      | none => []
    else []
  | _ => []

/-- The real per-instruction body emitted by the indexed spill allocator. -/
def bodyItem (vc : VCode) (edges : Array (Array (Array Reg)))
    (succs preds : Array (Array Nat)) (b : Nat) (vb : VBlock) (x : MInst × Nat) : List RItem :=
  (if x.2+1 == vb.insts.size then jumpCopies vc edges succs preds b else []) ++
    spillInstAt (spillHomesAt vc edges) x.2 x.1

/-- Exact decomposition of an actual indexed spill block: entry saves, live
terminator-result stores, unique-predecessor copies, then real body items. -/
theorem spillAllocAt_block {vc : VCode} {edges : Array (Array (Array Reg))}
    {succs preds : Array (Array Nat)} (cfg : vc.cfg = .ok (succs,preds))
    {b : Nat} {vb : VBlock} (block : vc.blocks[b]? = some vb) :
    (spillAllocAt vc edges).blocks[b]? = some (((if b == 0 then spillSaves else []) ++
      spillEntryStoresAt (spillHomesAt vc edges) vc succs preds b ++
      spillEntryCopiesAt (spillHomesAt vc edges) vc edges succs preds b ++
      vb.insts.toList.zipIdx.flatMap (bodyItem vc edges succs preds b vb)).toArray) := by
  unfold spillAllocAt
  rw [cfg]
  dsimp only
  rw [Array.getElem?_mapIdx,block]
  rfl

private theorem unique_index {vc : VCode} {succs preds : Array (Array Nat)}
    (cfg : vc.cfg = .ok (succs,preds)) {b s j : Nat} {ss : Array Nat}
    (row : succs[b]? = some ss) (edge : ss[j]? = some s) (pred : preds[s]? = some #[b]) :
    ss.toList.idxOf? s = some j := by
  have unique := (preds_single cfg row edge pred).2
  cases found : ss.toList.idxOf? s with
  | none => exact False.elim (List.idxOf?_eq_none_iff.mp found
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? edge)))
  | some index =>
    obtain ⟨bound,value,_⟩ := List.idxOf?_eq_some_iff.mp found
    have atIndex : ss[index]? = some s := by
      have atList : ss.toList[index]? = some s := by rw [List.getElem?_eq_getElem bound,value]
      simpa only [Array.getElem?_toList] using atList
    have same := unique index atIndex
    subst index
    rfl

/-- A real unique predecessor determines the same actual successor index for
both terminator-result stores and entry copies. Duplicate edges are accounted
for by VCode.cfg's per-edge predecessor counts; no first-index certificate. -/
theorem spill_entry_route {vc : VCode} {edges : Array (Array (Array Reg))}
    {succs preds : Array (Array Nat)} (cfg : vc.cfg = .ok (succs,preds))
    {b s j : Nat} {ss : Array Nat} {vb tb : VBlock} {row : Array (Array Reg)} {args : Array Reg}
    (source : vc.blocks[b]? = some vb) (target : vc.blocks[s]? = some tb)
    (successors : succs[b]? = some ss) (edge : ss[j]? = some s) (pred : preds[s]? = some #[b])
    (atRow : edges[b]? = some row) (atArgs : row[j]? = some args) :
    spillEntryStoresAt (spillHomesAt vc edges) vc succs preds s =
      (termEdgeDefs vb j).map (fun (x : Operand × Loc) => RItem.move x.2 (spillHomeAt (spillHomesAt vc edges) x.1.vreg x.1.cls)) ∧
    spillEntryCopiesAt (spillHomesAt vc edges) vc edges succs preds s =
      spillArgMovesAt (spillHomesAt vc edges) args tb.params := by
  have index := unique_index cfg successors edge pred
  constructor
  · unfold spillEntryStoresAt
    rw [pred]
    change (match vc.blocks[b]?,succs[b]? with
      | some v,some ss => match ss.toList.idxOf? s with
        | some i => (termEdgeDefs v i).map (fun (x : Operand × Loc) => RItem.move x.2 (spillHomeAt (spillHomesAt vc edges) x.1.vreg x.1.cls))
        | none => []
      | _,_ => []) = _
    rw [source,successors]
    dsimp only
    rw [index]
  · unfold spillEntryCopiesAt
    rw [pred]
    change (match vc.blocks[s]?,succs[b]? with
      | some v,some ss => match ss.toList.idxOf? s with
        | some i => spillArgMovesAt (spillHomesAt vc edges) (edges[b]?.bind (·[i]?) |>.getD #[]) v.params
        | none => []
      | _,_ => []) = _
    rw [target,successors]
    dsimp only
    rw [index,atRow]
    simp only [Option.bind_some,atArgs,Option.getD_some]

/-- Shared targets receive their selected vector before the actual jump.
This is the other real copy placement used by the indexed spill allocator. -/
theorem spill_jump_route {vc : VCode} {edges : Array (Array (Array Reg))}
    {succs preds : Array (Array Nat)} {b s : Nat} {tb : VBlock}
    {row : Array (Array Reg)} {args : Array Reg}
    (successors : succs[b]? = some #[s]) (shared : 1 < (preds[s]?.getD #[]).size)
    (target : vc.blocks[s]? = some tb) (atRow : edges[b]? = some row) (atArgs : row[0]? = some args) :
    jumpCopies vc edges succs preds b = spillArgMovesAt (spillHomesAt vc edges) args tb.params := by
  unfold jumpCopies
  rw [successors]
  change (if 1 < (preds[s]?.getD #[]).size then
    match vc.blocks[s]? with
    | some tb => spillArgMovesAt (spillHomesAt vc edges) (edges[b]?.bind (·[0]?) |>.getD #[]) tb.params
    | none => [] else []) = _
  rw [if_pos shared,target,atRow]
  simp only [Option.bind_some,atArgs,Option.getD_some]

end Backend.Proof.PerEdgeSpill

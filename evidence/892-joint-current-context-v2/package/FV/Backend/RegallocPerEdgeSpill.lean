import FV.Backend.SpillAlloc

/-! Per-successor spill fallback. Copies for a unique predecessor run on entry,
after terminator-result stores. Copies into shared targets run before a jump
from a single-successor source. Preparation splits all other edges. -/
namespace Backend

/-- Dense value/class keys avoid opaque hash operations, so complete actual
fallback executions can be reduced by Lean's kernel. Slot numbering still uses
first occurrence, independent of the dense key's position. -/
structure SpillHomesAt where
  slots : Array (Option Nat) := #[]
  size : Nat := 0
  deriving Inhabited

def spillHomeKeyAt (v : Nat) (c : RegClass) : Nat := 2*v + match c with | .int => 0 | .float => 1

def SpillHomesAt.insert (h : SpillHomesAt) (v : Nat) (c : RegClass) : SpillHomesAt :=
  let key := spillHomeKeyAt v c
  if (h.slots[key]?).join.isSome then h
  else
    let slots := h.slots ++ Array.replicate (key + 1 - h.slots.size) none
    ⟨slots.set! key (some h.size),h.size + 1⟩

def spillHomeAt (h : SpillHomesAt) (v : Nat) (c : RegClass) : Loc :=
  .stack ((h.slots[spillHomeKeyAt v c]?).join.getD 0) c

/-- Include outgoing-only registers when allocating spill homes. -/
def spillHomesAt (vc : VCode) (edges : Array (Array (Array Reg))) : SpillHomesAt :=
  let initial := vc.blocks.foldl (fun h b => (blockVregs b).foldl
    (fun h key => h.insert key.1 key.2) h) ({} : SpillHomesAt)
  edges.foldl (fun h row => row.foldl (fun h args => args.foldl
    (fun h r => h.insert r.homeNum r.homeCls) h) h) initial

def spillInstAt (h : SpillHomesAt) (k : Nat) (i : MInst) : List RItem :=
  match i.operands with
  | .error _ => [.op k #[]]
  | .ok ops =>
    let locs := spillLocs ops i.clobbers
    let pairs := (ops.zip locs).toList
    let loads := (pairs.filter (·.1.kind == .use)).map fun (o, l) => RItem.move (spillHomeAt h o.vreg o.cls) l
    let stores := if i.isTerminator then [] else
      (keptPairs i pairs).map fun (o, l) => RItem.move l (spillHomeAt h o.vreg o.cls)
    let restores := match i with
      | .rets _ => spillRestores
      | _ => []
    restores ++ loads ++ [.op k locs] ++ stores

def spillArgMovesAt (h : SpillHomesAt) (args params : Array Reg) : List RItem :=
  let tmp := h.size
  let ps := (args.toList.zip params.toList).zipIdx
  let phase1 := ps.flatMap fun ((a, _), i) =>
    let c := a.homeCls
    [RItem.move (spillHomeAt h a.homeNum c) (.reg (spillScratch c)),
     .move (.reg (spillScratch c)) (Loc.stack (tmp + i) c)]
  let phase2 := ps.flatMap fun ((_, p), i) =>
    let c := p.homeCls
    [RItem.move (Loc.stack (tmp + i) c) (.reg (spillScratch c)),
     .move (.reg (spillScratch c)) (spillHomeAt h p.homeNum c)]
  phase1 ++ phase2

def spillEntryStoresAt (h : SpillHomesAt) (vc : VCode) (succs preds : Array (Array Nat)) (s : Nat) : List RItem :=
  match preds[s]? with
  | some #[b] =>
    match vc.blocks[b]?, succs[b]? with
    | some vb, some ss =>
      match ss.toList.idxOf? s with
      | some j => (termEdgeDefs vb j).map fun (o, l) => RItem.move l (spillHomeAt h o.vreg o.cls)
      | none => []
    | _, _ => []
  | _ => []

/-- Copy on entry only when a unique actual predecessor/edge selects the row. -/
def spillEntryCopiesAt (h : SpillHomesAt) (vc : VCode) (edges : Array (Array (Array Reg)))
    (succs preds : Array (Array Nat)) (s : Nat) : List RItem :=
  match preds[s]? with
  | some #[b] =>
    match vc.blocks[s]?,succs[b]? with
    | some target,some ss =>
      match ss.toList.idxOf? s with
      | some j => spillArgMovesAt h (edges[b]?.bind (·[j]?) |>.getD #[]) target.params
      | none => []
    | _,_ => []
  | _ => []

/-- The indexed spill allocation. Its successful checker result is validated
before any runtime consumer may lower this fallback. -/
def spillAllocAt (vc : VCode) (edges : Array (Array (Array Reg))) : RFunc :=
  let (succs,preds) := match vc.cfg with | .ok sp => sp | .error _ => (#[],#[])
  let h := spillHomesAt vc edges
  let maxArgs := edges.foldl (fun n row => row.foldl (fun n args => max n args.size) n) 0
  let blocks := vc.blocks.mapIdx fun bi vb =>
    let n := vb.insts.size
    let body := (vb.insts.toList.zipIdx).flatMap fun (i,k) =>
      let moves := if k + 1 == n then
        match succs[bi]? with
        | some #[t] =>
          if (preds[t]?.getD #[]).size > 1 then
            match vc.blocks[t]? with
            | some target => spillArgMovesAt h (edges[bi]?.bind (·[0]?) |>.getD #[]) target.params
            | none => []
          else []
        | _ => []
      else []
      moves ++ spillInstAt h k i
    let pre := (if bi == 0 then spillSaves else []) ++ spillEntryStoresAt h vc succs preds bi ++
      spillEntryCopiesAt h vc edges succs preds bi
    (pre ++ body).toArray
  {blocks,spillSlots := h.size + maxArgs,saved := calleeSaved}

end Backend

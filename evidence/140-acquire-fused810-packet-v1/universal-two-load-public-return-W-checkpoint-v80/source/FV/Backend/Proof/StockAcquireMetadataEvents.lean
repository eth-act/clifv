import FV.Backend.Proof.StockAcquireMetadataOrder
import FV.Backend.Proof.StockPureDriverUnsunk
import FV.Backend.Proof.StockTraversalRecordOrigin

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- A boundary advances the counter. A source effect also records its slot. -/
def colorEventNext (state : FenceColors.Colors) (target : Option Nat) : FenceColors.Colors :=
  match target with
  | none => (state.1,state.2+1)
  | some slot => (state.1.set! slot state.2,state.2+1)

def bodyColorEvents (start : Nat) : List (Clif.Stmt × Nat) → List (Option Nat)
  | [] => []
  | x::xs => if Stock.colored x.1.inst then some (start+x.2)::bodyColorEvents start xs
      else bodyColorEvents start xs

def blockColorEvents (ranges : Array (Nat × Nat)) (x : Clif.Block × Nat) : List (Option Nat) :=
  none::(bodyColorEvents ranges[x.2]!.1 x.1.body.zipIdx ++ [some (ranges[x.2]!.2-1)])

def sourceColorEvents (ctx : Ctx) (ranges : Array (Nat × Nat)) : List (Option Nat) :=
  ctx.func.blocks.zipIdx.flatMap (blockColorEvents ranges)

/-- The event sequence is the actual body metadata computation. -/
theorem body_color_events_fold (start : Nat) (xs : List (Clif.Stmt × Nat)) (state : FenceColors.Colors) :
    (bodyColorEvents start xs).foldl colorEventNext state = xs.foldl (FenceColors.bodyNext start) state := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih =>
    cases effect : Stock.colored x.1.inst <;>
      simp [bodyColorEvents,effect,FenceColors.bodyNext,colorEventNext,ih]

/-- The event sequence retains both real block boundaries and every colored instruction. -/
theorem block_color_events_fold (ranges : Array (Nat × Nat)) (x : Clif.Block × Nat)
    (state : FenceColors.Colors) :
    (blockColorEvents ranges x).foldl colorEventNext state = FenceColors.blockNext ranges state x := by
  simp only [blockColorEvents,List.foldl_cons,List.foldl_append,List.foldl_nil,body_color_events_fold]
  rfl

/-- All blocks share the same actual metadata counter and source event order. -/
theorem source_color_events_fold (ranges : Array (Nat × Nat)) (xs : List (Clif.Block × Nat))
    (state : FenceColors.Colors) :
    (xs.flatMap (blockColorEvents ranges)).foldl colorEventNext state =
      xs.foldl (FenceColors.blockNext ranges) state := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons,List.foldl_append,block_color_events_fold,List.foldl_cons,ih]

/-- The actual sourceMetadata array is this complete source-ordered event fold. -/
theorem sourceMetadata_color_events (ctx : Ctx) (ranges : Array (Nat × Nat)) :
    (sourceMetadata ctx ranges).entryColor =
      ((sourceColorEvents ctx ranges).foldl colorEventNext (Array.replicate ctx.insts.size 0,0)).1 := by
  rw [FenceColors.sourceMetadata_projection]
  exact (congrArg Prod.fst (source_color_events_fold ranges ctx.func.blocks.zipIdx
    (Array.replicate ctx.insts.size 0,0))).symm

/-- Real retained records use the original buildCtx metadata, not a supplied color certificate. -/
theorem stock_lower_record_color_events {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧ original.func = f ∧
      record.input.entryColor =
        ((sourceColorEvents original ranges).foldl colorEventNext (Array.replicate original.insts.size 0,0)).1 := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,requests,oldBuild,allocation,finished⟩ := buildCtx_allocation build
  have kept := (((stock_lower_zeroColorLe run).2 event events).2 record records).1.1
  refine ⟨original,ranges,st0,oldBuild,(ctxSpec_of oldBuild).func,?_⟩
  rw [kept]
  have initialState := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2) finished
  dsimp only at initialState
  rw [initialState]
  change (sourceMetadata original ranges).entryColor = _
  exact sourceMetadata_color_events original ranges

end Backend.Stock.Proof.Acquire810

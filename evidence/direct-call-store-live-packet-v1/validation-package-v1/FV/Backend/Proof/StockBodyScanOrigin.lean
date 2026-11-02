import FV.Backend.Proof.StockDFG
import FV.Backend.Proof.StockBlockScan
import FV.Backend.Proof.StockBackwardSuffixSplit
import FV.Backend.Proof.StockTraversalRecordOrigin
import FV.Backend.Proof.StockCoreScanOrigin

/-! Separate the actual terminator record from the ordinary source body of a
successful original-node scan. Every index, state and code equation is derived
from the original driver execution and source ranges, without a replay premise. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

def sourceBodyIndices (f : Clif.Function) (bi : Nat) (b : Clif.Block) : List Nat :=
  ((List.range b.body.length).map (blockStart f bi + ·)).reverse

/-- Exact ordinary-body suffix of an actual backward scan. The machine code
executes the ordinary body first, then the terminator chunk. -/
structure SourceBodySplit (f : Clif.Function) (event : BlockScanEvent)
    (b : Clif.Block) (term : ScanRecord) (body : BlockScan) : Prop where
  block : f.blocks[event.block]? = some b
  termIndex : event.termInst = blockStart f event.block + b.body.length
  indices : event.indices = event.termInst :: sourceBodyIndices f event.block b
  termInst : term.inst = event.termInst
  termInput : term.input = event.input
  termRun : scanInstruction event.ctx event.block term.inst event.termInst event.isBranch term.input = .ok term.output
  records : event.output.records = term :: body.records
  state : body.state = event.output.state
  code : event.output.code = body.code ++ term.output.emitted
  scanned : ScansSpec (fun i => scanInstruction event.ctx event.block i event.termInst event.isBranch)
    (sourceBodyIndices f event.block b) term.output.state body
  retained : ∀ r ∈ body.records, r ∈ event.output.records
  positions : ∀ r ∈ body.records, ∃ j stm, b.body[j]? = some stm ∧ r.inst = blockStart f event.block + j

private theorem range_cons (start n : Nat) :
    (((Array.range (n + 1)).map (start + ·)).reverse.toList) =
      (start + n) :: ((List.range n).map (start + ·)).reverse := by
  simp [List.range_succ,List.map_append,List.reverse_append]

private theorem scans_cons {exec : Nat → State → Except String Scan} {i : Nat}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec (i :: indices) input output) :
    ∃ scan tail, exec i input = .ok scan ∧ ScansSpec exec indices scan.state tail ∧
      output.records = ⟨i,input,scan⟩ :: tail.records ∧ tail.state = output.state ∧
      output.code = tail.code ++ scan.emitted := by
  cases cert with
  | cons head rest => exact ⟨_,_,head,rest,rfl,rfl,rfl⟩

/-- Successful original Stock lowering derives the exact body/terminator split
and the original position of every body record. Neither scan certificates nor
record-position metadata are added to the accepted input conditions. -/
theorem stock_lower_body_scan_split {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ b term body, SourceBodySplit f event b term body := by
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  have nonempty : f.blocks.length ≠ 0 := fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
  have labelBound := (stock_backward_suffix_split parts).1
  have lookup : result.order.nodes[label]? = some (.original bi) := by
    rw [getElem!_pos result.order.nodes label labelBound] at node
    simp only [Array.getElem?_eq_getElem labelBound,node]
  have projected : bi ∈ stockOriginals result.order.nodes := by
    unfold stockOriginals
    apply List.mem_filterMap.mpr
    exact ⟨.original bi,Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup),rfl⟩
  have biBound := (stock_blockOrder_originals_nodup ordered nonempty).2 bi projected
  have block : f.blocks[bi]? = some f.blocks[bi] := by simp [biBound]
  obtain ⟨original,oldState,oldBuild,spec,view⟩ := buildCtx_source build
  have range : ranges[bi]! = (blockStart f bi,blockStart f bi + f.blocks[bi].body.length + 1) := by
    simp only [getElem!_def,spec.ranges bi f.blocks[bi] block]
  have origin := stock_lowerBlockCore_scanOrigin coreRun
  have eventBlock : event.block = bi := by rw [eventEq]; exact origin.2.2.1
  have termIndex : event.termInst = blockStart f bi + f.blocks[bi].body.length := by
    rw [eventEq,origin.2.2.2.1,range]
    dsimp only
    omega
  have indices : event.indices = event.termInst :: sourceBodyIndices f event.block f.blocks[bi] := by
    rw [eventEq,origin.2.2.2.2.1,range]
    dsimp only
    have len : blockStart f bi + f.blocks[bi].body.length + 1 - blockStart f bi = f.blocks[bi].body.length + 1 := by omega
    rw [len,range_cons]
    rw [← eventEq,termIndex,eventBlock]
    rfl
  have actual : scanBlock event.ctx event.block event.termInst event.isBranch event.indices event.input = .ok event.output := by
    rw [eventEq]; exact origin.2.2.2.2.2
  unfold scanBlock at actual
  have cert := runScans_spec actual
  rw [indices] at cert
  obtain ⟨scan,body,termRun,scanned,records,state,code⟩ := scans_cons cert
  let term : ScanRecord := ⟨event.termInst,event.input,scan⟩
  refine ⟨f.blocks[bi],term,body,?_,?_,indices,rfl,rfl,termRun,records,state,code,scanned,?_,?_⟩
  · rw [eventBlock]; exact block
  · rw [eventBlock]; exact termIndex
  · intro r member
    rw [records]
    exact List.mem_cons_of_mem _ member
  · intro r member
    have inIndices : r.inst ∈ sourceBodyIndices f event.block f.blocks[bi] := by
      rw [← scanned.order]
      exact List.mem_map.mpr ⟨r,member,rfl⟩
    unfold sourceBodyIndices at inIndices
    rw [List.mem_reverse] at inIndices
    obtain ⟨j,bounded,equal⟩ := List.mem_map.mp inIndices
    have bound := List.mem_range.mp bounded
    exact ⟨j,f.blocks[bi].body[j],List.getElem?_eq_getElem bound,equal.symm⟩
end Backend.Stock.Proof

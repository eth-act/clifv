import FV.Backend.Proof.StockMemorySretCopyBody
import FV.Backend.Proof.StockBodySplitUnique

namespace Backend.Stock.Memory.SretCopy
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false

/-- Use the identical actual scan split supplied by whole-driver assembly. -/
theorem captured_sret_copy_body_of_split {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {i0 i8 j0 j8 base destination low high : Nat} {lf0 lf8 sf0 sf8 : Clif.MemFlags}
    (loadLow : b.body[i0]? = some ⟨[low],.load .load .i64 lf0 base 0⟩)
    (loadHigh : b.body[i8]? = some ⟨[high],.load .load .i64 lf8 base 8⟩)
    (storeLow : b.body[j0]? = some ⟨[],.store .store .i64 sf0 low destination 0⟩)
    (storeHigh : b.body[j8]? = some ⟨[],.store .store .i64 sf8 high destination 8⟩)
    (lowEarlier : i0 < j0) (highEarlier : i8 < j8)
    (shape : ∀ j stm,b.body[j]? = some stm → j = i0 ∨ j = i8 ∨ j = j0 ∨ j = j8 ∨ stm.inst = .nop)
    {pi : Nat} {pb : Clif.Block} (parameterBlock : f.blocks[pi]? = some pb)
    (baseParameter : base ∈ pb.params.map (·.1))
    (destinationParameter : destination ∈ pb.params.map (·.1))
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR) {env : Clif.Env} {cp : Clif.Program}
    {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body) :
    ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
      ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
      ∀ ρ w,GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w →
        ∃ ρ' w',seqRun isem (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
            some (.fall ρ' w') ∧
          GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w' := by
  obtain ⟨otherTerm,otherBody,otherSplit,normal⟩ := captured_sret_copy_body run scope dominated events block
    loadLow loadHigh storeLow storeHigh lowEarlier highEarlier shape parameterBlock baseParameter destinationParameter
    stable memorySem memoryOk (env := env) (cp := cp)
  obtain ⟨rfl,rfl⟩ := split.unique otherSplit
  exact normal

end Backend.Stock.Memory.SretCopy

import FV.Backend.Proof.StockNoLoadDriver
import FV.Backend.Proof.StockProtectedSinkSource
import FV.Backend.Proof.StockSourceOrder

namespace Backend.Stock.Proof.SinkRules
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Actual source placeholders and mapped data supply both block helper frames. -/
theorem blockCore_protected_slot {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {slot : Nat}
    (safe : NoLoadAt ctx slot) (empty : ctx.insts[slot]!.results = [])
    {order : Order} {b : Clif.Block} {bi start stop : Nat} {data : V} {targets : Array Nat}
    {input : State} {output : LoweredBlockCore}
    (placeholder : ctx.insts[stop-1]? = some ⟨.op .unit,[],[],none⟩)
    (different : slot ≠ stop-1)
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok output) :
    SlotEq slot input output.state ∧ SlotEq slot input output.scan.input ∧
      ∀ r ∈ output.scan.output.records,SlotEq slot input r.input ∧ SlotEq slot input r.output.state := by
  apply slot_blockCore_of_helpers ?_ run
  intro reservations branch vs st next out trace call
  have patched := mapped_with_try_regs (mapped.termCtx placeholder data) reservations
  have localSafe := no_load_at_with_try_regs (no_load_at_term_ctx safe different data) reservations
  have localEmpty : ({termCtx ctx (stop-1) data with tryRegs := reservations} : Ctx).insts[slot]!.results = [] := by
    change (termCtx ctx (stop-1) data).insts[slot]!.results = []
    simpa only [getElem!_def,termCtx_insts_ne different data] using empty
  cases branch with
  | false => exact protected_slot_lower patched localSafe localEmpty call
  | true => exact protected_slot_branch patched localSafe localEmpty call

/-- Every actual source store stays unsunk through the full original driver.
Other source positions may contain loads, extensions and their actual sink rules. -/
theorem stock_lower_store_unsunk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {slot : Nat} {info : IInfo} {op : Clif.StoreOp} {ty : Clif.Ty}
    {flags : Clif.MemFlags} {value pointer : Nat} {offset : Int}
    (found : result.ctx.insts[slot]? = some info)
    (source : info.clif = some (.store op ty flags value pointer offset)) :
    result.final.sunk[slot]! = false ∧
      ∀ event ∈ result.blockScans.toList,event.input.sunk[slot]! = false ∧
        ∀ record ∈ event.output.records,record.input.sunk[slot]! = false ∧
          record.output.state.sunk[slot]! = false := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  have mapped := buildCtx_mappedInv scope hbuild
  have safe := store_no_load_at mapped found source
  have empty := store_results_empty mapped found source
  have nonempty : f.blocks.length ≠ 0 := fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
  have cores : ∀ label ∈ (Array.range order.nodes.size).reverse.toList,
      ∀ bi,order.nodes[label]! = .original bi → ∀ (data : V)
      {before : State} {core : LoweredBlockCore},
      lowerBlockCore built.1 order f f.blocks[bi]! bi built.2.1[bi]!.1 built.2.1[bi]!.2
        data order.successors[label]! before = .ok core →
      SlotEq slot before core.state ∧ SlotEq slot before core.scan.input ∧
        ∀ record ∈ core.scan.output.records,SlotEq slot before record.input ∧
          SlotEq slot before record.output.state := by
    intro label member bi tag data before core actual
    have labelBound : label < order.nodes.size := by
      simpa only [Array.toList_reverse,Array.toList_range,List.mem_reverse,List.mem_range] using member
    have lookup : order.nodes[label]? = some (.original bi) := by
      rw [getElem!_pos order.nodes label labelBound] at tag
      simp only [Array.getElem?_eq_getElem labelBound,tag]
    have projected : bi ∈ stockOriginals order.nodes := by
      unfold stockOriginals
      exact List.mem_filterMap.mpr ⟨.original bi,
        Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup),rfl⟩
    have biBound := (stock_blockOrder_originals_nodup horder nonempty).2 bi projected
    have block : f.blocks[bi]? = some f.blocks[bi] := by simp [biBound]
    obtain ⟨original,oldState,oldBuild,spec,view⟩ := buildCtx_source hbuild
    have range : built.2.1[bi]! = (blockStart f bi,blockStart f bi+f.blocks[bi].body.length+1) := by
      simp only [getElem!_def,spec.ranges bi f.blocks[bi] block]
    have placeholder : built.1.insts[built.2.1[bi]!.2-1]? = some ⟨.op .unit,[],[],none⟩ := by
      rw [range]
      have terminal : blockStart f bi+f.blocks[bi].body.length+1-1 = blockStart f bi+f.blocks[bi].body.length := by omega
      rw [terminal,view.insts]
      exact spec.facts.term bi f.blocks[bi] block
    have different : slot ≠ built.2.1[bi]!.2-1 := by
      intro same
      have conflict := Option.some.inj ((same ▸ found).symm.trans placeholder)
      have clif := congrArg IInfo.clif conflict
      rw [source] at clif
      cases clif
    exact blockCore_protected_slot mapped safe empty placeholder different actual
  have traversal := slot_traversal_of_cores cores hdriver
  have initial := build_ctx_sunk_false hbuild slot
  have events := traversal.2 built.2.2 (⟨rfl⟩ : SlotEq slot built.2.2 built.2.2)
    (by simp [SlotRecords])
  refine ⟨traversal.1.sunk.trans initial,?_⟩
  intro event member
  obtain ⟨pre,records⟩ := events event member
  refine ⟨pre.sunk.trans initial,?_⟩
  intro record retained
  obtain ⟨before,after⟩ := records record retained
  exact ⟨before.sunk.trans initial,after.sunk.trans initial⟩

end Backend.Stock.Proof.SinkRules

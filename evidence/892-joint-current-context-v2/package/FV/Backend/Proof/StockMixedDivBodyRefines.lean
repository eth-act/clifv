import FV.Backend.Proof.StockDivScanRefines
import FV.Backend.Proof.StockLocalSourceExecution
import FV.Backend.Proof.StockPureReturnRefines
import FV.Backend.Proof.StockPureNotrap
import FV.Backend.Proof.StockScanSemantics
import FV.Backend.Proof.IselCmpDiv
import FV.Backend.Proof.StockHighMulBodyRefines
import FV.Backend.Proof.StockGuardedOmission
import FV.Backend.Proof.StockPureBodyFamilies
import FV.Backend.Proof.StockPureSourceColors
import FV.Backend.Proof.StockPureDriverUnsunk
import FV.Backend.Proof.StockBlockScan
import FV.Backend.Proof.StockScanTrapSemantics
import FV.Backend.Proof.StockLocalTrapRefines
import FV.Backend.Proof.StockQuietSourceRecords
import FV.Backend.Proof.StockLastDivReturnDemand

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Every real mixed-body record is either a previously proved scalar record
or a retained, bound division record. The actual driver derives these cases. -/
inductive MixedDivRecord (f : Clif.Function) (ctx : Ctx) (bi : Nat) (r : ScanRecord) : Prop where
  | scalar {j : Nat} {b : Clif.Block} {stm : Clif.Stmt} {info : IInfo}
      (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
      (current : r.inst = blockStart f bi+j)
      (source : ctx.insts[r.inst]? = some info) (clif : info.clif = some stm.inst)
      (family : HighMulBody.Family stm.inst)
      (actual : PureBody.SourceRecord f ctx bi r) : MixedDivRecord f ctx bi r
  | division {j : Nat} {b : Clif.Block} {stm : Clif.Stmt} {step : Step} {info : IInfo}
      {op : Clif.DivOp} {ty : Clif.Ty} {x y z a : Nat}
      (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
      (current : r.inst = blockStart f bi+j)
      (source : ctx.insts[r.inst]? = some info) (clif : info.clif = some (.div op ty x y))
      (results : info.results = [z]) (statementResults : stm.results = [z])
      (mapped : ctx.valueReg? z = some (.vreg a .int))
      (recorded : r.output.step = some step) (emitted : step.decision = .emitted) :
      MixedDivRecord f ctx bi r

/-- Existing complete scalar handlers and the generic division handler compose
through one guarded original-source relation. -/
theorem MixedDivRecord.fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    (classified : MixedDivRecord f event.ctx event.block record)
    (sourceFamily : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastComplete.MemoryFormat stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (GuardedScanRel f result event.ctx event.block MR) record := by
  cases classified with
  | scalar block statement current source clif family actual =>
    exact QuietSourceColors.highmul_source_record_fall_refines run scope dominated events records
      block statement current family actual sourceFamily refines driver stable
  | division block statement current source clif results statementResults mapped recorded emitted =>
    exact stock_lower_div_scan_fall_refines run scope dominated events records
      block statement current _ source clif results statementResults mapped recorded emitted refines stable

/-- A real source trap is impossible at a pure prefix record; at a division,
the complete source bridge gives the real selected guard's coded halt. -/
theorem MixedDivRecord.trap_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    (classified : MixedDivRecord f event.ctx event.block record)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} :
    LocalScanTrapRefines (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
      isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) record := by
  cases classified with
  | @scalar j b stm info block statement current source clif family actual =>
    intro s code failed ρ w held
    obtain ⟨indexed,info',inst,rest,found,original,remaining,trapped⟩ := failed
    have sameInfo : info' = info := Option.some.inj (found.symm.trans source)
    subst info'
    have sameInst : inst = stm.inst := Option.some.inj (original.symm.trans clif)
    subst inst
    rw [LocalBody.local_outcome (LocalBody.LocalInst.of_pure (HighMulBody.family_pure family))] at trapped
    exact False.elim (HighMulBody.highmul_inst_notrap family s.2.1 s.2.2 code trapped)
  | @division j b stm step info op ty x y z a block statement current source clif results statementResults mapped recorded emitted =>
    intro s code failed ρ w held
    obtain ⟨indexed,info',inst,rest,found,original,remaining,trapped⟩ := failed
    have sameInfo : info' = info := Option.some.inj (found.symm.trans source)
    subst info'
    have sameInst : inst = .div op ty x y := Option.some.inj (original.symm.trans clif)
    subst inst
    have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
    obtain ⟨func,dfg,memory,values⟩ := held
    rw [position] at dfg values
    obtain ⟨d,output,bounds,trap⟩ := ScalarDiv.stock_lower_div_source_trap run scope dominated events
      records block statement current source clif results mapped recorded emitted refines dfg values trapped
    exact trap w

end Backend.Stock.Proof

namespace Backend.Stock.Proof.DivBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- The real single-block event selects the source block, independently of
its instruction families and source outcomes. -/
private theorem mixed_event_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    f.blocks[event.block]? = some b := by
  obtain ⟨original,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have bound := (List.getElem?_eq_some_iff.mp split.block).1
  rw [blocks] at bound
  have zero : event.block = 0 := by simpa using bound
  simp [zero,blocks]

/-- Derive every mixed body's actual record from its source syntax and real
whole-driver run. The final division's retention comes from return demand;
every pure prefix position derives quietness and its own concrete decision. -/
theorem actual_mixed_div_families {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {front : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ [stm])
    (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ term body, SourceBodySplit f event b term body ∧
      ∀ record ∈ body.records,MixedDivRecord f event.ctx event.block record := by
  have block := mixed_event_block run scope blocks events
  obtain ⟨term,last,body,step,info,a,split,lastMember,lastIndex,lastInput,
    lastRetained,lastStep,lastEmitted,lastSource,lastClif,lastResults,lastMapped⟩ :=
      actual_last_div_record run scope dominated events block shape division results ret
  have lastStatement : b.body[front.length]? = some stm := by
    rw [shape,List.getElem?_append_right (Nat.le_refl _)]; simp
  have unique : (sourceBodyIndices f event.block b).Nodup := by
    unfold sourceBodyIndices
    apply List.pairwise_reverse.mpr
    exact List.Pairwise.map (fun n => blockStart f event.block+n)
      (fun a b different eq => different (Nat.add_left_cancel eq.symm)) List.nodup_range
  refine ⟨term,body,split,?_⟩
  intro record member
  obtain ⟨j,item,statement,current⟩ := split.positions record member
  by_cases final : j = front.length
  · subst j
    have same : record = last := split.scanned.record_unique unique member lastMember
      (current.trans lastIndex.symm)
    subst record
    have sameItem : item = stm := Option.some.inj (statement.symm.trans lastStatement)
    subst item
    exact .division block lastStatement lastIndex lastSource lastClif lastResults results
      lastMapped lastStep lastEmitted
  · have inside := (List.getElem?_eq_some_iff.mp statement).1
    have before : j < front.length := by
      rw [shape,List.length_append] at inside
      simp only [List.length_cons,List.length_nil] at inside
      omega
    have original : front[j]? = some item := by
      rw [shape,List.getElem?_append_left before] at statement
      exact statement
    have itemFamily := family item (List.mem_of_getElem? original)
    have described := QuietSourceColors.actual_quiet_source_record run scope blocks events split
      member statement current (HighMulBody.family_quiet itemFamily)
      (HighMulBody.family_single itemFamily f)
    obtain ⟨sourceInfo,source,clif,sourceResults⟩ := ArithmeticBody.body_source_info run events split statement current
    exact .scalar block statement current source clif itemFamily described

end Backend.Stock.Proof.DivBody

namespace Backend.Stock.Proof.DivBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

private theorem mixed_memory_formats {f : Clif.Function} {b : Clif.Block}
    (blocks : f.blocks = [b]) {front : List Clif.Stmt} {stm : Clif.Stmt}
    (shape : b.body = front ++ [stm]) (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y : Nat} (division : stm.inst = .div op ty x y) :
    ∀ b' ∈ f.blocks,∀ item ∈ b'.body,CastComplete.MemoryFormat item.inst := by
  intro b' member item present
  have same : b' = b := by simpa only [blocks,List.mem_singleton] using member
  subst b'
  rw [shape] at present
  rcases List.mem_append.mp present with earlier | final
  · exact HighMulBody.family_formats (family item earlier)
  · have same : item = stm := by simpa only [List.mem_singleton] using final
    subst item
    rw [division]
    cases op <;> cases ty <;> simp [CastComplete.MemoryFormat,instNames]

private theorem mixed_local_family {b : Clif.Block} {front : List Clif.Stmt} {stm : Clif.Stmt}
    (shape : b.body = front ++ [stm]) (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y : Nat} (division : stm.inst = .div op ty x y) :
    ∀ item ∈ b.body,LocalBody.LocalInst item.inst := by
  intro item member
  rw [shape] at member
  rcases List.mem_append.mp member with earlier | final
  · exact LocalBody.LocalInst.of_pure (HighMulBody.family_pure (family item earlier))
  · have same : item = stm := by simpa only [List.mem_singleton] using final
    subst item
    simp [LocalBody.LocalInst,division]

/-- The complete real mixed body preserves successful source execution and
all original coded traps through one actual scan and one guarded relation. -/
theorem actual_mixed_div_body_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {front : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ [stm])
    (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ∃ term body,SourceBodySplit f event b term body ∧
      (∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
        ∀ ρ w,GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w → ∃ ρ' w',
          seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
            some (.fall ρ' w') ∧ GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w') ∧
      (∀ s code,SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
        (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s code →
        ∀ ρ w,GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w →
          TrapRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w code) := by
  obtain ⟨term,body,split,classified⟩ := actual_mixed_div_families run scope dominated blocks
    shape family division results ret events
  have formats := mixed_memory_formats blocks shape family division
  have normal : ∀ r ∈ body.records,ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block)
      isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) r := by
    intro r member
    exact MixedDivRecord.fall_refines run scope dominated events
      (split.retained r member) (classified r member) formats refines driver stable
  have trapping : ∀ r ∈ body.records,LocalScanTrapRefines
      (LocalBody.IndexedSourceTrap env cp f event.ctx event.block) isem result.final.alias
      (GuardedScanRel f result event.ctx event.block MR) r := by
    intro r member
    exact MixedDivRecord.trap_refines run scope dominated events
      (split.retained r member) (classified r member) refines
  refine ⟨term,body,split,?_,?_⟩
  · intro s s' source ρ w held
    apply split.scanned.fall_refines normal s s'
    · simpa only [sourceBodyIndices,List.reverse_reverse] using source
    · simpa only [split.state] using held
  · intro s code source ρ w held
    apply split.scanned.local_trap_refines normal trapping s code
    · simpa only [sourceBodyIndices,List.reverse_reverse] using source
    · simpa only [split.state] using held

/-- Actual ABI entry and return for any proved scalar prefix followed by a
returned division, retaining arbitrary original values and original slots. -/
theorem actual_mixed_div_entry_return_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    {front : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ [stm])
    (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame} (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,RunOkABI f result.code isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals mem) := by
  apply PureBody.actual_local_entry_return_refines_frame run scope dominated abi blocks
    (mixed_local_family shape family division) ret entered returned refines driver memorySem stable
    (fun event events => ?_) memory arguments
  obtain ⟨term,body,split,normal,trapping⟩ := actual_mixed_div_body_refines run scope dominated blocks
    shape family division results ret events refines driver stable
  exact ⟨term,body,split,normal⟩

/-- Actual ABI entry and the original trapped source prefix reach the selected
real coded trap inside the complete mixed function. -/
theorem actual_mixed_div_entry_trap_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {front : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ [stm])
    (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame} (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,VTrapFrom result.code isem ⟨0,0,ρ,w⟩ code := by
  apply LocalBody.actual_local_entry_trap_refines_frame run scope dominated blocks
    (mixed_local_family shape family division) ret entered trapped refines driver memorySem stable
    (fun event events => ?_) memory arguments
  obtain ⟨term,body,split,normal,trapping⟩ := actual_mixed_div_body_refines run scope dominated blocks
    shape family division results ret events refines driver stable
  exact ⟨term,body,split,trapping⟩

end Backend.Stock.Proof.DivBody


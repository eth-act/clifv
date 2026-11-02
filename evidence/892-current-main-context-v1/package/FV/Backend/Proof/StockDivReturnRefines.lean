import FV.Backend.Proof.StockDivBodyRefines
import FV.Backend.Proof.StockPureReturnRefines
import FV.Backend.Proof.StockSingleDivSourceTrap
namespace Backend.Stock.Proof.DivBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem event_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    f.blocks[event.block]? = some b := by
  obtain ⟨original,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have bound := (List.getElem?_eq_some_iff.mp split.block).1
  rw [blocks] at bound
  have zero : event.block = 0 := by simpa using bound
  simp [zero,blocks]

/-- Actual ABI entry, complete division body and return on every successful
original source run. Trapping source runs are not excluded from the source class. -/
theorem actual_single_div_entry_return_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    {stm : Clif.Stmt} (singleton : b.body = [stm])
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ, RunOkABI f result.code isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals mem) := by
  have family : ∀ item ∈ b.body, LocalBody.LocalInst item.inst := by
    intro item member
    have same : item = stm := by simpa only [singleton,List.mem_singleton] using member
    subst item
    simp [LocalBody.LocalInst,division]
  exact PureBody.actual_local_entry_return_refines_frame run scope dominated abi blocks
    family ret entered returned refines driver memorySem stable
    (fun event events => actual_single_div_body_refines run scope dominated events
      (event_block run scope blocks events) singleton division results ret refines stable)
    memory arguments

private theorem factor_seg {vb : VBlock} {pre code post : Array MInst}
    (parts : vb.insts = pre ++ code ++ post) : SegAt vb pre.size code.toList := by
  intro k hk
  have bound : k < code.size := by simpa using hk
  rw [parts,Array.append_assoc,Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [Array.getElem?_append_left bound]
  simp [bound]

/-- Actual ABI materialization followed by the retained division reaches its
real zero/overflow trap in the complete VCode, with original arguments and slots. -/
theorem actual_single_div_entry_trap_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {stm : Clif.Stmt} (singleton : b.body = [stm])
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ, VTrapFrom result.code isem ⟨0,0,ρ,w⟩ code := by
  obtain ⟨event,vb,pre,body,ρ',w',events,zero,placed,pieces,execution,mem',values,same,
    after,bodyCode⟩ := stock_lower_entry_prelude_refines_frame run scope dominated entered driver
      memorySem stable memory arguments
  have block := event_block run scope blocks events
  obtain ⟨term,record,scan,step,info,a,split,records,current,input,member,recorded,emitted,
    source,clif,infoResults,mapped⟩ := actual_single_div_record run scope dominated events block
      singleton division results ret
  have facts := entered
  obtain ⟨b',regs,entry,argTypes,paramTypes,set,frame⟩ := facts
  have sameBlock : b' = b := by
    have found : some b = some b' := by
      simpa only [Clif.Function.entry?,blocks,List.head?_cons] using entry
    exact Option.some.inj found.symm
  subst b'
  have sourceTrap := single_div_source_trap (s := ⟨fr,[],cm⟩)
    (by rw [frame]; exact singleton) division rfl (by rw [frame]; exact ret) trapped
  have held := stock_lower_entered_values_guarded_frame run scope dominated events entered values
    event.output.state w' mem'
  obtain ⟨func,dfg,memory,heldValues⟩ := held
  have chain := split.scanned.chain
  rw [records] at chain
  have finalState : event.output.state = record.output.state := split.state.symm.trans chain.2
  rw [finalState] at heldValues
  have statement : b.body[0]? = some stm := by simp [singleton]
  have position : record.inst = blockStart f event.block + 0 := by simpa using current
  obtain ⟨d,output,bounds,trap⟩ := ScalarDiv.stock_lower_div_source_trap run scope dominated events
    member block statement position source clif infoResults mapped recorded emitted refines dfg heldValues sourceTrap
  have scanCode : scan.code = record.output.emitted := by
    have scanned := split.scanned
    simp only [sourceBodyIndices,singleton,List.length_cons,List.length_nil,List.range_succ,
      List.range_zero,List.nil_append,List.map_cons,List.map_nil,List.reverse_cons,
      List.reverse_nil,List.nil_append,Nat.add_zero] at scanned
    cases scanned with
    | cons head rest =>
      cases rest
      simp only [List.cons.injEq] at records
      cases records.1
      simp only [Array.empty_append]
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have parts : vb.insts = pre ++ record.output.emitted.map (·.mapRegs resolve) ++
      (term.output.emitted.map (·.mapRegs resolve) ++ after) := by
    rw [pieces,bodyCode,split.code,scanCode,Array.map_append]
    simp only [Array.append_assoc,resolve]
  have segment : SegAt vb pre.size (record.output.emitted.toList.map (·.mapRegs resolve)) := by
    simpa only [Array.toList_map] using factor_seg parts
  have finished := trapRun_at placed segment (trap w')
  have room : pre.size < vb.insts.size := by
    obtain ⟨offset,i,ops,ρ1,w1,outs,final,traced,coded⟩ := trap w'
    obtain ⟨path,bound,atInst,rest⟩ := seqRun_stop_star placed segment traced
    have inside := (Array.getElem?_eq_some_iff.mp atInst).1
    omega
  have preSegment : SegAt vb 0 pre.toList := by
    intro k bounded
    have inside : k < pre.size := by simpa only [Array.length_toList] using bounded
    rw [Nat.zero_add,pieces,Array.getElem?_append_left inside]
    simp [inside]
  have path := seqRun_fall_star (vc := result.code) (sem := isem) placed preSegment
    (by simpa only [Nat.zero_add,Array.length_toList] using room) execution
  exact ⟨entrySeed event.ctx fr,finished.prefix (by simpa only [Nat.zero_add,Array.length_toList] using path)⟩

end Backend.Stock.Proof.DivBody

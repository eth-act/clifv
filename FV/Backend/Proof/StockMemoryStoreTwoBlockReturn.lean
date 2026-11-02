import FV.Backend.Proof.StockJumpEntryPrelude
import FV.Backend.Proof.StockOriginalEntryPrelude
import FV.Backend.Proof.StockMemoryStoreNonentryReturn
import FV.Backend.Proof.StockMemoryNopJumpSource
import FV.Backend.Proof.StockMemoryNopJumpSpec
import FV.Backend.Proof.StockTwoBlockShape
import FV.Backend.Proof.StockTwoBlockCompatibility

namespace Backend.Stock.Memory.StoreRoots
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock Backend.Stock.Proof Backend.Stock.Proof.Control
open Backend.Stock.Memory.StoreRoots
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Original two-block source syntax derives the complete guarded run from PC0.
The driver supplies order, retained records, code placement, and jump demands internally. -/
theorem two_block_store_return (kind : Kind) (ty : Clif.Ty) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true)
    {entry target : Clif.Block} (blocks : f.blocks = [entry,target])
    (nops : ∀ stm ∈ entry.body,stm.inst = .nop)
    (jump : entry.term = .jump ⟨target.id,[]⟩)
    {value pointer : Nat} {flags : Clif.MemFlags} {valueTy : Clif.Ty}
    (singleton : target.body = [⟨[],.store kind.sourceOp ty flags value pointer 0⟩])
    (ret : target.term = .ret []) (parameter : pointer ∈ entry.params.map (·.1))
    (valueParameter : (value,valueTy) ∈ entry.params)
    (width : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Backend.Proof.Sem} (refines : Refines F isem) (driver : DriverSem isem)
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (memoryOk : MemRelOk F sb syms f MR)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    RunOkABIAt f result.code result.edgeArgs isem MR fr.slots
      ⟨0,0,entrySeed result.ctx fr,w⟩ (.returned vals mem) := by
  have formats : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastComplete.MemoryFormat stm.inst := by
    intro b member stm present
    have which : b = entry ∨ b = target := by simpa [blocks] using member
    rcases which with same | same
    · subst b
      rw [nops stm present]
      simp [CastComplete.MemoryFormat,instNames]
    · subst b
      have same : stm = ⟨[],.store kind.sourceOp ty flags value pointer 0⟩ := by
        simpa only [singleton,List.mem_singleton] using present
      subst stm
      simp [CastComplete.MemoryFormat,instNames]
  have entrySource : f.blocks[0]? = some entry := by rw [blocks]; rfl
  have targetSource : f.blocks[1]? = some target := by rw [blocks]; rfl
  have different : entry.id ≠ target.id := by
    intro same
    have absent := scope.noEntryPred entry (by simp [blocks]) target.id
      (by simp [succIds,dests,jump])
    apply absent
    simp [blockIdx?,blocks,List.findIdx?_cons,same]
  have order : result.order = ⟨#[.original 0,.original 1],#[#[1],#[]]⟩ :=
    Except.ok.inj ((stock_lower_order run).symm.trans
      (TwoBlock.block_order blocks jump ret rfl different))
  have tag : result.order.nodes[0]? = some (.original 0) := by rw [order]; rfl
  obtain ⟨spec⟩ := stock_lower_nop_jump_body_spec run scope dominated tag entrySource nops jump
    driver (MR := MR) env cp
  have targetEq : spec.target = 1 := by
    have targets := spec.targets
    rw [order] at targets
    exact (List.cons.inj targets).1.symm
  have targetTag : result.order.nodes[spec.target]? = some (.original 1) := by
    rw [targetEq,order]
    rfl
  have index : blockIdx? f target.id = some 1 := by
    simp [blockIdx?,blocks,List.findIdx?_cons,different,Ne.symm different]
  obtain ⟨targetBlock,targetFound,found⟩ := block?_of_idx index
  have sameTarget : targetBlock = target := Option.some.inj (found.symm.trans targetSource)
  subst targetBlock
  obtain ⟨ranges,params,input,data,core,raw,prelude,coreRun,assembled,build,sizes,prepared,
    nextEvents,nextBlock,rawCode,placed⟩ := stock_lower_original_block_scan_assembly run targetTag
  have nextSource : f.blocks[core.scan.block]? = some target := by rw [nextBlock]; exact targetSource
  have nonempty : 0 < spec.core.code.size := by
    rw [spec.bodyCode]
    simp only [Array.size_append,Array.size_singleton]
    omega
  let entryCore : EntryCoreSpec f result entry := {
    ranges := spec.ranges
    params := spec.params
    core := spec.core
    raw := spec.raw
    preludeCode := spec.preludeCode
    build := spec.build
    sizes := spec.sizes
    assembled := spec.assembled
    events := spec.events
    block := entrySource
    rawCode := spec.rawCode
    placed := spec.placed
    nonempty := nonempty }
  obtain ⟨ρ',w',path,held,values,sameWorld⟩ := original_entry_prelude run scope dominated entryCore entered
    driver memorySem stable memory arguments
  have continuation : ∀ (left : Nat) (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = target.body →
      s.frame.term = target.term → SourceDefinedAt f result.ctx 1 0 s.frame →
      Clif.runLoop env cp left s = .returned vals mem →
      GuardedScanRel f result core.scan.ctx core.scan.block MR core.scan.output.state
        (0,s.frame,s.mem) ρ w →
      RunOkABIAt f result.code result.edgeArgs isem MR
        s.frame.slots ⟨spec.target,0,ρ,w⟩ (.returned vals mem) := by
    intro left s ρ w func callers body terminal defined returned held
    exact actual_nonentry_store_return kind ty run scope dominated abi targetTag targetSource
      (by decide) nextEvents nextBlock formats singleton ret entrySource parameter entrySource valueParameter width refines stable memorySem memoryOk
      func callers body terminal (by simpa only [nextBlock] using defined) returned held
  have entryFacts := entered
  obtain ⟨original,regs,entryLookup,argTypes,paramTypes,set,frame⟩ := entryFacts
  have originalSource : f.blocks[0]? = some original := by
    simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using entryLookup
  have sameEntry : original = entry := Option.some.inj (originalSource.symm.trans entrySource)
  subst original
  have defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 fr := by
    rw [spec.atBlock]
    exact Control.source_defined_entry_frame dominated result.ctx entered
  have finished := nop_jump_body_returns_at run scope dominated refines driver stable spec nops tag jump
    targetTag index targetFound nextEvents nextBlock (by rw [targetEq]; omega) continuation
    (s := ⟨fr,[],cm⟩) rfl (by rw [frame]) (by rw [frame]) defined returned held
  have seed : entrySeed spec.core.scan.ctx fr = entrySeed result.ctx fr := by
    classical
    let make (lookup : Nat → Option Reg) (key : Nat) : CV :=
      if h : ∃ pair : Nat × Clif.Val,
          lookup pair.1 = some (.vreg key .int) ∧ fr.regs pair.1 = some pair.2 then
        (Classical.choose h).2.bits.setWidth 128
      else 0
    change make spec.core.scan.ctx.valueReg? = make result.ctx.valueReg?
    rw [funext (stock_lower_record_context run scope spec.events).2.1]
  rw [← seed]
  exact RunOkABIAt.prefix path finished

/-- The original source class also satisfies the unchanged compiler ABI contract. -/
theorem two_block_store_return_function (kind : Kind) (ty : Clif.Ty) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true)
    {entry target : Clif.Block} (blocks : f.blocks = [entry,target])
    (nops : ∀ stm ∈ entry.body,stm.inst = .nop)
    (jump : entry.term = .jump ⟨target.id,[]⟩)
    {value pointer : Nat} {flags : Clif.MemFlags} {valueTy : Clif.Ty}
    (singleton : target.body = [⟨[],.store kind.sourceOp ty flags value pointer 0⟩])
    (ret : target.term = .ret []) (parameter : pointer ∈ entry.params.map (·.1))
    (valueParameter : (value,valueTy) ∈ entry.params)
    (width : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Backend.Proof.Sem} (refines : Refines F isem) (driver : DriverSem isem)
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (memoryOk : MemRelOk F sb syms f MR)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    RunOkABI f result.code isem MR fr.slots
      ⟨0,0,entrySeed result.ctx fr,w⟩ (.returned vals mem) := by
  have executed := two_block_store_return kind ty run scope dominated abi blocks nops jump
    singleton ret parameter valueParameter width entered refines driver memorySem stable memoryOk returned memory arguments
  have different : entry.id ≠ target.id := by
    intro same
    have absent := scope.noEntryPred entry (by simp [blocks]) target.id
      (by simp [succIds,dests,jump])
    apply absent
    simp [blockIdx?,blocks,List.findIdx?_cons,same]
  exact RunOkABIAt.legacyCompatible (TwoBlock.legacy_compatible run scope blocks jump ret rfl different) executed

end Backend.Stock.Memory.StoreRoots

import FV.Backend.Proof.StockBmaskScanRefines
import FV.Backend.Proof.StockZeroResultScan
import FV.Backend.Proof.StockScalarDivBodyRecords

namespace Backend.Stock.Proof.MaskBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192

/-- Existing arbitrary scalar/division bodies plus original bmask and nop. -/
def Family (inst : Clif.Inst) : Prop :=
  (HighMulBody.Family inst ∨ ∃ op ty x y,inst = .div op ty x y) ∨
    (∃ ty x,inst = .bmask ty x) ∨ inst = .nop

theorem family_formats {inst : Clif.Inst} (family : Family inst) : CastComplete.MemoryFormat inst := by
  rcases family with old | ⟨ty,x,rfl⟩ | rfl
  · exact SinkRules.scalar_div_formats old
  · simp [CastComplete.MemoryFormat,instNames]
  · simp [CastComplete.MemoryFormat,instNames]

private theorem records_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records,exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

/-- Quiet zero-result source instructions, including nop, are omitted by the
actual whole-driver scan even when other body positions have effect colors. -/
theorem actual_nop_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body)
    {record : ScanRecord} (member : record ∈ body.records)
    {j : Nat} {stm : Clif.Stmt} (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block+j) (nop : stm.inst = .nop) :
    ∃ step,record.output.step = some step ∧ step.decision = .omitted := by
  have bound := (List.getElem?_eq_some_iff.mp split.block).1
  rw [blocks] at bound
  have bi : event.block = 0 := by simpa using bound
  have atIndex : record.inst = j := by simpa [bi,blockStart] using current
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have ordinary : record.inst ≠ event.termInst := by
    rw [current,split.termIndex]; omega
  have preserved := (QuietSourceColors.stock_lower_quiet_single_block_unsunk run blocks statement
    (by rw [nop]; rfl)).2.2 event events
  have safe : record.input.sunk[record.inst]! = false := by
    rw [atIndex]
    exact (preserved.2 record (split.retained record member)).1
  obtain ⟨info,source,clif,_⟩ := ArithmeticBody.body_source_info run events split statement current
  have inv := (stock_lower_record_context run scope events).1
  obtain ⟨tys,computed,typed,arity⟩ := inv.resTys record.inst info stm.inst source clif
  have emptyTypes : tys = [] := by simpa only [nop,Clif.Inst.resultTypes,Option.some.injEq] using computed.symm
  have empty : info.results = [] := List.length_eq_zero_iff.mp (by simpa only [emptyTypes,List.length_nil] using arity)
  have bang : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,source]
  have expected := scan_zero_results (ctx := event.ctx) (block := event.block) (isBranch := event.isBranch)
    safe ordinary (by rw [bang]; exact empty)
    (by rw [bang,clif,nop]; rfl)
  have actual := records_execute split.scanned record member
  have equal := Except.ok.inj (actual.symm.trans expected)
  exact ⟨_,by rw [equal],rfl⟩

/-- Only the new cases are represented here; all earlier scalar/division
record contracts and their original theorem variants are reused unchanged. -/
inductive Record (f : Clif.Function) (ctx : Ctx) (bi : Nat) (r : ScanRecord) : Prop where
  | old (actual : MixedDivRecord f ctx bi r) : Record f ctx bi r
  | bmask {j : Nat} {b : Clif.Block} {stm : Clif.Stmt} {info : IInfo} {ty : Clif.Ty} {x : Nat}
      (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
      (current : r.inst = blockStart f bi+j) (mask : stm.inst = .bmask ty x)
      (source : ctx.insts[r.inst]? = some info) (clif : info.clif = some (.bmask ty x))
      (actual : PureBody.SourceRecord f ctx bi r) : Record f ctx bi r
  | nop {j : Nat} {b : Clif.Block} {stm : Clif.Stmt} {step : Step} {info : IInfo}
      (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
      (current : r.inst = blockStart f bi+j)
      (source : ctx.insts[r.inst]? = some info) (clif : info.clif = some .nop)
      (recorded : r.output.step = some step) (omitted : step.decision = .omitted) : Record f ctx bi r

/-- The real scan and source syntax derive every record class for arbitrary
interleavings, retaining old division behavior, bmask binding and zero-result nop. -/
theorem actual_families {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b]) (family : ∀ stm ∈ b.body,Family stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ term body,SourceBodySplit f event b term body ∧
      ∀ record ∈ body.records,Record f event.ctx event.block record := by
  obtain ⟨original,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have same : original = b := by
    have member := List.mem_of_getElem? split.block
    simpa only [blocks,List.mem_singleton] using member
  subst original
  have sourceFormats : ∀ b' ∈ f.blocks,∀ stm ∈ b'.body,CastComplete.MemoryFormat stm.inst := by
    intro b' member stm present
    have same : b' = b := by simpa only [blocks,List.mem_singleton] using member
    subst b'
    exact family_formats (family stm present)
  refine ⟨term,body,split,?_⟩
  intro record member
  obtain ⟨j,stm,statement,current⟩ := split.positions record member
  obtain ⟨info,source,clif,_⟩ := ArithmeticBody.body_source_info run events split statement current
  rcases family stm (List.mem_of_getElem? statement) with (scalar | ⟨op,ty,x,y,division⟩) | ⟨ty,x,mask⟩ | nop
  · exact .old (.scalar split.block statement current source clif scalar
      (QuietSourceColors.actual_quiet_source_record run scope blocks events split member statement current
        (HighMulBody.family_quiet scalar) (HighMulBody.family_single scalar f)))
  · exact .old (DivBody.actual_division_record run scope sourceFormats events split member statement current division)
  · exact .bmask split.block statement current mask source (clif.trans (congrArg some mask))
      (QuietSourceColors.actual_quiet_source_record run scope blocks events split member statement current
        (by rw [mask]; rfl) (by rw [mask]; rfl))
  · obtain ⟨step,recorded,omitted⟩ := actual_nop_record run scope blocks events split member statement current nop
    exact .nop split.block statement current source (clif.trans (congrArg some nop)) recorded omitted

/-- The shared guarded scan relation composes all old records with bmask and nop. -/
theorem Record.fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    (classified : Record f event.ctx event.block record)
    (sourceFormats : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastComplete.MemoryFormat stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (GuardedScanRel f result event.ctx event.block MR) record := by
  cases classified with
  | old actual => exact actual.fall_refines run scope dominated events records sourceFormats refines driver stable
  | nop block statement current source clif recorded omitted =>
    exact stock_lower_omitted_scan_fall_refines run scope dominated events records block statement current recorded omitted
  | bmask block statement current mask source0 clif0 actual =>
    obtain ⟨j',b',stm',found,atStmt,indexed,step,recorded,decision⟩ := actual
    have sameB := Option.some.inj (found.symm.trans block)
    subst b'
    have sameJ := Nat.add_left_cancel (indexed.symm.trans current)
    subst j'
    have sameStmt := Option.some.inj (atStmt.symm.trans statement)
    subst stm'
    rcases decision with omitted | ⟨emitted,info,z,a,source,clif,one,results,mapped⟩
    · exact stock_lower_omitted_scan_fall_refines run scope dominated events records block statement current recorded omitted
    · exact stock_lower_bmask_scan_fall_refines run scope dominated events records block statement current source
        (clif.trans (congrArg some mask)) one results mapped recorded emitted refines stable

/-- Real source traps remain handled by the existing division proof. Bmask
and nop cannot introduce a source trap, including when their scan was omitted. -/
theorem Record.trap_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    (classified : Record f event.ctx event.block record)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} :
    LocalScanTrapRefines (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
      isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) record := by
  cases classified with
  | old actual => exact actual.trap_refines run scope dominated events records refines
  | @bmask j b stm info ty x block statement current mask source clif actual =>
    intro s code failed ρ w held
    obtain ⟨indexed,info',inst,rest,found,original,remaining,trapped⟩ := failed
    have sameInfo := Option.some.inj (found.symm.trans source)
    subst info'
    have sameInst := Option.some.inj (original.symm.trans clif)
    subst inst
    rw [LocalBody.local_outcome (show LocalBody.LocalInst (.bmask ty x) from True.intro)] at trapped
    cases lookup : s.2.1.regs x <;>
      simp [Clif.evalInst,Clif.Frame.get,lookup,Clif.Res.ofOption] at trapped
  | nop block statement current source clif recorded omitted =>
    intro s code failed ρ w held
    obtain ⟨indexed,info',inst,rest,found,original,remaining,trapped⟩ := failed
    have sameInfo := Option.some.inj (found.symm.trans source)
    subst info'
    have sameInst := Option.some.inj (original.symm.trans clif)
    subst inst
    rw [LocalBody.local_outcome (show LocalBody.LocalInst .nop from True.intro)] at trapped
    cases trapped

end Backend.Stock.Proof.MaskBody

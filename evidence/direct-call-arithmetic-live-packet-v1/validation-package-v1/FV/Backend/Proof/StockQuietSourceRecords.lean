import FV.Backend.Proof.StockPureNotrap
import FV.Backend.Proof.StockScanSemantics
import FV.Backend.Proof.IselCmpDiv
import FV.Backend.Proof.StockHighMulBodyRefines
import FV.Backend.Proof.StockGuardedOmission
import FV.Backend.Proof.StockPureBodyFamilies
import FV.Backend.Proof.StockPureSourceColors
import FV.Backend.Proof.StockPureDriverUnsunk
import FV.Backend.Proof.StockBlockScan

namespace Backend.Stock.Proof.QuietSourceColors
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
private abbrev ColorState := Array Nat × Array Nat × Array (List Nat) × Nat
private def bodyStep (start bi : Nat) (x : Clif.Stmt × Nat) (s : ColorState) : Id (ForInStep ColorState) :=
  if colored x.1.inst then
    pure (.yield (s.1.set! (start+x.2) bi,s.2.1.set! (start+x.2) s.2.2.2,
      s.2.2.1.set! (start+x.2) (instArgs x.1.inst),s.2.2.2+1))
  else pure (.yield (s.1.set! (start+x.2) bi,s.2.1,
    s.2.2.1.set! (start+x.2) (instArgs x.1.inst),s.2.2.2))
private theorem body_color_at (start bi q : Nat) (xs : List (Clif.Stmt × Nat))
    (separate : ∀ x ∈ xs, colored x.1.inst = true → start+x.2 ≠ q) (s : ColorState) :
    ((forIn xs s (bodyStep start bi)).run).2.1[q]! = s.2.1[q]! := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    have tail : ∀ y ∈ xs, colored y.1.inst = true → start+y.2 ≠ q :=
      fun y hy => separate y (List.mem_cons_of_mem _ hy)
    rw [List.forIn_cons]
    cases coloredHere : colored x.1.inst with
    | false =>
      simp only [bodyStep,coloredHere,Bool.false_eq_true,ite_false]
      exact ih tail _
    | true =>
      simp only [bodyStep,coloredHere,ite_true]
      change ((forIn xs (s.1.set! (start+x.2) bi,s.2.1.set! (start+x.2) s.2.2.2,
        s.2.2.1.set! (start+x.2) (instArgs x.1.inst),s.2.2.2+1) (bodyStep start bi)).run).2.1[q]! = s.2.1[q]!
      rw [ih tail]
      exact Array.getElem!_set!_ne _ _ _ _ (separate x (List.mem_cons_self ..) coloredHere)

/-- Only the selected source position must be quiet. Other instructions may
carry division/trap colors; their distinct indexed writes cannot color it. -/
theorem sourceMetadata_quiet_single_block (ctx : Ctx) (ranges : Array (Nat × Nat)) (b : Clif.Block)
    (blocks : ctx.func.blocks = [b]) (range : ranges[0]! = (0,b.body.length+1))
    {q : Nat} {stm : Clif.Stmt} (statement : b.body[q]? = some stm)
    (quiet : colored stm.inst = false) : (sourceMetadata ctx ranges).entryColor[q]! = 0 := by
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have sourceAt : b.body[q] = stm := by
    have found := List.getElem?_eq_getElem inside
    rw [statement] at found
    exact (Option.some.inj found).symm
  have separate : ∀ x ∈ b.body.zipIdx, colored x.1.inst = true → ranges[0]!.1+x.2 ≠ q := by
    intro x member coloredHere equal
    have index : x.2 = q := by simpa only [range,Nat.zero_add] using equal
    have item := (List.mem_zipIdx member).2.2
    simp only [Nat.sub_zero,index] at item
    have same : x.1 = stm := item.trans sourceAt
    rw [same,quiet] at coloredHere
    cases coloredHere
  have inner := body_color_at ranges[0]!.1 0 q b.body.zipIdx separate
    (Array.replicate ctx.insts.size 0,Array.replicate ctx.insts.size 0,
      Array.replicate ctx.insts.size [],0+1)
  simp only [sourceMetadata,blocks,List.zipIdx_cons,List.zipIdx_nil,
    List.forIn_cons,List.forIn_nil,Id.run_bind,Id.run_pure]
  change (((forIn b.body.zipIdx _ (bodyStep ranges[0]!.1 0)).run).2.1.set!
    (ranges[0]!.2-1) _)[q]! = 0
  have different : ranges[0]!.2-1 ≠ q := by rw [range]; simp only; omega
  rw [Array.getElem!_set!_ne _ _ _ _ different,inner]
  by_cases bound : q < ctx.insts.size <;> simp [getElem!_def,Array.getElem?_replicate,bound]

theorem buildCtx_quiet_single_block {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} (build : Stock.buildCtx f = .ok (ctx,ranges,initial))
    {b : Clif.Block} (blocks : f.blocks = [b])
    {q : Nat} {stm : Clif.Stmt} (statement : b.body[q]? = some stm)
    (quiet : colored stm.inst = false) :
    initial.entryColor[q]! = 0 ∧ initial.sunk[q]! = false := by
  obtain ⟨original,st0,requests,oldBuild,_,finished⟩ := buildCtx_allocation build
  have spec := ctxSpec_of oldBuild
  have originalBlocks : original.func.blocks = [b] := by rw [spec.func]; exact blocks
  have range : ranges[0]! = (0,b.body.length+1) := by
    have found : f.blocks[0]? = some b := by rw [blocks]; rfl
    have r := spec.ranges 0 b found
    simp only [getElem!_def,r,Option.getD_some]
    simp [blockStart]
  have state := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2) finished
  dsimp only at state
  rw [state]
  constructor
  · change (sourceMetadata original ranges).entryColor[q]! = 0
    exact sourceMetadata_quiet_single_block original ranges b originalBlocks range statement quiet
  · change (Array.replicate original.insts.size false)[q]! = false
    by_cases bound : q < original.insts.size <;>
      simp [getElem!_def,Array.getElem?_replicate,bound]


/-- Actual whole-driver unsunkness at one quiet source slot remains available
when other slots have division/trap colors. -/
theorem stock_lower_quiet_single_block_unsunk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {b : Clif.Block} (blocks : f.blocks = [b])
    {q : Nat} {stm : Clif.Stmt} (statement : b.body[q]? = some stm)
    (quiet : colored stm.inst = false) :
    result.initial.entryColor[q]! = 0 ∧ result.final.sunk[q]! = false ∧
      ∀ event ∈ result.blockScans.toList, event.input.sunk[q]! = false ∧
        ∀ record ∈ event.output.records,
          record.input.sunk[q]! = false ∧ record.output.state.sunk[q]! = false := by
  have built : ∃ ctx ranges, Stock.buildCtx f = .ok (ctx,ranges,result.initial) := by
    have actual := run
    unfold Stock.lower at actual
    dsimp only at actual
    repeat' first
      | (solve | cases actual)
      | simp only [bind,Except.bind,pure,Except.pure] at actual
      | split at actual
    cases actual
    rename_i _ built hbuild _ order horder _ driver hdriver
    exact ⟨built.1,built.2.1,hbuild⟩
  obtain ⟨ctx,ranges,build⟩ := built
  obtain ⟨zero,safe⟩ := buildCtx_quiet_single_block build blocks statement quiet
  obtain ⟨final,events⟩ := stock_lower_zeroColorLe run
  refine ⟨zero,final.2 q zero safe,?_⟩
  intro event member
  obtain ⟨pre,records⟩ := events event member
  refine ⟨pre.2 q zero safe,?_⟩
  intro record retained
  obtain ⟨a,b⟩ := records record retained
  exact ⟨a.2 q zero safe,b.2 q zero safe⟩

end Backend.Stock.Proof.QuietSourceColors



namespace Backend.Stock.Proof.QuietSourceColors
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

private theorem records_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records, exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

/-- One original quiet statement derives its actual omission/emission and
result mapping even when other source statements are colored. -/
theorem actual_quiet_source_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body)
    {record : ScanRecord} (member : record ∈ body.records)
    {j : Nat} {stm : Clif.Stmt} (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block+j)
    (quiet : colored stm.inst = false)
    (single : (stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig))
      (f.sigDecls.lookup ·)).map List.length = some 1) :
    PureBody.SourceRecord f event.ctx event.block record := by
  have bound := (List.getElem?_eq_some_iff.mp split.block).1
  rw [blocks] at bound
  have bi : event.block = 0 := by simpa using bound
  have current' : record.inst = j := by simpa [bi,blockStart] using current
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have ordinary : record.inst ≠ event.termInst := by
    rw [current',split.termIndex,bi]
    simp only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add]
    omega
  have preserved := (stock_lower_quiet_single_block_unsunk run blocks statement quiet).2.2 event events
  have safe : record.input.sunk[record.inst]! = false := by
    rw [current']
    exact (preserved.2 record (split.retained record member)).1
  have actual := records_execute split.scanned record member
  obtain ⟨step,recorded,decision⟩ := stock_ordinary_unsunk_decision safe ordinary actual
  have decided : step.decision = .omitted ∨ step.decision = .emitted := by
    rcases decision with omitted | remembered | emitted
    · exact Or.inl omitted
    · exact False.elim ((Coverage.lower_record_noOpportunistic scope run events
        (split.retained record member) recorded) remembered)
    · exact Or.inr emitted
  refine ⟨j,b,stm,split.block,statement,current,step,recorded,?_⟩
  rcases decided with omitted | emitted
  · exact Or.inl omitted
  · obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split statement current
    have inv := (stock_lower_record_context run scope events).1
    obtain ⟨tys,types,typed,arity⟩ := inv.resTys record.inst info stm.inst source clif
    rw [types] at single
    have length : info.results.length = 1 := arity.trans (Option.some.inj single)
    obtain ⟨x,infoResults⟩ : ∃ x, info.results = [x] := by
      cases values : info.results with
      | nil => simp [values] at length
      | cons x rest =>
        cases rest with
        | nil => exact ⟨x,rfl⟩
        | cons y tail => simp [values] at length
    obtain ⟨emission,emissionRun,scan⟩ := stock_emitted_scan actual recorded emitted
    have atInst : event.ctx.insts[record.inst]! = info := by
      simp only [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,source,Option.getD_some]
    obtain ⟨r,mapped⟩ := ArithmeticBody.emission_result_mapped emissionRun
      (by rw [atInst]; exact infoResults)
    obtain ⟨a,rfl⟩ := inv.valueReg x r mapped
    exact Or.inr ⟨emitted,info,x,a,source,clif,infoResults,results.symm.trans infoResults,mapped⟩
end Backend.Stock.Proof.QuietSourceColors

namespace Backend.Stock.Proof.QuietSourceColors
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Reuse all previously proved scalar-family handlers at one actual quiet
prefix record, while other source positions may contain real division. -/
theorem highmul_source_record_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {record : ScanRecord} (records : record ∈ event.output.records)
    {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi+j)
    (family : HighMulBody.Family stm.inst)
    (recordSource : PureBody.SourceRecord f event.ctx bi record)
    (sourceFamily : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastComplete.MemoryFormat stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) isem result.final.alias
      (GuardedScanRel f result event.ctx bi MR) record := by
  obtain ⟨j',b',stm',found,atStmt,indexed,step,recorded,decision⟩ := recordSource
  have sameB : b' = b := Option.some.inj (found.symm.trans block)
  subst b'
  have sameJ : j' = j := Nat.add_left_cancel (indexed.symm.trans current)
  subst j'
  have sameStmt : stm' = stm := Option.some.inj (atStmt.symm.trans statement)
  subst stm'
  rcases decision with omitted | ⟨emitted,info,z,a,source,clif,one,results,mapped⟩
  · exact stock_lower_omitted_scan_fall_refines run scope dominated events records
      block statement current recorded omitted
  · have classified := HighMulBody.emitted_record_family block statement current recorded emitted
      source clif one results mapped family
    exact stock_lower_mixed_highmul_record_fall_refines run scope dominated events records
      sourceFamily classified refines driver stable
end Backend.Stock.Proof.QuietSourceColors


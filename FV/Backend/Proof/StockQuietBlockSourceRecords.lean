module

public import FV.Backend.Proof.StockQuietSourceRecords
public import FV.Backend.Proof.StockBlockRanges

@[expose] public section

namespace Backend.Stock.Proof.QuietSourceColors
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

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

private abbrev BlockColorState :=
  Array Nat × Array Nat × Array Nat × Array (List Nat) × Nat

private def blockStep (ranges : Array (Nat × Nat)) (x : Clif.Block × Nat)
    (s : BlockColorState) : Id (ForInStep BlockColorState) := do
  let inner := (forIn x.1.body.zipIdx
    (s.1,s.2.1,s.2.2.2.1,s.2.2.2.2+1) (bodyStep ranges[x.2]!.1 x.2)).run
  let ti := ranges[x.2]!.2-1
  pure (.yield (inner.1.set! ti x.2,inner.2.1.set! ti inner.2.2.2,
    s.2.2.1.push (inner.2.2.2+1),inner.2.2.1.set! ti (termArgs x.1.term),inner.2.2.2+1))

private theorem blocks_color_at (ranges : Array (Nat × Nat)) (q : Nat)
    (xs : List (Clif.Block × Nat))
    (separate : ∀ x ∈ xs,
      (∀ y ∈ x.1.body.zipIdx,colored y.1.inst = true → ranges[x.2]!.1+y.2 ≠ q) ∧
      ranges[x.2]!.2-1 ≠ q) (s : BlockColorState) :
    ((forIn xs s (blockStep ranges)).run).2.1[q]! = s.2.1[q]! := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    have tail := fun y hy => separate y (List.mem_cons_of_mem x hy)
    let inner := (forIn x.1.body.zipIdx
      (s.1,s.2.1,s.2.2.2.1,s.2.2.2.2+1) (bodyStep ranges[x.2]!.1 x.2)).run
    rw [List.forIn_cons]
    change ((forIn xs
      (inner.1.set! (ranges[x.2]!.2-1) x.2,inner.2.1.set! (ranges[x.2]!.2-1) inner.2.2.2,
        s.2.2.1.push (inner.2.2.2+1),inner.2.2.1.set! (ranges[x.2]!.2-1) (termArgs x.1.term),inner.2.2.2+1)
      (blockStep ranges)).run).2.1[q]! = s.2.1[q]!
    rw [ih tail,Array.getElem!_set!_ne _ _ _ _ (separate x (List.mem_cons_self ..)).2]
    exact body_color_at ranges[x.2]!.1 x.2 q x.1.body.zipIdx
      (separate x (List.mem_cons_self ..)).1 _

/-- Metadata writes at other source positions preserve a quiet slot across
the complete original block traversal, including every terminator write. -/
theorem sourceMetadata_zero_of_separate (ctx : Ctx) (ranges : Array (Nat × Nat)) (q : Nat)
    (separate : ∀ x ∈ ctx.func.blocks.zipIdx,
      (∀ y ∈ x.1.body.zipIdx,colored y.1.inst = true → ranges[x.2]!.1+y.2 ≠ q) ∧
      ranges[x.2]!.2-1 ≠ q) :
    (sourceMetadata ctx ranges).entryColor[q]! = 0 := by
  change ((forIn ctx.func.blocks.zipIdx
    (Array.replicate ctx.insts.size 0,Array.replicate ctx.insts.size 0,#[],
      Array.replicate ctx.insts.size [],0) (blockStep ranges)).run).2.1[q]! = 0
  rw [blocks_color_at ranges q ctx.func.blocks.zipIdx separate]
  by_cases bound : q < ctx.insts.size <;>
    simp [getElem!_def,Array.getElem?_replicate,bound]

/-- Original block lookup and disjoint source ranges derive quiet metadata
without requiring a single-block function or quiet neighboring blocks. -/
theorem buildCtx_quiet_block {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial))
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (quiet : colored stm.inst = false) :
    initial.entryColor[blockStart f bi+j]! = 0 ∧
      initial.sunk[blockStart f bi+j]! = false := by
  obtain ⟨original,st0,requests,oldBuild,_,finished⟩ := buildCtx_allocation build
  have spec := ctxSpec_of oldBuild
  let q := blockStart f bi+j
  have ownerRange : ranges[bi]? = some (blockStart f bi,blockStart f bi+b.body.length+1) := by
    simpa only [blockStart] using spec.ranges bi b block
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have zero : (sourceMetadata original ranges).entryColor[q]! = 0 := by
    apply sourceMetadata_zero_of_separate
    rw [spec.func]
    intro x member
    rcases x with ⟨other,k⟩
    have found : f.blocks[k]? = some other := List.mem_zipIdx_iff_getElem?.mp member
    have otherRange : ranges[k]? = some (blockStart f k,blockStart f k+other.body.length+1) := by
      simpa only [blockStart] using spec.ranges k other found
    have rangeBang : ranges[k]! = (blockStart f k,blockStart f k+other.body.length+1) := by
      simp only [getElem!_def,otherRange,Option.getD_some]
    constructor
    · intro y present coloredHere equal
      have atStmt : other.body[y.2]? = some y.1 := List.mem_zipIdx_iff_getElem?.mp present
      have bodyBound := (List.getElem?_eq_some_iff.mp atStmt).1
      by_cases indices : k = bi
      · subst k
        have same : other = b := Option.some.inj (found.symm.trans block)
        subst other
        have index : y.2 = j := Nat.add_left_cancel (by
          simpa only [rangeBang,Prod.fst,q] using equal)
        rw [index] at atStmt
        have sameStmt := Option.some.inj (atStmt.symm.trans statement)
        rw [sameStmt,quiet] at coloredHere
        cases coloredHere
      · have different := stock_buildCtx_other_block_slot build block found (Ne.symm indices)
          ownerRange otherRange (owner := q) (scanned := ranges[k]!.1+y.2)
          (by dsimp [q]; omega) (by dsimp [q]; omega)
          (by simp only [rangeBang,Prod.fst]; omega)
          (by simp only [rangeBang,Prod.fst]; omega)
        exact different equal
    · by_cases indices : k = bi
      · subst k
        have same : other = b := Option.some.inj (found.symm.trans block)
        subst other
        simp only [rangeBang,Prod.snd,q]
        omega
      · exact stock_buildCtx_other_block_slot build block found (Ne.symm indices)
          ownerRange otherRange (owner := q) (scanned := ranges[k]!.2-1)
          (by dsimp [q]; omega) (by dsimp [q]; omega)
          (by simp only [rangeBang,Prod.snd]; omega)
          (by simp only [rangeBang,Prod.snd]; omega)
  have state := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2) finished
  dsimp only at state
  rw [state]
  constructor
  · change (sourceMetadata original ranges).entryColor[q]! = 0
    exact zero
  · change (Array.replicate original.insts.size false)[q]! = false
    by_cases bound : q < original.insts.size <;>
      simp [getElem!_def,Array.getElem?_replicate,bound]


/-- Every actual scan retains a quiet original source slot across all original
and synthetic nodes, even when different blocks carry effects or traps. -/
theorem stock_lower_quiet_block_unsunk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (quiet : colored stm.inst = false) :
    result.initial.entryColor[blockStart f bi+j]! = 0 ∧
      result.final.sunk[blockStart f bi+j]! = false ∧
      ∀ event ∈ result.blockScans.toList,
        event.input.sunk[blockStart f bi+j]! = false ∧
        ∀ record ∈ event.output.records,
          record.input.sunk[blockStart f bi+j]! = false ∧
            record.output.state.sunk[blockStart f bi+j]! = false := by
  have built : ∃ ctx ranges,Stock.buildCtx f = .ok (ctx,ranges,result.initial) := by
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
  obtain ⟨zero,safe⟩ := buildCtx_quiet_block build block statement quiet
  obtain ⟨final,events⟩ := stock_lower_zeroColorLe run
  refine ⟨zero,final.2 _ zero safe,?_⟩
  intro event member
  obtain ⟨pre,records⟩ := events event member
  refine ⟨pre.2 _ zero safe,?_⟩
  intro record retained
  obtain ⟨a,b⟩ := records record retained
  exact ⟨a.2 _ zero safe,b.2 _ zero safe⟩

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

/-- Actual original block position derives omission/emission and result binding
without a single-block assumption or restrictions on neighboring effects. -/
theorem actual_quiet_source_record_at_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block}
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body)
    {record : ScanRecord} (member : record ∈ body.records)
    {j : Nat} {stm : Clif.Stmt} (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block+j)
    (quiet : colored stm.inst = false)
    (single : (stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig))
      (f.sigDecls.lookup ·)).map List.length = some 1) :
    PureBody.SourceRecord f event.ctx event.block record := by
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have ordinary : record.inst ≠ event.termInst := by
    rw [current,split.termIndex]
    omega
  have preserved := (stock_lower_quiet_block_unsunk run split.block statement quiet).2.2 event events
  have safe : record.input.sunk[record.inst]! = false := by
    rw [current]
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

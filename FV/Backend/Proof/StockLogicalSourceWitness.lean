import FV.Backend.Proof.StockLogicalRecordWitness
import FV.Backend.Proof.LowerValueRelations
import FV.Backend.Proof.StockLogicalCompleteValues
import FV.Backend.Proof.StockLogicalScanRefines
import FV.Backend.Proof.StockLogicalBodyRefines
import FV.Backend.Proof.StockLogicalSourceExecution

namespace Backend.Stock.Proof.LogicalSelected
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.LogicalSemantics
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem rrDominated : Dominated (formFunction .registers) := by
  constructor
  · decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [formFunction,formX,formY] at block
      subst b
      constructor
      · intro j stm statement y member
        cases j <;> simp at statement
        subst stm
        change y ∈ [7, 31] at member
        change y ∈ (([7, 31] ++ (availIn (formFunction .registers) ctx).getD 0 [] ++ []).filter (fun x => decide (x ∉ [100])))
        simp only [List.mem_filter, decide_eq_true_eq, List.append_nil]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp
      · intro y member
        change y ∈ [100] at member
        have equal := List.mem_singleton.mp member
        subst y
        change 100 ∈ (([7, 31] ++ (availIn (formFunction .registers) ctx).getD 0 [] ++ [100]).filter
          (fun x => decide (x ∉ ([] : List Nat))))
        simp
    | succ bi => simp [formFunction,formX,formY] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bounds := (inFix_fixOk (f := (formFunction .registers)) (ctx := ctx) (gn := id)).cand tl x available
    have length : (formFunction .registers).blocks.length = 1 := rfl
    omega
/-- The actual sparse-ID logical source has the original dominance property. -/
theorem logical_register_source_dominated : Dominated (formFunction .registers) := rrDominated

private theorem rrAvailable (ctx : Ctx) (y : Nat) :
    y ∈ availOf (formFunction .registers) (availIn (formFunction .registers) ctx) 0 0 ↔ y = 7 ∨ y = 31 := by
  have noEntry : y ∉ (availIn (formFunction .registers) ctx).getD 0 [] := by
    intro member
    have bound := (inFix_fixOk (f := (formFunction .registers)) (ctx := ctx) (gn := id)).cand 0 y member
    omega
  rw [mem_av (show (formFunction .registers).blocks[0]? = some
    ({id := 0, params := [(7, .i64), (31, .i64)], body := [⟨[100], .binary .bor .i64 7 31⟩], term := .ret [100]} : Clif.Block) from rfl)]
  constructor
  · intro available
    rcases available.1 with param | entry | ⟨k, stm, earlier, _, _⟩
    · simpa using param
    · exact False.elim (noEntry entry)
    · omega
  · intro equal
    rcases equal with rfl | rfl
    all_goals
      refine ⟨Or.inl (by simp), ?_⟩
      intro ⟨k, stm, _, statement, member⟩
      cases k <;> simp at statement
      subst stm
      simp at member

private def rrFrame : Clif.Frame := { formFrame .registers with
  body := [⟨[100],.binary .bor .i64 7 31⟩] }

private theorem rrRestricted (ctx : Ctx) :
    (restrict rrFrame (availOf (formFunction .registers)
      (availIn (formFunction .registers) ctx) 0 0)).regs = rrFrame.regs := by
  funext x
  by_cases seven : x = 7
  · subst x
    exact restrict_regs_of_mem ((rrAvailable ctx 7).mpr (Or.inl rfl))
  · by_cases thirtyone : x = 31
    · subst x
      exact restrict_regs_of_mem ((rrAvailable ctx 31).mpr (Or.inr rfl))
    · simp [restrict,rrFrame,formFrame,seven,thirtyone]

/-- A complete logical source step inhabits availability-restricted DFG and
actual record value transfer, preserving both parameter registers. -/
theorem stock_lower_logical_source_values_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (ρ' : Nat → CV) (fr' : Clif.Frame),
      Stock.lower (formFunction .registers) = .ok result ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) (formRegs .registers) ρ' ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (rrFrame,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf (formFunction .registers) (availIn (formFunction .registers) result.ctx) 0 1)
        event.ctx fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨input⟩ := stock_lower_logical_record_inputs_witness .registers
  have sourceX : rrFrame.getAs 7 .i64 = .ok (BitVec.ofNat 64 7) := rfl
  have sourceY : rrFrame.getAs 31 .i64 = .ok (BitVec.ofNat 64 5) := rfl
  have restrictedX := getAs_congr (fr := rrFrame) (x := 7) (ty := .i64)
    (congrFun (rrRestricted input.result.ctx) 7)
  have restrictedY := getAs_congr (fr := rrFrame) (x := 31) (ty := .i64)
    (congrFun (rrRestricted input.result.ctx) 31)
  have restrictedDFG := dfgCons_congr (ctx := input.event.ctx) (fr := formFrame .registers)
    (fr' := restrict rrFrame (availOf (formFunction .registers)
      (availIn (formFunction .registers) input.result.ctx) 0 0)) rfl rfl (rrRestricted input.result.ctx) input.dfg
  have guarded := input.held.mono (fun y (h : Demanded input.record.output.state y ∧ y ∈
    availOf (formFunction .registers) (availIn (formFunction .registers) input.result.ctx) 0 0) => h.1)
  have block : (formFunction .registers).blocks[0]? = some ((formFunction .registers).blocks[0]!) := rfl
  have statement : ((formFunction .registers).blocks[0]!).body[0]? =
      some (⟨[100],.binary .bor .i64 7 31⟩ : Clif.Stmt) := rfl
  have current : input.record.inst = blockStart (formFunction .registers) 0 + 0 := by
    have zero := input.current
    change input.record.inst = 0 at zero
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using zero
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨ρ',execution,value,kept,installed⟩ := stock_lower_logical_available_values input.run
    (formScope .registers) rrDominated input.events input.records block statement current .bor
    input.source input.clif input.results rfl input.mapped input.recorded input.emitted input.selectedId self
    restrictedDFG guarded (restrictedX.trans sourceX) (restrictedY.trans sourceY)
  let val : Clif.Val := ⟨Clif.Ty.i64,Clif.Sem.binary .bor (BitVec.ofNat 64 7) (BitVec.ofNat 64 5)⟩
  let fr' : Clif.Frame := { rrFrame with regs := rrFrame.regs.set 100 val, body := [] }
  have evaluated : instOutcome Clif.Env.empty {funcs := []} rrFrame Clif.Mem.empty
      (.binary .bor .i64 7 31) = .ok ([val],Clif.Mem.empty) := rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (rrFrame,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,.binary .bor .i64 7 31,[val],rrFrame.regs.set 100 val,[],
      input.source,input.clif,by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  have sourceHeld := source_single_result_values input.source input.clif input.results sourceStep evaluated installed
  exact ⟨input.result,input.event,input.record,ρ',fr',input.run,input.events,input.records,execution,sourceStep,sourceHeld⟩

/-- An actual source step inhabits the complete eleven-root transfer theorem
without supplying a chosen-rule premise. The old explicit-root witness remains. -/
theorem stock_lower_logical_complete_source_values_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (ρ' : Nat → CV) (fr' : Clif.Frame),
      Stock.lower (formFunction .registers) = .ok result ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) (formRegs .registers) ρ' ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (rrFrame,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf (formFunction .registers) (availIn (formFunction .registers) result.ctx) 0 1)
        event.ctx fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨input⟩ := stock_lower_logical_record_inputs_witness .registers
  have sourceX : rrFrame.getAs 7 .i64 = .ok (BitVec.ofNat 64 7) := rfl
  have sourceY : rrFrame.getAs 31 .i64 = .ok (BitVec.ofNat 64 5) := rfl
  have restrictedX := getAs_congr (fr := rrFrame) (x := 7) (ty := .i64)
    (congrFun (rrRestricted input.result.ctx) 7)
  have restrictedY := getAs_congr (fr := rrFrame) (x := 31) (ty := .i64)
    (congrFun (rrRestricted input.result.ctx) 31)
  have restrictedDFG := dfgCons_congr (ctx := input.event.ctx) (fr := formFrame .registers)
    (fr' := restrict rrFrame (availOf (formFunction .registers)
      (availIn (formFunction .registers) input.result.ctx) 0 0)) rfl rfl (rrRestricted input.result.ctx) input.dfg
  have guarded := input.held.mono (fun y (h : Demanded input.record.output.state y ∧ y ∈
    availOf (formFunction .registers) (availIn (formFunction .registers) input.result.ctx) 0 0) => h.1)
  have block : (formFunction .registers).blocks[0]? = some ((formFunction .registers).blocks[0]!) := rfl
  have statement : ((formFunction .registers).blocks[0]!).body[0]? =
      some (⟨[100],.binary .bor .i64 7 31⟩ : Clif.Stmt) := rfl
  have current : input.record.inst = blockStart (formFunction .registers) 0 + 0 := by
    have zero := input.current
    change input.record.inst = 0 at zero
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using zero
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  let val : Clif.Val := ⟨Clif.Ty.i64,Clif.Sem.binary .bor (BitVec.ofNat 64 7) (BitVec.ofNat 64 5)⟩
  let fr' : Clif.Frame := { rrFrame with regs := rrFrame.regs.set 100 val, body := [] }
  have evaluated : instOutcome Clif.Env.empty {funcs := []} rrFrame Clif.Mem.empty
      (.binary .bor .i64 7 31) = .ok ([val],Clif.Mem.empty) := rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (rrFrame,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,.binary .bor .i64 7 31,[val],rrFrame.regs.set 100 val,[],
      input.source,input.clif,by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  obtain ⟨u,v,ρ',getX,getY,execution,value,memory,kept,sourceHeld⟩ :=
    LogicalComplete.record_source_from_step input.run (formScope .registers) rrDominated
      input.events input.records block statement current .bor input.source input.clif input.results rfl
      input.mapped input.recorded input.emitted self restrictedDFG guarded sourceStep
  exact ⟨input.result,input.event,input.record,ρ',fr',input.run,input.events,input.records,execution,sourceStep,sourceHeld⟩

private theorem rr_scans_execute {exec : Nat → State → Except String Scan}
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

private theorem rr_record_exec (input : LogicalRecordInputs .registers) :
    scanInstruction input.event.ctx input.event.block input.record.inst input.event.termInst
      input.event.isBranch input.record.input = .ok input.record.output := by
  have member := input.records
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,
    label,bi,data,core,build,ordered,initial,empty,parts,folded,
    final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin input.run input.events
  rw [eventEq] at member ⊢
  have actual := (stock_lowerBlockCore_scanOrigin coreRun).2.2.2.2.2
  unfold scanBlock at actual
  exact rr_scans_execute (runScans_spec actual) input.record member

/-- A nonempty body from an actual whole-driver run inhabits both complete
logical scan refinement and body composition, with a real source step and the
original guarded relation for every initial machine world. -/
theorem stock_lower_logical_scan_body_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (body : BlockScan)
      (s t : SourcePoint),
      Stock.lower (formFunction .registers) = .ok result ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      body.records = [record] ∧
      ScansSpec (fun i => scanInstruction event.ctx event.block i event.termInst event.isBranch)
        [record.inst] record.input body ∧
      (∀ r ∈ body.records, MixedLogicalOrOmittedRecord (formFunction .registers) event.ctx 0 r) ∧
      SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} (formFunction .registers) event.ctx 0)
        [record.inst] s t ∧
      ScanFallRefines (IndexedSourceInst Clif.Env.empty {funcs := []} (formFunction .registers) event.ctx 0)
        ispec result.final.alias
        (GuardedScanRel (formFunction .registers) result event.ctx 0 (fun _ cm _ => cm = Clif.Mem.empty)) record ∧
      ∀ w, GuardedScanRel (formFunction .registers) result event.ctx 0 (fun _ cm _ => cm = Clif.Mem.empty)
        body.state s (formRegs .registers) w ∧
        ∃ ρ' w', seqRun ispec (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (formRegs .registers) w =
            some (.fall ρ' w') ∧
          GuardedScanRel (formFunction .registers) result event.ctx 0 (fun _ cm _ => cm = Clif.Mem.empty)
            record.input t ρ' w' := by
  obtain ⟨input⟩ := stock_lower_logical_record_inputs_witness .registers
  have restrictedDFG := dfgCons_congr (ctx := input.event.ctx) (fr := formFrame .registers)
    (fr' := restrict rrFrame (availOf (formFunction .registers)
      (availIn (formFunction .registers) input.result.ctx) 0 0)) rfl rfl (rrRestricted input.result.ctx) input.dfg
  have guarded := input.held.mono (fun y (h : Demanded input.record.output.state y ∧ y ∈
    availOf (formFunction .registers) (availIn (formFunction .registers) input.result.ctx) 0 0) => h.1)
  have block : (formFunction .registers).blocks[0]? = some ((formFunction .registers).blocks[0]!) := rfl
  have statement : ((formFunction .registers).blocks[0]!).body[0]? =
      some (⟨[100],.binary .bor .i64 7 31⟩ : Clif.Stmt) := rfl
  have current : input.record.inst = blockStart (formFunction .registers) 0 + 0 := by
    have zero := input.current
    change input.record.inst = 0 at zero
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using zero
  let val : Clif.Val := ⟨Clif.Ty.i64,Clif.Sem.binary .bor (BitVec.ofNat 64 7) (BitVec.ofNat 64 5)⟩
  let fr' : Clif.Frame := {rrFrame with regs := rrFrame.regs.set 100 val,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} rrFrame Clif.Mem.empty
      (.binary .bor .i64 7 31) = .ok ([val],Clif.Mem.empty) := rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (rrFrame,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,.binary .bor .i64 7 31,[val],rrFrame.regs.set 100 val,[],
      input.source,input.clif,by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  let s : SourcePoint := (0,rrFrame,Clif.Mem.empty)
  let t : SourcePoint := (1,fr',Clif.Mem.empty)
  have indexed : IndexedSourceInst Clif.Env.empty {funcs := []} (formFunction .registers)
      input.event.ctx 0 input.record.inst s t := ⟨current,rfl,sourceStep⟩
  have steps : SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} (formFunction .registers)
      input.event.ctx 0) [input.record.inst] s t := .cons indexed (.nil t)
  let body : BlockScan := ⟨input.record.output.state,[input.record],input.record.output.emitted⟩
  have rebuild : (⟨input.record.inst,input.record.input,input.record.output⟩ : ScanRecord) = input.record := by
    cases input.record; rfl
  have scanned : ScansSpec (fun i => scanInstruction input.event.ctx input.event.block i input.event.termInst
      input.event.isBranch) [input.record.inst] input.record.input body := by
    simpa only [body,Array.empty_append,rebuild] using
      (ScansSpec.cons (exec := fun i => scanInstruction input.event.ctx input.event.block i input.event.termInst
        input.event.isBranch) (rr_record_exec input) (ScansSpec.nil input.record.output.state))
  have family : MixedLogicalOrOmittedRecord (formFunction .registers) input.event.ctx 0 input.record :=
    Or.inr ⟨0,(formFunction .registers).blocks[0]!,⟨[100],.binary .bor .i64 7 31⟩,
      block,statement,current,input.step,input.recorded,input.emitted,.bor,input.info,.i64,7,31,100,_,
      input.source,input.clif,input.results,rfl,input.mapped⟩
  have families : ∀ r ∈ body.records, MixedLogicalOrOmittedRecord (formFunction .registers) input.event.ctx 0 r := by
    intro r member
    have eq := List.mem_singleton.mp member
    subst r
    exact family
  have retained : ∀ r ∈ body.records, r ∈ input.event.output.records := by
    intro r member
    have eq := List.mem_singleton.mp member
    subst r
    exact input.records
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have stable : MRStable (fun _ => True) (fun _ cm _ => cm = Clif.Mem.empty) := fun _ _ _ _ _ h => h
  have localProof := stock_lower_logical_scan_fall_refines (env := Clif.Env.empty) (cp := {funcs := []}) input.run (formScope .registers) rrDominated
    input.events input.records block statement current .bor input.source input.clif input.results rfl
    input.mapped input.recorded input.emitted self stable
  refine ⟨input.result,input.event,input.record,body,s,t,input.run,input.events,input.records,rfl,
    scanned,families,steps,localProof,?_⟩
  intro w
  have pre : GuardedScanRel (formFunction .registers) input.result input.event.ctx 0
      (fun _ cm _ => cm = Clif.Mem.empty) body.state s (formRegs .registers) w :=
    ⟨rfl,restrictedDFG,rfl,guarded⟩
  exact ⟨pre,stock_lower_mixed_logical_body_fall_refines input.run (formScope .registers) rrDominated
    input.events scanned retained families self stable s t steps (formRegs .registers) w pre⟩

private theorem rr_scan_length {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) : output.records.length = indices.length := by
  induction cert with
  | nil input => rfl
  | cons head rest ih => simpa only [List.length_cons] using congrArg Nat.succ ih

/-- The syntax-derived body theorem is inhabited by an actual nonempty whole
Stock scan and source execution, with its guarded relation for every world. -/
theorem stock_lower_actual_logical_body_witness :
    ∃ (result : Result) (event : BlockScanEvent) (b : Clif.Block) (term : ScanRecord)
      (body : BlockScan) (s t : SourcePoint),
      Stock.lower (formFunction .registers) = .ok result ∧
      event ∈ result.blockScans.toList ∧ (formFunction .registers).blocks = [b] ∧
      (∀ stm ∈ b.body, LogicalBody.Family stm.inst) ∧
      SourceBodySplit (formFunction .registers) event b term body ∧ body.records ≠ [] ∧
      SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} (formFunction .registers) event.ctx event.block)
        ((List.range b.body.length).map (blockStart (formFunction .registers) event.block + ·)) s t ∧
      ∀ w, GuardedScanRel (formFunction .registers) result event.ctx event.block
        (fun _ cm _ => cm = Clif.Mem.empty) event.output.state s (formRegs .registers) w ∧
        ∃ ρ' w', seqRun ispec (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (formRegs .registers) w =
            some (.fall ρ' w') ∧
          GuardedScanRel (formFunction .registers) result event.ctx event.block
            (fun _ cm _ => cm = Clif.Mem.empty) term.output.state t ρ' w' := by
  obtain ⟨input⟩ := stock_lower_logical_record_inputs_witness .registers
  let b := (formFunction .registers).blocks[0]!
  have blocks : (formFunction .registers).blocks = [b] := rfl
  have bodyLength : b.body.length = 1 := rfl
  have family : ∀ stm ∈ b.body, LogicalBody.Family stm.inst := by
    intro stm member
    change stm ∈ [⟨[100],.binary .bor .i64 7 31⟩] at member
    have eq := List.mem_singleton.mp member
    subst stm
    exact Or.inr (Or.inr ⟨.bor,.i64,7,31,rfl⟩)
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have stable : MRStable (fun _ => True) (fun _ cm _ => cm = Clif.Mem.empty) := fun _ _ _ _ _ h => h
  obtain ⟨term,body,split,transfer⟩ := LogicalBody.actual_logical_body_refines input.run
    (formScope .registers) rrDominated blocks family input.events self stable
    (env := Clif.Env.empty) (cp := {funcs := []})
  have eventZero : input.event.block = 0 := by
    have bound := (List.getElem?_eq_some_iff.mp split.block).1
    rw [blocks] at bound
    simp only [List.length_singleton] at bound
    omega
  have current : input.record.inst = 0 := input.current
  have termInst : term.inst = 1 := by
    have h := split.termInst.trans split.termIndex
    rw [eventZero,bodyLength] at h
    exact h
  have member : input.record ∈ body.records := by
    have retained := input.records
    rw [split.records] at retained
    rcases List.mem_cons.mp retained with eq | member
    · have same := congrArg (fun r : ScanRecord => r.inst) eq
      rw [current,termInst] at same
      omega
    · exact member
  have count : body.records.length = 1 := by
    simpa only [sourceBodyIndices,List.length_reverse,List.length_map,List.length_range,bodyLength]
      using rr_scan_length split.scanned
  have singleton : body.records = [input.record] := by
    cases recs : body.records with
    | nil => simp [recs] at member
    | cons r rest =>
      have zero : rest.length = 0 := by rw [recs] at count; simp only [List.length_cons] at count; omega
      have empty := List.length_eq_zero_iff.mp zero
      rw [empty] at recs
      have eq : input.record = r := List.mem_singleton.mp (by simpa only [recs] using member)
      simp [empty,← eq]
  have chain := split.scanned.chain
  rw [singleton] at chain
  have state : body.state = input.record.output.state := chain.2
  have eventState : input.event.output.state = input.record.output.state := split.state.symm.trans state
  have nonempty : body.records ≠ [] := by rw [singleton]; simp
  have restrictedDFG := dfgCons_congr (ctx := input.event.ctx) (fr := formFrame .registers)
    (fr' := restrict rrFrame (availOf (formFunction .registers)
      (availIn (formFunction .registers) input.result.ctx) 0 0)) rfl rfl (rrRestricted input.result.ctx) input.dfg
  have guarded := input.held.mono (fun y (h : Demanded input.record.output.state y ∧ y ∈
    availOf (formFunction .registers) (availIn (formFunction .registers) input.result.ctx) 0 0) => h.1)
  let val : Clif.Val := ⟨Clif.Ty.i64,Clif.Sem.binary .bor (BitVec.ofNat 64 7) (BitVec.ofNat 64 5)⟩
  let fr' : Clif.Frame := {rrFrame with regs := rrFrame.regs.set 100 val,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} rrFrame Clif.Mem.empty
      (.binary .bor .i64 7 31) = .ok ([val],Clif.Mem.empty) := rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx 0
      (rrFrame,Clif.Mem.empty) (fr',Clif.Mem.empty) := by
    rw [← current]
    exact ⟨input.info,.binary .bor .i64 7 31,[val],rrFrame.regs.set 100 val,[],
      input.source,input.clif,by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  let s : SourcePoint := (0,rrFrame,Clif.Mem.empty)
  let t : SourcePoint := (1,fr',Clif.Mem.empty)
  have indexed : IndexedSourceInst Clif.Env.empty {funcs := []} (formFunction .registers)
      input.event.ctx input.event.block 0 s t := by
    refine ⟨?_,rfl,sourceStep⟩
    rw [eventZero]
    rfl
  have steps : SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} (formFunction .registers)
      input.event.ctx input.event.block)
      ((List.range b.body.length).map (blockStart (formFunction .registers) input.event.block + ·)) s t := by
    have indices : ((List.range b.body.length).map (blockStart (formFunction .registers) input.event.block + ·)) = [0] := by
      rw [eventZero,bodyLength]
      rfl
    rw [indices]
    exact .cons indexed (.nil t)
  refine ⟨input.result,input.event,b,term,body,s,t,input.run,input.events,blocks,family,split,nonempty,steps,?_⟩
  intro w
  have pre : GuardedScanRel (formFunction .registers) input.result input.event.ctx input.event.block
      (fun _ cm _ => cm = Clif.Mem.empty) input.event.output.state s (formRegs .registers) w := by
    rw [eventZero,eventState]
    exact ⟨rfl,restrictedDFG,rfl,guarded⟩
  exact ⟨pre,transfer s t steps (formRegs .registers) w pre⟩

/-- A real returned CLIF run inhabits the complete source-execution bridge;
its nonempty body, residual fuel and exact terminator state are derived. -/
theorem stock_lower_logical_source_execution_witness :
    ∃ (result : Result) (event : BlockScanEvent) (b : Clif.Block) (term : ScanRecord)
      (body : BlockScan) (s : Clif.State) (vals : List Clif.Val) (cm : Clif.Mem),
      Stock.lower (formFunction .registers) = .ok result ∧
      event ∈ result.blockScans.toList ∧ SourceBodySplit (formFunction .registers) event b term body ∧
      b.body.length = 1 ∧ (∀ stm ∈ b.body, LogicalBody.Family stm.inst) ∧ s.frame.body = b.body ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 2 s = .returned vals cm ∧
      ∃ t left, left + b.body.length = 2 ∧
        Clif.runLoop Clif.Env.empty {funcs := []} left t = .returned vals cm ∧ t.frame.body = [] ∧
        SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} (formFunction .registers) event.ctx event.block)
          (List.range' (blockStart (formFunction .registers) event.block) b.body.length)
          (0,s.frame,s.mem) (b.body.length,t.frame,t.mem) ∧ LogicalBody.SourceFrameEq s t := by
  obtain ⟨input⟩ := stock_lower_logical_record_inputs_witness .registers
  let b := (formFunction .registers).blocks[0]!
  have blocks : (formFunction .registers).blocks = [b] := rfl
  have family : ∀ stm ∈ b.body, LogicalBody.Family stm.inst := by
    intro stm member
    change stm ∈ [⟨[100],.binary .bor .i64 7 31⟩] at member
    have eq := List.mem_singleton.mp member
    subst stm
    exact Or.inr (Or.inr ⟨.bor,.i64,7,31,rfl⟩)
  obtain ⟨term,body,split,families⟩ := LogicalBody.actual_logical_families input.run
    (formScope .registers) blocks family input.events
  let s : Clif.State := ⟨rrFrame,[],Clif.Mem.empty⟩
  let vals : List Clif.Val := [⟨.i64,7⟩]
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 2 s = .returned vals Clif.Mem.empty := by
    rfl
  obtain ⟨t,left,total,ends,empty,steps,frame⟩ := LogicalBody.actual_logical_source_execution_frame
    input.run input.events split family (j := 0) (by simp) (by rfl) returned
  refine ⟨input.result,input.event,b,term,body,s,vals,Clif.Mem.empty,input.run,input.events,
    split,rfl,family,rfl,returned,t,left,?_,ends,empty,?_,frame⟩
  · simpa only [Nat.sub_zero] using total
  · simpa only [Nat.add_zero,Nat.sub_zero] using steps

end Backend.Stock.Proof.LogicalSelected

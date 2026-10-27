import FV.Backend.Proof.StockInheritedDivision

namespace Backend.Stock.Proof.Inherited
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private theorem records_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {body : BlockScan}
    (scanned : ScansSpec exec indices input body) :
    ∀ record ∈ body.records,exec record.inst record.input = .ok record.output := by
  induction scanned with
  | nil => simp
  | cons head tail ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

private theorem lift_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {record : ScanRecord}
    (records : record ∈ event.output.records) {j : Nat} {stm : Clif.Stmt}
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f event.block+j)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (normal : ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (GuardedScanRel f result event.ctx event.block MR) record)
    (defs : ∀ m ∈ record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))),
      ∀ key ∈ vdefs m,record.input.base.nextVreg ≤ key ∧ key < record.output.state.base.nextVreg) :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  intro s s' source ρ w held
  obtain ⟨ρ',w',executed,post⟩ := normal s s' source ρ w held.1
  exact ⟨ρ',w',executed,post,record_fresh_carry run scope dominated events split records statement current
    source.2.2 available defs executed held.2⟩

/-- Block-local carry composition allows other blocks to contain the broader
scalar source family. The global source format condition is supplied by that
family's existing soundness lemma; no emitted-code or machine-value certificate
is added. Both normal continuation and the first local trap are preserved. -/
theorem constant_division_body_carry_refines_local {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    (formats : ∀ block ∈ f.blocks,∀ stm ∈ block.body,CastComplete.MemoryFormat stm.inst)
    (family : ∀ stm ∈ b.body,
      (∃ ty imm,stm.inst = .iconst ty imm) ∨ (∃ op ty x y,stm.inst = .div op ty x y) ∨ stm.inst = .nop)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    (∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
      (sourceBodyIndices f event.block b).reverse s s' → ∀ ρ w,
      CarryRel f result event.ctx event.block MR needed body.state s ρ w → ∃ ρ' w',
        seqRun isem (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.fall ρ' w') ∧ CarryRel f result event.ctx event.block MR needed term.output.state s' ρ' w') ∧
    (∀ s code,SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
      (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
      (sourceBodyIndices f event.block b).reverse s code → ∀ ρ w,
      CarryRel f result event.ctx event.block MR needed body.state s ρ w →
        TrapRun isem (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w code) := by
  have locals : ∀ record ∈ body.records,
      ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
        (CarryRel f result event.ctx event.block MR needed) record ∧
      LocalScanTrapRefines (LocalBody.IndexedSourceTrap env cp f event.ctx event.block) isem result.final.alias
        (CarryRel f result event.ctx event.block MR needed) record := by
    intro record member
    obtain ⟨j,stm,statement,current⟩ := split.positions record member
    have retained := split.retained record member
    obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split statement current
    have omittedCase : ∀ step,record.output.step = some step → step.decision = .omitted →
        ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
          (CarryRel f result event.ctx event.block MR needed) record := by
      intro step recorded omitted
      apply lift_record run scope dominated events split retained statement current available
        (stock_lower_omitted_scan_fall_refines run scope dominated events retained split.block statement current recorded omitted)
      obtain ⟨_,_,_,_,_,_,_,empty,_⟩ := scan_omitted (records_execute split.scanned record member) recorded omitted
      simp only [empty,Array.toList_empty,List.map_nil,List.not_mem_nil,false_implies,implies_true]
    have quietTrap : ((∃ ty imm,stm.inst = .iconst ty imm) ∨ stm.inst = .nop) →
        LocalScanTrapRefines (LocalBody.IndexedSourceTrap env cp f event.ctx event.block) isem result.final.alias
          (CarryRel f result event.ctx event.block MR needed) record := by
      intro quiet s code failed ρ w held
      obtain ⟨indexed,info',inst,rest,found,original,remaining,trapped⟩ := failed
      cases Option.some.inj (found.symm.trans source)
      have sameInst := Option.some.inj (original.symm.trans clif)
      subst inst
      rcases quiet with ⟨ty,imm,shape⟩ | shape
      · rw [shape,LocalBody.local_outcome (show LocalBody.LocalInst (.iconst ty imm) from rfl)] at trapped
        cases trapped
      · rw [shape,LocalBody.local_outcome (show LocalBody.LocalInst .nop from True.intro)] at trapped
        cases trapped
    rcases family stm (List.mem_of_getElem? statement) with
      ⟨ty,imm,constant⟩ | ⟨op,ty,x,y,division⟩ | nop
    · refine ⟨?_,quietTrap (Or.inl ⟨ty,imm,constant⟩)⟩
      have actual := QuietSourceColors.actual_quiet_source_record_at_block run scope events split member statement current
        (by rw [constant]; rfl) (by rw [constant]; rfl)
      obtain ⟨j',b',stm',found,atStmt,indexed,step,recorded,decision⟩ := actual
      cases Option.some.inj (found.symm.trans split.block)
      have sameJ := Nat.add_left_cancel (indexed.symm.trans current)
      subst j'
      cases Option.some.inj (atStmt.symm.trans statement)
      rcases decision with omitted | ⟨emitted,info',z,a,source',clif',one,statementResults,mapped⟩
      · exact omittedCase step recorded omitted
      · apply lift_record run scope dominated events split retained statement current available
          (stock_lower_constant_scan_fall_refines run scope dominated events retained split.block statement current
            source' (clif'.trans (congrArg some constant)) one statementResults mapped recorded emitted refines driver stable)
        exact constant_record_fresh_defs run scope events retained source' (clif'.trans (congrArg some constant))
          one mapped recorded emitted
    · have actual := DivBody.actual_division_record run scope formats events split member statement current division
      cases actual with
      | scalar block' statement' current' source' clif' scalar actual =>
        cases Option.some.inj (source'.symm.trans source)
        have shape := Option.some.inj (clif'.symm.trans (clif.trans (congrArg some division)))
        have pure := HighMulBody.family_pure scalar
        rw [shape] at pure
        cases pure
      | division block' statement' current' source' clif' one statementResults mapped recorded emitted =>
        have sameB := Option.some.inj (block'.symm.trans split.block)
        subst sameB
        refine ⟨division_scan_carry_fall_refines run scope dominated events retained split statement' current'
          _ source' clif' one statementResults mapped recorded emitted available refines stable,?_
          ⟩
        exact division_scan_carry_trap_refines run scope dominated events retained split statement' current'
          source' clif' one statementResults mapped recorded emitted refines
    · obtain ⟨step,recorded,omitted⟩ := MaskBody.actual_nop_record_at_block run scope events split member statement current nop
      exact ⟨omittedCase step recorded omitted,quietTrap (Or.inr nop)⟩
  exact ⟨split.scanned.fall_refines (fun r member => (locals r member).1),
    split.scanned.local_trap_refines (fun r member => (locals r member).1) (fun r member => (locals r member).2)⟩

/-- Existing arbitrary-position divisions and constant/nop records compose
under carry, including the first actual source trap. All classifications and
write frames are derived internally from the actual compiler execution. -/
theorem constant_division_body_carry_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,
      (∃ ty imm,stm.inst = .iconst ty imm) ∨ (∃ op ty x y,stm.inst = .div op ty x y) ∨ stm.inst = .nop)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    (∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
      (sourceBodyIndices f event.block b).reverse s s' → ∀ ρ w,
      CarryRel f result event.ctx event.block MR needed body.state s ρ w → ∃ ρ' w',
        seqRun isem (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.fall ρ' w') ∧ CarryRel f result event.ctx event.block MR needed term.output.state s' ρ' w') ∧
    (∀ s code,SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
      (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
      (sourceBodyIndices f event.block b).reverse s code → ∀ ρ w,
      CarryRel f result event.ctx event.block MR needed body.state s ρ w →
        TrapRun isem (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w code) := by
  have formats : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastComplete.MemoryFormat stm.inst := by
    intro block member stm present
    rcases family block member stm present with ⟨ty,imm,shape⟩ | ⟨op,ty,x,y,shape⟩ | shape
    all_goals simp [CastComplete.MemoryFormat,shape,instNames]
  exact constant_division_body_carry_refines_local run scope dominated events split formats
    (family b (List.mem_of_getElem? split.block)) available refines driver stable

end Backend.Stock.Proof.Inherited


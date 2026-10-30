import FV.Backend.Proof.StockMaskBlockRecords
import FV.Backend.Proof.StockInheritedValues
import FV.Backend.Proof.StockConstantFreshDefs

namespace Backend.Stock.Proof.Inherited
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The ordinary scan guard together with entry values required by subsequent
blocks. The carried set is independent of this scan's demand state. -/
def CarryRel (f : Clif.Function) (result : Result) (ctx : Ctx) (bi : Nat)
    (MR : MemRelT) (needed : Nat → Prop) (st : State) (s : SourcePoint)
    (ρ : Nat → CV) (w : Arm.ArmState) : Prop :=
  GuardedScanRel f result ctx bi MR st s ρ w ∧
    ValuesHeld needed ctx s.2.1 (fun k => ρ (aliasNum result.final.alias k))

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

/-- Actual omitted and constant/nop records carry entry values through a whole
original body. Every write bound is derived from actual omission or rule
selection/binding; no semantic callback or new accepted-program certificate is
assumed. Other blocks and source continuations remain unrestricted. -/
theorem constant_body_carry_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    (family : ∀ stm ∈ b.body,(∃ ty imm,stm.inst = .iconst ty imm) ∨ stm.inst = .nop)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
      (sourceBodyIndices f event.block b).reverse s s' → ∀ ρ w,
      CarryRel f result event.ctx event.block MR needed body.state s ρ w → ∃ ρ' w',
        seqRun isem (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.fall ρ' w') ∧ CarryRel f result event.ctx event.block MR needed term.output.state s' ρ' w' := by
  apply split.scanned.fall_refines
  intro record member
  obtain ⟨j,stm,statement,current⟩ := split.positions record member
  have retained := split.retained record member
  have omittedCase : ∀ step,record.output.step = some step → step.decision = .omitted →
      ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
        (CarryRel f result event.ctx event.block MR needed) record := by
    intro step recorded omitted
    apply lift_record run scope dominated events split retained statement current available
      (stock_lower_omitted_scan_fall_refines run scope dominated events retained split.block statement current recorded omitted)
    obtain ⟨_,_,_,_,_,_,_,empty,_⟩ := scan_omitted (records_execute split.scanned record member) recorded omitted
    simp only [empty,Array.toList_empty,List.map_nil,List.not_mem_nil,false_implies,implies_true]
  rcases family stm (List.mem_of_getElem? statement) with ⟨ty,imm,constant⟩ | nop
  · have actual := QuietSourceColors.actual_quiet_source_record_at_block run scope events split member statement current
      (by rw [constant]; rfl) (by rw [constant]; rfl)
    obtain ⟨j',b',stm',found,atStmt,indexed,step,recorded,decision⟩ := actual
    have sameB := Option.some.inj (found.symm.trans split.block)
    subst b'
    have sameJ := Nat.add_left_cancel (indexed.symm.trans current)
    subst j'
    have sameStmt := Option.some.inj (atStmt.symm.trans statement)
    subst stm'
    rcases decision with omitted | ⟨emitted,info,x,a,source,clif,one,results,mapped⟩
    · exact omittedCase step recorded omitted
    · apply lift_record run scope dominated events split retained statement current available
        (stock_lower_constant_scan_fall_refines run scope dominated events retained split.block statement current
          source (clif.trans (congrArg some constant)) one results mapped recorded emitted refines driver stable)
      exact constant_record_fresh_defs run scope events retained source (clif.trans (congrArg some constant))
        one mapped recorded emitted
  · obtain ⟨step,recorded,omitted⟩ := MaskBody.actual_nop_record_at_block run scope events split member statement current nop
    exact omittedCase step recorded omitted

end Backend.Stock.Proof.Inherited

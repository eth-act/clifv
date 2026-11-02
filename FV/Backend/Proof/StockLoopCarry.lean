import FV.Backend.Proof.StockLoopBounded
import FV.Backend.Proof.StockInheritedJumpDefined
import FV.Backend.Proof.StockInheritedJumpTrap
import FV.Backend.Proof.StockConditionalSourceTrap

/-! Back-edge carry for loop CFGs (#140, T7b-3).

At a block's entry the compositions need the successor's `GuardedScanRel`, which holds the
values that the successor's scan demands. On a forward edge the predecessor's terminator scan
demands every such value (`ordered_scan_demand_of_labels`). On a back edge `P → H` it does not:
Stock scans the blocks backward in reverse RPO, so the header's scan, and its demand for the
values defined before the loop, comes after the latch's scan.

The register of such a value is not written inside the loop. A record defines only the fresh
virtual registers of its own allocation interval, and the resolved register of every value
available at the record lies outside that interval (`stock_lower_available_alias_outside_record`);
the parameter `brif` and the `jump` define no registers; the edge copies into a block write only
the resolved registers of its parameters, which differ from the resolved register of every
inherited value (`stock_lower_entry_alias_apart`). None of these facts depends on the scan order.

So the loop blocks carry a demand-independent set with `CarryRel`. `EdgeCover` states what one
edge needs: each value the successor needs at entry (demanded there or carried), that is not a
successor parameter, is demanded or carried at the predecessor's end. The demand order gives it
on a forward edge (`EdgeCover.of_demand`); the header carry gives it on a back edge
(`EdgeCover.of_header`, `headerCarry`). The edge steps `*_successor_carry` replace the demand
premise of the forward edge steps by `EdgeCover`; `*_guarded_of_carry` are the back-edge cases. -/

namespace Backend.Stock.Proof.LoopCarry
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- The values that a successor at block `target` needs at entry and does not receive as block
arguments (`params` are its parameters): demanded by its scan or in its carry set `carried`.
The predecessor holds each at its end: demanded by its terminator scan `term`, or in its carry
set `carry`. -/
def EdgeCover (f : Clif.Function) (result : Result) (target : Nat) (params : List Nat)
    (next : State) (carried : Nat → Prop) (term : State) (carry : Nat → Prop) : Prop :=
  ∀ x,x ∈ availOf f (availIn f result.ctx) target 0 → x ∉ params →
    Demanded next x ∨ carried x → Demanded term x ∨ carry x

/-- A forward edge: the successor demand is below the predecessor demand, and the successor
carries only carried values. -/
theorem EdgeCover.of_demand {f : Clif.Function} {result : Result} {target : Nat} {params : List Nat}
    {next term : State} {carried carry : Nat → Prop}
    (demand : ∀ (x : Nat),next.demand[x]! ≤ term.demand[x]!) (inherit : ∀ x,carried x → carry x) :
    EdgeCover f result target params next carried term carry := by
  intro x _ _ needed
  rcases needed with demanded | kept
  · left
    unfold Demanded at demanded ⊢
    have le := demand x
    omega
  · exact Or.inr (inherit x kept)

/-- A back edge into a header: the carry set contains every inherited value that the header
scan demands, and the header carries the same set. -/
theorem EdgeCover.of_header {f : Clif.Function} {result : Result} {target : Nat} {params : List Nat}
    {next term : State} {carry : Nat → Prop}
    (header : ∀ x,Demanded next x → x ∈ availOf f (availIn f result.ctx) target 0 → x ∉ params → carry x) :
    EdgeCover f result target params next carry term carry := by
  intro x available notParameter needed
  rcases needed with demanded | kept
  · exact Or.inr (header x demanded available notParameter)
  · exact Or.inr kept

/-- The header carry: the values that the header scan demands at entry and that are available
there and not header parameters. In a loop CFG these are defined before the loop. -/
def headerCarry (f : Clif.Function) (result : Result) (header : BlockScanEvent) (x : Nat) : Prop :=
  Demanded header.output.state x ∧ x ∈ availOf f (availIn f result.ctx) header.block 0 ∧
    x ∉ ((f.blocks[header.block]?).getD default).params.map (·.1)

theorem headerCarry_available {f : Clif.Function} {result : Result} {header : BlockScanEvent} :
    ∀ x,headerCarry f result header x → x ∈ availOf f (availIn f result.ctx) header.block 0 :=
  fun _ carried => carried.2.1

/-- The header carry covers every back edge into the header. -/
theorem headerCarry_covers {f : Clif.Function} {result : Result} {header : BlockScanEvent}
    {targetBlock : Clif.Block} (block : f.blocks[header.block]? = some targetBlock) :
    ∀ x,Demanded header.output.state x → x ∈ availOf f (availIn f result.ctx) header.block 0 →
      x ∉ targetBlock.params.map (·.1) → headerCarry f result header x := by
  intro x demanded available notParameter
  refine ⟨demanded,available,?_⟩
  simpa only [block,Option.getD_some] using notParameter

/-- The header's `GuardedScanRel` at entry holds the header carry: entering the loop by a
forward edge establishes `CarryRel` of the header carry. -/
theorem headerCarry_entry {f : Clif.Function} {result : Result} {header : BlockScanEvent}
    {MR : MemRelT} {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result header.ctx header.block MR header.output.state (0,fr,cm) ρ w) :
    Inherited.CarryRel f result header.ctx header.block MR (headerCarry f result header)
      header.output.state (0,fr,cm) ρ w :=
  ⟨held,fun x carried => held.2.2.2 x ⟨carried.1,carried.2.1⟩⟩

section
open Backend.Proof.Driver.Fix
set_option Elab.async false
set_option maxRecDepth 20000

private theorem inherited_predecessor {f : Clif.Function} {ctx : Ctx}
    {bi tl : Nat} {b target : Clif.Block} {bc : Clif.BlockCall}
    (source : f.blocks[bi]? = some b) (destination : f.blocks[tl]? = some target)
    (edge : bc.block ∈ succIds b.term) (index : blockIdx? f bc.block = some tl)
    {x : Nat} (available : x ∈ availOf f (availIn f ctx) tl 0)
    (notParameter : x ∉ target.params.map (·.1)) :
    x ∈ availOf f (availIn f ctx) bi b.body.length := by
  obtain ⟨present,later⟩ := (mem_av destination).mp available
  have incoming : x ∈ (availIn f ctx).getD tl [] := by
    rcases present with parameter | incoming | ⟨j,stm,earlier,_,_⟩
    · exact False.elim (notParameter parameter)
    · exact incoming
    · omega
  have successor : tl ∈ succIdx f bi := by
    simp only [succIdx,source]
    exact List.mem_filterMap.mpr ⟨bc.block,edge,index⟩
  have fixed := inFix_fixOk (f := f) (ctx := ctx) (gn := id)
  refine (mem_av source).mpr ⟨?_,?_⟩
  · rcases fixed.out tl x incoming bi successor with parameter | defined | inherited
    · exact .inl (by rwa [parsOf_of source] at parameter)
    · obtain ⟨original,j,stm,found,statement,result⟩ := mem_defsOf.mp defined
      cases Option.some.inj (found.symm.trans source)
      exact .inr (.inr ⟨j,stm,lt_of_getElem? statement,statement,result⟩)
    · exact .inr (.inl inherited)
  · rintro ⟨j,stm,later,statement,_⟩
    have bound := lt_of_getElem? statement
    omega

/-- The values a successor needs, held at the predecessor's end: block arguments, and the
inherited values that the edge cover assigns to the predecessor's demand or carry. -/
theorem cover_held {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b targetBlock : Clif.Block} {bi tl : Nat} {bc : Clif.BlockCall}
    (atBlock : event.block = bi) (source : f.blocks[bi]? = some b)
    (destination : f.blocks[tl]? = some targetBlock) (edge : bc.block ∈ succIds b.term)
    (targetIndex : blockIdx? f bc.block = some tl)
    {next term : State} {carry carried : Nat → Prop}
    (carriedAvailable : ∀ x,carried x → x ∈ availOf f (availIn f result.ctx) tl 0)
    (cover : EdgeCover f result tl (targetBlock.params.map (·.1)) next carried term carry)
    {MR : MemRelT} {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (before : Inherited.CarryRel f result event.ctx event.block MR carry term (b.body.length,fr,cm) ρ w)
    (arguments : ValuesHeld (fun x => x ∈ bc.args) result.ctx fr
      (fun key => ρ (aliasNum result.final.alias key))) :
    ValuesHeld (fun x => x ∈ bc.args ∨
      (((Demanded next x ∧ x ∈ availOf f (availIn f result.ctx) tl 0) ∨ carried x) ∧
        x ∉ targetBlock.params.map (·.1)))
      result.ctx fr (fun key => ρ (aliasNum result.final.alias key)) := by
  intro x required v get
  rcases required with argument | ⟨need,notParameter⟩
  · exact arguments x argument v get
  · have convert : ∀ key,event.ctx.valueReg? x = some (.vreg key .int) →
        result.ctx.valueReg? x = some (.vreg key .int) := by
      intro key mapped
      rw [← (stock_lower_record_context run scope events).2.1 x]
      exact mapped
    have availableNext : x ∈ availOf f (availIn f result.ctx) tl 0 := by
      rcases need with ⟨_,available⟩ | kept
      · exact available
      · exact carriedAvailable x kept
    have covered := cover x availableNext notParameter (by
      rcases need with ⟨demanded,_⟩ | kept
      · exact Or.inl demanded
      · exact Or.inr kept)
    rcases covered with demanded | kept
    · have previous := inherited_predecessor source destination edge targetIndex availableNext notParameter
      obtain ⟨key,mapped,value⟩ := before.1.2.2.2 x ⟨demanded,by simpa only [atBlock] using previous⟩ v get
      exact ⟨key,convert key mapped,value⟩
    · obtain ⟨key,mapped,value⟩ := before.2 x kept v get
      exact ⟨key,convert key mapped,value⟩

end
end Backend.Stock.Proof.LoopCarry

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.LoopCarry
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `selected_successor_guarded_of_demand` with carry sets: the predecessor holds `carry` at its
end, the successor needs its scan demand and `carried`, and `EdgeCover` replaces the demand
order. It holds for forward edges and back edges. -/
theorem ConditionalBodySpec.selected_successor_carry
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    {index : Nat} {bc : Clif.BlockCall} (selected : (dests b.term)[index]? = some bc)
    {next : BlockScanEvent} (nextEvent : next ∈ result.blockScans.toList)
    (nextBlock : next.block = sourceTargetIndex f bc)
    {carry carried : Nat → Prop}
    (carriedAvailable : ∀ x,carried x → x ∈ availOf f (availIn f result.ctx) next.block 0)
    (cover : EdgeCover f result next.block (sourceTargetParams f bc) next.output.state carried
      spec.term.output.state carry)
    {fr fr' : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (before : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR carry
      spec.term.output.state (b.body.length,fr,cm) ρ w)
    (defined : SourceDefinedAt f result.ctx bi b.body.length fr)
    (entered : Clif.enterBlock fr bc = .ok fr')
    (arguments : ValuesHeld (fun x => x ∈ bc.args) result.ctx fr
      (fun key => ρ (aliasNum result.final.alias key))) :
    ∃ tl targetLabel ρ',blockIdx? f bc.block = some tl ∧
      result.order.nodes[targetLabel]? = some (.original tl) ∧
      SelectedCopyRoute result label index ρ targetLabel ρ' ∧
      SourceDefinedAt f result.ctx tl 0 fr' ∧
      Inherited.CarryRel f result next.ctx next.block MR carried next.output.state (0,fr',cm) ρ' w := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  obtain ⟨tl,middle,targetIndex,nonentry,successor,node⟩ :=
    stock_lower_selected_successor run scope tag source selected
  obtain ⟨targetBlock,args,regs,found,read,types,set,frame⟩ := enterBlock_spec entered
  have target : f.block? bc.block = some targetBlock := by rwa [before.1.1] at found
  have destination := blockIdx_block targetIndex target
  have nextAt : next.block = tl := by
    simpa only [sourceTargetIndex,targetIndex,Option.getD_some] using nextBlock
  have params : sourceTargetParams f bc = targetBlock.params.map (·.1) := by
    simp only [sourceTargetParams,target,Option.getD_some]
  have edge := edge_succ (mem_edgeIds_of_dests (List.mem_of_getElem? selected))
  have carriedAt : ∀ x,carried x → x ∈ availOf f (availIn f result.ctx) tl 0 := by
    intro x kept
    rw [← nextAt]
    exact carriedAvailable x kept
  have held := cover_held run scope spec.events spec.atBlock source destination edge targetIndex
    carriedAt (by rw [← nextAt,← params]; exact cover) before arguments
  obtain ⟨tl',targetLabel,ρ',targetIndex',targetTag,route,values⟩ :=
    stock_lower_selected_route_values run scope dominated tag source selected before.1.1 entered
      (needed := fun x => (Demanded next.output.state x ∧ x ∈ availOf f (availIn f result.ctx) tl 0) ∨
        carried x) (by
        intro x required
        have available : x ∈ availOf f (availIn f result.ctx) tl 0 := by
          rcases required with ⟨_,available⟩ | kept
          · exact available
          · exact carriedAt x kept
        simpa only [sourceTargetIndex,targetIndex,Option.getD_some] using available)
      (by rw [params]; exact held)
  have same : tl' = tl := Option.some.inj (targetIndex'.symm.trans targetIndex)
  subst tl'
  have dfg := stock_lower_source_enterBlock_dfg run scope dominated spec.events nextEvent
    source destination edge targetIndex before.1.1 (by simpa only [spec.atBlock] using before.1.2.1) entered
  have nextDefined := source_defined_enterBlock dominated.ssa result.ctx source before.1.1 edge
    targetIndex defined entered
  have convert : ∀ x key,result.ctx.valueReg? x = some (.vreg key .int) →
      next.ctx.valueReg? x = some (.vreg key .int) := by
    intro x key mapped
    rw [(stock_lower_record_context run scope nextEvent).2.1 x]
    exact mapped
  refine ⟨tl,targetLabel,ρ',targetIndex,targetTag,route,nextDefined,⟨?_,?_,?_,?_⟩,?_⟩
  · rw [frame]
    exact before.1.1
  · simpa only [nextAt] using dfg
  · simpa only [frame] using before.1.2.2.1
  · intro x required v get
    obtain ⟨key,mapped,value⟩ := values x (Or.inl ⟨required.1,by simpa only [nextAt] using required.2⟩) v get
    exact ⟨key,convert x key mapped,value⟩
  · intro x kept v get
    obtain ⟨key,mapped,value⟩ := values x (Or.inr kept) v get
    exact ⟨key,convert x key mapped,value⟩

/-- The back-edge step: `selected_successor_guarded_of_demand` with the carry in place of the
demand premise. The carry contains every inherited value that the successor scan demands at
entry, and the successor keeps the same carry. -/
theorem ConditionalBodySpec.selected_successor_guarded_of_carry
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    {index : Nat} {bc : Clif.BlockCall} (selected : (dests b.term)[index]? = some bc)
    {next : BlockScanEvent} (nextEvent : next ∈ result.blockScans.toList)
    (nextBlock : next.block = sourceTargetIndex f bc)
    {carry : Nat → Prop}
    (available : ∀ x,carry x → x ∈ availOf f (availIn f result.ctx) next.block 0)
    (header : ∀ x,Demanded next.output.state x → x ∈ availOf f (availIn f result.ctx) next.block 0 →
      x ∉ sourceTargetParams f bc → carry x)
    {fr fr' : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (before : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR carry
      spec.term.output.state (b.body.length,fr,cm) ρ w)
    (defined : SourceDefinedAt f result.ctx bi b.body.length fr)
    (entered : Clif.enterBlock fr bc = .ok fr')
    (arguments : ValuesHeld (fun x => x ∈ bc.args) result.ctx fr
      (fun key => ρ (aliasNum result.final.alias key))) :
    ∃ tl targetLabel ρ',blockIdx? f bc.block = some tl ∧
      result.order.nodes[targetLabel]? = some (.original tl) ∧
      SelectedCopyRoute result label index ρ targetLabel ρ' ∧
      SourceDefinedAt f result.ctx tl 0 fr' ∧
      Inherited.CarryRel f result next.ctx next.block MR carry next.output.state (0,fr',cm) ρ' w :=
  spec.selected_successor_carry run scope dominated tag selected nextEvent nextBlock available
    (EdgeCover.of_header header) before defined entered arguments

/-- The actual parameter branch emission defines no virtual registers. -/
theorem ConditionalBodySpec.parameter_branch_no_defs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (parameter : result.ctx.defInst? c = none)
    (conditionTy : result.ctx.valueType? c = some (.int 32) ∨ result.ctx.valueType? c = some (.int 64)) :
    ∀ m ∈ spec.origin.emission.code.toList,vdefs m = [] := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have parameterHere : spec.core.scan.ctx.defInst? c = none := by rw [ctxEq]; exact parameter
  obtain ⟨calls,source⟩ := spec.parameter_calls block termShape parameter
  have wideCase : ∀ wide : Bool,spec.core.scan.ctx.valueType? c = some (.int (if wide then 64 else 32)) →
      ∀ m ∈ spec.origin.emission.code.toList,vdefs m = [] := by
    intro wide typed
    obtain ⟨code,fragment,noDefs⟩ := calls.parameter_wide_no_defs inv source wide typed parameterHere
    have actualCode : spec.origin.emission.code.toList = code := by
      rw [spec.origin.emitted]
      have buffers := congrArg Array.toList fragment.emitted
      simpa only [Array.toList_append,Array.toList_empty,List.toList_toArray,List.nil_append] using buffers
    intro m member
    rw [actualCode] at member
    exact noDefs m member
  rcases conditionTy with narrow | wide
  · exact wideCase false (by rw [ctxEq]; exact narrow)
  · exact wideCase true (by rw [ctxEq]; exact wide)

/-- The body and the parameter branch keep every carried value: the body by
`scalar_body_carry_refines`, the branch because it defines no virtual registers. -/
private theorem branch_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (parameter : result.ctx.defInst? c = none)
    (conditionTy : result.ctx.valueType? c = some (.int 32) ∨ result.ctx.valueType? c = some (.int 64))
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {s t : Clif.State}
    (steps : SourceSteps (IndexedSourceInst env cp f spec.core.scan.ctx spec.core.scan.block)
      (List.range' (blockStart f spec.core.scan.block) b.body.length)
      (0,s.frame,s.mem) (b.body.length,t.frame,t.mem))
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world)
    {index : Nat} {inst : MInst} {ops : Array Operand} {regs : Nat → CV} {prefixWorld : Arm.ArmState}
    {outs : List CV} {endWorld : Arm.ArmState} {control : Ctl}
    (machine : seqRun isem (spec.core.code.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
      some (.stop index inst ops regs prefixWorld outs endWorld control)) :
    ValuesHeld needed spec.core.scan.ctx t.frame (fun key => regs (aliasNum result.final.alias key)) := by
  have block := spec.split.block
  have originalBlock : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using block
  have formats : ∀ block ∈ f.blocks,∀ stm ∈ block.body,CastComplete.MemoryFormat stm.inst := by
    intro block member stm present
    exact MaskBody.family_formats (family block member stm present)
  obtain ⟨ρ',w',bodyRun,post⟩ := (Inherited.scalar_body_carry_refines run scope dominated spec.events spec.split
    formats (family b (List.mem_of_getElem? block)) available refines driver stable (env := env) (cp := cp)).1
    (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
    (by simpa only [List.range'_eq_map_range,sourceBodyIndices,List.reverse_reverse] using steps)
    ρ world (by simpa only [spec.split.state] using held)
  rw [spec.bodyCode,Array.toList_append,List.map_append,seqRun_append_fall isem bodyRun] at machine
  have noDefs := spec.parameter_branch_no_defs run scope originalBlock termShape parameter conditionTy
  cases branch : seqRun isem (spec.origin.emission.code.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ' w' with
  | none =>
    rw [branch] at machine
    cases machine
  | some ending =>
    rw [branch] at machine
    cases ending with
    | fall _ _ => cases machine
    | stop index' inst' ops' regs' prefixWorld' outs' endWorld' control' =>
      simp only [Option.map_some,Option.some.injEq,SeqEnd.shift,SeqEnd.stop.injEq] at machine
      obtain ⟨_,_,_,registers,_⟩ := machine
      subst registers
      have frame : ∀ key,regs' key = ρ' key := by
        intro key
        apply Sequence.stop_frame isem branch key
        intro selected member defined
        obtain ⟨raw,inside,rfl⟩ := List.mem_map.mp member
        rw [Resolved.renamed_defs,noDefs raw inside,List.map_nil] at defined
        exact List.not_mem_nil defined
      have registerEq : regs' = ρ' := funext frame
      rw [registerEq]
      exact post.2

/-- `returning_parameter_core` with a carry set: the body and the parameter branch keep `CarryRel`
of every set that is available at the block entry. -/
theorem ConditionalBodySpec.returning_parameter_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (parameter : result.ctx.defInst? c = none)
    (conditionTy : result.ctx.valueType? c = some (.int 32) ∨ result.ctx.valueType? c = some (.int 64))
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {fuel : Nat} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    ∃ (t : Clif.State) (left : Nat) (value : Clif.Val) (fr : Clif.Frame),
      ∃ index inst ops regs prefixWorld endWorld,
      left+1+b.body.length = fuel ∧ t.frame.body = [] ∧ LocalBody.SourceFrameEq s t ∧
      SourceSteps (IndexedSourceInst env cp f spec.core.scan.ctx spec.core.scan.block)
        (List.range' (blockStart f spec.core.scan.block) b.body.length)
        (0,s.frame,s.mem) (b.body.length,t.frame,t.mem) ∧
      t.frame.get c = .ok value ∧
      Clif.enterBlock t.frame (if Clif.Sem.truthy value.bits then yes else no) = .ok fr ∧
      Clif.runLoop env cp left {t with frame := fr} = .returned vals cm ∧
      SourceDefinedAt f result.ctx spec.core.scan.block b.body.length t.frame ∧
      index+1 = spec.origin.emission.code.size ∧
      seqRun isem (spec.core.code.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
        some (.stop (spec.body.code.size+index) inst ops regs prefixWorld [] endWorld
          (.goto (if Clif.Sem.truthy value.bits then 0 else 1))) ∧
      Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.term.output.state
        (b.body.length,t.frame,t.mem) regs endWorld ∧
      inst.targets = result.order.successors[label]!.toList ∧ inst.isTerminator = true := by
  obtain ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩ :=
    spec.returning_parameter_core run scope dominated family refines driver stable
      termShape parameter conditionTy remaining atTerm defined returned held.1
  exact ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,total,empty,frame,steps,read,crossed,
    nextReturned,tDefined,last,machine,⟨post,branch_carry run scope dominated family refines driver stable
      spec termShape parameter conditionTy available steps held machine⟩,targets,terminal⟩

/-- `trapping_parameter_core` with a carry set. -/
theorem ConditionalBodySpec.trapping_parameter_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (parameter : result.ctx.defInst? c = none)
    (conditionTy : result.ctx.valueType? c = some (.int 32) ∨ result.ctx.valueType? c = some (.int 64))
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {fuel : Nat} {s : Clif.State} {code : Clif.TrapCode}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (trapped : Clif.runLoop env cp fuel s = .trapped code)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    TrapRun isem (spec.core.code.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world code ∨
    ∃ (t : Clif.State) (left : Nat) (value : Clif.Val) (fr : Clif.Frame),
      ∃ index inst ops regs prefixWorld endWorld,
      left+1+b.body.length = fuel ∧ t.frame.body = [] ∧ LocalBody.SourceFrameEq s t ∧
      SourceSteps (IndexedSourceInst env cp f spec.core.scan.ctx spec.core.scan.block)
        (List.range' (blockStart f spec.core.scan.block) b.body.length)
        (0,s.frame,s.mem) (b.body.length,t.frame,t.mem) ∧
      t.frame.get c = .ok value ∧
      Clif.enterBlock t.frame (if Clif.Sem.truthy value.bits then yes else no) = .ok fr ∧
      Clif.runLoop env cp left {t with frame := fr} = .trapped code ∧
      SourceDefinedAt f result.ctx spec.core.scan.block b.body.length t.frame ∧
      index+1 = spec.origin.emission.code.size ∧
      seqRun isem (spec.core.code.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
        some (.stop (spec.body.code.size+index) inst ops regs prefixWorld [] endWorld
          (.goto (if Clif.Sem.truthy value.bits then 0 else 1))) ∧
      Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.term.output.state
        (b.body.length,t.frame,t.mem) regs endWorld ∧
      inst.targets = result.order.successors[label]!.toList ∧ inst.isTerminator = true := by
  rcases spec.trapping_parameter_core run scope dominated family refines driver stable
      termShape parameter conditionTy remaining atTerm defined trapped held.1 with
    failed | ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
      total,empty,frame,steps,read,crossed,nextTrapped,tDefined,last,machine,post,targets,terminal⟩
  · exact Or.inl failed
  · exact Or.inr ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,total,empty,frame,steps,read,
      crossed,nextTrapped,tDefined,last,machine,⟨post,branch_carry run scope dominated family refines driver
        stable spec termShape parameter conditionTy available steps held machine⟩,targets,terminal⟩

end Backend.Stock.Proof.ConditionalValues

namespace Backend.Stock.Proof.Control
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.LoopCarry
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `direct_successor_guarded_of_demand` with `jump_successor_values_of_demand` for a jump
block, with carry sets: `EdgeCover` replaces the demand order. It holds for forward edges and
back edges. -/
theorem jump_successor_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b targetBlock : Clif.Block} {label bi tl : Nat} {bc : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : JumpBodySpec f result b label bi bc isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (jump : b.term = .jump bc)
    (targetTag : result.order.nodes[spec.target]? = some (.original tl))
    (targetIndex : blockIdx? f bc.block = some tl)
    (target : f.block? bc.block = some targetBlock)
    {next : BlockScanEvent} (nextEvent : next ∈ result.blockScans.toList) (nextBlock : next.block = tl)
    {carry carried : Nat → Prop}
    (carriedAvailable : ∀ x,carried x → x ∈ availOf f (availIn f result.ctx) tl 0)
    (cover : EdgeCover f result tl (targetBlock.params.map (·.1)) next.output.state carried
      spec.term.output.state carry)
    {fr fr' : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (before : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR carry
      spec.term.output.state (b.body.length,fr,cm) ρ w)
    (defined : SourceDefinedAt f result.ctx bi b.body.length fr)
    (entered : Clif.enterBlock fr bc = .ok fr') :
    ∃ ρ',edgeEnvAt result.code result.edgeArgs label spec.target 0 ρ = some ρ' ∧
      SourceDefinedAt f result.ctx tl 0 fr' ∧
      Inherited.CarryRel f result next.ctx next.block MR carried next.output.state (0,fr',cm) ρ' w := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  have destination := blockIdx_block targetIndex target
  have edge : bc.block ∈ succIds b.term := by simp [jump,succIds,dests]
  have selected : (dests b.term)[0]? = some bc := by simp [jump,dests]
  have successor : result.order.successors[label]![0]? = some spec.target := by
    have targets : result.order.successors[label]! = #[spec.target] := Array.toList_inj.mp spec.targets
    rw [targets]; rfl
  have arguments := stock_jump_body_argument_values run scope dominated spec jump targetTag before.1
  obtain ⟨ρ',copied,values⟩ := stock_lower_direct_per_edge_values run scope dominated tag source
    selected successor targetTag targetIndex before.1.1 target entered
    (needed := fun x => (Demanded next.output.state x ∧ x ∈ availOf f (availIn f result.ctx) tl 0) ∨
      carried x)
    (by
      intro x required
      rcases required with ⟨_,available⟩ | kept
      · exact available
      · exact carriedAvailable x kept)
    (cover_held run scope spec.events spec.atBlock source destination edge targetIndex
      carriedAvailable cover before arguments)
  have dfg := stock_lower_source_enterBlock_dfg run scope dominated spec.events nextEvent
    source destination edge targetIndex before.1.1 (by simpa only [spec.atBlock] using before.1.2.1) entered
  have nextDefined := source_defined_enterBlock dominated.ssa result.ctx source before.1.1 edge
    targetIndex defined entered
  obtain ⟨_,_,_,_,_,_,_,frame⟩ := enterBlock_spec entered
  have convert : ∀ x key,result.ctx.valueReg? x = some (.vreg key .int) →
      next.ctx.valueReg? x = some (.vreg key .int) := by
    intro x key mapped
    rw [(stock_lower_record_context run scope nextEvent).2.1 x]
    exact mapped
  refine ⟨ρ',copied,nextDefined,⟨?_,?_,?_,?_⟩,?_⟩
  · rw [frame]
    exact before.1.1
  · simpa only [nextBlock] using dfg
  · simpa only [frame] using before.1.2.2.1
  · intro x required v get
    obtain ⟨key,mapped,value⟩ := values x (Or.inl ⟨required.1,by simpa only [nextBlock] using required.2⟩) v get
    exact ⟨key,convert x key mapped,value⟩
  · intro x kept v get
    obtain ⟨key,mapped,value⟩ := values x (Or.inr kept) v get
    exact ⟨key,convert x key mapped,value⟩

/-- The back-edge step of a jump: `direct_successor_guarded_of_demand` with the carry in place of
the demand premise. The carry contains every inherited value that the successor scan demands
at entry, and the successor keeps the same carry. -/
theorem jump_successor_guarded_of_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b targetBlock : Clif.Block} {label bi tl : Nat} {bc : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : JumpBodySpec f result b label bi bc isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (jump : b.term = .jump bc)
    (targetTag : result.order.nodes[spec.target]? = some (.original tl))
    (targetIndex : blockIdx? f bc.block = some tl)
    (target : f.block? bc.block = some targetBlock)
    {next : BlockScanEvent} (nextEvent : next ∈ result.blockScans.toList) (nextBlock : next.block = tl)
    {carry : Nat → Prop}
    (available : ∀ x,carry x → x ∈ availOf f (availIn f result.ctx) tl 0)
    (header : ∀ x,Demanded next.output.state x → x ∈ availOf f (availIn f result.ctx) tl 0 →
      x ∉ targetBlock.params.map (·.1) → carry x)
    {fr fr' : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (before : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR carry
      spec.term.output.state (b.body.length,fr,cm) ρ w)
    (defined : SourceDefinedAt f result.ctx bi b.body.length fr)
    (entered : Clif.enterBlock fr bc = .ok fr') :
    ∃ ρ',edgeEnvAt result.code result.edgeArgs label spec.target 0 ρ = some ρ' ∧
      SourceDefinedAt f result.ctx tl 0 fr' ∧
      Inherited.CarryRel f result next.ctx next.block MR carry next.output.state (0,fr',cm) ρ' w :=
  jump_successor_carry run scope dominated spec tag jump targetTag targetIndex target nextEvent nextBlock
    available (EdgeCover.of_header header) before defined entered

end Backend.Stock.Proof.Control

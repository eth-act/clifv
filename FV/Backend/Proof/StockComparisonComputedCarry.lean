import FV.Backend.Proof.StockComparisonLoopCarryBounded
import FV.Backend.Proof.StockComparisonComputedCores

/-! Comparison branches on computed operands with carry sets (#140, CB-8).

The register comparison branch on two nonconstant operands defines no virtual registers
(`comparison_computed_branch_no_defs`), so `branch_carry_of_no_defs` gives its carry cores as for
the parameter forms. `ComputedMetadata` adds this form to the three forms of
`ComparisonMetadata`; `returning/trapping_computed_any_carry_core` dispatch on it, and
`returning/trapping_empty_computed_carry_below` compose the core with the selected successor
(`returning/trapping_empty_carry_below_of_core`). -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.LoopCarry Backend.Stock.Proof.ScalarCmp
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `returning_comparison_computed_core` with a carry set: the body and the comparison branch keep
`CarryRel` of every set that is available at the block entry. -/
theorem ConditionalBodySpec.returning_comparison_computed_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (typeY : result.ctx.valueType? y = some (.int (if wide then 64 else 32)))
    (constantX : NonConstantSource result.ctx x) (constantY : NonConstantSource result.ctx y)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {fuel : Nat} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    ReturningCarryCore spec needed fuel s vals cm ρ world := by
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  have noDefs := spec.comparison_computed_branch_no_defs run scope block termShape origin wide typeX typeY
    constantX constantY
  obtain ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩ :=
    spec.returning_comparison_computed_core run scope dominated family refines driver stable termShape origin wide
      typeX typeY constantX constantY remaining atTerm defined returned held.1
  exact ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,total,empty,frame,steps,read,crossed,
    nextReturned,tDefined,last,machine,⟨post,spec.branch_carry_of_no_defs run scope dominated family refines
      driver stable noDefs available steps held machine⟩,targets,terminal⟩

/-- `trapping_comparison_computed_core` with a carry set. -/
theorem ConditionalBodySpec.trapping_comparison_computed_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (typeY : result.ctx.valueType? y = some (.int (if wide then 64 else 32)))
    (constantX : NonConstantSource result.ctx x) (constantY : NonConstantSource result.ctx y)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {fuel : Nat} {s : Clif.State} {code : Clif.TrapCode}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (trapped : Clif.runLoop env cp fuel s = .trapped code)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    TrappingCarryCore spec needed fuel s code ρ world := by
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  have noDefs := spec.comparison_computed_branch_no_defs run scope block termShape origin wide typeX typeY
    constantX constantY
  rcases spec.trapping_comparison_computed_core run scope dominated family refines driver stable termShape origin wide
      typeX typeY constantX constantY remaining atTerm defined trapped held.1 with
    failed | ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
      total,empty,frame,steps,read,crossed,nextTrapped,tDefined,last,machine,post,targets,terminal⟩
  · exact Or.inl failed
  · exact Or.inr ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,total,empty,frame,steps,read,
      crossed,nextTrapped,tDefined,last,machine,⟨post,spec.branch_carry_of_no_defs run scope dominated family
        refines driver stable noDefs available steps held machine⟩,targets,terminal⟩

/-- Context metadata of a branch condition `c`: an `icmp` of two nonconstant operands of one
wide type (`NonConstantSource`: a parameter, or a result of an instruction other than `iconst`),
or one of the three forms of `ComparisonMetadata`. -/
def ComputedMetadata (ctx : Ctx) (c : Nat) : Prop :=
  (∃ (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat) (wide : Bool),
    ctx.defClif? c = some (.icmp cc ty x y) ∧
    ctx.valueType? x = some (.int (if wide then 64 else 32)) ∧
    ctx.valueType? y = some (.int (if wide then 64 else 32)) ∧
    NonConstantSource ctx x ∧ NonConstantSource ctx y) ∨
  ComparisonMetadata ctx c

/-- The comparison metadata of a branch derives its named call packet. -/
theorem ConditionalBodySpec.computed_metadata_calls {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (comparison : ComputedMetadata result.ctx c) :
    ∃ calls : ConditionalCalls.Calls spec.core.scan.ctx (spec.ranges[bi]!.2-1)
      result.order.successors[label]!.toList
      {spec.input with current := some (spec.ranges[bi]!.2-1),color := none,base.emitted := #[]}
      spec.origin.out spec.origin.emission.state,calls.source = .value c := by
  rcases comparison with ⟨cc,ty,x,y,wide,origin,typeX,typeY,constantX,constantY⟩ | comparison
  · exact spec.comparison_computed_calls run scope block termShape origin constantY
  · obtain ⟨cc,ty,x,y,origin,parameterX⟩ := comparison.origin
    exact spec.comparison_calls run scope block termShape origin parameterX

/-- The carry return core of a branch on a comparison in any form of `ComputedMetadata`. -/
theorem ConditionalBodySpec.returning_computed_any_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (comparison : ComputedMetadata result.ctx c)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {fuel : Nat} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    ReturningCarryCore spec needed fuel s vals cm ρ world := by
  rcases comparison with ⟨cc,ty,x,y,wide,origin,typeX,typeY,constantX,constantY⟩ | comparison
  · exact spec.returning_comparison_computed_carry_core run scope dominated family refines driver stable
      termShape origin wide typeX typeY constantX constantY available remaining atTerm defined returned held
  · exact spec.returning_comparison_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined returned held

/-- The carry first-trap core of a branch on a comparison in any form of `ComputedMetadata`. -/
theorem ConditionalBodySpec.trapping_computed_any_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (comparison : ComputedMetadata result.ctx c)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {fuel : Nat} {s : Clif.State} {code : Clif.TrapCode}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (trapped : Clif.runLoop env cp fuel s = .trapped code)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    TrappingCarryCore spec needed fuel s code ρ world := by
  rcases comparison with ⟨cc,ty,x,y,wide,origin,typeX,typeY,constantX,constantY⟩ | comparison
  · exact spec.trapping_comparison_computed_carry_core run scope dominated family refines driver stable
      termShape origin wide typeX typeY constantX constantY available remaining atTerm defined trapped held
  · exact spec.trapping_comparison_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined trapped held

/-- `returning_empty_comparison_carry_below` for a branch on a comparison in any form of
`ComputedMetadata`. -/
theorem ConditionalBodySpec.returning_empty_computed_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (comparison : ComputedMetadata result.ctx c)
    (emptyArgs : yes.args = [] ∧ no.args = [])
    {carry : Nat → Prop}
    (available : ∀ x,carry x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {vals : List Clif.Val} {cm : Clif.Mem} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryReturnBelow f result bc spec.term.output.state carry isem MR env cp vals cm fuel))
    {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR carry
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.returned vals cm) :=
  spec.returning_empty_carry_below_of_core run scope dominated driver tag termShape emptyArgs successors callers
    (spec.returning_computed_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined returned held)

/-- `trapping_empty_comparison_carry_below` for a branch on a comparison in any form of
`ComputedMetadata`. -/
theorem ConditionalBodySpec.trapping_empty_computed_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (comparison : ComputedMetadata result.ctx c)
    (emptyArgs : yes.args = [] ∧ no.args = [])
    {carry : Nat → Prop}
    (available : ∀ x,carry x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {trapCode : Clif.TrapCode} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryTrapBelow f result bc spec.term.output.state carry isem MR env cp trapCode fuel))
    {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (trapped : Clif.runLoop env cp fuel s = .trapped trapCode)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR carry
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.trapped trapCode) :=
  spec.trapping_empty_carry_below_of_core run scope dominated driver tag termShape emptyArgs successors callers
    (spec.trapping_computed_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined trapped held)

end Backend.Stock.Proof.ConditionalValues

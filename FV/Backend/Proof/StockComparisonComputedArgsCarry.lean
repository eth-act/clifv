import FV.Backend.Proof.StockComparisonArgsCarryBounded
import FV.Backend.Proof.StockComparisonComputedCarry
import FV.Backend.Proof.StockComparisonZeroComputedCores

/-! Comparison branches on computed operands with carry sets and block arguments (#140, CB-9).

CB-8 composes a branch on a comparison in any form of `ComputedMetadata` whose successors take no
arguments (`returning/trapping_empty_computed_carry_below`). T7b-9 composes a branch whose selected
successor takes block arguments from the branch's named call packet and a carry core
(`returning/trapping_selected_carry_below_of_core`). Here the two are combined:
`returning/trapping_selected_computed_carry_below` take the packet of `computed_metadata_calls` and
the carry cores of `returning/trapping_computed_any_carry_core`.

The zero form `icmp eq|ne x, (iconst 0)` with a computed first operand (`cbz`/`cbnz`, CB-9 step 2)
defines no virtual registers (`comparison_zero_computed_branch_no_defs`), so
`branch_carry_of_no_defs` gives its carry cores. `ComputedZeroMetadata` adds this form to the four
forms of `ComputedMetadata`, and `returning/trapping_selected_computed_zero_carry_below` compose
a branch on any of the five forms whose selected successor may take block arguments. -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.LoopCarry Backend.Stock.Proof.ScalarCmp
  Backend.Stock.Proof.ComparisonBranch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- A branch on a comparison in any form of `ComputedMetadata` has the named call packet. -/
theorem ConditionalBodySpec.computed_branch_calls {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (comparison : ComputedMetadata result.ctx c) :
    spec.BranchCalls := by
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  obtain ⟨calls,_⟩ := spec.computed_metadata_calls run scope block termShape comparison
  exact ⟨calls⟩

/-- **A computed comparison branch with block arguments composes below the fuel, for returns.**
`returning_empty_computed_carry_below` where the selected successor may take arguments, through
an original or a critical-edge successor; the condition is a comparison in any form of
`ComputedMetadata`. -/
theorem ConditionalBodySpec.returning_selected_computed_carry_below
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
  spec.returning_selected_carry_below_of_core run scope dominated driver tag termShape
    (spec.computed_branch_calls run scope termShape comparison) successors callers
    (spec.returning_computed_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined returned held)

/-- **A computed comparison branch with block arguments composes below the fuel, for first
traps.** `trapping_empty_computed_carry_below` where the selected successor may take
arguments. -/
theorem ConditionalBodySpec.trapping_selected_computed_carry_below
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
  spec.trapping_selected_carry_below_of_core run scope dominated driver tag termShape
    (spec.computed_branch_calls run scope termShape comparison) successors callers
    (spec.trapping_computed_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined trapped held)

/-- `returning_comparison_zero_computed_core` with a carry set. -/
theorem ConditionalBodySpec.returning_comparison_zero_computed_carry_core {f : Clif.Function} {result : Result}
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
    (constantX : NonConstantSource result.ctx x) (bandX : cc = .ne ∨ NonBandSource result.ctx x)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : result.ctx.defClif? y = some (.iconst ty' k))
    (equality : cc = .eq ∨ cc = .ne) (zero : k = 0)
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
  have noDefs := spec.comparison_zero_computed_branch_no_defs run scope block termShape origin wide typeX constantX
    bandX constY equality zero
  obtain ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩ :=
    spec.returning_comparison_zero_computed_core run scope dominated family refines driver stable termShape
      origin wide typeX constantX bandX constY equality zero remaining atTerm defined returned held.1
  exact ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,total,empty,frame,steps,read,crossed,
    nextReturned,tDefined,last,machine,⟨post,spec.branch_carry_of_no_defs run scope dominated family refines
      driver stable noDefs available steps held machine⟩,targets,terminal⟩

/-- `trapping_comparison_zero_computed_core` with a carry set. -/
theorem ConditionalBodySpec.trapping_comparison_zero_computed_carry_core {f : Clif.Function} {result : Result}
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
    (constantX : NonConstantSource result.ctx x) (bandX : cc = .ne ∨ NonBandSource result.ctx x)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : result.ctx.defClif? y = some (.iconst ty' k))
    (equality : cc = .eq ∨ cc = .ne) (zero : k = 0)
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
  have noDefs := spec.comparison_zero_computed_branch_no_defs run scope block termShape origin wide typeX constantX
    bandX constY equality zero
  rcases spec.trapping_comparison_zero_computed_core run scope dominated family refines driver stable termShape
      origin wide typeX constantX bandX constY equality zero remaining atTerm defined trapped held.1 with
    failed | ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
      total,empty,frame,steps,read,crossed,nextTrapped,tDefined,last,machine,post,targets,terminal⟩
  · exact Or.inl failed
  · exact Or.inr ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,total,empty,frame,steps,read,
      crossed,nextTrapped,tDefined,last,machine,⟨post,spec.branch_carry_of_no_defs run scope dominated family
        refines driver stable noDefs available steps held machine⟩,targets,terminal⟩

/-- Context metadata of a branch condition `c`: an `icmp eq|ne x, y` where `x` is a nonconstant
operand of one wide type (`NonConstantSource`), not a `band` result for `eq` (`NonBandSource`),
and `y` is a result of `iconst 0`; or one of the four forms of `ComputedMetadata`. -/
def ComputedZeroMetadata (ctx : Ctx) (c : Nat) : Prop :=
  (∃ (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat) (wide : Bool) (ty' : Clif.Ty) (k : BitVec ty'.width),
    ctx.defClif? c = some (.icmp cc ty x y) ∧
    ctx.valueType? x = some (.int (if wide then 64 else 32)) ∧
    NonConstantSource ctx x ∧ (cc = .ne ∨ NonBandSource ctx x) ∧
    ctx.defClif? y = some (.iconst ty' k) ∧ (cc = .eq ∨ cc = .ne) ∧ k = 0) ∨
  ComputedMetadata ctx c

/-- A branch on a comparison in any form of `ComputedZeroMetadata` has the named call packet. -/
theorem ConditionalBodySpec.computed_zero_branch_calls {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (comparison : ComputedZeroMetadata result.ctx c) :
    spec.BranchCalls := by
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  rcases comparison with ⟨cc,ty,x,y,wide,ty',k,origin,typeX,constantX,bandX,constY,equality,zero⟩ | comparison
  · obtain ⟨calls,_⟩ := spec.comparison_zero_computed_calls run scope block termShape origin bandX
    exact ⟨calls⟩
  · exact spec.computed_branch_calls run scope termShape comparison

/-- The carry return core of a branch on a comparison in any form of `ComputedZeroMetadata`. -/
theorem ConditionalBodySpec.returning_computed_zero_any_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (comparison : ComputedZeroMetadata result.ctx c)
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
  rcases comparison with ⟨cc,ty,x,y,wide,ty',k,origin,typeX,constantX,bandX,constY,equality,zero⟩ | comparison
  · exact spec.returning_comparison_zero_computed_carry_core run scope dominated family refines driver stable
      termShape origin wide typeX constantX bandX constY equality zero available remaining atTerm defined
      returned held
  · exact spec.returning_computed_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined returned held

/-- The carry first-trap core of a branch on a comparison in any form of
`ComputedZeroMetadata`. -/
theorem ConditionalBodySpec.trapping_computed_zero_any_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (comparison : ComputedZeroMetadata result.ctx c)
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
  rcases comparison with ⟨cc,ty,x,y,wide,ty',k,origin,typeX,constantX,bandX,constY,equality,zero⟩ | comparison
  · exact spec.trapping_comparison_zero_computed_carry_core run scope dominated family refines driver stable
      termShape origin wide typeX constantX bandX constY equality zero available remaining atTerm defined
      trapped held
  · exact spec.trapping_computed_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined trapped held

/-- **A branch on a comparison in any form of `ComputedZeroMetadata`, with block arguments,
composes below the fuel, for returns.** `returning_selected_computed_carry_below` with the zero
form of a computed operand. -/
theorem ConditionalBodySpec.returning_selected_computed_zero_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (comparison : ComputedZeroMetadata result.ctx c)
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
  spec.returning_selected_carry_below_of_core run scope dominated driver tag termShape
    (spec.computed_zero_branch_calls run scope termShape comparison) successors callers
    (spec.returning_computed_zero_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined returned held)

/-- **A branch on a comparison in any form of `ComputedZeroMetadata`, with block arguments,
composes below the fuel, for first traps.** -/
theorem ConditionalBodySpec.trapping_selected_computed_zero_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (comparison : ComputedZeroMetadata result.ctx c)
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
  spec.trapping_selected_carry_below_of_core run scope dominated driver tag termShape
    (spec.computed_zero_branch_calls run scope termShape comparison) successors callers
    (spec.trapping_computed_zero_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined trapped held)

end Backend.Stock.Proof.ConditionalValues

import FV.Backend.Proof.StockComparisonComputedArgsCarry
import FV.Backend.Proof.StockComparisonImmComputedCores

/-! Immediate comparison branches on computed operands with carry sets and block arguments (#140,
CB-9).

The 12-bit immediate form `icmp cc x, (iconst k)` with a computed first operand
(`subs xzr, x, #imm` and `b.cond`, CB-9 step 3) defines no virtual registers
(`comparison_imm_computed_branch_no_defs`), so `branch_carry_of_no_defs` gives its carry cores.
`ComputedArgsMetadata` adds this form to the five forms of `ComputedZeroMetadata`, and
`returning/trapping_selected_computed_args_carry_below` compose a branch on any of the six forms
whose selected successor may take block arguments. -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.LoopCarry Backend.Stock.Proof.ScalarCmp
  Backend.Stock.Proof.ComparisonBranch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `returning_comparison_imm_computed_core` with a carry set. -/
theorem ConditionalBodySpec.returning_comparison_imm_computed_carry_core {f : Clif.Function} {result : Result}
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
    (constantX : NonConstantSource result.ctx x)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : result.ctx.defClif? y = some (.iconst ty' k))
    {imm : Imm12} (fits : Imm12.ofNat? k.toNat = some imm)
    (nonzero : cc = .eq ∨ cc = .ne → k ≠ 0)
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
  have noDefs := spec.comparison_imm_computed_branch_no_defs run scope block termShape origin wide typeX constantX
    constY fits nonzero
  obtain ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩ :=
    spec.returning_comparison_imm_computed_core run scope dominated family refines driver stable termShape origin wide
      typeX constantX constY fits nonzero remaining atTerm defined returned held.1
  exact ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,total,empty,frame,steps,read,crossed,
    nextReturned,tDefined,last,machine,⟨post,spec.branch_carry_of_no_defs run scope dominated family refines
      driver stable noDefs available steps held machine⟩,targets,terminal⟩

/-- `trapping_comparison_imm_computed_core` with a carry set. -/
theorem ConditionalBodySpec.trapping_comparison_imm_computed_carry_core {f : Clif.Function} {result : Result}
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
    (constantX : NonConstantSource result.ctx x)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : result.ctx.defClif? y = some (.iconst ty' k))
    {imm : Imm12} (fits : Imm12.ofNat? k.toNat = some imm)
    (nonzero : cc = .eq ∨ cc = .ne → k ≠ 0)
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
  have noDefs := spec.comparison_imm_computed_branch_no_defs run scope block termShape origin wide typeX constantX
    constY fits nonzero
  rcases spec.trapping_comparison_imm_computed_core run scope dominated family refines driver stable termShape origin
      wide typeX constantX constY fits nonzero remaining atTerm defined trapped held.1 with
    failed | ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
      total,empty,frame,steps,read,crossed,nextTrapped,tDefined,last,machine,post,targets,terminal⟩
  · exact Or.inl failed
  · exact Or.inr ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,total,empty,frame,steps,read,
      crossed,nextTrapped,tDefined,last,machine,⟨post,spec.branch_carry_of_no_defs run scope dominated family
        refines driver stable noDefs available steps held machine⟩,targets,terminal⟩

/-- Context metadata of a branch condition `c`: an `icmp cc x, y` where `x` is a nonconstant
operand of one wide type (`NonConstantSource`) and `y` is a result of an encodable 12-bit
`iconst k`, `k ≠ 0` for `eq`/`ne`; or one of the five forms of `ComputedZeroMetadata`. -/
def ComputedArgsMetadata (ctx : Ctx) (c : Nat) : Prop :=
  (∃ (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat) (wide : Bool) (ty' : Clif.Ty) (k : BitVec ty'.width)
      (imm : Imm12),
    ctx.defClif? c = some (.icmp cc ty x y) ∧
    ctx.valueType? x = some (.int (if wide then 64 else 32)) ∧ NonConstantSource ctx x ∧
    ctx.defClif? y = some (.iconst ty' k) ∧ Imm12.ofNat? k.toNat = some imm ∧
    (cc = .eq ∨ cc = .ne → k ≠ 0)) ∨
  ComputedZeroMetadata ctx c

/-- A branch on a comparison in any form of `ComputedArgsMetadata` has the named call packet. -/
theorem ConditionalBodySpec.computed_args_branch_calls {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (comparison : ComputedArgsMetadata result.ctx c) :
    spec.BranchCalls := by
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  rcases comparison with ⟨cc,ty,x,y,wide,ty',k,imm,origin,typeX,constantX,constY,fits,nonzero⟩ | comparison
  · obtain ⟨calls,_⟩ := spec.comparison_imm_computed_calls run scope block termShape origin constY nonzero
    exact ⟨calls⟩
  · exact spec.computed_zero_branch_calls run scope termShape comparison

/-- The carry return core of a branch on a comparison in any form of `ComputedArgsMetadata`. -/
theorem ConditionalBodySpec.returning_computed_args_any_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (comparison : ComputedArgsMetadata result.ctx c)
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
  rcases comparison with ⟨cc,ty,x,y,wide,ty',k,imm,origin,typeX,constantX,constY,fits,nonzero⟩ | comparison
  · exact spec.returning_comparison_imm_computed_carry_core run scope dominated family refines driver stable
      termShape origin wide typeX constantX constY fits nonzero available remaining atTerm defined returned held
  · exact spec.returning_computed_zero_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined returned held

/-- The carry first-trap core of a branch on a comparison in any form of
`ComputedArgsMetadata`. -/
theorem ConditionalBodySpec.trapping_computed_args_any_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (comparison : ComputedArgsMetadata result.ctx c)
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
  rcases comparison with ⟨cc,ty,x,y,wide,ty',k,imm,origin,typeX,constantX,constY,fits,nonzero⟩ | comparison
  · exact spec.trapping_comparison_imm_computed_carry_core run scope dominated family refines driver stable
      termShape origin wide typeX constantX constY fits nonzero available remaining atTerm defined trapped held
  · exact spec.trapping_computed_zero_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined trapped held

/-- **A branch on a comparison in any form of `ComputedArgsMetadata`, with block arguments,
composes below the fuel, for returns.** `returning_selected_computed_carry_below` with the zero
and 12-bit immediate forms of a computed operand. -/
theorem ConditionalBodySpec.returning_selected_computed_args_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (comparison : ComputedArgsMetadata result.ctx c)
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
    (spec.computed_args_branch_calls run scope termShape comparison) successors callers
    (spec.returning_computed_args_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined returned held)

/-- **A branch on a comparison in any form of `ComputedArgsMetadata`, with block arguments,
composes below the fuel, for first traps.** -/
theorem ConditionalBodySpec.trapping_selected_computed_args_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (comparison : ComputedArgsMetadata result.ctx c)
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
    (spec.computed_args_branch_calls run scope termShape comparison) successors callers
    (spec.trapping_computed_args_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined trapped held)

end Backend.Stock.Proof.ConditionalValues

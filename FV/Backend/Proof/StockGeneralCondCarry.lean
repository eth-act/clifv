import FV.Backend.Proof.StockPlainConditionCores
import FV.Backend.Proof.StockComparisonGeneralLoopCarry

/-! Branches on a plain computed condition or a comparison, with carry sets (#140, CB-11).

`PlainMetadata` is the context metadata of a plain wide condition (`PlainSource` and an `i32` or
`i64` type). It contains every wide parameter (`PlainMetadata.of_parameter`). `CondMetadata`
adds it to the six comparison forms of `ComputedArgsMetadata` (CB-9). A branch on a condition in
any form of `CondMetadata` has the named call packet (`cond_branch_calls`) and the carry cores
`returning/trapping_cond_any_carry_core`. With them a branch composes below the fuel whose
selected successor may take block arguments (`returning/trapping_selected_cond_carry_below`) or
whose successors take none (`returning/trapping_empty_cond_carry_below`). -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.LoopCarry Backend.Stock.Proof.PlainBranch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Context metadata of a plain wide condition: no lowering rule looks through its definition,
and it has type `i32` or `i64`. -/
def PlainMetadata (ctx : Ctx) (c : Nat) : Prop :=
  PlainSource ctx c ∧ (ctx.valueType? c = some (.int 32) ∨ ctx.valueType? c = some (.int 64))

/-- A wide parameter is a plain wide condition. -/
theorem PlainMetadata.of_parameter {ctx : Ctx} {c : Nat} (parameter : ctx.defInst? c = none)
    (conditionTy : ctx.valueType? c = some (.int 32) ∨ ctx.valueType? c = some (.int 64)) :
    PlainMetadata ctx c :=
  ⟨plain_of_parameter parameter,conditionTy⟩

/-- Context metadata of a branch condition: a plain wide condition (which includes a wide
parameter), or a comparison in one of the six forms of `ComputedArgsMetadata`. -/
def CondMetadata (ctx : Ctx) (c : Nat) : Prop :=
  PlainMetadata ctx c ∨ ComputedArgsMetadata ctx c

/-- A branch on a condition in any form of `CondMetadata` has the named call packet. -/
theorem ConditionalBodySpec.cond_branch_calls {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (condition : CondMetadata result.ctx c) :
    spec.BranchCalls := by
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  rcases condition with ⟨plain,_⟩ | comparison
  · obtain ⟨calls,_⟩ := spec.plain_calls run scope block termShape plain
    exact ⟨calls⟩
  · exact spec.computed_args_branch_calls run scope termShape comparison

/-- The carry return core of a branch on a condition in any form of `CondMetadata`. -/
theorem ConditionalBodySpec.returning_cond_any_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (condition : CondMetadata result.ctx c)
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
  rcases condition with ⟨plain,conditionTy⟩ | comparison
  · exact spec.returning_plain_carry_core run scope dominated family refines driver stable termShape plain
      conditionTy available remaining atTerm defined returned held
  · exact spec.returning_computed_args_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined returned held

/-- The carry first-trap core of a branch on a condition in any form of `CondMetadata`. -/
theorem ConditionalBodySpec.trapping_cond_any_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (condition : CondMetadata result.ctx c)
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
  rcases condition with ⟨plain,conditionTy⟩ | comparison
  · exact spec.trapping_plain_carry_core run scope dominated family refines driver stable termShape plain
      conditionTy available remaining atTerm defined trapped held
  · exact spec.trapping_computed_args_any_carry_core run scope dominated family refines driver stable termShape
      comparison available remaining atTerm defined trapped held

/-- **A branch on a condition in any form of `CondMetadata`, with block arguments, composes below
the fuel, for returns.** The selected successor may take arguments, through an original or a
critical-edge successor. -/
theorem ConditionalBodySpec.returning_selected_cond_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (condition : CondMetadata result.ctx c)
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
    (spec.cond_branch_calls run scope termShape condition) successors callers
    (spec.returning_cond_any_carry_core run scope dominated family refines driver stable termShape
      condition available remaining atTerm defined returned held)

/-- **A branch on a condition in any form of `CondMetadata`, with block arguments, composes below
the fuel, for first traps.** -/
theorem ConditionalBodySpec.trapping_selected_cond_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (condition : CondMetadata result.ctx c)
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
    (spec.cond_branch_calls run scope termShape condition) successors callers
    (spec.trapping_cond_any_carry_core run scope dominated family refines driver stable termShape
      condition available remaining atTerm defined trapped held)

/-- **A branch on a condition in any form of `CondMetadata`, with empty block arguments, composes
below the fuel, for returns.** -/
theorem ConditionalBodySpec.returning_empty_cond_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (condition : CondMetadata result.ctx c)
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
    (spec.returning_cond_any_carry_core run scope dominated family refines driver stable termShape
      condition available remaining atTerm defined returned held)

/-- **A branch on a condition in any form of `CondMetadata`, with empty block arguments, composes
below the fuel, for first traps.** -/
theorem ConditionalBodySpec.trapping_empty_cond_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (condition : CondMetadata result.ctx c)
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
    (spec.trapping_cond_any_carry_core run scope dominated family refines driver stable termShape
      condition available remaining atTerm defined trapped held)

end Backend.Stock.Proof.ConditionalValues

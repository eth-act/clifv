import FV.Backend.Proof.StockPlainBandCores
import FV.Backend.Proof.StockBranchCond5Carry

/-! Branches on a `PlainSource'` condition or a condition of `BranchCondMetadata5`, with carry
sets (#140, CB-15).

`PlainMetadata'` is the context metadata of a wide `PlainSource'` condition: it is not the one-bit
test of the `tbnz` rule 3251 and not a comparison origin, and it has type `i32` or `i64`. It
contains `PlainMetadata` (`PlainMetadata.weak`), and also a `band` whose mask is a register or a
constant that is not a one-bit mask. `BranchCondMetadata7` adds it to the forms of
`BranchCondMetadata5` (CB-13). A branch on a condition in any form has two successor labels
(`branch_cond7_labels`) and the carry cores `returning/trapping_branch_cond7_carry_core`; with them
it composes below the fuel with or without block arguments
(`returning/trapping_selected_branch_cond7_carry_below`,
`returning/trapping_empty_branch_cond7_carry_below`). The actual `cbnz` of a `PlainMetadata'`
branch is one instruction (`plain_emission_nonempty'`). -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.LoopCarry Backend.Stock.Proof.PlainBranch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Context metadata of a wide `PlainSource'` condition: no lowering rule looks through its
definition, and it has type `i32` or `i64`. -/
def PlainMetadata' (ctx : Ctx) (c : Nat) : Prop :=
  PlainSource' ctx c ∧ (ctx.valueType? c = some (.int 32) ∨ ctx.valueType? c = some (.int 64))

/-- `PlainMetadata` implies `PlainMetadata'`. -/
theorem PlainMetadata.weak {ctx : Ctx} {c : Nat} (plain : PlainMetadata ctx c) : PlainMetadata' ctx c :=
  ⟨plain.1.weak,plain.2⟩

/-- Context metadata of a branch condition: a wide `PlainSource'` condition, or a condition in a
form of `BranchCondMetadata5`. -/
def BranchCondMetadata7 (ctx : Ctx) (c : Nat) : Prop :=
  PlainMetadata' ctx c ∨ BranchCondMetadata5 ctx c

/-- The real emission of a branch on a wide `PlainSource'` condition is not empty. -/
theorem ConditionalBodySpec.plain_emission_nonempty' {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (plain : PlainMetadata' result.ctx c) :
    0 < spec.origin.emission.code.size := by
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  have size := spec.plain_emission_size' run scope block termShape plain.1 plain.2
  omega

/-- A branch on a condition in any form of `BranchCondMetadata7` has two successor labels. -/
theorem ConditionalBodySpec.branch_cond7_labels {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (condition : BranchCondMetadata7 result.ctx c) :
    ∃ yesLabel noLabel,result.order.successors[label]!.toList = [yesLabel,noLabel] := by
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  rcases condition with ⟨plain,_⟩ | condition
  · obtain ⟨calls,_⟩ := spec.plain_calls' run scope block termShape plain
    exact ⟨calls.yes,calls.no,calls.labels_eq⟩
  · exact spec.branch_cond5_labels run scope termShape condition

/-- The carry return core of a branch on a condition in any form of `BranchCondMetadata7`. -/
theorem ConditionalBodySpec.returning_branch_cond7_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (condition : BranchCondMetadata7 result.ctx c)
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
  rcases condition with ⟨plain,conditionTy⟩ | condition
  · exact spec.returning_plain_carry_core' run scope dominated family refines driver stable termShape plain
      conditionTy available remaining atTerm defined returned held
  · exact spec.returning_branch_cond5_carry_core run scope dominated family refines driver stable termShape
      condition available remaining atTerm defined returned held

/-- The carry first-trap core of a branch on a condition in any form of `BranchCondMetadata7`. -/
theorem ConditionalBodySpec.trapping_branch_cond7_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (condition : BranchCondMetadata7 result.ctx c)
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
  rcases condition with ⟨plain,conditionTy⟩ | condition
  · exact spec.trapping_plain_carry_core' run scope dominated family refines driver stable termShape plain
      conditionTy available remaining atTerm defined trapped held
  · exact spec.trapping_branch_cond5_carry_core run scope dominated family refines driver stable termShape
      condition available remaining atTerm defined trapped held

/-- **A branch on a condition in any form of `BranchCondMetadata7`, with block arguments, composes below
the fuel, for returns.** The selected successor may take arguments, through an original or a
critical-edge successor. -/
theorem ConditionalBodySpec.returning_selected_branch_cond7_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (condition : BranchCondMetadata7 result.ctx c)
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
  spec.returning_selected_carry_below_of_labels run scope dominated driver tag termShape
    (spec.branch_cond7_labels run scope termShape condition) successors callers
    (spec.returning_branch_cond7_carry_core run scope dominated family refines driver stable termShape
      condition available remaining atTerm defined returned held)

/-- **A branch on a condition in any form of `BranchCondMetadata7`, with block arguments, composes below
the fuel, for first traps.** -/
theorem ConditionalBodySpec.trapping_selected_branch_cond7_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (condition : BranchCondMetadata7 result.ctx c)
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
  spec.trapping_selected_carry_below_of_labels run scope dominated driver tag termShape
    (spec.branch_cond7_labels run scope termShape condition) successors callers
    (spec.trapping_branch_cond7_carry_core run scope dominated family refines driver stable termShape
      condition available remaining atTerm defined trapped held)

/-- **A branch on a condition in any form of `BranchCondMetadata7`, with empty block arguments, composes
below the fuel, for returns.** -/
theorem ConditionalBodySpec.returning_empty_branch_cond7_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (condition : BranchCondMetadata7 result.ctx c)
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
    (spec.returning_branch_cond7_carry_core run scope dominated family refines driver stable termShape
      condition available remaining atTerm defined returned held)

/-- **A branch on a condition in any form of `BranchCondMetadata7`, with empty block arguments, composes
below the fuel, for first traps.** -/
theorem ConditionalBodySpec.trapping_empty_branch_cond7_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (condition : BranchCondMetadata7 result.ctx c)
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
    (spec.trapping_branch_cond7_carry_core run scope dominated family refines driver stable termShape
      condition available remaining atTerm defined trapped held)

end Backend.Stock.Proof.ConditionalValues

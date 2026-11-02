import FV.Backend.Proof.StockComparisonComputedArgsLoopTrap
import FV.Backend.Proof.StockComparisonComputedLoopDomain
import FV.Backend.Proof.StockComparisonArgsLoopDomain

/-! The loop class with computed comparisons and block arguments satisfies the per-successor
production domain (#140, CB-9).

`StockComparisonArgsLoopDomain` (T7b-9) with `ComputedArgsTerms`. A branch entry establishes
`GuardedScanRel` at the entry scan with the prelude of its condition (`branch_entry_prelude`): the
CB-8 prelude for a parameter or a condition of `ComputedCondition`, and
`comparison_zero_computed_entry_prelude` for the zero form with a computed first operand. A jump or
branch entry then continues into nonentry blocks with `computed_args_loop_returns_below` /
`computed_args_loop_traps_below` at the entry run's fuel; a return entry is
`parameter_return_entry_frame`. The edge copies of a branch with block arguments are nonempty
per-successor vectors, so the class is not legacy-compatible: the result is `Scalar.DomainAt`. -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ScalarCmp Backend.Stock.Proof.ComparisonBranch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `comparison_zero_entry_prelude` for a nonconstant first operand: the actual one-instruction
`cbz`/`cbnz` emission derives nonempty core code. -/
theorem comparison_zero_computed_entry_prelude {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {c : Nat} {yes no : Clif.BlockCall} {isem : Backend.Proof.Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b 0 0 c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (constantX : NonConstantSource result.ctx x) (bandX : cc = .ne ∨ NonBandSource result.ctx x)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : result.ctx.defClif? y = some (.iconst ty' k))
    (equality : cc = .eq ∨ cc = .ne) (zero : k = 0)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ' w',Star (VStepAt result.code result.edgeArgs isem)
      (.run ⟨0,0,entrySeed spec.core.scan.ctx fr,w⟩)
      (.run ⟨0,spec.preludeCode.size,ρ',w'⟩) ∧
      GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR
        spec.core.scan.output.state (0,fr,cm) ρ' w' ∧
      ValuesHeld (fun _ => True) spec.core.scan.ctx fr
        (fun key => ρ' (aliasNum result.final.alias key)) ∧ SameWorld F w' w := by
  have block : f.blocks[0]? = some b := by simpa only [spec.atBlock] using spec.split.block
  have count := spec.comparison_zero_computed_emission_size run scope block termShape origin wide typeX
    constantX bandX constY equality zero
  have nonempty : 0 < spec.core.code.size := by
    rw [spec.bodyCode]
    simp only [Array.size_append,count]
    omega
  let entry : Control.EntryCoreSpec f result b := {
    ranges := spec.ranges
    params := spec.params
    core := spec.core
    raw := spec.raw
    preludeCode := spec.preludeCode
    build := spec.build
    sizes := spec.sizes
    assembled := spec.assembled
    events := spec.events
    block := block
    rawCode := spec.rawCode
    placed := spec.placed
    nonempty := nonempty }
  exact Control.original_entry_prelude run scope dominated entry entered driver memorySem stable memory arguments

end Backend.Stock.Proof.ConditionalValues

namespace Backend.Stock.Proof.ComparisonComputedArgsLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues
  Backend.Stock.Proof.ForwardSource Backend.Stock.Proof.LoopCarry Backend.Stock.Proof.ParameterCfg
  Backend.Stock.Proof.ParameterLoopCfg Backend.Stock.Proof.ComparisonLoopCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The entry prelude of a branch on a parameter or on a comparison in any form of
`ComputedArgsCondition`. -/
theorem branch_entry_prelude {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {c : Nat} {yes no : Clif.BlockCall} {isem : Backend.Proof.Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b 0 0 c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no)
    (condition : ParameterCondition f c ∨ ComputedArgsCondition f c)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ' w',Star (VStepAt result.code result.edgeArgs isem)
      (.run ⟨0,0,entrySeed spec.core.scan.ctx fr,w⟩)
      (.run ⟨0,spec.preludeCode.size,ρ',w'⟩) ∧
      GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR
        spec.core.scan.output.state (0,fr,cm) ρ' w' ∧
      ValuesHeld (fun _ => True) spec.core.scan.ctx fr
        (fun key => ρ' (aliasNum result.final.alias key)) ∧ SameWorld F w' w := by
  rcases condition with parameter | ⟨bi,j,b',stm,cc,ty,x,y,block,lookup,member,inst,zero | operands⟩
  · exact ComparisonComputedLoopCfg.branch_entry_prelude run scope dominated spec termShape (Or.inl parameter)
      entered driver memorySem stable memory arguments
  · obtain ⟨equality,⟨wide,operandX⟩,ty',k,⟨ibi,i,ib,constant,constantBlock,constantLookup,constantResult,
      constantInst⟩,zero⟩ := zero
    have origin : result.ctx.defClif? c = some (.icmp cc ty x y) := by
      rw [← inst]
      exact ComparisonLoopCfg.statement_metadata dominated block lookup member spec.build
    have constY : result.ctx.defClif? y = some (.iconst ty' k) := by
      rw [← constantInst]
      exact ComparisonLoopCfg.statement_metadata dominated constantBlock constantLookup constantResult spec.build
    obtain ⟨typeX,constantX,bandX⟩ := operandX.metadata scope dominated spec.build
    exact comparison_zero_computed_entry_prelude run scope dominated spec termShape origin wide typeX constantX
      bandX constY equality zero entered driver memorySem stable memory arguments
  · exact ComparisonComputedLoopCfg.branch_entry_prelude run scope dominated spec termShape
      (Or.inr ⟨bi,j,b',stm,cc,ty,x,y,block,lookup,member,inst,operands⟩)
      entered driver memorySem stable memory arguments

/-- Instruction-zero ABI return simulation of a function of the class whose entry jumps. -/
theorem computed_args_loop_jump_entry_returns {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : ComputedArgsTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {bc : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (jump : entry.term = .jump bc)
    {env : Clif.Env} {cp : Clif.Program} {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) {fuel : Nat} {vals : List Clif.Val} {outMem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w0 : Arm.ArmState} (memory : MR fr.slots cm w0) (arguments : ArgsAtEntry F f.sig args w0) :
    ∃ ρ0,RunOkABIAt f result.code result.edgeArgs isem MR fr.slots ⟨0,0,ρ0,w0⟩ (.returned vals outMem) := by
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨spec⟩ := Control.stock_lower_jump_body_spec run scope dominated family tag source jump
    refines driver stable env cp
  obtain ⟨_,remaining,atTerm⟩ := entry_frame_parts source entered
  obtain ⟨ρentry,wentry,path,guarded,allValues,sameWorld⟩ := Control.jump_entry_prelude run scope dominated spec
    entered driver memorySem stable memory arguments
  have finished := jump_carry_returns run scope dominated family refines driver stable spec tag jump
    (fun targetTag targetSource targetNonentry nextEvent nextBlock =>
      computed_args_loop_returns_below run scope dominated abi terms family refines driver stable env cp fuel
        targetTag targetSource targetNonentry nextEvent nextBlock)
    (s := ⟨fr,[],cm⟩) rfl remaining atTerm (Control.source_defined_entry_frame dominated result.ctx entered)
    returned (entry_carry source guarded)
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- Instruction-zero ABI first-trap simulation of a function of the class whose entry jumps. -/
theorem computed_args_loop_jump_entry_traps {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : ComputedArgsTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {bc : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (jump : entry.term = .jump bc)
    {env : Clif.Env} {cp : Clif.Program} {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w0 : Arm.ArmState} (memory : MR fr.slots cm w0) (arguments : ArgsAtEntry F f.sig args w0) :
    ∃ ρ0,RunOkABIAt f result.code result.edgeArgs isem MR fr.slots ⟨0,0,ρ0,w0⟩ (.trapped code) := by
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨spec⟩ := Control.stock_lower_jump_body_spec run scope dominated family tag source jump
    refines driver stable env cp
  obtain ⟨_,remaining,atTerm⟩ := entry_frame_parts source entered
  obtain ⟨ρentry,wentry,path,guarded,allValues,sameWorld⟩ := Control.jump_entry_prelude run scope dominated spec
    entered driver memorySem stable memory arguments
  have finished := jump_carry_traps run scope dominated family refines driver stable spec tag jump
    (fun targetTag targetSource targetNonentry nextEvent nextBlock =>
      computed_args_loop_traps_below run scope dominated abi terms family refines driver stable env cp fuel
        targetTag targetSource targetNonentry nextEvent nextBlock)
    (s := ⟨fr,[],cm⟩) rfl remaining atTerm (Control.source_defined_entry_frame dominated result.ctx entered)
    trapped (entry_carry source guarded)
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- Instruction-zero ABI return simulation of a function of the class whose entry branches on a
wide parameter or on a comparison, with any block arguments. -/
theorem computed_args_loop_branch_entry_returns {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : ComputedArgsTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {c : Nat} {yes no : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (term : entry.term = .brif c yes no) (condition : ParameterCondition f c ∨ ComputedArgsCondition f c)
    {env : Clif.Env} {cp : Clif.Program} {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) {fuel : Nat} {vals : List Clif.Val} {outMem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w0 : Arm.ArmState} (memory : MR fr.slots cm w0) (arguments : ArgsAtEntry F f.sig args w0) :
    ∃ ρ0,RunOkABIAt f result.code result.edgeArgs isem MR fr.slots ⟨0,0,ρ0,w0⟩ (.returned vals outMem) := by
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag source term
    refines driver stable env cp
  obtain ⟨_,remaining,atTerm⟩ := entry_frame_parts source entered
  obtain ⟨ρentry,wentry,path,guarded,allValues,sameWorld⟩ := branch_entry_prelude run scope dominated spec
    term condition entered driver memorySem stable memory arguments
  have finished := branch_args_carry_returns run scope dominated family refines driver stable spec tag
    term condition
    (fun targetTag targetSource targetNonentry nextEvent nextBlock =>
      computed_args_loop_returns_below run scope dominated abi terms family refines driver stable env cp fuel
        targetTag targetSource targetNonentry nextEvent nextBlock)
    (s := ⟨fr,[],cm⟩) rfl remaining atTerm (Control.source_defined_entry_frame dominated result.ctx entered)
    returned (entry_carry source guarded)
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- Instruction-zero ABI first-trap simulation of a function of the class whose entry branches
on a wide parameter or on a comparison, with any block arguments. -/
theorem computed_args_loop_branch_entry_traps {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : ComputedArgsTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {c : Nat} {yes no : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (term : entry.term = .brif c yes no) (condition : ParameterCondition f c ∨ ComputedArgsCondition f c)
    {env : Clif.Env} {cp : Clif.Program} {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w0 : Arm.ArmState} (memory : MR fr.slots cm w0) (arguments : ArgsAtEntry F f.sig args w0) :
    ∃ ρ0,RunOkABIAt f result.code result.edgeArgs isem MR fr.slots ⟨0,0,ρ0,w0⟩ (.trapped code) := by
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag source term
    refines driver stable env cp
  obtain ⟨_,remaining,atTerm⟩ := entry_frame_parts source entered
  obtain ⟨ρentry,wentry,path,guarded,allValues,sameWorld⟩ := branch_entry_prelude run scope dominated spec
    term condition entered driver memorySem stable memory arguments
  have finished := branch_args_carry_traps run scope dominated family refines driver stable spec tag
    term condition
    (fun targetTag targetSource targetNonentry nextEvent nextBlock =>
      computed_args_loop_traps_below run scope dominated abi terms family refines driver stable env cp fuel
        targetTag targetSource targetNonentry nextEvent nextBlock)
    (s := ⟨fr,[],cm⟩) rfl remaining atTerm (Control.source_defined_entry_frame dominated result.ctx entered)
    trapped (entry_carry source guarded)
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- **The loop class with computed comparisons and block arguments satisfies the per-successor
production domain.** Every block jumps (with any arguments), returns, branches with any arguments
on a wide parameter or on a comparison (`ComputedArgsCondition`: a form of `ComputedCondition`, or
`eq`/`ne` of a computed wide value with zero, where the value is not a `band` result for `eq`),
or, outside the entry, ends in `trap`. No rank: targets may be loop headers, and back edges and self
loops are allowed, also when a branch passes block arguments on them. -/
theorem domainAt_of_computed_args_loop_cfg {f : Clif.Function}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    (terms : ComputedArgsTerms f)
    (entryKind : ∀ b,f.blocks[0]? = some b → ∀ c,b.term ≠ .trap c)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst) : Scalar.DomainAt f := by
  have entry : ∃ (b : Clif.Block),f.blocks[0]? = some b := by
    cases blocks : f.blocks with
    | nil => exact False.elim (scope.nonempty blocks)
    | cons b rest => exact ⟨b,by simp only [List.getElem?_cons_zero]⟩
  obtain ⟨b,source⟩ := entry
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable world memory arguments
    rcases terms 0 b source with ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,condition⟩ | ⟨leafCode,trap⟩
    · exact computed_args_loop_jump_entry_returns run scope dominated abi terms family source jump
        entered returned refines driver memorySem stable memory arguments
    · exact parameter_return_entry_frame run scope dominated abi family source ret
        entered returned refines driver memorySem stable memory arguments
    · exact computed_args_loop_branch_entry_returns run scope dominated abi terms family
        source term condition entered returned refines driver memorySem stable memory arguments
    · exact False.elim (entryKind b source leafCode trap)
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable world memory arguments
    rcases terms 0 b source with ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,condition⟩ | ⟨leafCode,trap⟩
    · exact computed_args_loop_jump_entry_traps run scope dominated abi terms family source jump
        entered trapped refines driver memorySem stable memory arguments
    · exact parameter_return_entry_trap_frame run scope dominated abi family source ret
        entered trapped refines driver memorySem stable memory arguments
    · exact computed_args_loop_branch_entry_traps run scope dominated abi terms family
        source term condition entered trapped refines driver memorySem stable memory arguments
    · exact False.elim (entryKind b source leafCode trap)

end Backend.Stock.Proof.ComparisonComputedArgsLoopCfg

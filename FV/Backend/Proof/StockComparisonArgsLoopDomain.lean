import FV.Backend.Proof.StockComparisonArgsLoopTrap
import FV.Backend.Proof.StockComparisonLoopDomain
import FV.Backend.Proof.StockParameterArgsLoopDomain

/-! The loop class with comparison branches and block arguments satisfies the per-successor
production domain (#140, T7b-9).

The entry block jumps, returns, or branches on a wide parameter or on a comparison, with any
block arguments. A branch entry establishes `GuardedScanRel` at the entry scan with the prelude of
its condition (`branch_entry_prelude`, T7b-7), which is `CarryRel` of the entry's empty definition
carry (`entry_carry`). A jump or branch entry then continues into nonentry blocks with
`comparison_args_loop_returns_below` / `comparison_args_loop_traps_below` at the entry run's
fuel; a return entry is `parameter_return_entry_frame`. The edge copies of a branch with block
arguments are nonempty per-successor vectors, so the class is not legacy-compatible: the result
is `Scalar.DomainAt`, as for the parameter loop class with block arguments (T7b-8). -/

namespace Backend.Stock.Proof.ComparisonArgsLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues
  Backend.Stock.Proof.ForwardSource Backend.Stock.Proof.LoopCarry Backend.Stock.Proof.ParameterCfg
  Backend.Stock.Proof.ParameterLoopCfg Backend.Stock.Proof.ComparisonLoopCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Instruction-zero ABI return simulation of a function of the class whose entry jumps. -/
theorem comparison_args_loop_jump_entry_returns {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : ArgsLoopTerms f)
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
      comparison_args_loop_returns_below run scope dominated abi terms family refines driver stable env cp fuel
        targetTag targetSource targetNonentry nextEvent nextBlock)
    (s := ⟨fr,[],cm⟩) rfl remaining atTerm (Control.source_defined_entry_frame dominated result.ctx entered)
    returned (entry_carry source guarded)
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- Instruction-zero ABI first-trap simulation of a function of the class whose entry jumps. -/
theorem comparison_args_loop_jump_entry_traps {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : ArgsLoopTerms f)
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
      comparison_args_loop_traps_below run scope dominated abi terms family refines driver stable env cp fuel
        targetTag targetSource targetNonentry nextEvent nextBlock)
    (s := ⟨fr,[],cm⟩) rfl remaining atTerm (Control.source_defined_entry_frame dominated result.ctx entered)
    trapped (entry_carry source guarded)
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- Instruction-zero ABI return simulation of a function of the class whose entry branches on a
wide parameter or on a comparison, with any block arguments. -/
theorem comparison_args_loop_branch_entry_returns {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : ArgsLoopTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {c : Nat} {yes no : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (term : entry.term = .brif c yes no) (condition : ParameterCondition f c ∨ ComparisonCondition f c)
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
      comparison_args_loop_returns_below run scope dominated abi terms family refines driver stable env cp fuel
        targetTag targetSource targetNonentry nextEvent nextBlock)
    (s := ⟨fr,[],cm⟩) rfl remaining atTerm (Control.source_defined_entry_frame dominated result.ctx entered)
    returned (entry_carry source guarded)
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- Instruction-zero ABI first-trap simulation of a function of the class whose entry branches
on a wide parameter or on a comparison, with any block arguments. -/
theorem comparison_args_loop_branch_entry_traps {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : ArgsLoopTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {c : Nat} {yes no : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (term : entry.term = .brif c yes no) (condition : ParameterCondition f c ∨ ComparisonCondition f c)
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
      comparison_args_loop_traps_below run scope dominated abi terms family refines driver stable env cp fuel
        targetTag targetSource targetNonentry nextEvent nextBlock)
    (s := ⟨fr,[],cm⟩) rfl remaining atTerm (Control.source_defined_entry_frame dominated result.ctx entered)
    trapped (entry_carry source guarded)
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- **The loop class with comparison branches and block arguments satisfies the per-successor
production domain.** Every block jumps (with any arguments), returns, branches with any arguments
on a wide parameter or on a comparison (`ComparisonCondition`: two wide parameters, a wide
parameter and an encodable 12-bit constant, or `eq`/`ne` of a wide parameter with zero), or,
outside the entry, ends in `trap`. No rank: targets may be loop headers, and back edges and self
loops are allowed, also when a branch passes block arguments on them. -/
theorem domainAt_of_comparison_args_loop_cfg {f : Clif.Function}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    (terms : ArgsLoopTerms f)
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
    · exact comparison_args_loop_jump_entry_returns run scope dominated abi terms family source jump
        entered returned refines driver memorySem stable memory arguments
    · exact parameter_return_entry_frame run scope dominated abi family source ret
        entered returned refines driver memorySem stable memory arguments
    · exact comparison_args_loop_branch_entry_returns run scope dominated abi terms family
        source term condition entered returned refines driver memorySem stable memory arguments
    · exact False.elim (entryKind b source leafCode trap)
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable world memory arguments
    rcases terms 0 b source with ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,condition⟩ | ⟨leafCode,trap⟩
    · exact comparison_args_loop_jump_entry_traps run scope dominated abi terms family source jump
        entered trapped refines driver memorySem stable memory arguments
    · exact parameter_return_entry_trap_frame run scope dominated abi family source ret
        entered trapped refines driver memorySem stable memory arguments
    · exact comparison_args_loop_branch_entry_traps run scope dominated abi terms family
        source term condition entered trapped refines driver memorySem stable memory arguments
    · exact False.elim (entryKind b source leafCode trap)

end Backend.Stock.Proof.ComparisonArgsLoopCfg

import FV.Backend.Proof.StockParameterLoopTrap
import FV.Backend.Proof.StockConditionalEntryPrelude
import FV.Backend.Proof.StockJumpEntryPrelude
import FV.Backend.Proof.StockParameterReturnEntry
import FV.Backend.Proof.StockParameterReturnPrelude
import FV.Backend.Proof.StockParameterCompatibility
import FV.Backend.Proof.StockScalarContract

/-! The loop parameter class satisfies the unchanged production domain (#140, T7b-5).

The entry block jumps, returns or branches on a wide parameter. Its prelude establishes
`GuardedScanRel` at the entry scan (`jump_entry_prelude`, `conditional_entry_prelude`), which is
`CarryRel` of the entry's empty definition carry (`entry_carry`). A jump or branch entry then
continues into nonentry blocks with `loop_returns_below` / `loop_traps_below` at the entry
run's fuel; a return entry is `parameter_return_entry_frame`. Per-edge compatibility is
`parameter_legacy_compatible_of_leaf`, which uses no rank. -/

namespace Backend.Stock.Proof.ParameterLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues
  Backend.Stock.Proof.ForwardSource Backend.Stock.Proof.LoopCarry Backend.Stock.Proof.ParameterCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The entry block carries nothing, so its `GuardedScanRel` is `CarryRel` of its definition
carry. -/
theorem entry_carry {f : Clif.Function} {result : Result} {entry : Clif.Block}
    (source : f.blocks[0]? = some entry) {ctx : Ctx} {bi : Nat} {MR : MemRelT} {st : State}
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result ctx bi MR st (0,fr,cm) ρ w) :
    Inherited.CarryRel f result ctx bi MR (defCarry f result 0) st (0,fr,cm) ρ w :=
  ⟨held,fun x kept => absurd kept (defCarry_entry source x)⟩

/-- Instruction-zero ABI return simulation of a loop-class function whose entry jumps. -/
theorem loop_jump_entry_returns {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : NonentryParameterLeafTerms f)
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
      loop_returns_below run scope dominated abi terms family refines driver stable env cp fuel
        targetTag targetSource targetNonentry nextEvent nextBlock)
    (s := ⟨fr,[],cm⟩) rfl remaining atTerm (Control.source_defined_entry_frame dominated result.ctx entered)
    returned (entry_carry source guarded)
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- Instruction-zero ABI first-trap simulation of a loop-class function whose entry jumps. -/
theorem loop_jump_entry_traps {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : NonentryParameterLeafTerms f)
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
      loop_traps_below run scope dominated abi terms family refines driver stable env cp fuel
        targetTag targetSource targetNonentry nextEvent nextBlock)
    (s := ⟨fr,[],cm⟩) rfl remaining atTerm (Control.source_defined_entry_frame dominated result.ctx entered)
    trapped (entry_carry source guarded)
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- Instruction-zero ABI return simulation of a loop-class function whose entry branches on a
wide parameter. -/
theorem loop_conditional_entry_returns {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : NonentryParameterLeafTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {c : Nat} {yes no : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (term : entry.term = .brif c yes no) (yesEmpty : yes.args = []) (noEmpty : no.args = [])
    (parameter : ParameterCondition f c)
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
  have metadata := parameter_metadata parameter dominated.ssa spec.build
  obtain ⟨_,remaining,atTerm⟩ := entry_frame_parts source entered
  obtain ⟨ρentry,wentry,path,guarded,allValues,sameWorld⟩ := conditional_entry_prelude run scope dominated spec
    term metadata.1 metadata.2 entered driver memorySem stable memory arguments
  have finished := conditional_carry_returns run scope dominated family refines driver stable spec tag
    term yesEmpty noEmpty parameter
    (fun targetTag targetSource targetNonentry nextEvent nextBlock =>
      loop_returns_below run scope dominated abi terms family refines driver stable env cp fuel
        targetTag targetSource targetNonentry nextEvent nextBlock)
    (s := ⟨fr,[],cm⟩) rfl remaining atTerm (Control.source_defined_entry_frame dominated result.ctx entered)
    returned (entry_carry source guarded)
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- Instruction-zero ABI first-trap simulation of a loop-class function whose entry branches on
a wide parameter. -/
theorem loop_conditional_entry_traps {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : NonentryParameterLeafTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {c : Nat} {yes no : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (term : entry.term = .brif c yes no) (yesEmpty : yes.args = []) (noEmpty : no.args = [])
    (parameter : ParameterCondition f c)
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
  have metadata := parameter_metadata parameter dominated.ssa spec.build
  obtain ⟨_,remaining,atTerm⟩ := entry_frame_parts source entered
  obtain ⟨ρentry,wentry,path,guarded,allValues,sameWorld⟩ := conditional_entry_prelude run scope dominated spec
    term metadata.1 metadata.2 entered driver memorySem stable memory arguments
  have finished := conditional_carry_traps run scope dominated family refines driver stable spec tag
    term yesEmpty noEmpty parameter
    (fun targetTag targetSource targetNonentry nextEvent nextBlock =>
      loop_traps_below run scope dominated abi terms family refines driver stable env cp fuel
        targetTag targetSource targetNonentry nextEvent nextBlock)
    (s := ⟨fr,[],cm⟩) rfl remaining atTerm (Control.source_defined_entry_frame dominated result.ctx entered)
    trapped (entry_carry source guarded)
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- **The loop parameter class satisfies the unchanged production domain.** Every block jumps
(with any arguments), returns, branches on a wide parameter with empty arguments, or, outside
the entry, ends in `trap`. No rank: jump and branch targets may be loop headers, and back
edges and self loops are allowed. -/
theorem domain_of_parameter_loop_cfg {f : Clif.Function}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    (terms : ParameterLeafTerms f)
    (entryKind : ∀ b,f.blocks[0]? = some b → ∀ c,b.term ≠ .trap c)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst) : Scalar.Domain f := by
  have entry : ∃ (b : Clif.Block),f.blocks[0]? = some b := by
    cases blocks : f.blocks with
    | nil => exact False.elim (scope.nonempty blocks)
    | cons b rest => exact ⟨b,by simp only [List.getElem?_cons_zero]⟩
  obtain ⟨b,source⟩ := entry
  have nonentry := parameter_leaf_terms_nonentry terms
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have compatible := parameter_legacy_compatible_of_leaf terms run scope dominated family
      refines driver stable env cp
    rcases terms 0 b source with
      ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,yesEmpty,noEmpty,parameter⟩ | ⟨leafCode,trap⟩
    · obtain ⟨ρ,simulation⟩ := loop_jump_entry_returns run scope dominated abi nonentry family source jump
        entered returned refines driver memorySem stable memory arguments
      exact ⟨ρ,simulation.legacyCompatible compatible⟩
    · obtain ⟨ρ,simulation⟩ := parameter_return_entry_frame run scope dominated abi family source ret
        entered returned refines driver memorySem stable memory arguments
      exact ⟨ρ,simulation.legacyCompatible compatible⟩
    · obtain ⟨ρ,simulation⟩ := loop_conditional_entry_returns run scope dominated abi nonentry family
        source term yesEmpty noEmpty parameter entered returned refines driver memorySem stable memory arguments
      exact ⟨ρ,simulation.legacyCompatible compatible⟩
    · exact False.elim (entryKind b source leafCode trap)
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have compatible := parameter_legacy_compatible_of_leaf terms run scope dominated family
      refines driver stable env cp
    rcases terms 0 b source with
      ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,yesEmpty,noEmpty,parameter⟩ | ⟨leafCode,trap⟩
    · obtain ⟨ρ,simulation⟩ := loop_jump_entry_traps run scope dominated abi nonentry family source jump
        entered trapped refines driver memorySem stable memory arguments
      exact ⟨ρ,simulation.legacyCompatible compatible⟩
    · obtain ⟨ρ,simulation⟩ := parameter_return_entry_trap_frame run scope dominated abi family source ret
        entered trapped refines driver memorySem stable memory arguments
      exact ⟨ρ,simulation.legacyCompatible compatible⟩
    · obtain ⟨ρ,simulation⟩ := loop_conditional_entry_traps run scope dominated abi nonentry family
        source term yesEmpty noEmpty parameter entered trapped refines driver memorySem stable memory arguments
      exact ⟨ρ,simulation.legacyCompatible compatible⟩
    · exact False.elim (entryKind b source leafCode trap)

end Backend.Stock.Proof.ParameterLoopCfg

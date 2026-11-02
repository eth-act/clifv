import FV.Backend.Proof.StockComparisonLoopTrap
import FV.Backend.Proof.StockComparisonLoopCompatibility
import FV.Backend.Proof.StockParameterLoopDomain
import FV.Backend.Proof.StockComparisonAt
import FV.Backend.Proof.StockComparisonImmAt
import FV.Backend.Proof.StockComparisonZeroAt

/-! The comparison loop class satisfies the unchanged production domain (#140, T7b-7).

`StockParameterLoopDomain` with `LoopTerms`. The entry block jumps, returns, or branches on a
wide parameter or on a comparison. A branch entry establishes `GuardedScanRel` at the entry scan
with the prelude of its condition (`branch_entry_prelude`: `conditional_entry_prelude`, or the
prelude of the comparison form), which is `CarryRel` of the empty entry carry (`entry_carry`).
A jump or branch entry then continues with `comparison_loop_returns_below` /
`comparison_loop_traps_below`; a return entry is `parameter_return_entry_frame`. Per-edge
compatibility is `loop_legacy_compatible`. -/

namespace Backend.Stock.Proof.ComparisonLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues
  Backend.Stock.Proof.ForwardSource Backend.Stock.Proof.LoopCarry Backend.Stock.Proof.ParameterCfg
  Backend.Stock.Proof.ParameterLoopCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The entry prelude of a branch on a parameter or on a comparison in any of the three forms. -/
theorem branch_entry_prelude {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {c : Nat} {yes no : Clif.BlockCall} {isem : Backend.Proof.Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b 0 0 c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no)
    (condition : ParameterCondition f c ∨ ComparisonCondition f c)
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
  rcases condition with parameter | comparison
  · have metadata := parameter_metadata parameter dominated.ssa spec.build
    exact conditional_entry_prelude run scope dominated spec termShape metadata.1 metadata.2 entered driver
      memorySem stable memory arguments
  · rcases comparison.metadata dominated spec.build with
      ⟨cc,ty,x,y,wide,origin,typeX,typeY,parameterX,parameterY⟩ |
      ⟨cc,ty,x,y,wide,ty',k,imm,origin,typeX,parameterX,constY,fits,nonzero⟩ |
      ⟨cc,ty,x,y,wide,ty',k,origin,typeX,parameterX,constY,equality,zero⟩
    · exact comparison_entry_prelude run scope dominated spec termShape origin wide typeX typeY parameterX
        parameterY entered driver memorySem stable memory arguments
    · exact comparison_imm_entry_prelude run scope dominated spec termShape origin wide typeX parameterX
        constY fits nonzero entered driver memorySem stable memory arguments
    · exact comparison_zero_entry_prelude run scope dominated spec termShape origin wide typeX parameterX
        constY equality zero entered driver memorySem stable memory arguments

/-- Instruction-zero ABI return simulation of a comparison-loop function whose entry jumps. -/
theorem comparison_loop_jump_entry_returns {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : LoopTerms f)
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
      comparison_loop_returns_below run scope dominated abi terms family refines driver stable env cp fuel
        targetTag targetSource targetNonentry nextEvent nextBlock)
    (s := ⟨fr,[],cm⟩) rfl remaining atTerm (Control.source_defined_entry_frame dominated result.ctx entered)
    returned (entry_carry source guarded)
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- Instruction-zero ABI first-trap simulation of a comparison-loop function whose entry
jumps. -/
theorem comparison_loop_jump_entry_traps {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : LoopTerms f)
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
      comparison_loop_traps_below run scope dominated abi terms family refines driver stable env cp fuel
        targetTag targetSource targetNonentry nextEvent nextBlock)
    (s := ⟨fr,[],cm⟩) rfl remaining atTerm (Control.source_defined_entry_frame dominated result.ctx entered)
    trapped (entry_carry source guarded)
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- Instruction-zero ABI return simulation of a comparison-loop function whose entry branches on
a wide parameter or on a comparison. -/
theorem comparison_loop_branch_entry_returns {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : LoopTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {c : Nat} {yes no : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (term : entry.term = .brif c yes no) (yesEmpty : yes.args = []) (noEmpty : no.args = [])
    (condition : ParameterCondition f c ∨ ComparisonCondition f c)
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
  have finished := branch_carry_returns run scope dominated family refines driver stable spec tag
    term yesEmpty noEmpty condition
    (fun targetTag targetSource targetNonentry nextEvent nextBlock =>
      comparison_loop_returns_below run scope dominated abi terms family refines driver stable env cp fuel
        targetTag targetSource targetNonentry nextEvent nextBlock)
    (s := ⟨fr,[],cm⟩) rfl remaining atTerm (Control.source_defined_entry_frame dominated result.ctx entered)
    returned (entry_carry source guarded)
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- Instruction-zero ABI first-trap simulation of a comparison-loop function whose entry
branches on a wide parameter or on a comparison. -/
theorem comparison_loop_branch_entry_traps {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : LoopTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {c : Nat} {yes no : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (term : entry.term = .brif c yes no) (yesEmpty : yes.args = []) (noEmpty : no.args = [])
    (condition : ParameterCondition f c ∨ ComparisonCondition f c)
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
  have finished := branch_carry_traps run scope dominated family refines driver stable spec tag
    term yesEmpty noEmpty condition
    (fun targetTag targetSource targetNonentry nextEvent nextBlock =>
      comparison_loop_traps_below run scope dominated abi terms family refines driver stable env cp fuel
        targetTag targetSource targetNonentry nextEvent nextBlock)
    (s := ⟨fr,[],cm⟩) rfl remaining atTerm (Control.source_defined_entry_frame dominated result.ctx entered)
    trapped (entry_carry source guarded)
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- **The comparison loop class satisfies the unchanged production domain.** Every block jumps
(with any arguments), returns, branches with empty arguments on a wide parameter or on a
comparison (`ComparisonCondition`: two wide parameters, a wide parameter and an encodable
12-bit constant, or `eq`/`ne` of a wide parameter with zero), or, outside the entry, ends in
`trap`. No rank: jump and branch targets may be loop headers. -/
theorem domain_of_comparison_loop_cfg {f : Clif.Function}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    (terms : LoopTerms f)
    (entryKind : ∀ b,f.blocks[0]? = some b → ∀ c,b.term ≠ .trap c)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst) : Scalar.Domain f := by
  have entry : ∃ (b : Clif.Block),f.blocks[0]? = some b := by
    cases blocks : f.blocks with
    | nil => exact False.elim (scope.nonempty blocks)
    | cons b rest => exact ⟨b,by simp only [List.getElem?_cons_zero]⟩
  obtain ⟨b,source⟩ := entry
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have compatible := loop_legacy_compatible terms run scope dominated family refines driver stable env cp
    rcases terms 0 b source with
      ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,yesEmpty,noEmpty,condition⟩ | ⟨leafCode,trap⟩
    · obtain ⟨ρ,simulation⟩ := comparison_loop_jump_entry_returns run scope dominated abi terms family source
        jump entered returned refines driver memorySem stable memory arguments
      exact ⟨ρ,simulation.legacyCompatible compatible⟩
    · obtain ⟨ρ,simulation⟩ := parameter_return_entry_frame run scope dominated abi family source ret
        entered returned refines driver memorySem stable memory arguments
      exact ⟨ρ,simulation.legacyCompatible compatible⟩
    · obtain ⟨ρ,simulation⟩ := comparison_loop_branch_entry_returns run scope dominated abi terms family
        source term yesEmpty noEmpty condition entered returned refines driver memorySem stable memory arguments
      exact ⟨ρ,simulation.legacyCompatible compatible⟩
    · exact False.elim (entryKind b source leafCode trap)
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have compatible := loop_legacy_compatible terms run scope dominated family refines driver stable env cp
    rcases terms 0 b source with
      ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,yesEmpty,noEmpty,condition⟩ | ⟨leafCode,trap⟩
    · obtain ⟨ρ,simulation⟩ := comparison_loop_jump_entry_traps run scope dominated abi terms family source
        jump entered trapped refines driver memorySem stable memory arguments
      exact ⟨ρ,simulation.legacyCompatible compatible⟩
    · obtain ⟨ρ,simulation⟩ := parameter_return_entry_trap_frame run scope dominated abi family source ret
        entered trapped refines driver memorySem stable memory arguments
      exact ⟨ρ,simulation.legacyCompatible compatible⟩
    · obtain ⟨ρ,simulation⟩ := comparison_loop_branch_entry_traps run scope dominated abi terms family
        source term yesEmpty noEmpty condition entered trapped refines driver memorySem stable memory arguments
      exact ⟨ρ,simulation.legacyCompatible compatible⟩
    · exact False.elim (entryKind b source leafCode trap)

end Backend.Stock.Proof.ComparisonLoopCfg

import FV.Backend.Proof.StockParameterArgsLeaf
import FV.Backend.Proof.StockConditionalSelectedAt

/-!
# Parameter CFG compositions with block arguments through critical edges

The parameter route's return and first-trap inductions, where a parameter branch may pass block
arguments to original or critical-edge successors. Each branch uses the order-free
argument-carrying compositions (`returning/trapping_selected_parameter_at`). Jump, return and
trap blocks are as before.
-/

namespace Backend.Stock.Proof.ParameterCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues Backend.Stock.Proof.ForwardSource
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem local_family {f : Clif.Function} {b : Clif.Block} {bi : Nat}
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst) (source : f.blocks[bi]? = some b) :
    ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
  intro stm member
  rcases family b (List.mem_of_getElem? source) stm member with
    (scalar | ⟨op,ty,x,y,shape⟩) | ⟨ty,x,shape⟩ | shape
  · exact LocalBody.LocalInst.of_pure (HighMulBody.family_pure scalar)
  all_goals simp [LocalBody.LocalInst,shape]

/-- Returns compose through jump blocks and parameter branches to return leaves; trap leaves
never return. -/
theorem any_nonentry_args_parameter_returns_of_leaf {f : Clif.Function} {result : Result} {rank : Nat → Nat}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (ranked : Ranked f rank) (terms : NonentryArgsParameterLeafTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    (env : Clif.Env) (cp : Clif.Program) {label bi : Nat} {b : Clif.Block}
    (tag : result.order.nodes[label]? = some (.original bi))
    (block : f.blocks[bi]? = some b) (nonentry : bi ≠ 0) :
    ∃ event,event ∈ result.blockScans.toList ∧ event.block = bi ∧
      ReturnsAt f result label bi b event isem MR env cp := by
  have nonempty : f.blocks.length ≠ 0 := fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
  obtain ⟨source,computed,size,bounded⟩ := stock_blockOrder_sourceTable (stock_lower_order run)
  have composed : ∀ n label bi b,result.order.nodes.size-label = n →
      result.order.nodes[label]? = some (.original bi) → f.blocks[bi]? = some b → bi ≠ 0 →
      ∃ event,event ∈ result.blockScans.toList ∧ event.block = bi ∧
        ReturnsAt f result label bi b event isem MR env cp := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro label bi b count tag block nonentry
      rcases terms bi b block nonentry with ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,parameter⟩ | ⟨leafCode,trap⟩
      · obtain ⟨spec⟩ := Control.stock_lower_jump_body_spec run scope dominated family tag block jump refines driver stable env cp
        obtain ⟨tl,targetLabel,targetIndex,targetNonentry,successors,targetTag⟩ :=
          CriticalOwners.jump_successor run scope tag block jump
        have sameTarget : spec.target = targetLabel := by
          have row : result.order.successors[label]! = #[targetLabel] := by
            simp only [getElem!_def,successors,Option.getD_some]
          have targets := spec.targets
          rw [row] at targets
          exact (List.cons.inj targets).1.symm
        have sourceRow := jump_source_row computed block jump targetIndex
        have edge : tl ∈ source[bi]!.toList := by rw [sourceRow]; simp
        have later := successor_labels (stock_lower_order run) nonempty ranked computed tag targetTag edge
        have targetBound := (Array.getElem?_eq_some_iff.mp targetTag).1
        have smaller : result.order.nodes.size-targetLabel < n := by omega
        obtain ⟨targetBlock,targetFound,targetSource⟩ := block?_of_idx targetIndex
        obtain ⟨next,nextEvent,nextBlock,nextReturns⟩ := ih _ smaller targetLabel tl targetBlock rfl targetTag targetSource targetNonentry
        have demand := successor_demand run scope ranked computed
          (by simpa only [spec.atBlock] using tag)
          (by simpa only [nextBlock] using targetTag)
          (by simpa only [spec.atBlock,nextBlock] using edge) spec.events nextEvent spec.split
        refine ⟨spec.core.scan,spec.events,spec.atBlock,?_⟩
        intro fuel s vals cm ρ w func callers remaining atTerm defined returned held
        have continuation : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
            s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body → s.frame.term = targetBlock.term →
            SourceDefinedAt f result.ctx tl 0 s.frame → Clif.runLoop env cp fuel s = .returned vals cm →
            GuardedScanRel f result next.ctx next.block MR next.output.state (0,s.frame,s.mem) ρ w →
            RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨spec.target,0,ρ,w⟩ (.returned vals cm) := by
          intro fuel s ρ w func callers remaining atTerm defined returned held
          simpa only [sameTarget] using nextReturns fuel s vals cm ρ w func callers remaining atTerm defined returned held
        have finished := Control.jump_body_returns_at run scope dominated family refines driver stable spec tag jump
          (by simpa only [sameTarget] using targetTag) targetIndex targetFound nextEvent nextBlock demand continuation
          callers remaining atTerm (by simpa only [spec.atBlock] using defined) returned held
        simpa only [jump_nonentry_prelude spec nonentry] using finished
      · obtain ⟨spec⟩ := CfgReturn.stock_lower_return_block_spec run scope dominated abi family tag block ret refines driver stable env cp
        refine ⟨spec.core.scan,spec.events,spec.atBlock,?_⟩
        intro fuel s vals cm ρ w func callers remaining atTerm defined returned held
        have finished := CfgReturnAt.return_block_returns_at run scope dominated abi family ret refines driver stable spec
          func callers remaining atTerm (by simpa only [spec.atBlock] using defined) returned held
        simpa only [spec.noPrelude nonentry] using finished
      · obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag block term refines driver stable env cp
        have metadata := parameter_metadata parameter dominated.ssa spec.build
        refine ⟨spec.core.scan,spec.events,spec.atBlock,?_⟩
        intro fuel s vals cm ρ w func callers remaining atTerm defined returned held
        have successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
            Nonempty (SuccessorReturn f result label bc isem MR env cp vals cm) := by
          intro index bc selected
          obtain ⟨tl,targetLabel,targetBlock,lookup,found,source,targetTag,targetNonentry,forward⟩ :=
            selected_ranked_target run scope ranked tag block selected
          have targetBound := (Array.getElem?_eq_some_iff.mp targetTag).1
          have smaller : result.order.nodes.size-targetLabel < n := by omega
          obtain ⟨next,member,atBlock,nextReturns⟩ :=
            ih _ smaller targetLabel tl targetBlock rfl targetTag source targetNonentry
          refine ⟨{
            index := tl
            targetLabel := targetLabel
            block := targetBlock
            event := next
            lookup := lookup
            found := found
            tag := targetTag
            member := member
            atBlock := atBlock
            forward := forward
            returns := ?_ }⟩
          intro fuel s ρ w func callers remaining atTerm defined returned held
          exact nextReturns fuel s vals cm ρ w func callers remaining atTerm defined returned held
        have finished := spec.returning_selected_parameter_at run scope dominated family refines driver stable
          tag term metadata.1 metadata.2 successors callers remaining atTerm
          (by simpa only [spec.atBlock] using defined) returned held
        simpa only [conditional_nonentry_prelude spec nonentry] using finished
      · obtain ⟨event,raw,preludeCode,events,atBlock,rawCode,noPrelude,placed⟩ :=
          ConditionalValues.stock_lower_trap_block_code run tag block trap
        refine ⟨event,events,atBlock,?_⟩
        intro fuel s vals cm ρ w func callers remaining atTerm defined returned held
        exact absurd returned (TrapBody.trap_source_noreturn (local_family family block) (j := 0)
          (by simpa using remaining) (atTerm.trans trap))
  exact composed _ label bi b rfl tag block nonentry

/-- First traps compose through jump blocks and parameter branches; a trap leaf traps in its
body or at its terminator. -/
theorem any_nonentry_args_parameter_traps_of_leaf {f : Clif.Function} {result : Result} {rank : Nat → Nat}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (ranked : Ranked f rank) (terms : NonentryArgsParameterLeafTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    (env : Clif.Env) (cp : Clif.Program) {label bi : Nat} {b : Clif.Block}
    (tag : result.order.nodes[label]? = some (.original bi))
    (block : f.blocks[bi]? = some b) (nonentry : bi ≠ 0) :
    ∃ event,event ∈ result.blockScans.toList ∧ event.block = bi ∧
      TrapsAt f result label bi b event isem MR env cp := by
  have nonempty : f.blocks.length ≠ 0 := fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
  obtain ⟨source,computed,size,bounded⟩ := stock_blockOrder_sourceTable (stock_lower_order run)
  have composed : ∀ n label bi b,result.order.nodes.size-label = n →
      result.order.nodes[label]? = some (.original bi) → f.blocks[bi]? = some b → bi ≠ 0 →
      ∃ event,event ∈ result.blockScans.toList ∧ event.block = bi ∧
        TrapsAt f result label bi b event isem MR env cp := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro label bi b count tag block nonentry
      rcases terms bi b block nonentry with ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,parameter⟩ | ⟨leafCode,trap⟩
      · obtain ⟨spec⟩ := Control.stock_lower_jump_body_spec run scope dominated family tag block jump refines driver stable env cp
        obtain ⟨tl,targetLabel,targetIndex,targetNonentry,successors,targetTag⟩ :=
          CriticalOwners.jump_successor run scope tag block jump
        have sameTarget : spec.target = targetLabel := by
          have row : result.order.successors[label]! = #[targetLabel] := by
            simp only [getElem!_def,successors,Option.getD_some]
          have targets := spec.targets
          rw [row] at targets
          exact (List.cons.inj targets).1.symm
        have sourceRow := jump_source_row computed block jump targetIndex
        have edge : tl ∈ source[bi]!.toList := by rw [sourceRow]; simp
        have later := successor_labels (stock_lower_order run) nonempty ranked computed tag targetTag edge
        have targetBound := (Array.getElem?_eq_some_iff.mp targetTag).1
        have smaller : result.order.nodes.size-targetLabel < n := by omega
        obtain ⟨targetBlock,targetFound,targetSource⟩ := block?_of_idx targetIndex
        obtain ⟨next,nextEvent,nextBlock,nextTraps⟩ := ih _ smaller targetLabel tl targetBlock rfl targetTag targetSource targetNonentry
        have demand := successor_demand run scope ranked computed
          (by simpa only [spec.atBlock] using tag)
          (by simpa only [nextBlock] using targetTag)
          (by simpa only [spec.atBlock,nextBlock] using edge) spec.events nextEvent spec.split
        refine ⟨spec.core.scan,spec.events,spec.atBlock,?_⟩
        intro fuel s code ρ w func callers remaining atTerm defined returned held
        have continuation : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
            s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body → s.frame.term = targetBlock.term →
            SourceDefinedAt f result.ctx tl 0 s.frame → Clif.runLoop env cp fuel s = .trapped code →
            GuardedScanRel f result next.ctx next.block MR next.output.state (0,s.frame,s.mem) ρ w →
            RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨spec.target,0,ρ,w⟩ (.trapped code) := by
          intro fuel s ρ w func callers remaining atTerm defined returned held
          simpa only [sameTarget] using nextTraps fuel s code ρ w func callers remaining atTerm defined returned held
        have finished := Control.jump_body_traps_at run scope dominated family refines driver stable spec tag jump
          (by simpa only [sameTarget] using targetTag) targetIndex targetFound nextEvent nextBlock demand continuation
          callers remaining atTerm (by simpa only [spec.atBlock] using defined) returned held
        simpa only [jump_nonentry_prelude spec nonentry] using finished
      · obtain ⟨spec⟩ := CfgReturn.stock_lower_return_block_spec run scope dominated abi family tag block ret refines driver stable env cp
        refine ⟨spec.core.scan,spec.events,spec.atBlock,?_⟩
        intro fuel s code ρ w func callers remaining atTerm defined returned held
        have finished := CfgReturnAt.return_block_traps_at run scope dominated family ret refines driver stable spec
          callers remaining atTerm returned held
        simpa only [spec.noPrelude nonentry] using finished
      · obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag block term refines driver stable env cp
        have metadata := parameter_metadata parameter dominated.ssa spec.build
        refine ⟨spec.core.scan,spec.events,spec.atBlock,?_⟩
        intro fuel s code ρ w func callers remaining atTerm defined returned held
        have successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
            Nonempty (SuccessorTrap f result label bc isem MR env cp code) := by
          intro index bc selected
          obtain ⟨tl,targetLabel,targetBlock,lookup,found,source,targetTag,targetNonentry,forward⟩ :=
            selected_ranked_target run scope ranked tag block selected
          have targetBound := (Array.getElem?_eq_some_iff.mp targetTag).1
          have smaller : result.order.nodes.size-targetLabel < n := by omega
          obtain ⟨next,member,atBlock,nextTraps⟩ :=
            ih _ smaller targetLabel tl targetBlock rfl targetTag source targetNonentry
          refine ⟨{
            index := tl
            targetLabel := targetLabel
            block := targetBlock
            event := next
            lookup := lookup
            found := found
            tag := targetTag
            member := member
            atBlock := atBlock
            forward := forward
            traps := ?_ }⟩
          intro fuel s ρ w func callers remaining atTerm defined returned held
          exact nextTraps fuel s code ρ w func callers remaining atTerm defined returned held
        have finished := spec.trapping_selected_parameter_at run scope dominated family refines driver stable
          tag term metadata.1 metadata.2 successors callers remaining atTerm
          (by simpa only [spec.atBlock] using defined) returned held
        simpa only [conditional_nonentry_prelude spec nonentry] using finished
      · obtain ⟨event,raw,preludeCode,events,atBlock,rawCode,noPrelude,placed⟩ :=
          ConditionalValues.stock_lower_trap_block_code run tag block trap
        refine ⟨event,events,atBlock,?_⟩
        intro fuel s code ρ w func callers remaining atTerm defined trapped held
        have finished := ConditionalValues.trap_block_traps_at run scope dominated family block trap
          refines driver stable events atBlock rawCode placed remaining atTerm trapped held
        simpa only [noPrelude nonentry] using finished
  exact composed _ label bi b rfl tag block nonentry

/-- A conditional successor can continue through arbitrarily many ranked jump/return blocks. -/
theorem any_args_parameter_return_successor_of_leaf {f : Clif.Function} {result : Result} {rank : Nat → Nat}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (ranked : Ranked f rank) (terms : NonentryArgsParameterLeafTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} {vals : List Clif.Val} {cm : Clif.Mem}
    {label : Nat} {bc : Clif.BlockCall} {tl targetLabel : Nat} {b : Clif.Block}
    (lookup : blockIdx? f bc.block = some tl) (found : f.block? bc.block = some b)
    (source : f.blocks[tl]? = some b)
    (tag : result.order.nodes[targetLabel]? = some (.original tl))
    (nonentry : tl ≠ 0) (forward : label < targetLabel) :
    Nonempty (SuccessorReturn f result label bc isem MR env cp vals cm) := by
  obtain ⟨event,member,atBlock,returns⟩ := any_nonentry_args_parameter_returns_of_leaf run scope dominated abi ranked terms family
    refines driver stable env cp tag source nonentry
  refine ⟨{
    index := tl
    targetLabel := targetLabel
    block := b
    event := event
    lookup := lookup
    found := found
    tag := tag
    member := member
    atBlock := atBlock
    forward := forward
    returns := ?_ }⟩
  intro fuel s ρ w func callers remaining atTerm defined terminal held
  exact returns fuel s vals cm ρ w func callers remaining atTerm defined terminal held

/-- A conditional successor can continue through arbitrarily many ranked jump/return blocks. -/
theorem any_args_parameter_trap_successor_of_leaf {f : Clif.Function} {result : Result} {rank : Nat → Nat}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (ranked : Ranked f rank) (terms : NonentryArgsParameterLeafTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} {trapCode : Clif.TrapCode}
    {label : Nat} {bc : Clif.BlockCall} {tl targetLabel : Nat} {b : Clif.Block}
    (lookup : blockIdx? f bc.block = some tl) (found : f.block? bc.block = some b)
    (source : f.blocks[tl]? = some b)
    (tag : result.order.nodes[targetLabel]? = some (.original tl))
    (nonentry : tl ≠ 0) (forward : label < targetLabel) :
    Nonempty (SuccessorTrap f result label bc isem MR env cp trapCode) := by
  obtain ⟨event,member,atBlock,traps⟩ := any_nonentry_args_parameter_traps_of_leaf run scope dominated abi ranked terms family
    refines driver stable env cp tag source nonentry
  refine ⟨{
    index := tl
    targetLabel := targetLabel
    block := b
    event := event
    lookup := lookup
    found := found
    tag := tag
    member := member
    atBlock := atBlock
    forward := forward
    traps := ?_ }⟩
  intro fuel s ρ w func callers remaining atTerm defined terminal held
  exact traps fuel s trapCode ρ w func callers remaining atTerm defined terminal held

/-- Instruction-zero ABI return simulation for any ranked scalar jump/return
source graph whose entry jumps onward. All blocks may have ordinary bodies and
inherited source values; no fixed chain length or forwarding premise is used. -/
theorem any_args_parameter_jump_return_frame_of_leaf {f : Clif.Function} {result : Result} {rank : Nat → Nat}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (ranked : Ranked f rank) (terms : NonentryArgsParameterLeafTerms f)
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
  obtain ⟨spec⟩ := Control.stock_lower_jump_body_spec run scope dominated family tag source jump refines driver stable env cp
  obtain ⟨tl,targetLabel,targetIndex,targetNonentry,successors,targetTag⟩ :=
    CriticalOwners.jump_successor run scope tag source jump
  have sameTarget : spec.target = targetLabel := by
    have row : result.order.successors[0]! = #[targetLabel] := by simp only [getElem!_def,successors,Option.getD_some]
    have targets := spec.targets
    rw [row] at targets
    exact (List.cons.inj targets).1.symm
  obtain ⟨targetBlock,targetFound,targetSource⟩ := block?_of_idx targetIndex
  obtain ⟨next,nextEvent,nextBlock,nextReturns⟩ := any_nonentry_args_parameter_returns_of_leaf run scope dominated abi ranked terms family refines driver stable
    env cp targetTag targetSource targetNonentry
  obtain ⟨table,computed,size,bounded⟩ := stock_blockOrder_sourceTable (stock_lower_order run)
  have edge : tl ∈ table[0]!.toList := by rw [jump_source_row computed source jump targetIndex]; simp
  have demand := successor_demand run scope ranked computed
    (by simpa only [spec.atBlock] using tag)
    (by simpa only [nextBlock] using targetTag)
    (by simpa only [spec.atBlock,nextBlock] using edge) spec.events nextEvent spec.split
  have remaining : fr.body = entry.body := by
    obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := entered
    have found' : f.blocks[0]? = some b := by simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using found
    cases Option.some.inj (found'.symm.trans source)
    exact congrArg Clif.Frame.body frame
  have atTerm : fr.term = entry.term := by
    obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := entered
    have found' : f.blocks[0]? = some b := by simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using found
    cases Option.some.inj (found'.symm.trans source)
    exact congrArg Clif.Frame.term frame
  obtain ⟨ρentry,wentry,path,guarded,allValues,sameWorld⟩ := Control.jump_entry_prelude run scope dominated spec
    entered driver memorySem stable memory arguments
  have continuation : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body → s.frame.term = targetBlock.term →
      SourceDefinedAt f result.ctx tl 0 s.frame → Clif.runLoop env cp fuel s = .returned vals outMem →
      GuardedScanRel f result next.ctx next.block MR next.output.state (0,s.frame,s.mem) ρ w →
      RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨spec.target,0,ρ,w⟩ (.returned vals outMem) := by
    intro fuel s ρ w func callers remaining atTerm defined returned held
    simpa only [sameTarget] using nextReturns fuel s vals outMem ρ w func callers remaining atTerm defined returned held
  have finished := Control.jump_body_returns_at run scope dominated family refines driver stable spec tag jump
    (by simpa only [sameTarget] using targetTag) targetIndex targetFound nextEvent nextBlock demand continuation
    rfl remaining atTerm
    (by simpa only [spec.atBlock] using Control.source_defined_entry_frame dominated result.ctx entered)
    returned guarded
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- Instruction-zero ABI first-trap simulation for any ranked scalar jump/return
source graph whose entry jumps onward. All blocks may have ordinary bodies and
inherited source values; no fixed chain length or forwarding premise is used. -/
theorem any_args_parameter_jump_trap_frame_of_leaf {f : Clif.Function} {result : Result} {rank : Nat → Nat}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (ranked : Ranked f rank) (terms : NonentryArgsParameterLeafTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {bc : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (jump : entry.term = .jump bc)
    {env : Clif.Env} {cp : Clif.Program} {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) {fuel : Nat} {code : Clif.TrapCode}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w0 : Arm.ArmState} (memory : MR fr.slots cm w0) (arguments : ArgsAtEntry F f.sig args w0) :
    ∃ ρ0,RunOkABIAt f result.code result.edgeArgs isem MR fr.slots ⟨0,0,ρ0,w0⟩ (.trapped code) := by
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨spec⟩ := Control.stock_lower_jump_body_spec run scope dominated family tag source jump refines driver stable env cp
  obtain ⟨tl,targetLabel,targetIndex,targetNonentry,successors,targetTag⟩ :=
    CriticalOwners.jump_successor run scope tag source jump
  have sameTarget : spec.target = targetLabel := by
    have row : result.order.successors[0]! = #[targetLabel] := by simp only [getElem!_def,successors,Option.getD_some]
    have targets := spec.targets
    rw [row] at targets
    exact (List.cons.inj targets).1.symm
  obtain ⟨targetBlock,targetFound,targetSource⟩ := block?_of_idx targetIndex
  obtain ⟨next,nextEvent,nextBlock,nextTraps⟩ := any_nonentry_args_parameter_traps_of_leaf run scope dominated abi ranked terms family refines driver stable
    env cp targetTag targetSource targetNonentry
  obtain ⟨table,computed,size,bounded⟩ := stock_blockOrder_sourceTable (stock_lower_order run)
  have edge : tl ∈ table[0]!.toList := by rw [jump_source_row computed source jump targetIndex]; simp
  have demand := successor_demand run scope ranked computed
    (by simpa only [spec.atBlock] using tag)
    (by simpa only [nextBlock] using targetTag)
    (by simpa only [spec.atBlock,nextBlock] using edge) spec.events nextEvent spec.split
  have remaining : fr.body = entry.body := by
    obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := entered
    have found' : f.blocks[0]? = some b := by simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using found
    cases Option.some.inj (found'.symm.trans source)
    exact congrArg Clif.Frame.body frame
  have atTerm : fr.term = entry.term := by
    obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := entered
    have found' : f.blocks[0]? = some b := by simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using found
    cases Option.some.inj (found'.symm.trans source)
    exact congrArg Clif.Frame.term frame
  obtain ⟨ρentry,wentry,path,guarded,allValues,sameWorld⟩ := Control.jump_entry_prelude run scope dominated spec
    entered driver memorySem stable memory arguments
  have continuation : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body → s.frame.term = targetBlock.term →
      SourceDefinedAt f result.ctx tl 0 s.frame → Clif.runLoop env cp fuel s = .trapped code →
      GuardedScanRel f result next.ctx next.block MR next.output.state (0,s.frame,s.mem) ρ w →
      RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨spec.target,0,ρ,w⟩ (.trapped code) := by
    intro fuel s ρ w func callers remaining atTerm defined returned held
    simpa only [sameTarget] using nextTraps fuel s code ρ w func callers remaining atTerm defined returned held
  have finished := Control.jump_body_traps_at run scope dominated family refines driver stable spec tag jump
    (by simpa only [sameTarget] using targetTag) targetIndex targetFound nextEvent nextBlock demand continuation
    rfl remaining atTerm
    (by simpa only [spec.atBlock] using Control.source_defined_entry_frame dominated result.ctx entered)
    returned guarded
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

end Backend.Stock.Proof.ParameterCfg

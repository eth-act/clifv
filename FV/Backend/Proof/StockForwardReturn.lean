import FV.Backend.Proof.StockCfgReturnBlockAt
import FV.Backend.Proof.StockForwardDemand
import FV.Backend.Proof.StockCriticalOwners
import FV.Backend.Proof.StockCfgJumpReturnAt
import FV.Backend.Proof.LowerLoopRun

namespace Backend.Stock.Proof.ForwardSource
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Source-only control-flow class; jump destinations and bodies are unrestricted
apart from the separately stated ranking and scalar-body conditions. -/
def JumpReturnBlocks (f : Clif.Function) : Prop :=
  ∀ b ∈ f.blocks,(∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs)

/-- Restrict only continuations; the entry may be conditional. -/
def NonentryJumpReturnBlocks (f : Clif.Function) : Prop :=
  ∀ bi b,f.blocks[bi]? = some b → bi ≠ 0 →
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs)

/-- Instruction-zero return simulation at an actual retained nonentry scan. -/
def ReturnsAt (f : Clif.Function) (result : Result) (label bi : Nat) (b : Clif.Block)
    (event : BlockScanEvent) (isem : Backend.Proof.Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) : Prop :=
  ∀ (fuel : Nat) (s : Clif.State) (vals : List Clif.Val) (cm : Clif.Mem)
    (ρ : Nat → CV) (w : Arm.ArmState),
    s.frame.func = f → s.callers = [] → s.frame.body = b.body → s.frame.term = b.term →
    SourceDefinedAt f result.ctx bi 0 s.frame → Clif.runLoop env cp fuel s = .returned vals cm →
    GuardedScanRel f result event.ctx event.block MR event.output.state (0,s.frame,s.mem) ρ w →
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨label,0,ρ,w⟩ (.returned vals cm)

/-- Actual single-jump mapping preserves its selected original source target. -/
theorem jump_source_row {f : Clif.Function} {source : Array (Array Nat)}
    (computed : stockSourceTable f = .ok source) {bi ti : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (block : f.blocks[bi]? = some b) (jump : b.term = .jump bc)
    (target : blockIdx? f bc.block = some ti) : source[bi]! = #[ti] := by
  obtain ⟨ss,mapped,found⟩ := (Prep.amapM_ok computed).2 bi b (by simpa using block)
  rw [jump] at mapped
  have identified : f.blocks.findIdx? (·.id == bc.block) = some ti := target
  have same : ss = #[ti] := by
    simpa [destinations,Array.mapM_eq_mapM_toList,identified] using mapped.symm
  simp only [getElem!_def,found,Option.getD_some,same]

private theorem assemble_nonentry_code {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {bi label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {params : List Nat} {uses : Array UseState} {code : Array MInst} {block : VBlock}
    (nonentry : bi ≠ 0)
    (run : assembleOriginalBlock ctx f b bi label targets outgoing params uses code = .ok block) :
    block.insts = code := by
  unfold assembleOriginalBlock at run
  dsimp only at run
  simp only [show (bi == 0) = false from by simp [nonentry],Bool.false_eq_true,ite_false] at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; rfl

theorem jump_nonentry_prelude {f : Clif.Function} {result : Result} {b : Clif.Block}
    {label bi : Nat} {bc : Clif.BlockCall} {isem : Backend.Proof.Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program}
    (spec : Control.JumpBodySpec f result b label bi bc isem MR env cp) (nonentry : bi ≠ 0) :
    spec.preludeCode.size = 0 := by
  have code := assemble_nonentry_code nonentry spec.assembled
  have sizes := congrArg Array.size (spec.rawCode.symm.trans code)
  simp only [Array.size_append] at sizes
  omega

/-- Compose arbitrary many ranked scalar jump blocks and a return from their
actual retained scans. The induction follows the real node labels; neither a
fixed block count nor a source result-forwarding restriction is required. -/
theorem nonentry_returns_of_termsAt {f : Clif.Function} {result : Result} {rank : Nat → Nat}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (ranked : Ranked f rank) (terms : NonentryJumpReturnBlocks f)
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
      rcases terms bi b block nonentry with ⟨bc,jump⟩ | ⟨xs,ret⟩
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
  exact composed _ label bi b rfl tag block nonentry

/-- The original all-block variant is preserved. -/
theorem nonentry_returns {f : Clif.Function} {result : Result} {rank : Nat → Nat}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (ranked : Ranked f rank) (terms : JumpReturnBlocks f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    (env : Clif.Env) (cp : Clif.Program) {label bi : Nat} {b : Clif.Block}
    (tag : result.order.nodes[label]? = some (.original bi))
    (block : f.blocks[bi]? = some b) (nonentry : bi ≠ 0) :
    ∃ event,event ∈ result.blockScans.toList ∧ event.block = bi ∧
      ReturnsAt f result label bi b event isem MR env cp := by
  exact nonentry_returns_of_termsAt run scope dominated abi ranked
    (fun bi b found _ => terms b (List.mem_of_getElem? found)) family
    refines driver stable env cp tag block nonentry

end Backend.Stock.Proof.ForwardSource

import FV.Backend.Proof.StockLinearCfgShape
import FV.Backend.Proof.StockLinearCfgDemand
import FV.Backend.Proof.StockCfgReturnTrapAt
import FV.Backend.Proof.StockCfgJumpTrapAt
import FV.Backend.Proof.StockJumpEntryPrelude

namespace Backend.Stock.Proof.LinearCfg
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

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

private theorem nonentry_prelude {f : Clif.Function} {result : Result} {b : Clif.Block}
    {label bi : Nat} {bc : Clif.BlockCall} {isem : Backend.Proof.Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program}
    (spec : Control.JumpBodySpec f result b label bi bc isem MR env cp) (nonentry : bi ≠ 0) :
    spec.preludeCode.size = 0 := by
  have code := assemble_nonentry_code nonentry spec.assembled
  have sizes := congrArg Array.size (spec.rawCode.symm.trans code)
  simp only [Array.size_append] at sizes
  omega

/-- Instruction-zero first-trap simulation for a complete three-block scalar
chain, including local traps in either jumping block or the final block. -/
theorem scalar_trap_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {entry middle target : Clif.Block}
    {first second : Clif.BlockCall} {xs : List Nat}
    (blocks : f.blocks = [entry,middle,target])
    (firstJump : entry.term = .jump first) (secondJump : middle.term = .jump second)
    (ret : target.term = .ret xs)
    (firstDestination : first.block = middle.id) (secondDestination : second.block = target.id)
    (entryMiddle : entry.id ≠ middle.id) (entryTarget : entry.id ≠ target.id)
    (middleTarget : middle.id ≠ target.id)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {env : Clif.Env} {cp : Clif.Program} {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {fuel : Nat} {code : Clif.TrapCode}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w0 : Arm.ArmState} (memory : MR fr.slots cm w0) (arguments : ArgsAtEntry F f.sig args w0) :
    ∃ ρ0,RunOkABIAt f result.code result.edgeArgs isem MR fr.slots ⟨0,0,ρ0,w0⟩ (.trapped code) := by
  have source : f.blocks[0]? = some entry := by simp [blocks]
  have middleSource : f.blocks[1]? = some middle := by simp [blocks]
  have targetSource : f.blocks[2]? = some target := by simp [blocks]
  have order : result.order = ⟨#[.original 0,.original 1,.original 2],#[#[1],#[2],#[]]⟩ :=
    Except.ok.inj ((stock_lower_order run).symm.trans (block_order_three blocks firstJump secondJump ret
      firstDestination secondDestination entryMiddle entryTarget middleTarget))
  have entryTag : result.order.nodes[0]? = some (.original 0) := by simp [order]
  have middleTag : result.order.nodes[1]? = some (.original 1) := by simp [order]
  have targetTag : result.order.nodes[2]? = some (.original 2) := by simp [order]
  obtain ⟨es⟩ := Control.stock_lower_jump_body_spec run scope dominated family entryTag source firstJump
    refines driver stable env cp
  obtain ⟨ms⟩ := Control.stock_lower_jump_body_spec run scope dominated family middleTag middleSource secondJump
    refines driver stable env cp
  obtain ⟨ts⟩ := CfgReturn.stock_lower_return_block_spec run scope dominated abi family targetTag
    targetSource ret refines driver stable env cp
  have et : es.target = 1 := by
    have targets := es.targets
    rw [order] at targets
    exact (List.cons.inj targets).1.symm
  have mt : ms.target = 2 := by
    have targets := ms.targets
    rw [order] at targets
    exact (List.cons.inj targets).1.symm
  have firstIndex : blockIdx? f first.block = some 1 := by
    simp [blockIdx?,blocks,firstDestination,List.findIdx?_cons,entryMiddle,Ne.symm entryMiddle]
  have secondIndex : blockIdx? f second.block = some 2 := by
    simp [blockIdx?,blocks,secondDestination,List.findIdx?_cons,entryTarget,Ne.symm entryTarget,middleTarget,Ne.symm middleTarget]
  have middleFound : f.block? first.block = some middle := by
    simp [Clif.Function.block?,blocks,firstDestination,entryMiddle,Ne.symm entryMiddle]
  have targetFound : f.block? second.block = some target := by
    simp [Clif.Function.block?,blocks,secondDestination,entryTarget,Ne.symm entryTarget,middleTarget,Ne.symm middleTarget]
  have em := jump_successor_demand run scope blocks firstJump secondJump order es.events ms.events
    (Or.inl ⟨es.atBlock,ms.atBlock⟩) es.split
  have mm := jump_successor_demand run scope blocks firstJump secondJump order ms.events ts.events
    (Or.inr ⟨ms.atBlock,ts.atBlock⟩) ms.split
  have targetReturns : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = target.body → s.frame.term = target.term →
      SourceDefinedAt f result.ctx 2 0 s.frame → Clif.runLoop env cp fuel s = .trapped code →
      GuardedScanRel f result ts.core.scan.ctx ts.core.scan.block MR ts.core.scan.output.state
        (0,s.frame,s.mem) ρ w → RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
          ⟨ms.target,0,ρ,w⟩ (.trapped code) := by
    intro fuel s ρ w func callers remaining atTerm defined returned held
    have finished := CfgReturnAt.return_block_traps_at run scope dominated family ret refines driver stable ts
      callers remaining atTerm returned held
    simpa only [mt,ts.noPrelude (by decide)] using finished
  have middleReturns : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = middle.body → s.frame.term = middle.term →
      SourceDefinedAt f result.ctx 1 0 s.frame → Clif.runLoop env cp fuel s = .trapped code →
      GuardedScanRel f result ms.core.scan.ctx ms.core.scan.block MR ms.core.scan.output.state
        (0,s.frame,s.mem) ρ w → RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
          ⟨es.target,0,ρ,w⟩ (.trapped code) := by
    intro fuel s ρ w func callers remaining atTerm defined returned held
    have finished := Control.jump_body_traps_at run scope dominated family refines driver stable ms middleTag secondJump
      (by simpa only [mt] using targetTag) secondIndex targetFound ts.events ts.atBlock mm targetReturns
      callers remaining atTerm (by simpa only [ms.atBlock] using defined) returned held
    simpa only [et,nonentry_prelude ms (by decide)] using finished
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
  obtain ⟨ρentry,wentry,path,guarded,allValues,sameWorld⟩ := Control.jump_entry_prelude run scope dominated
    es entered driver memorySem stable memory arguments
  have finished := Control.jump_body_traps_at run scope dominated family refines driver stable es entryTag firstJump
    (by simpa only [et] using middleTag) firstIndex middleFound ms.events ms.atBlock em middleReturns
    rfl remaining atTerm
    (by simpa only [es.atBlock] using Control.source_defined_entry_frame dominated result.ctx entered)
    returned guarded
  exact ⟨entrySeed es.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

end Backend.Stock.Proof.LinearCfg

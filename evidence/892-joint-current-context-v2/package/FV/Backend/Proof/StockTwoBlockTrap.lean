import FV.Backend.Proof.StockCfgReturnTrapEdgeAt
import FV.Backend.Proof.StockJumpDemand
import FV.Backend.Proof.LowerShapeOkFacts
import FV.Backend.Proof.StockJumpEntryPrelude
import FV.Backend.Proof.StockComputedCfg
import FV.Backend.Proof.StockTwoBlockShape
import FV.Backend.Proof.StockInheritedJumpTrap

namespace Backend.Stock.Proof.TwoBlock
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Instruction-zero traps are attributed to the actual entry body or to
its later successor, retaining the complete entry ABI and original trap code. -/
theorem entry_division_trap_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {entry target : Clif.Block} {bc : Clif.BlockCall} {xs : List Nat}
    (blocks : f.blocks = [entry,target]) (jump : entry.term = .jump bc) (ret : target.term = .ret xs)
    (destination : bc.block = target.id) (different : entry.id ≠ target.id)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    (entryFamily : ∀ stm ∈ entry.body,(∃ ty imm,stm.inst = .iconst ty imm) ∨
      (∃ op ty x y,stm.inst = .div op ty x y) ∨ stm.inst = .nop)
    (forwarded : ∀ stm ∈ entry.body,∀ x ∈ stm.results,x ∈ bc.args)
    {env : Clif.Env} {cp : Clif.Program} {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w0 : Arm.ArmState} (memory : MR fr.slots cm w0) (arguments : ArgsAtEntry F f.sig args w0) :
    ∃ ρ0,RunOkABIAt f result.code result.edgeArgs isem MR fr.slots ⟨0,0,ρ0,w0⟩ (.trapped code) := by
  have source : f.blocks[0]? = some entry := by rw [blocks]; rfl
  have targetSource : f.blocks[1]? = some target := by rw [blocks]; rfl
  have sourceEntry := entered
  have remaining : fr.body = entry.body := by
    obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := sourceEntry
    have found' : f.blocks[0]? = some b := by simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using found
    cases Option.some.inj (found'.symm.trans source)
    exact congrArg Clif.Frame.body frame
  have atTerm : fr.term = entry.term := by
    obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := sourceEntry
    have found' : f.blocks[0]? = some b := by simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using found
    cases Option.some.inj (found'.symm.trans source)
    exact congrArg Clif.Frame.term frame
  have order : result.order = ⟨#[.original 0,.original 1],#[#[1],#[]]⟩ :=
    Except.ok.inj ((stock_lower_order run).symm.trans (block_order blocks jump ret destination different))
  have tag : result.order.nodes[0]? = some (.original 0) := by rw [order]; rfl
  obtain ⟨spec⟩ := Control.stock_lower_jump_body_spec run scope dominated family tag source jump
    refines driver stable env cp
  have available : ∀ x,x ∈ entry.params.map (·.1) →
      x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0 := by
    intro x parameter
    rw [spec.atBlock]
    apply (mem_av source).mpr
    refine ⟨.inl parameter,?_⟩
    rintro ⟨j,stm,_,statement,defined⟩
    exact param_not_result dominated.ssa (List.mem_of_getElem? source) (List.mem_of_getElem? source)
      parameter (List.mem_flatMap.mpr ⟨stm,List.mem_of_getElem? statement,defined⟩)
  obtain ⟨ρentry,wentry,entryPath,guarded,allValues,sameWorld⟩ := Control.jump_entry_prelude run scope dominated
    spec sourceEntry driver memorySem stable memory arguments
  have formats : ∀ block ∈ f.blocks,∀ stm ∈ block.body,CastComplete.MemoryFormat stm.inst := by
    intro block member stm present
    exact MaskBody.family_formats (family block member stm present)
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have segment : SegAt {spec.raw with
      insts := spec.raw.insts.map (·.mapRegs resolve)
      params := spec.raw.params.map resolve
      branchArgs := spec.raw.branchArgs.map resolve}
      spec.preludeCode.size (spec.core.code.toList.map (·.mapRegs resolve)) := by
    intro k hk
    have bound : k < spec.core.code.size := by simpa using hk
    simp only [spec.rawCode,Array.map_append]
    rw [Array.getElem?_append_right (by simpa only [Array.size_map] using Nat.le_add_right spec.preludeCode.size k)]
    simp only [Array.size_map,Nat.add_sub_cancel_left]
    simp [bound]
  have carry :=
    Inherited.division_jump_carry_traps_or_continues_defined run scope dominated refines driver stable
      spec jump formats entryFamily available remaining atTerm trapped
      ⟨guarded,allValues.mono (fun _ _ => True.intro)⟩
      (by simpa only [spec.atBlock] using Control.source_defined_entry_frame dominated result.ctx entered)
  rcases carry with failed | continuation
  · obtain ⟨offset,i,ops,ρ',w',outs,final,execution,coded⟩ := failed
    obtain ⟨path,bound,inst,operands,semantics,arity,control⟩ :=
      seqRun_stop_starAt (edges := result.edgeArgs) spec.placed segment execution
    have finished : RunOkABIAt f result.code result.edgeArgs isem MR fr.slots
        ⟨0,spec.preludeCode.size,ρentry,wentry⟩ (.trapped code) :=
      ⟨0,spec.preludeCode.size+offset,ρ',w',_,i,ops,outs,final,path,spec.placed,
        inst,operands,semantics,coded⟩
    exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix entryPath finished⟩
  · obtain ⟨t,left,ρ,w,total,continued,empty,frame,sourceFrame,atJump,executed,post,tDefined⟩ := continuation
    have targetValue : spec.target = 1 := by
      have labels := spec.targets
      rw [order] at labels
      exact (List.cons.inj labels).1.symm
    have targetTag : result.order.nodes[spec.target]? = some (.original 1) := by rw [order,targetValue]; rfl
    obtain ⟨returnSpec⟩ := CfgReturn.stock_lower_return_block_spec run scope dominated abi family targetTag
      targetSource ret refines driver stable env cp
    have targetIndex : blockIdx? f bc.block = some 1 := by
      simp [blockIdx?,blocks,destination,List.findIdx?_cons,different,Ne.symm different]
    have targetFound : f.block? bc.block = some target := by
      simp [Clif.Function.block?,blocks,destination,different,Ne.symm different]
    cases left with
    | zero => cases continued
    | succ left =>
      have crossing : ∃ fr',Clif.enterBlock t.frame bc = .ok fr' := by
        cases call : Clif.enterBlock t.frame bc with
        | ok fr' => exact ⟨fr',rfl⟩
        | trap code => exact False.elim (enterBlock_ne_trap call)
        | stuck message =>
          rw [Clif.runLoop_succ] at continued
          simp only [Clif.step,empty,atJump,Clif.stepTerm,call,Clif.StepResult.ofRes] at continued
          cases continued
      obtain ⟨fr',crossed⟩ := crossing
      have outgoing := Control.stock_jump_body_argument_values run scope dominated spec jump targetTag post.1
      have carried : ValuesHeld (fun x => x ∈ entry.params.map (·.1)) result.ctx t.frame
          (fun k => ρ (aliasNum result.final.alias k)) := by
        intro x member v read
        obtain ⟨key,mapped,value⟩ := post.2 x member v read
        refine ⟨key,?_,value⟩
        rw [← (stock_lower_record_context run scope spec.events).2.1 x]
        exact mapped
      have successor : result.order.successors[0]![0]? = some spec.target := by rw [order,targetValue]; rfl
      have nextReturned : Clif.runLoop env cp left ⟨fr',[],t.mem⟩ = .trapped code := by
        rw [Clif.runLoop_succ] at continued
        have callers : t.callers = [] := frame.1.trans rfl
        simpa only [Clif.step,empty,atJump,Clif.stepTerm,crossed,Clif.StepResult.ofRes,callers] using continued
      obtain ⟨ρ',copied,finished⟩ := CfgReturnAt.direct_successor_traps_at run scope dominated abi family
        spec.events tag source (by simp [jump,dests]) successor targetTag targetIndex targetFound spec.atBlock
        refines driver stable ret returnSpec post.1 (by simpa only [spec.atBlock] using tDefined) crossed (by
          intro x needed
          rcases needed with argument | ⟨available,notParameter⟩
          · exact outgoing x argument
          · rcases successor_entry_coverage blocks forwarded available notParameter with parameter | argument
            · exact carried x parameter
            · exact outgoing x argument) nextReturned
      have last : spec.preludeCode.size+spec.body.code.size+1 =
          (spec.raw.insts.map (·.mapRegs resolve)).size := by
        simp only [spec.rawCode,spec.bodyCode,Array.size_map,Array.size_append,Array.size_singleton]
        omega
      obtain ⟨ps,cfg⟩ := stock_lower_computed_cfg run scope
      have actualSuccessor : succOf result.code 0 0 = some spec.target := by
        simp only [succOf,cfg]
        rw [order,targetValue]
        rfl
      have path := seqRun_goto_starAt spec.placed segment executed last actualSuccessor
        (by simpa only [vdefUpd,writeV,List.foldl_nil,Array.toList_empty,List.filter_nil,List.zip_nil_left] using copied)
      have whole := RunOkABIAt.prefix entryPath (RunOkABIAt.prefix path finished)
      exact ⟨entrySeed spec.core.scan.ctx fr,by simpa only [frame.2.2.1] using whole⟩

/-- Complete instruction-zero return simulation for a two-block source class.
The entry constants/nops may retain inherited parameters; all its new results
are forwarded. The return block uses the entire existing scalar/division/mask
family. Every register, source, graph and machine placement fact is derived
from the original execution and actual compiler result. -/
theorem entry_trap_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {entry target : Clif.Block} {bc : Clif.BlockCall} {xs : List Nat}
    (blocks : f.blocks = [entry,target]) (jump : entry.term = .jump bc) (ret : target.term = .ret xs)
    (destination : bc.block = target.id) (different : entry.id ≠ target.id)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    (quiet : ∀ stm ∈ entry.body,(∃ ty imm,stm.inst = .iconst ty imm) ∨ stm.inst = .nop)
    (forwarded : ∀ stm ∈ entry.body,∀ x ∈ stm.results,x ∈ bc.args)
    {env : Clif.Env} {cp : Clif.Program} {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w0 : Arm.ArmState} (memory : MR fr.slots cm w0) (arguments : ArgsAtEntry F f.sig args w0) :
    ∃ ρ0,RunOkABIAt f result.code result.edgeArgs isem MR fr.slots ⟨0,0,ρ0,w0⟩ (.trapped code) := by
  apply entry_division_trap_frame run scope dominated abi blocks jump ret destination different family
    ?_ forwarded entered trapped refines driver memorySem stable memory arguments
  intro stm member
  rcases quiet stm member with constant | nop
  · exact Or.inl constant
  · exact Or.inr (Or.inr nop)


/-- Broader scalar-entry variant; original interfaces remain available. -/
theorem entry_scalar_trap_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {entry target : Clif.Block} {bc : Clif.BlockCall} {xs : List Nat}
    (blocks : f.blocks = [entry,target]) (jump : entry.term = .jump bc) (ret : target.term = .ret xs)
    (destination : bc.block = target.id) (different : entry.id ≠ target.id)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    (entryFamily : ∀ stm ∈ entry.body,MaskBody.Family stm.inst)
    (forwarded : ∀ stm ∈ entry.body,∀ x ∈ stm.results,x ∈ bc.args)
    {env : Clif.Env} {cp : Clif.Program} {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w0 : Arm.ArmState} (memory : MR fr.slots cm w0) (arguments : ArgsAtEntry F f.sig args w0) :
    ∃ ρ0,RunOkABIAt f result.code result.edgeArgs isem MR fr.slots ⟨0,0,ρ0,w0⟩ (.trapped code) := by
  have source : f.blocks[0]? = some entry := by rw [blocks]; rfl
  have targetSource : f.blocks[1]? = some target := by rw [blocks]; rfl
  have sourceEntry := entered
  have remaining : fr.body = entry.body := by
    obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := sourceEntry
    have found' : f.blocks[0]? = some b := by simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using found
    cases Option.some.inj (found'.symm.trans source)
    exact congrArg Clif.Frame.body frame
  have atTerm : fr.term = entry.term := by
    obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := sourceEntry
    have found' : f.blocks[0]? = some b := by simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using found
    cases Option.some.inj (found'.symm.trans source)
    exact congrArg Clif.Frame.term frame
  have order : result.order = ⟨#[.original 0,.original 1],#[#[1],#[]]⟩ :=
    Except.ok.inj ((stock_lower_order run).symm.trans (block_order blocks jump ret destination different))
  have tag : result.order.nodes[0]? = some (.original 0) := by rw [order]; rfl
  obtain ⟨spec⟩ := Control.stock_lower_jump_body_spec run scope dominated family tag source jump
    refines driver stable env cp
  have available : ∀ x,x ∈ entry.params.map (·.1) →
      x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0 := by
    intro x parameter
    rw [spec.atBlock]
    apply (mem_av source).mpr
    refine ⟨.inl parameter,?_⟩
    rintro ⟨j,stm,_,statement,defined⟩
    exact param_not_result dominated.ssa (List.mem_of_getElem? source) (List.mem_of_getElem? source)
      parameter (List.mem_flatMap.mpr ⟨stm,List.mem_of_getElem? statement,defined⟩)
  obtain ⟨ρentry,wentry,entryPath,guarded,allValues,sameWorld⟩ := Control.jump_entry_prelude run scope dominated
    spec sourceEntry driver memorySem stable memory arguments
  have formats : ∀ block ∈ f.blocks,∀ stm ∈ block.body,CastComplete.MemoryFormat stm.inst := by
    intro block member stm present
    exact MaskBody.family_formats (family block member stm present)
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have segment : SegAt {spec.raw with
      insts := spec.raw.insts.map (·.mapRegs resolve)
      params := spec.raw.params.map resolve
      branchArgs := spec.raw.branchArgs.map resolve}
      spec.preludeCode.size (spec.core.code.toList.map (·.mapRegs resolve)) := by
    intro k hk
    have bound : k < spec.core.code.size := by simpa using hk
    simp only [spec.rawCode,Array.map_append]
    rw [Array.getElem?_append_right (by simpa only [Array.size_map] using Nat.le_add_right spec.preludeCode.size k)]
    simp only [Array.size_map,Nat.add_sub_cancel_left]
    simp [bound]
  have carry :=
    Inherited.scalar_jump_carry_traps_or_continues_defined run scope dominated refines driver stable
      spec jump formats entryFamily available remaining atTerm trapped
      ⟨guarded,allValues.mono (fun _ _ => True.intro)⟩
      (by simpa only [spec.atBlock] using Control.source_defined_entry_frame dominated result.ctx entered)
  rcases carry with failed | continuation
  · obtain ⟨offset,i,ops,ρ',w',outs,final,execution,coded⟩ := failed
    obtain ⟨path,bound,inst,operands,semantics,arity,control⟩ :=
      seqRun_stop_starAt (edges := result.edgeArgs) spec.placed segment execution
    have finished : RunOkABIAt f result.code result.edgeArgs isem MR fr.slots
        ⟨0,spec.preludeCode.size,ρentry,wentry⟩ (.trapped code) :=
      ⟨0,spec.preludeCode.size+offset,ρ',w',_,i,ops,outs,final,path,spec.placed,
        inst,operands,semantics,coded⟩
    exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix entryPath finished⟩
  · obtain ⟨t,left,ρ,w,total,continued,empty,frame,sourceFrame,atJump,executed,post,tDefined⟩ := continuation
    have targetValue : spec.target = 1 := by
      have labels := spec.targets
      rw [order] at labels
      exact (List.cons.inj labels).1.symm
    have targetTag : result.order.nodes[spec.target]? = some (.original 1) := by rw [order,targetValue]; rfl
    obtain ⟨returnSpec⟩ := CfgReturn.stock_lower_return_block_spec run scope dominated abi family targetTag
      targetSource ret refines driver stable env cp
    have targetIndex : blockIdx? f bc.block = some 1 := by
      simp [blockIdx?,blocks,destination,List.findIdx?_cons,different,Ne.symm different]
    have targetFound : f.block? bc.block = some target := by
      simp [Clif.Function.block?,blocks,destination,different,Ne.symm different]
    cases left with
    | zero => cases continued
    | succ left =>
      have crossing : ∃ fr',Clif.enterBlock t.frame bc = .ok fr' := by
        cases call : Clif.enterBlock t.frame bc with
        | ok fr' => exact ⟨fr',rfl⟩
        | trap code => exact False.elim (enterBlock_ne_trap call)
        | stuck message =>
          rw [Clif.runLoop_succ] at continued
          simp only [Clif.step,empty,atJump,Clif.stepTerm,call,Clif.StepResult.ofRes] at continued
          cases continued
      obtain ⟨fr',crossed⟩ := crossing
      have outgoing := Control.stock_jump_body_argument_values run scope dominated spec jump targetTag post.1
      have carried : ValuesHeld (fun x => x ∈ entry.params.map (·.1)) result.ctx t.frame
          (fun k => ρ (aliasNum result.final.alias k)) := by
        intro x member v read
        obtain ⟨key,mapped,value⟩ := post.2 x member v read
        refine ⟨key,?_,value⟩
        rw [← (stock_lower_record_context run scope spec.events).2.1 x]
        exact mapped
      have successor : result.order.successors[0]![0]? = some spec.target := by rw [order,targetValue]; rfl
      have nextReturned : Clif.runLoop env cp left ⟨fr',[],t.mem⟩ = .trapped code := by
        rw [Clif.runLoop_succ] at continued
        have callers : t.callers = [] := frame.1.trans rfl
        simpa only [Clif.step,empty,atJump,Clif.stepTerm,crossed,Clif.StepResult.ofRes,callers] using continued
      obtain ⟨ρ',copied,finished⟩ := CfgReturnAt.direct_successor_traps_at run scope dominated abi family
        spec.events tag source (by simp [jump,dests]) successor targetTag targetIndex targetFound spec.atBlock
        refines driver stable ret returnSpec post.1 (by simpa only [spec.atBlock] using tDefined) crossed (by
          intro x needed
          rcases needed with argument | ⟨available,notParameter⟩
          · exact outgoing x argument
          · rcases successor_entry_coverage blocks forwarded available notParameter with parameter | argument
            · exact carried x parameter
            · exact outgoing x argument) nextReturned
      have last : spec.preludeCode.size+spec.body.code.size+1 =
          (spec.raw.insts.map (·.mapRegs resolve)).size := by
        simp only [spec.rawCode,spec.bodyCode,Array.size_map,Array.size_append,Array.size_singleton]
        omega
      obtain ⟨ps,cfg⟩ := stock_lower_computed_cfg run scope
      have actualSuccessor : succOf result.code 0 0 = some spec.target := by
        simp only [succOf,cfg]
        rw [order,targetValue]
        rfl
      have path := seqRun_goto_starAt spec.placed segment executed last actualSuccessor
        (by simpa only [vdefUpd,writeV,List.foldl_nil,Array.toList_empty,List.filter_nil,List.zip_nil_left] using copied)
      have whole := RunOkABIAt.prefix entryPath (RunOkABIAt.prefix path finished)
      exact ⟨entrySeed spec.core.scan.ctx fr,by simpa only [frame.2.2.1] using whole⟩

end Backend.Stock.Proof.TwoBlock

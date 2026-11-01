import FV.Backend.Proof.StockConditionalLeaf
import FV.Backend.Proof.StockTrapRefines

/-!
# Trap leaf blocks of conditional CFGs

A nonentry original block whose body is in the mask family and whose terminator is `trap c`
supplies both successor continuations of the conditional CFG composition. Its source never
returns (`SuccessorReturn.of_trap_block` holds vacuously). A trapped source run either traps in a
body statement, or runs the whole body and traps at the terminator with `c`; the machine side
runs the body chunk and then the terminator chunk, which is exactly `udf c`
(`SuccessorTrap.of_trap_block`).
-/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch collectOutgoing scanBlock lowerBlockCore

/-- A successful `trap` core contains its actual scan code, with no separate branch chunk. -/
theorem stock_trap_core_code {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : V} {targets : Array Nat}
    {input : State} {core : LoweredBlockCore} {c : Clif.TrapCode}
    (trap : b.term = .trap c)
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    core.code = core.scan.output.code := by
  unfold lowerBlockCore at run
  dsimp only at run
  simp only [trap,Bool.false_eq_true,ite_false] at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; simp

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

private theorem local_family {f : Clif.Function} {b : Clif.Block} {bi : Nat}
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst) (source : f.blocks[bi]? = some b) :
    ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
  intro stm member
  rcases family b (List.mem_of_getElem? source) stm member with
    (scalar | ⟨op,ty,x,y,shape⟩) | ⟨ty,x,shape⟩ | shape
  · exact LocalBody.LocalInst.of_pure (HighMulBody.family_pure scalar)
  all_goals simp [LocalBody.LocalInst,shape]

/-- An actual original `trap` node: its scan event and its placed code, which is the prelude
followed by the scan code. A nonentry node has no prelude. -/
theorem stock_lower_trap_block_code {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {label bi : Nat} {b : Clif.Block} {c : Clif.TrapCode}
    (tag : result.order.nodes[label]? = some (.original bi)) (source : f.blocks[bi]? = some b)
    (trap : b.term = .trap c) :
    ∃ (event : BlockScanEvent) (raw : VBlock) (preludeCode : Array MInst),
      event ∈ result.blockScans.toList ∧ event.block = bi ∧
      raw.insts = preludeCode ++ event.output.code ∧ (bi ≠ 0 → preludeCode.size = 0) ∧
      result.code.blocks[label]? = some {raw with
        insts := raw.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
        params := raw.params.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
        branchArgs := raw.branchArgs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))} := by
  obtain ⟨ranges,params,input,data,core,raw,preludeCode,coreRun,assembled,build,sizes,prepared,
    events,atBlock,rawCode,placed⟩ := stock_lower_original_block_scan_assembly run tag
  have sourceValue : f.blocks[bi]! = b := by rw [List.getElem!_eq_getElem?_getD,source]; rfl
  rw [sourceValue] at coreRun assembled
  have coreCode := stock_trap_core_code trap coreRun
  refine ⟨core.scan,raw,preludeCode,events,atBlock,by rw [rawCode,coreCode],?_,placed⟩
  intro nonentry
  have code := assemble_nonentry_code nonentry assembled
  have sizes := congrArg Array.size (rawCode.symm.trans code)
  simp only [Array.size_append] at sizes
  omega

/-- The actual source's first trap in an original `trap` block becomes the same machine trap
under the actual per-successor semantics: in the body, or at the terminator's `udf`. -/
theorem trap_block_traps_at {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi : Nat} {c : Clif.TrapCode}
    (source : f.blocks[bi]? = some b) (trap : b.term = .trap c)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    {event : BlockScanEvent} {raw : VBlock} {preludeCode : Array MInst}
    (events : event ∈ result.blockScans.toList) (atBlock : event.block = bi)
    (rawCode : raw.insts = preludeCode ++ event.output.code)
    (placed : result.code.blocks[label]? = some {raw with
      insts := raw.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
      params := raw.params.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
      branchArgs := raw.branchArgs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))})
    {fuel : Nat} {s : Clif.State} {code : Clif.TrapCode}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (trapped : Clif.runLoop env cp fuel s = .trapped code)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result event.ctx event.block MR event.output.state (0,s.frame,s.mem) ρ w) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,preludeCode.size,ρ,w⟩ (.trapped code) := by
  have block : f.blocks[event.block]? = some b := by rw [atBlock]; exact source
  obtain ⟨term,body,split,normal,trapping⟩ := MaskBody.actual_body_refines_at_block run scope dominated family
    events block refines driver stable (env := env) (cp := cp)
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have emitted := TrapBody.trap_term_emitted run scope events split trap
  have pieces : raw.insts.map (·.mapRegs resolve) =
      preludeCode.map (·.mapRegs resolve) ++ body.code.map (·.mapRegs resolve) ++
      term.output.emitted.map (·.mapRegs resolve) := by
    simp only [rawCode,split.code,Array.map_append,Array.append_assoc]
  have segment : SegAt {raw with
      insts := raw.insts.map (·.mapRegs resolve)
      params := raw.params.map resolve
      branchArgs := raw.branchArgs.map resolve}
      preludeCode.size (body.code.toList.map (·.mapRegs resolve)) := by
    intro k hk
    have bound : k < body.code.size := by simpa using hk
    rw [pieces,Array.append_assoc,Array.getElem?_append_right (by simpa only [Array.size_map] using Nat.le_add_right preludeCode.size k)]
    simp only [Array.size_map,Nat.add_sub_cancel_left]
    rw [Array.getElem?_append_left (by simpa only [Array.size_map] using bound)]
    simp [bound]
  rcases TrapBody.trap_source_execution run events split (local_family family block) (j := 0)
    (by omega) (by simpa using remaining) (atTerm.trans trap) trapped with
    sourceTrap | ⟨codeEq,s',steps⟩
  · have machineTrap := trapping (0,s.frame,s.mem) code
      (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using sourceTrap) ρ w held
    obtain ⟨offset,i,ops,ρ',w',outs,final,execution,trapCode⟩ := machineTrap
    obtain ⟨path,bound,inst,operands,semantics,arity,control⟩ :=
      seqRun_stop_starAt (edges := result.edgeArgs) placed segment execution
    exact ⟨label,preludeCode.size+offset,ρ',w',_,i,ops,outs,final,path,placed,
      inst,operands,semantics,trapCode⟩
  · rw [codeEq]
    obtain ⟨ρ',w',bodyRun,_⟩ := normal (0,s.frame,s.mem) s'
      (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using steps) ρ w held
    have size : (raw.insts.map (·.mapRegs resolve)).size = preludeCode.size + body.code.size + 1 := by
      rw [pieces,emitted]
      simp only [Array.size_append,Array.size_map,List.size_toArray,List.length_cons,List.length_nil]
    have bodyPath := seqRun_fall_starAt (edges := result.edgeArgs) placed segment
      (by
        simp only [List.length_map,Array.length_toList]
        show preludeCode.size + body.code.size < (raw.insts.map (·.mapRegs resolve)).size
        omega) bodyRun
    simp only [List.length_map,Array.length_toList] at bodyPath
    have atTrap : (raw.insts.map (·.mapRegs resolve))[preludeCode.size + body.code.size]? = some (.udf c) := by
      rw [pieces,emitted,Array.getElem?_append_right (by simp only [Array.size_append,Array.size_map]; omega)]
      simp only [Array.size_append,Array.size_map,Nat.sub_self]
      rw [Array.getElem?_map]
      rfl
    obtain ⟨w3,halted,_⟩ := refines (.udf c) [] w' [] w' (ispec_udf c w')
    exact ⟨label,preludeCode.size + body.code.size,ρ',w',_,.udf c,#[],[],w3,bodyPath,placed,
      atTrap,rfl,halted,rfl⟩

/-- A nonentry original `trap` block supplies the conditional first-trap continuation. -/
theorem SuccessorTrap.of_trap_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} {trapCode : Clif.TrapCode} {label : Nat} {bc : Clif.BlockCall}
    {tl targetLabel : Nat} {b : Clif.Block} {c : Clif.TrapCode}
    (lookup : blockIdx? f bc.block = some tl) (found : f.block? bc.block = some b)
    (source : f.blocks[tl]? = some b)
    (tag : result.order.nodes[targetLabel]? = some (.original tl))
    (trap : b.term = .trap c) (nonentry : tl ≠ 0) (forward : label < targetLabel) :
    Nonempty (SuccessorTrap f result label bc isem MR env cp trapCode) := by
  obtain ⟨event,raw,preludeCode,events,atBlock,rawCode,noPrelude,placed⟩ :=
    stock_lower_trap_block_code run tag source trap
  refine ⟨{
    index := tl
    targetLabel := targetLabel
    block := b
    event := event
    lookup := lookup
    found := found
    tag := tag
    member := events
    atBlock := atBlock
    forward := forward
    traps := ?_ }⟩
  intro fuel s ρ w func callers remaining atTerm defined trapped held
  have finished := trap_block_traps_at run scope dominated family source trap refines driver stable
    events atBlock rawCode placed remaining atTerm trapped held
  simpa only [noPrelude nonentry] using finished

/-- A nonentry original `trap` block never returns, so it supplies the conditional return
continuation vacuously. -/
theorem SuccessorReturn.of_trap_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {isem : Backend.Proof.Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {vals : List Clif.Val} {cm : Clif.Mem} {label : Nat}
    {bc : Clif.BlockCall} {tl targetLabel : Nat} {b : Clif.Block} {c : Clif.TrapCode}
    (lookup : blockIdx? f bc.block = some tl) (found : f.block? bc.block = some b)
    (source : f.blocks[tl]? = some b)
    (tag : result.order.nodes[targetLabel]? = some (.original tl))
    (trap : b.term = .trap c) (forward : label < targetLabel) :
    Nonempty (SuccessorReturn f result label bc isem MR env cp vals cm) := by
  obtain ⟨event,raw,preludeCode,events,atBlock,rawCode,noPrelude,placed⟩ :=
    stock_lower_trap_block_code run tag source trap
  refine ⟨{
    index := tl
    targetLabel := targetLabel
    block := b
    event := event
    lookup := lookup
    found := found
    tag := tag
    member := events
    atBlock := atBlock
    forward := forward
    returns := ?_ }⟩
  intro fuel s ρ w func callers remaining atTerm defined returned held
  exact absurd returned (TrapBody.trap_source_noreturn (local_family family source) (j := 0)
    (by simpa using remaining) (atTerm.trans trap))

end Backend.Stock.Proof.ConditionalValues

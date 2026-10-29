module

public import FV.Backend.Proof.StockCfgReturnRefines
public import FV.Backend.Proof.StockOriginalBlockOrigin
public import FV.Backend.Proof.StockMaskBlockRefines

@[expose] public section

namespace Backend.Stock.Proof.CfgReturn
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch collectOutgoing scanBlock lowerBlockCore

/-- A successful return core contains its actual scan code, with no separate
branch chunk. This applies to arbitrary original CFG blocks. -/
theorem stock_return_core_code {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : V} {targets : Array Nat}
    {input : State} {core : LoweredBlockCore} {xs : List Nat}
    (ret : b.term = .ret xs)
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    core.code = core.scan.output.code := by
  unfold lowerBlockCore at run
  dsimp only at run
  simp only [ret,Bool.false_eq_true,ite_false] at run
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

/-- One actual original return node retains its scan/assembly and starts the
ABI-correct return run at its own label and actual prelude offset. -/
structure ReturnBlockSpec (f : Clif.Function) (result : Result) (b : Clif.Block)
    (label bi : Nat) (isem : Backend.Proof.Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) where
  ranges : Array (Nat × Nat)
  params : List Nat
  input : State
  data : V
  core : LoweredBlockCore
  raw : VBlock
  preludeCode : Array MInst
  term : ScanRecord
  body : BlockScan
  build : Stock.buildCtx f = .ok (result.ctx,ranges,result.initial)
  sizes : sigParamBytes f.sig = .ok params
  coreRun : lowerBlockCore result.ctx result.order f b bi ranges[bi]!.1 ranges[bi]!.2
    data result.order.successors[label]! input = .ok core
  assembled : assembleOriginalBlock result.ctx f b bi label result.order.successors[label]!
    core.outgoing params core.state.uses core.code = .ok raw
  prepared : Coverage.blockData f b.term = .ok data
  events : core.scan ∈ result.blockScans.toList
  atBlock : core.scan.block = bi
  split : SourceBodySplit f core.scan b term body
  rawCode : raw.insts = preludeCode ++ core.code
  noPrelude : bi ≠ 0 → preludeCode.size = 0
  placed : result.code.blocks[label]? = some {raw with
    insts := raw.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
    params := raw.params.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
    branchArgs := raw.branchArgs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))}
  returns : ∀ (fuel : Nat) (s : Clif.State) (vals : List Clif.Val) (cm : Clif.Mem),
    s.frame.func = f → s.callers = [] → s.frame.body = b.body → s.frame.term = b.term →
    SourceDefinedAt f result.ctx core.scan.block 0 s.frame →
    Clif.runLoop env cp fuel s = .returned vals cm → ∀ ρ w,
    GuardedScanRel f result core.scan.ctx core.scan.block MR core.scan.output.state (0,s.frame,s.mem) ρ w →
    RunOkABI f result.code isem MR s.frame.slots ⟨label,preludeCode.size,ρ,w⟩ (.returned vals cm)

/-- Original scope and actual retained records derive return semantics at the
selected node. No singleton-function, helper, placement or body callback is
required of the accepted program. -/
theorem stock_lower_return_block_spec {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {label bi : Nat} {b : Clif.Block} {xs : List Nat}
    (tag : result.order.nodes[label]? = some (.original bi)) (source : f.blocks[bi]? = some b)
    (ret : b.term = .ret xs)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    (env : Clif.Env) (cp : Clif.Program) :
    Nonempty (ReturnBlockSpec f result b label bi isem MR env cp) := by
  obtain ⟨ranges,params,input,data,core,raw,preludeCode,coreRun,assembled,build,sizes,prepared,
    events,atBlock,rawCode,placed⟩ := stock_lower_original_block_scan_assembly run tag
  have sourceValue : f.blocks[bi]! = b := by rw [List.getElem!_eq_getElem?_getD,source]; rfl
  rw [sourceValue] at coreRun assembled prepared
  have coreCode := stock_return_core_code ret coreRun
  have noPrelude : bi ≠ 0 → preludeCode.size = 0 := by
    intro nonentry
    have code := assemble_nonentry_code nonentry assembled
    have sizes := congrArg Array.size (rawCode.symm.trans code)
    simp only [Array.size_append] at sizes
    omega
  obtain ⟨term,body,split,normal,trapping⟩ := MaskBody.actual_body_refines_at_block run scope dominated family
    events (b := b) (by rw [atBlock]; exact source) refines driver stable (env := env) (cp := cp)
  have localFamily : ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
    intro stm member
    rcases family b (List.mem_of_getElem? source) stm member with (scalar | ⟨op,ty,x,y,shape⟩) | ⟨ty,x,shape⟩ | shape
    · exact LocalBody.LocalInst.of_pure (HighMulBody.family_pure scalar)
    all_goals simp [LocalBody.LocalInst,shape]
  refine ⟨{
    ranges := ranges
    params := params
    input := input
    data := data
    core := core
    raw := raw
    preludeCode := preludeCode
    term := term
    body := body
    build := build
    sizes := sizes
    coreRun := coreRun
    assembled := assembled
    prepared := prepared
    events := events
    atBlock := atBlock
    split := split
    rawCode := rawCode
    noPrelude := noPrelude
    placed := placed
    returns := ?_}⟩
  intro fuel s vals cm func callers remaining atTerm defined returned ρ w held
  have code : (raw.insts.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) =
      preludeCode.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++
      core.scan.output.code.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ #[] := by
    simp only [rawCode,coreCode,Array.map_append,Array.append_empty]
  have finished := actual_local_return_refines_at_block run scope dominated abi localFamily ret events split
    func callers remaining atTerm defined returned refines stable normal placed code ρ w held
  simpa only [Array.size_map] using finished

end Backend.Stock.Proof.CfgReturn

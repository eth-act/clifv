import FV.Backend.Proof.StockGeneralLoopDomain2
import FV.Backend.Proof.StockGeneralArgsLoopDomain3

/-! The legacy loop class with plain `i8` conditions satisfies the unchanged production domain
(#140, CB-12).

The CB-11 transport (`StockGeneralLoopDomain2`) with the condition `GeneralCondition` of
`GeneralArgsLoopCfg3`. A branch on a condition of the class has two successors in the actual block
order: its named call packet (`general_cond_branch_calls`) names them (`branch_target_count`). Its
arguments are empty, so its original and critical-edge vectors are empty, and the actual code keeps
exact per-edge/single-vector agreement (`general_loop_legacy_compatible`). The class is the split
class `GeneralArgsLoopCfg3` with empty `brif` arguments (`GeneralTerms.args`), so its returns and
first traps hold over the actual per-successor vectors (`domainAt_of_general_args_loop_cfg`), and
`RunOkABIAt.legacyCompatible` and `EdgeLegacyCompatible.star` transport them to the legacy
observations of the unsplit code (`domain_of_general_loop_cfg`, `Scalar.Domain`). -/

namespace Backend.Stock.Proof.GeneralArgsLoopCfg3
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues
  Backend.Stock.Proof.ForwardSource Backend.Stock.Proof.ParameterCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem selected_empty {b : Clif.Block} {c index id : Nat} {yes no : Clif.BlockCall} {args : List Clif.TryArg}
    (term : b.term = .brif c yes no) (yesEmpty : yes.args = []) (noEmpty : no.args = [])
    (selected : (destinations b.term)[index]? = some (id,args)) :
    ∃ bc,(dests b.term)[index]? = some bc ∧ bc.args = [] := by
  cases index with
  | zero => exact ⟨yes,by simp [term,dests],yesEmpty⟩
  | succ index =>
    cases index with
    | zero => exact ⟨no,by simp [term,dests],noEmpty⟩
    | succ index => simp [term,destinations] at selected

private theorem assembled_arguments {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {bi label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {params : List Nat} {uses : Array UseState} {code : Array MInst} {block : VBlock}
    (run : assembleOriginalBlock ctx f b bi label targets outgoing params uses code = .ok block) :
    block.branchArgs = (if targets.size == 1 then outgoing[0]! else #[]) := by
  unfold assembleOriginalBlock at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; simp_all

/-- A branch on a condition of the class has two successors in the actual block order. -/
theorem branch_target_count {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (term : b.term = .brif c yes no) (condition : GeneralCondition f c) :
    result.order.successors[label]!.size = 2 := by
  obtain ⟨calls⟩ := spec.general_cond_branch_calls run scope term (condition_metadata condition scope dominated spec.build)
  have size := congrArg List.length calls.labels_eq
  simpa only [Array.length_toList,List.length_cons,List.length_nil] using size

/-- **The legacy loop class with plain `i8` conditions keeps exact per-edge/single-vector
agreement** of the actual code: jumps carry their arguments, branches carry none, and returns and
traps have no outgoing edge. -/
theorem general_loop_legacy_compatible {f : Clif.Function} {result : Result}
    (terms : GeneralTerms f) (run : Stock.lower f = .ok result)
    (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR) (env : Clif.Env) (cp : Clif.Program) :
    EdgeLegacyCompatible result.code result.edgeArgs := by
  have built : ∃ ranges,Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) := by
    unfold Stock.lower at run
    dsimp only at run
    repeat' first
      | (solve | cases run)
      | simp only [bind,Except.bind,pure,Except.pure] at run
      | split at run
    cases run
    exact ⟨_,by assumption⟩
  obtain ⟨ranges,build⟩ := built
  have inv := buildCtx_mappedInv scope build
  obtain ⟨ps,cfg⟩ := stock_lower_computed_cfg run scope
  have sizes := (stock_lower_graph_bounds run).1
  have nodes : result.code.blocks.size = result.order.nodes.size :=
    (stock_prepare_dimensions run).1.symm.trans (stock_prepare_dimensions run).2.1
  intro label index target selected
  simp only [succOf,cfg] at selected
  cases row : result.order.successors[label]? with
  | none => simp only [row,Option.bind_none] at selected; cases selected
  | some ss =>
    simp only [row,Option.bind_some] at selected
    have labelBound : label < result.order.nodes.size := by
      have bound := (Array.getElem?_eq_some_iff.mp row).1
      omega
    cases tag : result.order.nodes[label]? with
    | none => have absent := Array.getElem?_eq_none_iff.mp tag; omega
    | some node =>
      cases node with
      | original bi =>
        obtain ⟨b,id,args,ti,source,destination,found,targetNode⟩ := stock_lower_indexed_successor_origin run tag row selected
        rcases terms bi b source with ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,yesEmpty,noEmpty,condition⟩ | ⟨leafCode,trap⟩
        · have only : index = 0 := by
            cases index with
            | zero => rfl
            | succ index => simp [jump,destinations] at destination
          subst index
          obtain ⟨tl,targetLabel,identified,nonentry,successors,targetTag⟩ := CriticalOwners.jump_successor run scope tag source jump
          have sameRow : ss = #[targetLabel] := Option.some.inj (row.symm.trans successors)
          have sameTarget : targetLabel = target := by simpa [sameRow] using selected
          subst targetLabel
          have successorsBang : result.order.successors[label]! = #[target] := by simp only [getElem!_def,successors,Option.getD_some]
          obtain ⟨vb,placed,labelled,arguments⟩ := stock_lower_original_jump_args run scope tag source jump successorsBang targetTag
          have vector := stock_lower_selected_outgoing run scope tag source (bc := bc) (index := 0)
            (by simp [jump,dests]) (by simpa only [getElem!_def,row,Option.getD_some] using selected) targetTag
          exact ⟨vb,placed,by simpa only [outgoingAt,arguments] using vector⟩
        · simp only [ret,destinations,List.getElem?_nil] at destination; cases destination
        · obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag source term refines driver stable env cp
          have targetCount := branch_target_count run scope dominated spec term condition
          have rawArgs : spec.raw.branchArgs = #[] := by
            have args := assembled_arguments spec.assembled
            simpa only [targetCount,show (2 == 1) = false from rfl,Bool.false_eq_true,ite_false] using args
          obtain ⟨bc,selectedBc,empty⟩ := selected_empty term yesEmpty noEmpty destination
          have successor : result.order.successors[label]![index]? = some target := by
            simpa only [getElem!_def,row,Option.getD_some] using selected
          have vector : outgoingAt result label index = some #[] := by
            rcases targetNode with original | synthetic
            · have actual := stock_lower_selected_outgoing run scope tag source selectedBc successor original
              simpa only [edgeArgumentNumbers,empty,List.map_nil] using actual
            · exact stock_lower_deferred_outgoing run tag successor synthetic
          refine ⟨_,spec.placed,?_⟩
          simpa only [outgoingAt,rawArgs,Array.map_empty] using vector
        · simp only [trap,destinations,List.getElem?_nil] at destination; cases destination
      | edge pred k ti =>
        obtain ⟨b,id,args,source,destination,found⟩ := stock_lower_critical_source run tag
        rcases terms pred b source with ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,yesEmpty,noEmpty,condition⟩ | ⟨leafCode,trap⟩
        · exact False.elim (CriticalOwners.jump_no_edge (stock_lower_order run) source jump k ti
            (Array.mem_toList_iff.mpr (Array.mem_of_getElem? tag)))
        · simp only [ret,destinations,List.getElem?_nil] at destination; cases destination
        · obtain ⟨bc,selectedBc,empty⟩ := selected_empty term yesEmpty noEmpty destination
          obtain ⟨input,next,registers,targetLabel,call,successors,targetTag,placed⟩ := stock_lower_critical_code run tag
          have sameRow : ss = #[targetLabel] := Option.some.inj (row.symm.trans successors)
          have zero : index = 0 := by
            cases index with
            | zero => rfl
            | succ index => simp [sameRow] at selected
          subst index
          have mapping := stock_branchArgs_selected_mapping inv.func source selectedBc call
          have noRegisters : registers = #[] := by
            rw [empty] at mapping
            simp only [List.mapM_nil,Option.pure_def,Option.some.injEq] at mapping
            exact Array.toList_inj.mp mapping.symm
          have vector := stock_lower_critical_argument_vector run scope tag source selectedBc
          refine ⟨_,placed,?_⟩
          simpa only [outgoingAt,edgeArgumentNumbers,empty,List.map_nil,noRegisters,Array.map_empty] using vector
        · simp only [trap,destinations,List.getElem?_nil] at destination; cases destination

/-- **The legacy loop class with plain `i8` conditions satisfies the unchanged production
domain.** Every block jumps (with any arguments), returns, branches with empty arguments on a
condition of `GeneralArgsLoopCfg2` or on a narrow condition (`NarrowCondition`: an `i8` parameter,
or an `i8` result of a statement that is not an `icmp`, a `band` or a `uextend`), or, outside the
entry, ends in `trap`. No rank: jump and branch targets may be loop headers. -/
theorem domain_of_general_loop_cfg {f : Clif.Function}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    (terms : GeneralTerms f)
    (entryKind : ∀ b,f.blocks[0]? = some b → ∀ c,b.term ≠ .trap c)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst) : Scalar.Domain f := by
  have domainAt := domainAt_of_general_args_loop_cfg scope dominated abi ordinary terms.args entryKind family
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have compatible := general_loop_legacy_compatible terms run scope dominated family refines driver stable env cp
    obtain ⟨ρ,simulation⟩ := domainAt.returns run entered returned refines driver memorySem stable memory arguments
    exact ⟨ρ,simulation.legacyCompatible compatible⟩
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have compatible := general_loop_legacy_compatible terms run scope dominated family refines driver stable env cp
    obtain ⟨ρ,b,k,ρ',w,vb,i,ops,outs,w',path,tail⟩ :=
      domainAt.traps run entered trapped refines driver memorySem stable memory arguments
    exact ⟨ρ,b,k,ρ',w,vb,i,ops,outs,w',compatible.star path,tail⟩

end Backend.Stock.Proof.GeneralArgsLoopCfg3

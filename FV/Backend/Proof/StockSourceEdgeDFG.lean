import FV.Backend.Proof.LowerCertBase
import FV.Backend.Proof.StockBodyScanOrigin



namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual scan contexts preserve source consistency across original blocks.
The overwritten terminator placeholder has no source definition. -/
theorem stock_lower_scan_dfg_iff {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) (fr : Clif.Frame) :
    DFGCons event.ctx fr ↔ DFGCons result.ctx fr := by
  obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope events
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  have atBlock : event.block = bi := by
    rw [eventEq]
    exact (stock_lowerBlockCore_scanOrigin coreRun).2.2.1
  have block : f.blocks[bi]? = some b := by rw [← atBlock]; exact split.block
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  have range := spec.ranges bi b block
  have rangeValue : ranges[bi]! = (blockStart f bi,blockStart f bi+b.body.length+1) := by
    simp only [getElem!_def,range]
  have placeholder : result.ctx.insts[ranges[bi]!.2-1]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [rangeValue]
    have terminal : blockStart f bi+b.body.length+1-1 = blockStart f bi+b.body.length := by omega
    rw [terminal,view.insts]
    exact spec.facts.term bi b block
  rw [eventEq,(stock_lowerBlockCore_scanOrigin coreRun).2.1]
  change DFGCons (Driver.termCtx result.ctx (ranges[bi]!.2-1) data) fr ↔ DFGCons result.ctx fr
  exact (buildCtx_mappedInv scope build).dfgCons_termCtx_iff placeholder data fr

/-- A source frame can move between the actual predecessor and successor scan
contexts without an additional DFG certificate from the input program. -/
theorem stock_lower_scan_dfg_transfer {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {first second : BlockScanEvent} (source : first ∈ result.blockScans.toList)
    (target : second ∈ result.blockScans.toList) {fr : Clif.Frame}
    (consistent : DFGCons first.ctx fr) : DFGCons second.ctx fr :=
  (stock_lower_scan_dfg_iff run scope target fr).mpr
    ((stock_lower_scan_dfg_iff run scope source fr).mp consistent)

end Backend.Stock.Proof

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option autoImplicit false
set_option Elab.async false

private theorem inherited_predecessor {f : Clif.Function} {ctx : Ctx}
    {bi tl : Nat} {b target : Clif.Block} {bc : Clif.BlockCall}
    (source : f.blocks[bi]? = some b) (destination : f.blocks[tl]? = some target)
    (edge : bc.block ∈ succIds b.term) (index : blockIdx? f bc.block = some tl)
    {x : Nat} (available : x ∈ availOf f (availIn f ctx) tl 0)
    (notParameter : x ∉ target.params.map (·.1)) :
    x ∈ (availIn f ctx).getD tl [] ∧ x ∉ defsOf f tl ∧
      x ∈ availOf f (availIn f ctx) bi b.body.length := by
  obtain ⟨present,later⟩ := (mem_av destination).mp available
  have incoming : x ∈ (availIn f ctx).getD tl [] := by
    rcases present with parameter | incoming | ⟨j,stm,earlier,_,_⟩
    · exact False.elim (notParameter parameter)
    · exact incoming
    · omega
  have noDef : x ∉ defsOf f tl := by
    intro defined
    obtain ⟨original,j,stm,found,statement,result⟩ := mem_defsOf.mp defined
    cases Option.some.inj (found.symm.trans destination)
    exact later ⟨j,stm,Nat.zero_le _,statement,result⟩
  have successor : tl ∈ succIdx f bi := by
    simp only [succIdx,source]
    exact List.mem_filterMap.mpr ⟨bc.block,edge,index⟩
  have fixed := inFix_fixOk (f := f) (ctx := ctx) (gn := id)
  refine ⟨incoming,noDef,(mem_av source).mpr ⟨?_,?_⟩⟩
  · rcases fixed.out tl x incoming bi successor with parameter | defined | inherited
    · exact .inl (by rwa [parsOf_of source] at parameter)
    · obtain ⟨original,j,stm,found,statement,result⟩ := mem_defsOf.mp defined
      cases Option.some.inj (found.symm.trans source)
      exact .inr (.inr ⟨j,stm,lt_of_getElem? statement,statement,result⟩)
    · exact .inr (.inl inherited)
  · rintro ⟨j,stm,later,statement,_⟩
    have bound := lt_of_getElem? statement
    omega

/-- Source successor binding preserves the original restricted DFG invariant.
All parameter and inherited-definition facts follow from the original input
conditions, including parameter freedom of inherited expressions. -/
theorem source_enterBlock_dfg {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st0 : LState}
    (build : Backend.buildCtx f = .ok (ctx,ranges,st0)) (dominated : Dominated f)
    {bi tl : Nat} {b target : Clif.Block} {bc : Clif.BlockCall}
    (source : f.blocks[bi]? = some b) (destination : f.blocks[tl]? = some target)
    (edge : bc.block ∈ succIds b.term) (index : blockIdx? f bc.block = some tl)
    {fr fr' : Clif.Frame} (func : fr.func = f)
    (consistent : DFGCons ctx (restrict fr (availOf f (availIn f ctx) bi b.body.length)))
    (entered : Clif.enterBlock fr bc = .ok fr') :
    DFGCons ctx (restrict fr' (availOf f (availIn f ctx) tl 0)) := by
  obtain ⟨original,args,regs,found,read,types,set,rfl⟩ := enterBlock_spec entered
  rw [func] at found
  cases Option.some.inj ((blockIdx_block index found).symm.trans destination)
  have facts := ctxFacts_of build
  have nodup := (List.nodup_append.mp (block_nodup dominated.ssa destination)).1
  refine ⟨?_,?_⟩
  · intro x d info inst value defined atDef clif pure held
    have available : x ∈ availOf f (availIn f ctx) tl 0 := restrict_regs_isSome (by rw [held]; rfl)
    have lookup : regs x = some value := by
      rw [restrict_regs_of_mem available] at held
      exact held
    by_cases parameter : x ∈ target.params.map (·.1)
    · rw [defInst_par facts dominated.ssa destination parameter] at defined
      cases defined
    · obtain ⟨incoming,noDef,previous⟩ := inherited_predecessor source destination edge index available parameter
      have oldHeld : (restrict fr (availOf f (availIn f ctx) bi b.body.length)).regs x = some value := by
        rw [restrict_regs_of_mem previous,← setMany_other set parameter]
        exact lookup
      obtain ⟨vals,evaluated,result⟩ := consistent.1 x d info inst value defined atDef clif pure oldHeld
      refine ⟨vals,fun cm => ?_,result⟩
      rw [← evaluated cm]
      refine evalInst_congr ?_ ?_ cm inst ?_
      · rfl
      · rfl
      · intro y member
        have afterArg := avail_step dominated build available defined atDef clif (.inl member)
        have beforeArg := avail_step dominated build previous defined atDef clif (.inl member)
        have arg : y ∈ defArgs ctx x := by rw [defArgs_eq defined atDef clif]; exact member
        have noParameter := dominated.paramFree ctx ranges st0 build tl x incoming noDef y arg
        rw [parsOf_of destination] at noParameter
        rw [restrict_regs_of_mem afterArg,restrict_regs_of_mem beforeArg]
        exact setMany_other set noParameter
  · intro x ty value type held
    have available : x ∈ availOf f (availIn f ctx) tl 0 := restrict_regs_isSome (by rw [held]; rfl)
    have lookup : regs x = some value := by rw [restrict_regs_of_mem available] at held; exact held
    by_cases parameter : x ∈ target.params.map (·.1)
    · obtain ⟨q,member,rfl,valueType⟩ := setMany_param_ty set nodup types parameter lookup
      have expected := (facts.types dominated.ssa).2 target (List.mem_of_getElem? destination) q member
      rw [expected] at type
      rw [valueType]
      exact Option.some.inj type
    · have previous := (inherited_predecessor source destination edge index available parameter).2.2
      apply consistent.2 x ty value type
      rw [restrict_regs_of_mem previous,← setMany_other set parameter]
      exact lookup

end Backend.Stock.Proof

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option autoImplicit false
set_option Elab.async false

private theorem sourceView_avail {ctx original : Ctx} (view : DFGViewEq ctx original)
    (f : Clif.Function) : availIn f ctx = availIn f original := by
  have args : defArgs ctx = defArgs original := by
    funext x
    simp only [defArgs,Ctx.defInst?,view.valDef,view.insts]
  have users : fUsers ctx = fUsers original := by simp only [fUsers,usersN,args,view.valDef]
  have bytes : fInB0 f ctx id = fInB0 f original id := by unfold fInB0; rw [view.valDef]
  have work : fWork0 f ctx id = fWork0 f original id := by
    simp only [fWork0,view.valDef,bytes,args]
  simp only [availIn,inFix_eq,users,bytes,work,view.valDef]

/-- Original successor binding establishes DFG consistency in the actual next
Stock scan context, under the original scope and dominance conditions. -/
theorem stock_lower_source_enterBlock_dfg {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {first second : BlockScanEvent} (sourceEvent : first ∈ result.blockScans.toList)
    (targetEvent : second ∈ result.blockScans.toList)
    {bi tl : Nat} {b target : Clif.Block} {bc : Clif.BlockCall}
    (source : f.blocks[bi]? = some b) (destination : f.blocks[tl]? = some target)
    (edge : bc.block ∈ succIds b.term) (index : blockIdx? f bc.block = some tl)
    {fr fr' : Clif.Frame} (func : fr.func = f)
    (consistent : DFGCons first.ctx (restrict fr (availOf f (availIn f result.ctx) bi b.body.length)))
    (entered : Clif.enterBlock fr bc = .ok fr') :
    DFGCons second.ctx (restrict fr' (availOf f (availIn f result.ctx) tl 0)) := by
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi', data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run sourceEvent
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  have avail := sourceView_avail view f
  have oldCons := (view.dfgCons_iff _).mp ((stock_lower_scan_dfg_iff run scope sourceEvent _).mp consistent)
  rw [avail] at oldCons
  have after := source_enterBlock_dfg oldBuild dominated source destination edge index func oldCons entered
  rw [← avail] at after
  exact (stock_lower_scan_dfg_iff run scope targetEvent _).mpr ((view.dfgCons_iff _).mpr after)

end Backend.Stock.Proof


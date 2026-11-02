import FV.Backend.Proof.StockJumpDemand
import FV.Backend.Proof.StockConditionalCoreOrigin
import FV.Backend.Proof.StockConditionalBodyRefines

/-! A conditional branch whose two successors are original blocks collects the source
arguments of both successors before its body is scanned. Every argument is therefore demanded
after the body, and a guarded post-body frame holds the values of the selected successor's
arguments. Demand, availability and register maps come from the actual compiler run. -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix Backend.Stock.Proof.Control
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm branchArgs emitBranch collectOutgoing scanBlock lowerBlockCore

/-- Outgoing collection over two original successors marks the arguments of the first
successor, then those of the second. -/
theorem stock_collect_conditional_marks {ctx : Ctx} {f : Clif.Function}
    (func : ctx.func = f) {bi c : Nat} {b : Clif.Block} {yes no : Clif.BlockCall}
    (source : f.blocks[bi]? = some b) (term : b.term = .brif c yes no) {order : Order}
    {first second yesBlock noBlock : Nat}
    (firstTag : order.nodes[first]? = some (.original yesBlock))
    (secondTag : order.nodes[second]? = some (.original noBlock))
    {input next : State} {outgoing : Array (Array Reg)}
    (run : collectOutgoing ctx order bi #[first,second] input = .ok (next,outgoing)) :
    ∃ middle yesRegs noRegs,branchArgs ctx input bi 0 = .ok (yesRegs,middle) ∧
      branchArgs ctx middle bi 1 = .ok (noRegs,next) ∧
      middle = yes.args.foldl State.mark input ∧ next = no.args.foldl State.mark middle := by
  have tag0 : order.nodes[first]! = .original yesBlock := by simp [getElem!_def,firstTag]
  have tag1 : order.nodes[second]! = .original noBlock := by simp [getElem!_def,secondTag]
  simp only [collectOutgoing] at run
  change ([(first,0),(second,1)] : List (Nat × Nat)).foldlM (outgoingStep ctx order bi)
    (input,#[]) = .ok (next,outgoing) at run
  simp only [List.foldlM_cons,List.foldlM_nil] at run
  unfold outgoingStep at run
  simp only [tag0,tag1] at run
  cases call0 : branchArgs ctx input bi 0 with
  | error message => simp only [call0,bind,Except.bind] at run; cases run
  | ok pair =>
    obtain ⟨yesRegs,middle⟩ := pair
    simp only [call0,bind,Except.bind,pure,Except.pure] at run
    cases call1 : branchArgs ctx middle bi 1 with
    | error message => simp only [call1] at run; cases run
    | ok pair =>
      obtain ⟨noRegs,state⟩ := pair
      simp only [call1,Except.ok.injEq,Prod.mk.injEq] at run
      obtain ⟨rfl,-⟩ := run
      exact ⟨middle,yesRegs,noRegs,rfl,call1,
        stock_branchArgs_selected_marks func source (by simp [term,dests]) call0,
        stock_branchArgs_selected_marks func source (by simp [term,dests]) call1⟩

private theorem mapped_member {ctx : Ctx} {xs : List Nat} {rs : List Reg}
    (mapped : xs.mapM ctx.valueReg? = some rs) {x : Nat} (member : x ∈ xs) :
    ∃ r,ctx.valueReg? x = some r := by
  induction xs generalizing rs with
  | nil => cases member
  | cons y ys ih =>
    simp only [List.mapM_cons,Option.bind_eq_bind,Option.bind_eq_some_iff,
      Option.pure_def,Option.some.injEq] at mapped
    obtain ⟨r,lookup,tail,rest,rfl⟩ := mapped
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨r,lookup⟩
    · exact ih rest member

private theorem marks_size (xs : List Nat) (st : State) :
    (xs.foldl State.mark st).demand.size = st.demand.size := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih =>
    simpa only [List.foldl_cons,State.mark,Array.size_modify] using ih (st.mark x)

private theorem view_avail {ctx original : Ctx}
    (view : DFGViewEq ctx original) (f : Clif.Function) :
    availIn f ctx = availIn f original := by
  have args : defArgs ctx = defArgs original := by
    funext x
    simp only [defArgs,Ctx.defInst?,view.valDef,view.insts]
  have users : fUsers ctx = fUsers original := by
    simp only [fUsers,usersN,args,view.valDef]
  have bytes : fInB0 f ctx id = fInB0 f original id := by
    unfold fInB0
    rw [view.valDef]
  have work : fWork0 f ctx id = fWork0 f original id := by
    simp only [fWork0,view.valDef,bytes,args]
  simp only [availIn,inFix_eq,users,bytes,work,view.valDef]

/-- Every source argument of either original successor is demanded after the body. -/
theorem ConditionalBodySpec.arguments_demanded {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (term : b.term = .brif c yes no) {first second yesBlock noBlock : Nat}
    (targets : result.order.successors[label]! = #[first,second])
    (firstTag : result.order.nodes[first]? = some (.original yesBlock))
    (secondTag : result.order.nodes[second]? = some (.original noBlock))
    {x : Nat} (member : x ∈ yes.args ∨ x ∈ no.args) :
    Demanded spec.term.output.state x := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  have func := (buildCtx_mappedInv scope spec.build).func
  have coreRun := spec.coreRun
  rw [targets] at coreRun
  obtain ⟨emission,afterEdges,_,_,outgoing,scanInput,_,branchFlag,_⟩ :=
    conditional_core_calls term coreRun
  obtain ⟨middle,yesRegs,noRegs,yesCall,noCall,middleEq,afterEq⟩ :=
    stock_collect_conditional_marks func source term firstTag secondTag outgoing
  have outputDemand := (stock_branch_scan_body_code spec.split branchFlag).2
  have terminal : spec.term ∈ spec.core.scan.output.records := by
    rw [spec.split.records]
    exact List.mem_cons_self ..
  obtain ⟨r,mapped⟩ : ∃ r,result.ctx.valueReg? x = some r := by
    rcases member with member | member
    · exact mapped_member (stock_branchArgs_selected_mapping func source
        (by simp [term,dests]) yesCall) member
    · exact mapped_member (stock_branchArgs_selected_mapping func source
        (by simp [term,dests]) noCall) member
  have currentMap : spec.core.scan.ctx.valueReg? x = some r := by
    rw [(stock_lower_record_context run scope spec.events).2.1 x]
    exact mapped
  have bound := (Extent.lower_mapped_demand_bounds run scope spec.events terminal currentMap).1
  rw [spec.split.termInput,scanInput] at bound
  have startBound : x < emission.state.demand.size := by
    have size : afterEdges.demand.size = emission.state.demand.size := by
      rw [afterEq,marks_size,middleEq,marks_size]
    rw [← size]
    exact bound
  have middleBound : x < (yes.args.foldl State.mark emission.state).demand.size := by
    rw [marks_size]
    exact startBound
  have marked : Demanded (no.args.foldl State.mark (yes.args.foldl State.mark emission.state)) x := by
    rcases member with member | member
    · exact (demanded_markList_iff _ _ x middleBound).mpr
        (Or.inr ((demanded_markList_iff _ _ x startBound).mpr (Or.inl member)))
    · exact (demanded_markList_iff _ _ x middleBound).mpr (Or.inl member)
  unfold Demanded at marked ⊢
  rw [outputDemand,spec.split.termInput,scanInput]
  rw [afterEq,middleEq] at *
  exact marked

/-- A guarded post-body frame holds the source arguments of either original successor. -/
theorem ConditionalBodySpec.argument_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (term : b.term = .brif c yes no) {first second yesBlock noBlock : Nat}
    (targets : result.order.successors[label]! = #[first,second])
    (firstTag : result.order.nodes[first]? = some (.original yesBlock))
    (secondTag : result.order.nodes[second]? = some (.original noBlock))
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
      (b.body.length,fr,cm) ρ w)
    {bc : Clif.BlockCall} (selected : bc = yes ∨ bc = no) :
    ValuesHeld (fun x => x ∈ bc.args) result.ctx fr (fun k => ρ (aliasNum result.final.alias k)) := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  obtain ⟨original,st0,oldBuild,_,view⟩ := buildCtx_source spec.build
  intro x member v read
  have either : x ∈ yes.args ∨ x ∈ no.args :=
    selected.elim (fun same => Or.inl (same ▸ member)) (fun same => Or.inr (same ▸ member))
  have available := (dominated.uses original spec.ranges st0 oldBuild bi b source).2 x
    (by rcases either with inside | inside <;> simp [term,abiTerm,Driver.termArgs,inside])
  have available' : x ∈ availOf f (availIn f result.ctx) spec.core.scan.block b.body.length := by
    rw [spec.atBlock,view_avail view f]
    exact available
  obtain ⟨n,mapped,value⟩ := held.2.2.2 x
    ⟨spec.arguments_demanded run scope term targets firstTag secondTag either,available'⟩ v read
  refine ⟨n,?_,value⟩
  rw [← (stock_lower_record_context run scope spec.events).2.1 x]
  exact mapped

end Backend.Stock.Proof.ConditionalValues

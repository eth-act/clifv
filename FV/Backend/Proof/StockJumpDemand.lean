import FV.Backend.Proof.StockBranchArgumentDemand
import FV.Backend.Proof.StockJumpBodyRefines
import FV.Backend.Proof.StockDemandExtent

namespace Backend.Stock.Proof.Control
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm branchArgs emitBranch collectOutgoing scanBlock lowerBlockCore

/-- The actual single original successor collects all source jump arguments
before scanning the predecessor body. -/
theorem stock_collect_jump_marks {ctx : Ctx} {f : Clif.Function}
    (func : ctx.func = f) {bi label tl : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (source : f.blocks[bi]? = some b) (jump : b.term = .jump bc) {order : Order}
    (target : order.nodes[label]? = some (.original tl))
    {input next : State} {outgoing : Array (Array Reg)}
    (run : collectOutgoing ctx order bi #[label] input = .ok (next,outgoing)) :
    ∃ args,branchArgs ctx input bi 0 = .ok (args,next) ∧
      next = bc.args.foldl State.mark input := by
  have tag : order.nodes[label]! = .original tl := by simp [getElem!_def,target]
  simp only [collectOutgoing] at run
  change ([(label,0)] : List (Nat × Nat)).foldlM (outgoingStep ctx order bi)
    (input,#[]) = .ok (next,outgoing) at run
  simp only [List.foldlM_cons,List.foldlM_nil,pure,Except.pure] at run
  unfold outgoingStep at run
  simp only [tag] at run
  cases call : branchArgs ctx input bi 0 with
  | error e => simp only [call,bind,Except.bind] at run; cases run
  | ok pair =>
    obtain ⟨args,state⟩ := pair
    simp only [call,bind,Except.bind,pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    exact ⟨args,rfl,stock_branchArgs_selected_marks func source (by rw [jump]; rfl) call⟩

/-- Outgoing demand reaches the retained scan of the same actual core, rather
than a separately selected existential block. The branch emission is retained. -/
theorem stock_jump_core_outgoing_marks {ctx : Ctx} {f : Clif.Function}
    (func : ctx.func = f) {bi label tl start stop : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (source : f.blocks[bi]? = some b) (jump : b.term = .jump bc) {order : Order}
    (target : order.nodes[label]? = some (.original tl))
    {input : State} {data : V} {core : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi start stop data #[label] input = .ok core) :
    ∃ branch args,core.branch = some branch ∧ core.scan.isBranch = true ∧
      branchArgs ctx branch.state bi 0 = .ok (args,bc.args.foldl State.mark branch.state) ∧
      collectOutgoing ctx order bi #[label] branch.state =
        .ok (bc.args.foldl State.mark branch.state,core.outgoing) ∧
      core.scan.input.demand = (bc.args.foldl State.mark branch.state).demand := by
  let actualCtx : Ctx := {ctx with
    insts := ctx.insts.set! (stop-1) ⟨data,[],[],none⟩
    tryRegs := input.tryRegs[stop-1]!}
  unfold lowerBlockCore at run
  dsimp only at run
  simp only [jump] at run
  cases branchCall : emitBranch actualCtx f (.jump bc) bi (stop-1) #[label] input with
  | error message =>
    dsimp only [actualCtx] at branchCall
    simp only [branchCall,Functor.map,Except.map,bind,Except.bind] at run
    cases run
  | ok emission =>
    dsimp only [actualCtx] at branchCall
    simp only [branchCall,Functor.map,Except.map,bind,Except.bind,Option.map_some,Option.getD_some] at run
    cases collected : collectOutgoing ctx order bi #[label] emission.state with
    | error message => simp only [collected,bind,Except.bind] at run; cases run
    | ok pair =>
      obtain ⟨next,args⟩ := pair
      obtain ⟨registers,call,marked⟩ := stock_collect_jump_marks func source jump target collected
      cases scanned : scanBlock actualCtx bi (stop-1) true
          (((Array.range (stop-start)).map (start+·)).reverse.toList)
          {next with color := some next.endColor[bi]!} with
      | error message =>
        dsimp only [actualCtx] at scanned
        simp only [collected,scanned,bind,Except.bind] at run
        cases run
      | ok scan =>
        dsimp only [actualCtx] at scanned
        simp only [collected,scanned,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at run
        cases run
        exact ⟨emission,registers,rfl,rfl,by simpa only [marked] using call,
          by simpa only [marked] using collected,by simp only [marked]⟩

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

/-- Every source argument of the actual direct jump is demanded after the
body. Both the register mapping and the demand-array bound are derived from
the original compiler run; no extra accepted-program condition is required. -/
theorem stock_jump_body_arguments_demanded {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi : Nat} {bc : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : JumpBodySpec f result b label bi bc isem MR env cp)
    (jump : b.term = .jump bc) {tl : Nat}
    (target : result.order.nodes[spec.target]? = some (.original tl)) :
    ∀ x ∈ bc.args,Demanded spec.term.output.state x := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  have targets : result.order.successors[label]! = #[spec.target] := Array.toList_inj.mp spec.targets
  have coreRun := spec.coreRun
  rw [targets] at coreRun
  have func := (buildCtx_mappedInv scope spec.build).func
  obtain ⟨branch,args,branchEq,branchFlag,call,collected,demand⟩ :=
    stock_jump_core_outgoing_marks func source jump target coreRun
  have mapping := stock_branchArgs_selected_mapping func source (by rw [jump]; rfl) call
  have outputDemand := (stock_branch_scan_body_code spec.split branchFlag).2
  have terminal : spec.term ∈ spec.core.scan.output.records := by
    rw [spec.split.records]
    exact List.mem_cons_self ..
  intro x member
  obtain ⟨r,mapped⟩ := mapped_member mapping member
  have currentMap : spec.core.scan.ctx.valueReg? x = some r := by
    rw [(stock_lower_record_context run scope spec.events).2.1 x]
    exact mapped
  have bound := (Extent.lower_mapped_demand_bounds run scope spec.events terminal currentMap).1
  rw [spec.split.termInput] at bound
  have initialBound : x < branch.state.demand.size := by
    rw [demand,marks_size] at bound
    exact bound
  have marked := (demanded_markList_iff branch.state bc.args x initialBound).mpr (Or.inl member)
  change spec.term.output.state.demand[x]! ≠ 0
  rw [outputDemand,spec.split.termInput,demand]
  exact marked

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

/-- A real post-body guard supplies every outgoing source value. Demand,
availability and the scan-to-global register-map correspondence are all derived
internally, preserving the original input conditions. -/
theorem stock_jump_body_argument_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi : Nat} {bc : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : JumpBodySpec f result b label bi bc isem MR env cp)
    (jump : b.term = .jump bc) {tl : Nat}
    (target : result.order.nodes[spec.target]? = some (.original tl))
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
      (b.body.length,fr,cm) ρ w) :
    ValuesHeld (fun x => x ∈ bc.args) result.ctx fr (fun k => ρ (aliasNum result.final.alias k)) := by
  have demanded := stock_jump_body_arguments_demanded run scope spec jump target
  have source := spec.split.block
  rw [spec.atBlock] at source
  obtain ⟨original,st0,oldBuild,ctxSpec,view⟩ := buildCtx_source spec.build
  intro x member v read
  have available := (dominated.uses original spec.ranges st0 oldBuild bi b source).2 x
    (by simpa only [jump,abiTerm,Driver.termArgs] using member)
  have available' : x ∈ availOf f (availIn f result.ctx) spec.core.scan.block b.body.length := by
    rw [spec.atBlock,view_avail view f]
    exact available
  obtain ⟨n,mapped,value⟩ := held.2.2.2 x ⟨demanded x member,available'⟩ v read
  refine ⟨n,?_,value⟩
  rw [← (stock_lower_record_context run scope spec.events).2.1 x]
  exact mapped

end Backend.Stock.Proof.Control

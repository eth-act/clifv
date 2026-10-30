import FV.Backend.Proof.StockDriverBounds
import FV.Backend.Proof.LowerAlias
import FV.Backend.Proof.StockBranchArgumentShape

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm lowerBlockCore branchArgs collectOutgoing scanBlock emitBranch

/-- All actual per-successor vectors in a collected row are virtual-int. -/
def RowArgumentShape (row : Array (Array Reg)) : Prop := ∀ args ∈ row.toList,ArgumentShape args

private theorem runTerm_regs {ctx : Ctx} {term : String} {args : List V}
    {st next : State} {out : Option V} {trace : List RuleId}
    (h : Stock.runTerm ctx term args st = .ok (out,next,trace)) : next.tryRegs = st.tryRegs := by
  unfold Stock.runTerm at h
  cases hr : Isle.Interp.run program (Stock.sem ctx) {} term args st with
  | error e => rw [hr] at h; cases h
  | ok result =>
    rw [hr] at h
    cases h
    unfold Isle.Interp.run at hr
    cases ht : program.termByName? term with
    | none => simp only [ht] at hr; cases hr
    | some t =>
      simp only [ht] at hr
      cases ha : (applyTerm program (Stock.sem ctx) {} (Config.fuel ({} : Config))
          t.ret t.id args).run (st,#[]) with
      | error e => simp only [ha,bind,Except.bind] at hr; cases hr
      | ok result =>
        rcases result with ⟨out,next,trace⟩
        simp only [ha,bind,Except.bind,pure,Except.pure] at hr
        cases hr
        exact (stock_apply_allocationLe ha).2

private theorem emit_regs {ctx : Ctx} {f : Clif.Function} {term : Clif.Terminator}
    {bi ti : Nat} {targets : Array Nat} {input : State} {out : BranchEmission}
    (run : emitBranch ctx f term bi ti targets input = .ok out) : out.state.tryRegs = input.tryRegs := by
  unfold emitBranch at run
  dsimp only at run
  let before := {input with current := some ti,color := none,base.emitted := #[]}
  change ((do
    let (value,next,trace) ← Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList] before
    if value.isNone then throw s!"no lowering rule for terminator {repr term}"
    let code ← branchCode f term targets next.base.emitted
    pure ⟨next,code,⟨bi,ti,.emitted,before,next,[],trace,code⟩,trace⟩) : Except String BranchEmission) = .ok out at run
  cases root : Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList] before with
  | error err => simp only [root,bind,Except.bind] at run; cases run
  | ok result =>
    rcases result with ⟨value,next,trace⟩
    simp only [root,bind,Except.bind] at run
    split at run
    · cases run
    · cases code : branchCode f term targets next.base.emitted with
      | error err => simp only [code,bind,Except.bind] at run; cases run
      | ok instructions =>
        simp only [code,pure,Except.pure] at run
        cases run
        exact runTerm_regs (st := before) root

private theorem outgoing_step_shape {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial))
    {order : Order} {bi : Nat} {input output : State × Array (Array Reg)} {target : Nat × Nat}
    (reservations : input.1.tryRegs = initial.tryRegs) (shaped : RowArgumentShape input.2)
    (run : outgoingStep ctx order bi input target = .ok output) :
    output.1.tryRegs = initial.tryRegs ∧ RowArgumentShape output.2 := by
  unfold outgoingStep at run
  split at run
  · cases run
    refine ⟨reservations,?_⟩
    intro args member
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with old | same
    · exact shaped args old
    · subst args; simp [ArgumentShape]
  · obtain ⟨⟨args,next⟩,call,run⟩ := Except.bind_ok run
    cases run
    obtain ⟨_,shape,frame⟩ := stock_branchArgs_shape build reservations call
    refine ⟨frame.trans reservations,?_⟩
    intro rs member
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with old | same
    · exact shaped rs old
    · subst rs; exact shape

private theorem collect_shape {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial))
    {order : Order} {bi : Nat} {targets : Array Nat} {input next : State} {row : Array (Array Reg)}
    (reservations : input.tryRegs = initial.tryRegs)
    (run : collectOutgoing ctx order bi targets input = .ok (next,row)) : RowArgumentShape row := by
  have fold : ∀ (xs : List (Nat × Nat)) (a b : State × Array (Array Reg)),
      a.1.tryRegs = initial.tryRegs → RowArgumentShape a.2 →
      xs.foldlM (outgoingStep ctx order bi) a = .ok b →
      b.1.tryRegs = initial.tryRegs ∧ RowArgumentShape b.2 := by
    intro xs
    induction xs with
    | nil => intro a b reserved shaped call; cases call; exact ⟨reserved,shaped⟩
    | cons x xs ih =>
      intro a b reserved shaped call
      rw [List.foldlM_cons] at call
      obtain ⟨middle,step,rest⟩ := Except.bind_ok call
      obtain ⟨reserved',shaped'⟩ := outgoing_step_shape build reserved shaped step
      exact ih middle b reserved' shaped' rest
  unfold collectOutgoing at run
  exact (fold _ (input,#[]) (next,row) reservations (by simp [RowArgumentShape]) run).2

private theorem core_shape {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial))
    {order : Order} {b : Clif.Block} {bi start stop : Nat} {data : V} {targets : Array Nat}
    {input : State} {core : LoweredBlockCore} (reservations : input.tryRegs = initial.tryRegs)
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) : RowArgumentShape core.outgoing := by
  unfold lowerBlockCore at run
  dsimp only at run
  let termCtx := {ctx with insts := ctx.insts.set! (stop-1) ⟨data,[],[],none⟩,tryRegs := input.tryRegs[stop-1]!}
  cases term : b.term <;> simp only [term,bind,Except.bind,pure,Except.pure,Option.map_none,Option.getD_none] at run
  all_goals try dsimp only at run
  all_goals first
    | (solve
        | obtain ⟨⟨next,row⟩,collected,run⟩ := Except.bind_ok run
          obtain ⟨scanned,_,run⟩ := Except.bind_ok run
          cases run
          exact collect_shape build reservations collected)
    | skip
  all_goals
    cases called : emitBranch termCtx f b.term bi (stop-1) targets input with
    | error err =>
      dsimp only [termCtx] at called
      rw [term] at called
      simp only [called,Functor.map,Except.map,bind,Except.bind] at run
      cases run
    | ok emitted =>
      have framed := (emit_regs called).trans reservations
      dsimp only [termCtx] at called
      rw [term] at called
      simp only [called,Functor.map,Except.map,bind,Except.bind,pure,Except.pure,Option.map_some,Option.getD_some] at run
      obtain ⟨⟨next,row⟩,collected,run⟩ := Except.bind_ok run
      obtain ⟨scanned,_,run⟩ := Except.bind_ok run
      cases run
      exact collect_shape build framed collected

private theorem node_shape {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial))
    {order : Order} {params : List Nat} {label : Nat} {input output : DriverState}
    (reservations : input.state.tryRegs = initial.tryRegs)
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    ∃ row,output.edgeArgs = input.edgeArgs.set! label row ∧ RowArgumentShape row := by
  unfold lowerNode at run
  cases tag : order.nodes[label]! with
  | edge pred index target =>
    simp only [tag] at run
    obtain ⟨⟨args,next⟩,call,run⟩ := Except.bind_ok run
    cases run
    have shape := (stock_branchArgs_shape build reservations call).2.1
    exact ⟨#[args],rfl,by simpa [RowArgumentShape] using shape⟩
  | original bi =>
    simp only [tag] at run
    repeat' first
      | (solve | cases run)
      | (solve | cases run; exact ⟨_,rfl,core_shape build reservations (by assumption)⟩)
      | simp only [bind,Except.bind,pure,Except.pure] at run
      | split at run

private def AllRows (rows : Array (Array (Array Reg))) : Prop :=
  ∀ (b : Nat) (row : Array (Array Reg)),rows[b]? = some row → RowArgumentShape row

private theorem set_rows {rows : Array (Array (Array Reg))} (shape : AllRows rows)
    (b : Nat) {row : Array (Array Reg)} (shaped : RowArgumentShape row) : AllRows (rows.set! b row) := by
  intro k rs lookup
  rw [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds] at lookup
  split at lookup
  · split at lookup
    · cases lookup; exact shaped
    · cases lookup
  · exact shape k rs lookup

private theorem nodes_shape {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial))
    {order : Order} {params labels : List Nat} {input output : DriverState}
    (bound : input.state.alias.size ≤ initial.base.nextVreg ∧ initial.base.nextVreg ≤ input.state.base.nextVreg ∧
      input.state.tryRegs = initial.tryRegs) (shaped : AllRows input.edgeArgs)
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output) : AllRows output.edgeArgs := by
  induction labels generalizing input with
  | nil => cases run; exact shaped
  | cons label rest ih =>
    rw [List.foldlM_cons] at run
    obtain ⟨middle,step,restRun⟩ := Except.bind_ok run
    obtain ⟨row,installed,rowShape⟩ := node_shape build bound.2.2 step
    have middleBound := stock_lowerNode_allocationBounds build bound step
    have middleShape : AllRows middle.edgeArgs := by rw [installed]; exact set_rows shaped label rowShape
    exact ih middleBound middleShape restRun

private def startDriver (initial : State) (n : Nat) : DriverState := {
  state := initial,blocks := Array.replicate n default,edgeArgs := Array.replicate n #[],
  schedule := #[],scans := #[],blockScans := #[],rules := #[] }

/-- Every outgoing vector of every actual complete Stock driver is virtual-int,
including ordinary values and TryCall return/payload registers. Actual build,
reservation preservation, collection, traversal and final aliasing derive this
without a caller-provided state or vector certificate. -/
theorem stock_lower_outgoing_shape {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    ∀ (b j : Nat) (row : Array (Array Reg)) (args : Array Reg),
      result.edgeArgs[b]? = some row → row[j]? = some args → ArgumentShape args := by
  have origin : ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (driver : DriverState),
      Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) ∧
      (Array.range result.order.nodes.size).reverse.toList.foldlM
        (fun d k => lowerNode result.ctx ranges result.order f params k d)
        (startDriver result.initial result.order.nodes.size) = .ok driver ∧
      result.edgeArgs = driver.edgeArgs.map (fun row => row.map fun rs => rs.map
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) := by
    unfold Stock.lower at run
    dsimp only at run
    repeat' first
      | (solve | cases run)
      | simp only [bind,Except.bind,pure,Except.pure] at run
      | split at run
    cases run
    exact ⟨_,_,_,by assumption,by assumption,rfl⟩
  obtain ⟨ranges,params,driver,build,folded,edges⟩ := origin
  have initialBound : result.initial.alias.size ≤ result.initial.base.nextVreg := by
    obtain ⟨original,st0,requests,_,_,same⟩ := buildCtx_allocation build
    have state := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2) same
    change result.initial = _ at state
    rw [state]
    exact Nat.zero_le _
  have all := nodes_shape build ⟨initialBound,Nat.le_refl _,rfl⟩
    (input := startDriver result.initial result.order.nodes.size)
    (by intro b row found; simp [startDriver,Array.getElem?_replicate] at found; rcases found with ⟨_,rfl⟩; simp [RowArgumentShape]) folded
  intro b j row args atRow atArgs
  rw [edges,Array.getElem?_map] at atRow
  obtain ⟨originalRow,sourceRow,sameRow⟩ := Option.map_eq_some_iff.mp atRow
  subst row
  rw [Array.getElem?_map] at atArgs
  obtain ⟨originalArgs,sourceArgs,sameArgs⟩ := Option.map_eq_some_iff.mp atArgs
  subst args
  have vector := all b originalRow sourceRow originalArgs (Array.mem_toList_iff.mpr (Array.mem_of_getElem? sourceArgs))
  intro r member
  simp only [Array.toList_map,List.mem_map] at member
  obtain ⟨old,inside,rfl⟩ := member
  obtain ⟨n,rfl⟩ := vector old inside
  exact ⟨_,by rw [resolve_vreg]⟩

end Backend.Stock.Proof

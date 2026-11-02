import FV.Backend.Proof.StockCfgTraversalScans
import FV.Backend.Proof.StockCfgJumpDemand

namespace Backend.Stock.Proof.CfgDemand
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private def DemandLE (before after : State) :=
  ∀ (x : Nat),before.demand[x]! ≤ after.demand[x]!

private theorem demand_refl (st : State) : DemandLE st st := fun _ => Nat.le_refl _
private theorem demand_trans {a b c : State} (ab : DemandLE a b) (bc : DemandLE b c) :
    DemandLE a c := fun x => Nat.le_trans (ab x) (bc x)

private theorem mark_mono (st : State) (v : Nat) : DemandLE st (st.mark v) := by
  intro x
  by_cases equal : x = v
  · subst x
    by_cases bounded : v < st.demand.size
    · rw [(mark_demand st v bounded).1]
      omega
    · change st.demand[v]! ≤ (st.demand.modify v (· + 1))[v]!
      have small : ¬ v < (st.demand.modify v (· + 1)).size := by simpa only [Array.size_modify] using bounded
      simp only [getElem!_def, Array.getElem?_eq_none (Nat.le_of_not_lt bounded),
        Array.getElem?_eq_none (Nat.le_of_not_lt small), Option.getD_none]
      exact Nat.le_refl _
  · rw [mark_other st v x equal]
    exact Nat.le_refl _
private theorem setAlias_demand {st next : State} {dst src : Reg}
    (h : st.setAlias dst src = .ok next) : next.demand = st.demand := by
  cases dst <;> cases src <;>
    simp only [State.setAlias, bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at h
  all_goals repeat' first | (solve | cases h) | (solve | cases h; rfl) | split at h

private theorem forIn_demand {α β : Type} (field : α → State)
    (step : β → α → Except String (ForInStep α))
    (keeps : ∀ x a b, step x a = .ok (.yield b) → DemandLE (field a) (field b))
    (no_break : ∀ x a b, step x a ≠ .ok (.done b))
    (xs : List β) {a next : α} (h : forIn xs a step = .ok next) :
    DemandLE (field a) (field next) := by
  induction xs generalizing a with
  | nil => simp only [List.forIn_nil, pure, Except.pure] at h; cases h; exact demand_refl _
  | cons x xs ih =>
    rw [List.forIn_cons] at h
    cases call : step x a with
    | error e => simp only [call, bind, Except.bind] at h; cases h
    | ok result =>
      cases result with
      | done b => exact False.elim (no_break x a b call)
      | yield b =>
        simp only [call, bind, Except.bind] at h
        exact demand_trans (keeps x a b call) (ih h)

private def argStep (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (acc : State × Array Reg) :
    Except String (ForInStep (State × Array Reg)) := do
  match arg with
  | .val v =>
    let some r := ctx.valueReg? v | throw s!"unknown value v{v}"
    pure (.yield (acc.1.mark v, acc.2.push r))
  | .ret i =>
    if index < nh then throw "try_call return on exception edge"
    let some r := rets[i]? | throw "try_call return index"
    pure (.yield (acc.1, acc.2.push r))
  | .exn i =>
    if index == nh then throw "try_call payload on normal edge"
    let some r := pays[i]? | throw "try_call payload index"
    pure (.yield (acc.1, acc.2.push r))

private theorem arg_demand (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (a b : State × Array Reg)
    (h : argStep ctx rets pays index nh arg a = .ok (.yield b)) :
    DemandLE a.1 b.1 := by
  cases arg <;> unfold argStep at h
  all_goals repeat' first | (solve | cases h <;> exact mark_mono _ _) | (solve | cases h <;> exact demand_refl _) | split at h

private theorem arg_no_break (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (a b : State × Array Reg) :
    argStep ctx rets pays index nh arg a ≠ .ok (.done b) := by
  intro h
  cases arg <;> unfold argStep at h
  all_goals repeat' first | (solve | cases h) | split at h

private theorem branch_demand {ctx : Ctx} {st next : State} {block index : Nat}
    {args : Array Reg} (h : branchArgs ctx st block index = .ok (args, next)) :
    DemandLE st next := by
  unfold branchArgs at h
  dsimp only at h
  split at h
  · rename_i id values lookup
    split at h
    · rename_i target found
      split at h
      · cases h
      · let ti := (st.instBlock.findIdx? (· == block)).getD 0 + ctx.func.blocks[block]!.body.length
        let reservations := st.tryRegs[ti]!
        let nh := match ctx.func.blocks[block]!.term with
          | .tryCall _ _ et | .tryCallIndirect _ _ et => et.handlers.length
          | _ => 0
        change (do
          let result ← forIn values (st, #[]) (argStep ctx reservations.1 reservations.2 index nh)
          pure (result.2, result.1)) = .ok (args, next) at h
        cases loop : forIn values (st, #[]) (argStep ctx reservations.1 reservations.2 index nh) with
        | error e => simp only [loop, bind, Except.bind] at h; cases h
        | ok result =>
          simp only [loop, bind, Except.bind, pure, Except.pure] at h
          cases h
          exact forIn_demand (fun a : State × Array Reg => a.1) _
            (arg_demand ctx reservations.1 reservations.2 index nh)
            (arg_no_break ctx reservations.1 reservations.2 index nh) values loop
    · cases h
  · cases h

private theorem fold_demand {α β : Type} (field : α → State)
    (step : α → β → Except String α)
    (hs : ∀ a b next, step a b = .ok next → DemandLE (field a) (field next))
    (xs : List β) {a next : α} (h : xs.foldlM step a = .ok next) :
    DemandLE (field a) (field next) := by
  induction xs generalizing a with
  | nil => cases h; exact demand_refl _
  | cons x xs ih =>
    rw [List.foldlM_cons] at h
    cases he : step a x with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok middle =>
      simp only [he, bind, Except.bind] at h
      exact demand_trans (hs a x middle he) (ih h)


private theorem outgoing_demand {ctx : Ctx} {order : Order} {bi : Nat} {targets : Array Nat}
    {st next : State} {outgoing : Array (Array Reg)}
    (h : collectOutgoing ctx order bi targets st = .ok (next, outgoing)) :
    DemandLE st next := by
  unfold collectOutgoing at h
  apply fold_demand (fun a : State × Array (Array Reg) => a.1) _ ?_ _ h
  intro acc target result step
  unfold outgoingStep at step
  split at step
  · cases step; exact demand_refl _
  · cases call : branchArgs ctx acc.1 bi target.2 with
    | error e => simp only [call, bind, Except.bind] at step; cases step
    | ok pair =>
      rcases pair with ⟨regs, state⟩
      simp only [call, bind, Except.bind, pure, Except.pure] at step
      cases step
      exact branch_demand call


/-- All ordinary, returned and exceptional successor arguments preserve
previous demand, including the actual marking of ordinary source values. -/
theorem branch_args_demand_mono {ctx : Ctx} {st next : State} {block index : Nat}
    {args : Array Reg} (run : branchArgs ctx st block index = .ok (args,next)) :
    ∀ (x : Nat),st.demand[x]! ≤ next.demand[x]! := branch_demand run

/-- Actual outgoing collection preserves demand through direct and synthetic
successor rows, including returned values and exception payloads. -/
theorem outgoing_demand_mono {ctx : Ctx} {order : Order} {bi : Nat} {targets : Array Nat}
    {st next : State} {args : Array (Array Reg)}
    (run : collectOutgoing ctx order bi targets st = .ok (next,args)) :
    ∀ (x : Nat),st.demand[x]! ≤ next.demand[x]! := outgoing_demand run
private def commitValue (ctx : Ctx) (st : State) (value : Nat) : Except String State := do
  if let some saved := st.opportunistic[value]! then
    let some dst := ctx.valueReg? value | throw s!"unknown v{value}"
    let [src] := saved.regs | throw "multi-register opportunistic definition"
    let next ← st.setAlias dst src
    pure {next with opportunistic := next.opportunistic.set! value none}
  else pure st

private theorem commit_value_demand {ctx : Ctx} {st next : State} {value : Nat}
    (run : commitValue ctx st value = .ok next) : DemandLE st next := by
  unfold commitValue at run
  split at run
  · split at run
    · split at run
      · obtain ⟨aliased,called,rest⟩ := Except.bind_ok run
        simp only [pure,Except.pure,Except.ok.injEq] at rest
        subst next
        intro x
        change st.demand[x]! ≤ aliased.demand[x]!
        rw [setAlias_demand called]
        exact Nat.le_refl _
      · cases run
    · cases run
  · cases run
    exact demand_refl _

private theorem commit_values_demand {ctx : Ctx} {values : List Nat} {st next : State}
    (run : commitOpportunisticValues ctx values st = .ok next) : DemandLE st next := by
  unfold commitOpportunisticValues at run
  apply fold_demand (fun s : State => s) _ ?_ values run
  intro input value output called
  change commitValue ctx input value = .ok output at called
  exact commit_value_demand called

private theorem commit_demand {ctx : Ctx} {block i : Nat} {st next : State}
    (run : commitOpportunistic ctx block i st = .ok (some next)) : DemandLE st next := by
  unfold commitOpportunistic at run
  dsimp only at run
  split at run
  · cases run
  · obtain ⟨committed,called,rest⟩ := Except.bind_ok run
    simp only [pure,Except.pure,Except.ok.injEq,Option.some.injEq] at rest
    subst next
    exact commit_values_demand called

private theorem emitted_demand {ctx : Ctx} {i : Nat} {st : State}
    {emission : Emission}
    (h : emitInstruction ctx i st = .ok emission) : DemandLE st emission.state := by
  unfold emitInstruction at h
  cases hr : Stock.runTerm ctx "lower" [.inst i] st with
  | error e => simp only [hr, bind, Except.bind] at h; cases h
  | ok root =>
    rcases root with ⟨out, next, trace⟩
    simp only [hr, bind, Except.bind] at h
    cases out with
    | none => cases h
    | some out =>
      cases out <;> try (cases h)
      rename_i rss
      dsimp only at h
      split at h
      · cases h
      · cases hb : bindResults ctx (ctx.insts[i]!.results.zip rss) next with
        | error e => simp only [hb] at h; cases h
        | ok result =>
          rcases result with ⟨final, copies⟩
          simp only [hb, pure, Except.pure] at h
          cases h
          have same : final.demand = next.demand := stock_bindResults_demand hb
          intro x
          rw [same]
          exact stock_named_demand_mono hr x


private theorem emitted_scan_demand {ctx : Ctx} {block i : Nat} {input : State} {output : Scan}
    (run : (emitInstruction ctx i (scanState input i) >>= fun e => pure (e.scan block i (scanState input i))) =
      .ok output) : DemandLE input output.state := by
  obtain ⟨emission,called,rest⟩ := Except.bind_ok run
  simp only [pure,Except.pure,Except.ok.injEq] at rest
  subst output
  intro x
  have le := emitted_demand called x
  simpa only [Emission.scan,scanState_demands] using le

/-- Every successful scan decision preserves demand: emitted, omitted, sunk,
branch-only and opportunistic paths are all covered without a source family
restriction or a replay certificate. -/
theorem instruction_demand_mono {ctx : Ctx} {block i ti : Nat} {isBranch : Bool}
    {input : State} {output : Scan}
    (run : scanInstruction ctx block i ti isBranch input = .ok output) :
    ∀ (x : Nat),input.demand[x]! ≤ output.state.demand[x]! := by
  by_cases sunk : input.sunk[i]! = true
  · simp only [scanInstruction,sunk,ite_true] at run
    cases run
    exact demand_refl _
  · simp only [scanInstruction,sunk] at run
    by_cases terminal : i = ti
    · subst ti
      cases isBranch <;>
        simp only [beq_self_eq_true,Bool.true_and,Bool.false_eq_true,ite_false,
          ite_true,Bool.not_true,Bool.false_and,Bool.and_false] at run
      · exact emitted_scan_demand run
      · cases run
        intro x
        change input.demand[x]! ≤ (scanState input i).demand[x]!
        rw [scanState_demands]
        exact Nat.le_refl _
    · have notTerm : (i == ti) = false := by simp [terminal]
      simp only [notTerm,Bool.false_and,Bool.false_eq_true,ite_false] at run
      split at run
      · cases run
        intro x
        change input.demand[x]! ≤ (scanState input i).demand[x]!
        rw [scanState_demands]
        exact Nat.le_refl _
      · split at run
        · cases called : commitOpportunistic ctx block i (scanState input i) with
          | error message => simp only [called,bind,Except.bind] at run; cases run
          | ok committed =>
            simp only [called,bind,Except.bind] at run
            cases committed with
            | none => exact emitted_scan_demand run
            | some next =>
              cases run
              intro x
              have le := commit_demand called x
              simpa only [scanState_demands] using le
        · exact emitted_scan_demand run

private theorem scans_demand {ctx : Ctx} {block ti : Nat} {isBranch : Bool}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec (fun i => scanInstruction ctx block i ti isBranch) indices input output) :
    DemandLE input output.state := by
  induction cert with
  | nil input => exact demand_refl _
  | cons head rest ih => exact demand_trans (instruction_demand_mono head) ih

/-- A complete real backward scan preserves every demand entering it, across
all ordinary instructions and its terminator. -/
theorem block_demand_mono {ctx : Ctx} {block ti : Nat} {isBranch : Bool}
    {indices : List Nat} {input : State} {output : BlockScan}
    (run : scanBlock ctx block ti isBranch indices input = .ok output) :
    ∀ (x : Nat),input.demand[x]! ≤ output.state.demand[x]! := by
  unfold scanBlock at run
  exact scans_demand (runScans_spec run)

private theorem core_input_demand {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : Backend.V} {targets : Array Nat}
    {input : State} {core : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    DemandLE input core.scan.input := by
  let branchCtx : Ctx := {ctx with
    insts := ctx.insts.set! (stop-1) ⟨data,[],[],none⟩
    tryRegs := input.tryRegs[stop-1]!}
  let branchFlag : Bool := match b.term with | .ret .. | .trap .. | .returnCall .. => false | _ => true
  let finish (emitted : Option BranchEmission) : Except String LoweredBlockCore := do
    let (next,outgoing) ← collectOutgoing ctx order bi targets ((emitted.map (·.state)).getD input)
    let beforeScan := {next with color := some next.endColor[bi]!}
    let indices := ((Array.range (stop-start)).map (start+·)).reverse.toList
    let body ← scanBlock branchCtx bi (stop-1) branchFlag indices beforeScan
    pure ⟨body.state,body.code ++ (emitted.map (·.code)).getD #[],outgoing,emitted,
      ⟨branchCtx,bi,stop-1,branchFlag,indices,beforeScan,body⟩⟩
  have normalized : lowerBlockCore ctx order f b bi start stop data targets input =
      ((if branchFlag then some <$> emitBranch branchCtx f b.term bi (stop-1) targets input
        else pure none) >>= finish) := by
    unfold lowerBlockCore
    change (if branchFlag then _ else _) = _
    by_cases flag : branchFlag = true <;> simp only [flag,ite_true,ite_false] <;> rfl
  rw [normalized] at run
  obtain ⟨emitted,selected,rest⟩ := Except.bind_ok run
  change (if branchFlag then some <$> emitBranch branchCtx f b.term bi (stop-1) targets input
    else pure none) = .ok emitted at selected
  have branchMono : DemandLE input ((emitted.map (·.state)).getD input) := by
    cases flag : branchFlag with
    | false =>
      simp only [flag,Bool.false_eq_true,ite_false,pure,Except.pure] at selected
      cases selected
      exact demand_refl _
    | true =>
      simp only [flag,ite_true] at selected
      cases called : emitBranch branchCtx f b.term bi (stop-1) targets input with
      | error message => simp only [called,Functor.map,Except.map] at selected; cases selected
      | ok branch =>
        simp only [called,Functor.map,Except.map] at selected
        cases selected
        have mono := Control.emit_branch_demand_mono called
        exact mono
  unfold finish at rest
  obtain ⟨pair,collected,rest⟩ := Except.bind_ok rest
  obtain ⟨next,args⟩ := pair
  dsimp only at rest
  obtain ⟨body,scanned,rest⟩ := Except.bind_ok rest
  simp only [pure,Except.pure,Except.ok.injEq] at rest
  subst core
  change DemandLE input next
  exact demand_trans branchMono (outgoing_demand collected)

/-- Real block cores preserve incoming demand both before the backward scan
and after the whole core, including branches and all outgoing argument forms. -/
theorem core_demand_mono {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : Backend.V} {targets : Array Nat}
    {input : State} {core : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    (∀ (x : Nat),input.demand[x]! ≤ core.scan.input.demand[x]!) ∧
    (∀ (x : Nat),input.demand[x]! ≤ core.state.demand[x]!) := by
  have before := core_input_demand run
  have origin := stock_lowerBlockCore_scanOrigin run
  have scanned := block_demand_mono origin.2.2.2.2.2
  refine ⟨before,?_⟩
  intro x
  rw [origin.1]
  exact Nat.le_trans (before x) (scanned x)

/-- Every actual original or synthetic-node transition preserves demand. -/
theorem node_demand_mono {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    ∀ (x : Nat),input.state.demand[x]! ≤ output.state.demand[x]! := by
  cases node : order.nodes[label]! with
  | original bi =>
    obtain ⟨data,core,called,state,scans⟩ := LinearCfg.original_node_scan run node
    rw [state]
    exact (core_demand_mono called).2
  | edge pred index target =>
    unfold lowerNode at run
    simp only [node] at run
    cases called : branchArgs ctx input.state pred index with
    | error message => simp only [called,bind,Except.bind] at run; cases run
    | ok pair =>
      obtain ⟨args,next⟩ := pair
      simp only [called,bind,Except.bind,pure,Except.pure] at run
      cases run
      exact branch_args_demand_mono called

/-- Demand flows through any actual compiler traversal segment, including
arbitrary intervening ordinary blocks and synthetic critical-edge nodes. -/
theorem traversal_demand_mono {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {labels : List Nat} {input output : DriverState}
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output) :
    ∀ (x : Nat),input.state.demand[x]! ≤ output.state.demand[x]! :=
  fold_demand (fun d : DriverState => d.state) _
    (fun _ _ _ called => node_demand_mono called) labels run

/-- A successor's retained demands reach a later predecessor terminator through
its actual compiler traversal, including any intervening ordinary or edge nodes.
The scan identities and intermediate states come from the successful driver run. -/
theorem ordered_scan_demand {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {earlier intervening suffix : List Nat} {firstLabel secondLabel : Nat}
    {first second : BlockScanEvent} {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (labels : (Array.range result.order.nodes.size).reverse.toList =
      earlier ++ firstLabel :: (intervening ++ secondLabel :: suffix))
    (firstTag : result.order.nodes[firstLabel]! = .original first.block)
    (secondTag : result.order.nodes[secondLabel]! = .original second.block)
    (fm : first ∈ result.blockScans.toList) (sm : second ∈ result.blockScans.toList)
    (split : SourceBodySplit f second b term body) :
    ∀ (x : Nat),first.output.state.demand[x]! ≤ term.output.state.demand[x]! := by
  obtain ⟨ranges,params,input,afterFirst,beforeSecond,fc,sc,fd,sd,
    build,fr,sr,state,gap,fcm,scm⟩ :=
    CfgTrace.actual_ordered_original_cores run labels firstTag secondTag
  have fo := stock_lowerBlockCore_scanOrigin fr
  have so := stock_lowerBlockCore_scanOrigin sr
  have feq : first = fc.scan := CfgTrace.actual_scan_unique run scope fm fcm fo.2.2.1.symm
  have seq : second = sc.scan := CfgTrace.actual_scan_unique run scope sm scm so.2.2.1.symm
  have through := traversal_demand_mono gap
  have before := (core_demand_mono sr).1
  have terminal := instruction_demand_mono split.termRun
  intro x
  have firstState : first.output.state = afterFirst.state := by rw [feq,state,fo.1]
  have secondInput : sc.scan.input = term.input := by rw [← seq,split.termInput]
  rw [firstState]
  exact Nat.le_trans (through x) (Nat.le_trans (by simpa only [secondInput] using before x) (terminal x))

/-- The actual descending label order supplies the traversal decomposition.
Callers need only the successor/predecessor label inequality, not a traversal
certificate, independently selected states or adjacency of original blocks. -/
theorem ordered_scan_demand_of_labels {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {firstLabel secondLabel : Nat} {first second : BlockScanEvent}
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (bounded : firstLabel < result.order.nodes.size) (before : secondLabel < firstLabel)
    (firstTag : result.order.nodes[firstLabel]! = .original first.block)
    (secondTag : result.order.nodes[secondLabel]! = .original second.block)
    (fm : first ∈ result.blockScans.toList) (sm : second ∈ result.blockScans.toList)
    (split : SourceBodySplit f second b term body) :
    ∀ (x : Nat),first.output.state.demand[x]! ≤ term.output.state.demand[x]! := by
  have firstMember : firstLabel ∈ (Array.range result.order.nodes.size).reverse.toList := by
    simpa only [Array.toList_reverse,Array.toList_range,List.mem_reverse,List.mem_range] using bounded
  obtain ⟨earlier,rest,labels⟩ := List.append_of_mem firstMember
  have remaining := (stock_backward_suffix_split labels).2
  have secondMember : secondLabel ∈ rest := by
    rw [remaining]
    simpa only [Array.toList_reverse,Array.toList_range,List.mem_reverse,List.mem_range] using before
  obtain ⟨intervening,suffix,restEq⟩ := List.append_of_mem secondMember
  rw [restEq] at labels
  exact ordered_scan_demand run scope labels firstTag secondTag fm sm split

/-- Every retained scan's input and output demands survive the actual remaining
traversal to the returned final state, without any source-family restriction. -/
theorem retained_scan_final_demand {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (member : event ∈ result.blockScans.toList) :
    (∀ (x : Nat),event.input.demand[x]! ≤ result.final.demand[x]!) ∧
    (∀ (x : Nat),event.output.state.demand[x]! ≤ result.final.demand[x]!) := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run member
  have origin := stock_lowerBlockCore_scanOrigin coreRun
  have tail := traversal_demand_mono suffixRun
  have scanned := block_demand_mono origin.2.2.2.2.2
  have outputState : event.output.state = after.state := by rw [eventEq,stateEq,origin.1]
  have finish : ∀ (x : Nat),event.output.state.demand[x]! ≤ result.final.demand[x]! := by
    intro x
    rw [outputState,← final]
    exact tail x
  refine ⟨?_,finish⟩
  intro x
  rw [eventEq]
  exact Nat.le_trans (scanned x) (by simpa only [eventEq] using finish x)

end Backend.Stock.Proof.CfgDemand

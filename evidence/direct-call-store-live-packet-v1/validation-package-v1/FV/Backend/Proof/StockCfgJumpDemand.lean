import FV.Backend.Proof.RegallocInstsFP
import FV.Backend.Proof.StockJumpDemand
import FV.Backend.Proof.StockDemandMono

namespace Backend.Stock.Proof.Control
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm collectOutgoing scanBlock

/-- Real branch emission retains every preexisting demand count. -/
theorem emit_branch_demand_mono {ctx : Ctx} {f : Clif.Function} {term : Clif.Terminator}
    {bi ti : Nat} {targets : Array Nat} {input : State} {output : BranchEmission}
    (run : emitBranch ctx f term bi ti targets input = .ok output) :
    ∀ (x : Nat),input.demand[x]! ≤ output.state.demand[x]! := by
  unfold emitBranch at run
  cases called : Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList]
      {input with current := some ti,color := none,base.emitted := #[]} with
  | error e => simp only [called,bind,Except.bind] at run; cases run
  | ok triple =>
    obtain ⟨value,next,trace⟩ := triple
    simp only [called,bind,Except.bind] at run
    cases value with
    | none => simp at run
    | some value =>
      simp only [Option.isNone_some,Bool.false_eq_true,ite_false] at run
      cases code : branchCode f term targets next.base.emitted with
      | error e => simp only [code,bind,Except.bind] at run; cases run
      | ok code =>
        simp only [code,bind,Except.bind,pure,Except.pure] at run
        cases run
        have mono := stock_named_demand_mono called
        exact mono

private theorem mark_demand_mono (st : State) (value : Nat) :
    ∀ (x : Nat),st.demand[x]! ≤ (st.mark value).demand[x]! := by
  intro x
  by_cases same : x = value
  · subst x
    by_cases bound : value < st.demand.size
    · rw [(mark_demand st value bound).1]; omega
    · change st.demand[value]! ≤ (st.demand.modify value (·+1))[value]!
      have small : ¬ value < (st.demand.modify value (·+1)).size := by simpa only [Array.size_modify] using bound
      simp only [getElem!_def,Array.getElem?_eq_none (Nat.le_of_not_lt bound),
        Array.getElem?_eq_none (Nat.le_of_not_lt small),Option.getD_none]
      exact Nat.le_refl _
  · rw [mark_other st value x same]
    exact Nat.le_refl _

private theorem marks_demand_mono (values : List Nat) (st : State) :
    ∀ (x : Nat),st.demand[x]! ≤ (values.foldl State.mark st).demand[x]! := by
  induction values generalizing st with
  | nil => exact fun _ => Nat.le_refl _
  | cons value values ih =>
    intro x
    exact Nat.le_trans (mark_demand_mono st value x) (ih (st.mark value) x)

/-- Before reverse-scanning a jump body, real emission and outgoing collection
retain every demand already supplied by a later compiled block. -/
theorem jump_core_input_demand_mono {ctx : Ctx} {f : Clif.Function}
    (func : ctx.func = f) {bi label tl start stop : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (source : f.blocks[bi]? = some b) (jump : b.term = .jump bc) {order : Order}
    (target : order.nodes[label]? = some (.original tl))
    {input : State} {data : V} {core : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi start stop data #[label] input = .ok core) :
    core.scan.isBranch = true ∧ ∀ (x : Nat),input.demand[x]! ≤ core.scan.input.demand[x]! := by
  let actualCtx : Ctx := {ctx with
    insts := ctx.insts.set! (stop-1) ⟨data,[],[],none⟩
    tryRegs := input.tryRegs[stop-1]!}
  unfold lowerBlockCore at run
  dsimp only at run
  simp only [jump] at run
  cases branchCall : emitBranch actualCtx f (.jump bc) bi (stop-1) #[label] input with
  | error e =>
    dsimp only [actualCtx] at branchCall
    simp only [branchCall,Functor.map,Except.map,bind,Except.bind] at run; cases run
  | ok emission =>
    dsimp only [actualCtx] at branchCall
    simp only [branchCall,Functor.map,Except.map,bind,Except.bind,Option.map_some,Option.getD_some] at run
    cases collected : collectOutgoing ctx order bi #[label] emission.state with
    | error e => simp only [collected,bind,Except.bind] at run; cases run
    | ok pair =>
      obtain ⟨next,args⟩ := pair
      obtain ⟨registers,call,marked⟩ := stock_collect_jump_marks func source jump target collected
      cases scanned : scanBlock actualCtx bi (stop-1) true
          (((Array.range (stop-start)).map (start+·)).reverse.toList)
          {next with color := some next.endColor[bi]!} with
      | error e =>
        dsimp only [actualCtx] at scanned
        simp only [collected,scanned,bind,Except.bind] at run; cases run
      | ok scan =>
        dsimp only [actualCtx] at scanned
        simp only [collected,scanned,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at run
        cases run
        refine ⟨rfl,?_⟩
        intro x
        change input.demand[x]! ≤ next.demand[x]!
        rw [marked]
        exact Nat.le_trans (emit_branch_demand_mono branchCall x) (marks_demand_mono bc.args emission.state x)

/-- The post-body invariant uses the actual demand entering the compiler core,
including demands from successor blocks compiled earlier in the reverse traversal. -/
theorem jump_body_input_demand_le_term {f : Clif.Function} {result : Result}
    (scope : LowerScope f) {b : Clif.Block} {label bi : Nat} {bc : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : JumpBodySpec f result b label bi bc isem MR env cp)
    (jump : b.term = .jump bc) {tl : Nat}
    (target : result.order.nodes[spec.target]? = some (.original tl)) :
    ∀ (x : Nat),spec.input.demand[x]! ≤ spec.term.output.state.demand[x]! := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  have targets : result.order.successors[label]! = #[spec.target] := Array.toList_inj.mp spec.targets
  have coreRun := spec.coreRun
  rw [targets] at coreRun
  obtain ⟨branch,mono⟩ := jump_core_input_demand_mono (buildCtx_mappedInv scope spec.build).func source jump target coreRun
  have demand := (stock_branch_scan_body_code spec.split branch).2
  intro x
  rw [demand,spec.split.termInput]
  exact mono x

end Backend.Stock.Proof.Control

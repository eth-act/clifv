import FV.Backend.Proof.StockEmissionAliasClasses
namespace Backend.Stock.Proof.ScanAliasClassDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Flow Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.BindingClassDraft Backend.Stock.Proof.HelperAliasClassDraft Backend.Stock.Proof.OperandClassDraft
open Backend.Stock.Proof.EmissionAliasClassDraft Backend.Stock.Proof.ScanClassDraft Backend.Stock.Proof.Coverage
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem scanState_table (st : State) (i : Nat) :
    (scanState st i).opportunistic = st.opportunistic := by
  unfold scanState
  dsimp only
  split <;> rfl

private theorem commitValues_empty (ctx : Ctx) (values : List Nat) (st : State)
    (empty : NoOpportunity st) : commitOpportunisticValues ctx values st = .ok st := by
  unfold commitOpportunisticValues
  induction values with
  | nil => rfl
  | cons v values ih =>
    rw [List.foldlM_cons]
    simp only [empty v, pure, Except.pure, bind, Except.bind]
    exact ih

private theorem commit_empty {ctx : Ctx} {block i : Nat} {st next : State}
    (empty : NoOpportunity st) (run : commitOpportunistic ctx block i st = .ok (some next)) :
    next = st := by
  unfold commitOpportunistic at run
  dsimp only at run
  split at run
  · cases run
  · rw [commitValues_empty ctx _ st empty] at run
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at run
    exact run.symm

private theorem reset_classes (ctx : Ctx) (st : State) (i : Nat)
    (input : ClsIs ctx st.base st.base) :
    ClsIs ctx (scanState st i).base (scanState st i).base := by
  have classes : (scanState st i).base.classes = st.base.classes := by
    unfold scanState; dsimp only; split <;> rfl
  have frontier : (scanState st i).base.nextVreg = st.base.nextVreg := by
    unfold scanState; dsimp only; split <;> rfl
  refine ⟨?_,?_,?_,?_,⟨[],by simp,by simp⟩⟩
  · simpa only [Sz,classes,frontier] using input.sz
  · intro x r lookup; change RegCls (scanState st i).base.classes r
    rw [classes]; exact input.vals x r lookup
  · intro r member; change RegCls (scanState st i).base.classes r
    rw [classes]; exact input.try1 r member
  · intro r member; change RegCls (scanState st i).base.classes r
    rw [classes]; exact input.try2 r member


private theorem scan_alias {ctx : Ctx} {block ii ti : Nat} {branch : Bool}
    (emits : ∀ before emission,AliasClasses before → ReservedClasses ctx before →
      ClsIs ctx before.base before.base → emitInstruction ctx ii before = .ok emission → AliasClasses emission.state)
    {input : State} {output : Scan} (old : AliasClasses input) (reserved : ReservedClasses ctx input)
    (invariant : ClsIs ctx input.base input.base) (empty : NoOpportunity input)
    (run : scanInstruction ctx block ii ti branch input = .ok output) : AliasClasses output.state := by
  have normalized : NoOpportunity (scanState input ii) := by
    intro v; rw [scanState_table]; exact empty v
  have aliases : AliasClasses (scanState input ii) := by
    unfold scanState; dsimp only; split <;> exact old
  have reservations : ReservedClasses ctx (scanState input ii) := by
    unfold scanState; dsimp only; split <;> exact reserved
  have emit (h : (emitInstruction ctx ii (scanState input ii) >>= fun e =>
      pure (e.scan block ii (scanState input ii))) = .ok output) : AliasClasses output.state := by
    cases call : emitInstruction ctx ii (scanState input ii) with
    | error e => simp only [call,bind,Except.bind] at h; cases h
    | ok emission =>
      simp only [call,bind,Except.bind,pure,Except.pure] at h
      cases h
      exact emits _ _ aliases reservations (reset_classes ctx input ii invariant) call
  by_cases sunk : input.sunk[ii]! = true
  · simp only [scanInstruction,sunk,ite_true] at run; cases run; exact old
  · simp only [scanInstruction,sunk,ite_false] at run
    by_cases skipped : (ii == ti && branch) = true
    · simp only [skipped,ite_true] at run; cases run; exact aliases
    · simp only [skipped,ite_false] at run
      cases mandatory : (if ii == ti then true else ctx.insts[ii]!.clif.any mustLower) <;>
        simp only [mandatory] at run
      all_goals
        by_cases omitted : (!(if ii == ti then true else ctx.insts[ii]!.clif.any mustLower) &&
          !ctx.insts[ii]!.results.any (fun v => (scanState input ii).demand[v]! != 0)) = true
        · simp only [mandatory] at omitted
          simp only [omitted,ite_true] at run; cases run; exact aliases
        · simp only [mandatory] at omitted
          simp only [omitted,ite_false] at run
          by_cases committing : ((scanState input ii).entryColor[ii]! == 0 &&
              !(if ii == ti then true else ctx.insts[ii]!.clif.any mustLower)) = true
          · simp only [mandatory] at committing
            simp only [committing,ite_true] at run
            cases call : commitOpportunistic ctx block ii (scanState input ii) with
            | error e => simp only [call,bind,Except.bind] at run; cases run
            | ok result =>
              simp only [call,bind,Except.bind] at run
              cases result with
              | none => exact emit run
              | some next =>
                have same := commit_empty normalized call
                cases run
                rw [same]
                exact aliases
          · simp only [mandatory] at committing
            simp only [committing,ite_false] at run
            exact emit run

private theorem single_noOpportunity {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {block ii ti : Nat} {branch : Bool} (slot : ScanSlot ctx ii ti branch)
    {input : State} {output : Scan} (empty : NoOpportunity input)
    (run : scanInstruction ctx block ii ti branch input = .ok output) : NoOpportunity output.state := by
  have single : scanBlock ctx block ti branch [ii] input =
      .ok ⟨output.state,[⟨ii,input,output⟩],output.emitted⟩ := by
    unfold scanBlock
    rw [runScans_ref]
    simp only [Stock.runScansRef,run,bind,Except.bind,pure,Except.pure,Array.empty_append]
  exact scanBlock_noOpportunity mapped clean (fun j member => by
    cases List.mem_singleton.mp member; exact slot) empty single

/-- Every actual source/terminal scan retains alias/reservation classes and the
already-proved empty remembered table. The latter derives from real construction
and prevents opportunistic commits from importing an unproved register class. -/
theorem stock_scan_slot_alias_classes {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {block ii ti : Nat} {branch : Bool} (slot : ScanSlot ctx ii ti branch)
    {input : State} (invariant : ClsIs ctx input.base input.base)
    (reserved : ReservedClasses ctx input) (old : AliasClasses input) (empty : NoOpportunity input)
    {output : Scan} (run : scanInstruction ctx block ii ti branch input = .ok output) :
    AliasClasses output.state ∧ ReservedClasses ctx output.state ∧ NoOpportunity output.state := by
  have growth := ClassGrowthDraft.stock_scan_classGrowth run
  refine ⟨?_,fun r member => intCls_step growth (reserved r member),single_noOpportunity mapped clean slot empty run⟩
  rcases slot with ⟨info,inst,source,original⟩ | branchSlot | ⟨term,data,retTrap,prepared,source⟩
  · exact scan_alias (fun before emission aliases reserves classes emitted =>
      (stock_emitInstruction_alias_classes mapped clean source original classes reserves aliases emitted).1)
      old reserved invariant empty run
  · obtain ⟨equal,isBranch⟩ := branchSlot
    subst ii
    subst branch
    by_cases sunk : input.sunk[ti]! = true
    · simp only [scanInstruction,sunk,ite_true] at run; cases run; exact old
    · simp only [scanInstruction,sunk,ite_false,beq_self_eq_true,Bool.true_and,ite_true] at run
      cases run
      unfold scanState; dsimp only; split <;> exact old
  · exact scan_alias (fun before emission aliases reserves classes emitted =>
      (stock_emit_empty_results_alias_classes source rfl reserves aliases emitted).1)
      old reserved invariant empty run

/-- Complete real backward scans preserve alias classes at the final state and
at every recorded endpoint. All helper writes, binding and commit attempts are
composed internally under initialized class/no-opportunity invariants. -/
theorem stock_scanBlock_alias_classes {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {block ti : Nat} {branch : Bool} {indices : List Nat} (slots : ∀ i ∈ indices,ScanSlot ctx i ti branch)
    {input : State} (invariant : ClsIs ctx input.base input.base) (reserved : ReservedClasses ctx input)
    (old : AliasClasses input) (empty : NoOpportunity input) {output : BlockScan}
    (run : scanBlock ctx block ti branch indices input = .ok output) :
    AliasClasses output.state ∧ ReservedClasses ctx output.state ∧ NoOpportunity output.state ∧
      ∀ record ∈ output.records,AliasClasses record.input ∧ AliasClasses record.output.state := by
  have cert := runScans_spec run
  clear run
  induction cert with
  | nil input => exact ⟨old,reserved,empty,by simp⟩
  | @cons ii indices input scan tail head rest ih =>
    have first := stock_scan_slot_alias_classes mapped clean (slots ii (List.mem_cons_self ..)) invariant reserved old empty head
    have classes := (stock_scan_slot_classes mapped clean (slots ii (List.mem_cons_self ..)) invariant head).1
    have last := ih (fun j member => slots j (List.mem_cons_of_mem ii member)) classes first.2.1 first.1 first.2.2
    refine ⟨last.1,last.2.1,last.2.2.1,?_⟩
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨old,first.1⟩
    · exact last.2.2.2 record member

end Backend.Stock.Proof.ScanAliasClassDraft

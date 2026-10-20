import FV.Backend.Proof.StockTerminalRoots
import FV.Backend.Proof.StockCoverageScans

/-! Preserve every empty-CLIF slot through actual emissions and backward scans.
Existing NoOpportunity discharges commit paths; no new source check is added. -/
namespace Backend.Stock.Proof.Coverage
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

def TerminalUnsunk (ctx : Ctx) (st : State) : Prop :=
  ∀ i : Nat,ctx.insts[i]!.clif = none → st.sunk[i]! = false

theorem stock_buildCtx_terminal_unsunk {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) : TerminalUnsunk ctx initial := by
  unfold Stock.buildCtx at build
  cases legacy : Backend.buildCtx f with
  | error e => simp only [legacy, bind, Except.bind] at build; cases build
  | ok result =>
    rcases result with ⟨original, ranges, before⟩
    simp only [legacy, bind, Except.bind] at build
    cases requestRun : allocationRequests f ranges with
    | error e => simp only [requestRun, bind, Except.bind] at build; cases build
    | ok requests =>
      simp only [requestRun, bind, Except.bind, pure, Except.pure] at build
      cases build
      intro i slot
      change (Array.replicate original.insts.size false)[i]! = false
      by_cases inside : i < original.insts.size <;>
        simp [getElem!_def,Array.getElem?_replicate,inside] <;> rfl

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

private theorem scan_preserves {ctx : Ctx} {block i ti : Nat} {isBranch : Bool}
    (P : State → Prop)
    (normalize : ∀ st i,P st → P (scanState st i))
    (emitPreserves : ∀ before emission, P before →
      emitInstruction ctx i before = .ok emission → P emission.state)
    {input : State} {output : Scan} (empty : NoOpportunity input) (safe : P input)
    (run : scanInstruction ctx block i ti isBranch input = .ok output) :
    P output.state := by
  have normalizedEmpty : NoOpportunity (scanState input i) := by
    intro v
    rw [scanState_table]
    exact empty v
  have normalized : P (scanState input i) := normalize _ _ safe
  have emitted (h : (emitInstruction ctx i (scanState input i) >>= fun e =>
      pure (e.scan block i (scanState input i))) = .ok output) : P output.state := by
    cases hr : emitInstruction ctx i (scanState input i) with
    | error e => simp only [hr, bind, Except.bind] at h; cases h
    | ok emission =>
      simp only [hr, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact emitPreserves _ _ normalized hr
  by_cases sunk : input.sunk[i]! = true
  · simp only [scanInstruction, sunk, ite_true] at run
    cases run; exact safe
  · simp only [scanInstruction, sunk, ite_false] at run
    by_cases skipped : (i == ti && isBranch) = true
    · simp only [skipped, ite_true] at run
      cases run; exact normalized
    · simp only [skipped, ite_false] at run
      cases mandatory : (if i == ti then true else ctx.insts[i]!.clif.any mustLower) <;>
        simp only [mandatory] at run
      all_goals
        by_cases omitted : (! (if i == ti then true else ctx.insts[i]!.clif.any mustLower) &&
          !ctx.insts[i]!.results.any (fun v => (scanState input i).demand[v]! != 0)) = true
        · simp only [mandatory] at omitted
          simp only [omitted, ite_true] at run
          cases run; exact normalized
        · simp only [mandatory] at omitted
          simp only [omitted, ite_false] at run
          by_cases committing : ((scanState input i).entryColor[i]! == 0 &&
              !(if i == ti then true else ctx.insts[i]!.clif.any mustLower)) = true
          · simp only [mandatory] at committing
            simp only [committing, ite_true] at run
            cases hc : commitOpportunistic ctx block i (scanState input i) with
            | error e => simp only [hc, bind, Except.bind] at run; cases run
            | ok result =>
              simp only [hc, bind, Except.bind] at run
              cases result with
              | none => exact emitted run
              | some next =>
                have eq := commit_empty normalizedEmpty hc
                cases run
                rw [eq]
                exact normalized
          · simp only [mandatory] at committing
            simp only [committing, ite_false] at run
            exact emitted run

private theorem emit_preserves {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx)) {i : Nat}
    (kind : (∃ info inst,ctx.insts[i]? = some info ∧ info.clif = some inst) ∨
      ∃ t data,retOrTrap t = true ∧ Backend.termData t = .ok data ∧ ctx.insts[i]? = some ⟨data,[],[],none⟩)
    {before : State} {emission : Emission} (safe : TerminalUnsunk ctx before)
    (run : emitInstruction ctx i before = .ok emission) : TerminalUnsunk ctx emission.state := by
  unfold emitInstruction at run
  cases root : Stock.runTerm ctx "lower" [.inst i] before with
  | error e => simp only [root,bind,Except.bind] at run; cases run
  | ok result =>
    obtain ⟨out,next,rules⟩ := result
    have preserved : TerminalUnsunk ctx next := by
      intro terminal slot
      rcases kind with ⟨info,inst,source,clif⟩ | ⟨t,data,rt,prepared,source⟩
      · exact stock_statement_terminal_unsunk mapped clean source clif root slot (safe terminal slot)
      · exact stock_retTrap_terminal_unsunk mapped clean rt prepared source root slot (safe terminal slot)
    simp only [root,bind,Except.bind] at run
    cases out with
    | none => cases run
    | some out =>
      cases out <;> try (cases run)
      rename_i rss
      dsimp only at run
      split at run
      · cases run
      · cases binding : bindResults ctx (ctx.insts[i]!.results.zip rss) next with
        | error e => simp only [binding,bind,Except.bind] at run; cases run
        | ok pair =>
          obtain ⟨bound,copies⟩ := pair
          simp only [binding,pure,Except.pure] at run
          cases run
          intro terminal slot
          rw [bindResults_noSink binding]
          exact preserved terminal slot

private theorem normalize_safe (ctx : Ctx) (st : State) (i : Nat)
    (safe : TerminalUnsunk ctx st) : TerminalUnsunk ctx (scanState st i) := by
  intro j slot
  unfold scanState
  dsimp only
  split <;> exact safe j slot

private theorem scan_slot_safe {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {block i ti : Nat} {branch : Bool} (slot : ScanSlot ctx i ti branch)
    {input : State} {output : Scan} (empty : NoOpportunity input) (safe : TerminalUnsunk ctx input)
    (run : scanInstruction ctx block i ti branch input = .ok output) : TerminalUnsunk ctx output.state := by
  rcases slot with ordinary | ⟨same,br⟩ | terminal
  · exact scan_preserves (TerminalUnsunk ctx) (normalize_safe ctx)
      (fun before emission held emitted => emit_preserves mapped clean (.inl ordinary) held emitted) empty safe run
  · subst i
    subst branch
    by_cases sunk : input.sunk[ti]! = true
    · simp only [scanInstruction,sunk,ite_true] at run
      cases run; exact safe
    · simp only [scanInstruction,sunk,ite_false,beq_self_eq_true,Bool.true_and,ite_true] at run
      cases run; exact normalize_safe ctx input ti safe
  · exact scan_preserves (TerminalUnsunk ctx) (normalize_safe ctx)
      (fun before emission held emitted => emit_preserves mapped clean (.inr terminal) held emitted) empty safe run

/-- Actual complete backward scans preserve unsunk terminal placeholders and
supply that invariant at both endpoints of every actual retained record. -/
theorem stock_scanBlock_terminal_unsunk {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {block ti : Nat} {branch : Bool} {indices : List Nat}
    (slots : ∀ i ∈ indices,ScanSlot ctx i ti branch)
    {input : State} {output : BlockScan} (empty : NoOpportunity input) (safe : TerminalUnsunk ctx input)
    (run : scanBlock ctx block ti branch indices input = .ok output) :
    TerminalUnsunk ctx output.state ∧ ∀ record ∈ output.records,
      TerminalUnsunk ctx record.input ∧ TerminalUnsunk ctx record.output.state := by
  have memories := scanBlock_records_noOpportunity mapped clean slots empty run
  have cert := runScans_spec run
  clear run empty
  induction cert with
  | nil input => exact ⟨safe,by simp⟩
  | @cons i indices input scan tail head rest ih =>
    have first := scan_slot_safe mapped clean (slots i (List.mem_cons_self))
      (memories _ (List.mem_cons_self)).1 safe head
    have later := ih (fun k hk => slots k (List.mem_cons_of_mem i hk)) first
      (fun r hr => memories r (List.mem_cons_of_mem _ hr))
    refine ⟨later.1,?_⟩
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨safe,first⟩
    · exact later.2 record member
end Backend.Stock.Proof.Coverage

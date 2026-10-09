import FV.Backend.Proof.StockAliasBounds
import FV.Backend.Proof.StockBlockScan

/-! Alias caps through complete real instruction and block scans. The cap is
supplied by the initial allocation, not a new compiler acceptance condition. -/
namespace Backend.Stock.Proof
open Backend.Proof Isle Isle.Interp Isle.Aarch64
attribute [local irreducible] Isle.Aarch64.program
set_option maxRecDepth 4096

private theorem named_bound {ctx : Ctx} {term : String} {args : List V}
    {st next : State} {out : Option V} {trace : List RuleId} {cap : Nat}
    (payloads : ∀ r ∈ ctx.tryRegs.2, ∃ n, r = .vreg n .int ∧ n < cap)
    (bound : st.alias.size ≤ cap)
    (h : Stock.runTerm ctx term args st = .ok (out, next, trace)) :
    next.alias.size ≤ cap := by
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
          t.ret t.id args).run (st, #[]) with
      | error e => simp only [ha, bind, Except.bind] at hr; cases hr
      | ok result =>
        rcases result with ⟨out, next, trace⟩
        simp only [ha, bind, Except.bind, pure, Except.pure] at hr
        cases hr
        exact stock_apply_aliasBelow payloads bound ha

private theorem emitted_bound {ctx : Ctx} {i : Nat} {st : State}
    {emission : Emission} {cap : Nat}
    (payloads : ∀ r ∈ ctx.tryRegs.2, ∃ n, r = .vreg n .int ∧ n < cap)
    (mapped : ∀ x r, ctx.valueReg? x = some r → ∃ n, r = .vreg n .int ∧ n < cap)
    (bound : st.alias.size ≤ cap)
    (h : emitInstruction ctx i st = .ok emission) : emission.state.alias.size ≤ cap := by
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
          exact stock_bindResults_aliasBelow mapped (named_bound payloads bound hr) hb

private theorem alias_set_bound {st next : State} {n : Nat} {src : Reg} {cap : Nat}
    (bound : st.alias.size ≤ cap) (dest : n < cap)
    (h : st.setAlias (.vreg n .int) src = .ok next) : next.alias.size ≤ cap := by
  cases src <;> simp only [State.setAlias, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at h
  all_goals repeat' first | (solve | cases h) | split at h
  all_goals
    cases h
    simp only [Array.size_set!, Array.size_append, Array.size_replicate]
    omega

private theorem fold_bound {α β : Type} (P : α → Prop)
    (step : α → β → Except String α)
    (keeps : ∀ a b next, P a → step a b = .ok next → P next)
    (xs : List β) {a next : α} (bound : P a)
    (h : xs.foldlM step a = .ok next) : P next := by
  induction xs generalizing a with
  | nil => cases h; exact bound
  | cons x xs ih =>
    rw [List.foldlM_cons] at h
    cases call : step a x with
    | error e => simp only [call, bind, Except.bind] at h; cases h
    | ok middle =>
      simp only [call, bind, Except.bind] at h
      exact ih (keeps a x middle bound call) h

private theorem commit_bound {ctx : Ctx} {block i : Nat} {st next : State} {cap : Nat}
    (mapped : ∀ x r, ctx.valueReg? x = some r → ∃ n, r = .vreg n .int ∧ n < cap)
    (bound : st.alias.size ≤ cap)
    (h : commitOpportunistic ctx block i st = .ok (some next)) : next.alias.size ≤ cap := by
  have values {values : List Nat} {a b : State} (bound : a.alias.size ≤ cap)
      (h : commitOpportunisticValues ctx values a = .ok b) : b.alias.size ≤ cap := by
    unfold commitOpportunisticValues at h
    apply fold_bound (fun s : State => s.alias.size ≤ cap) _ ?_ values bound h
    intro a v b old he
    split at he
    · split at he
      · rename_i dst hdst
        split at he
        · rename_i src _
          cases hs : a.setAlias dst src with
          | error e => simp only [hs, bind, Except.bind] at he; cases he
          | ok q =>
            simp only [hs, bind, Except.bind, pure, Except.pure] at he
            cases he
            obtain ⟨n, rfl, below⟩ := mapped v dst hdst
            exact alias_set_bound (next := q) old below hs
        · cases he
      · cases he
    · cases he; exact old
  unfold commitOpportunistic at h
  dsimp only at h
  split at h
  · cases h
  · cases hv : commitOpportunisticValues ctx (ctx.insts[i]!.results) st with
    | error e => simp only [hv, bind, Except.bind] at h; cases h
    | ok q =>
      simp only [hv, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact values bound hv

private theorem scan_state_alias (st : State) (i : Nat) :
    (scanState st i).alias = st.alias := by
  unfold scanState
  dsimp only
  split <;> rfl

/-- All real scan decisions preserve the initial alias cap, including selected
rule execution, result binding, and opportunistic aliases to fresh temporaries. -/
theorem stock_scan_aliasBelow {ctx : Ctx} {block i ti : Nat} {branch : Bool}
    {st : State} {output : Scan} {cap : Nat}
    (payloads : ∀ r ∈ ctx.tryRegs.2, ∃ n, r = .vreg n .int ∧ n < cap)
    (mapped : ∀ x r, ctx.valueReg? x = some r → ∃ n, r = .vreg n .int ∧ n < cap)
    (bound : st.alias.size ≤ cap)
    (h : scanInstruction ctx block i ti branch st = .ok output) :
    output.state.alias.size ≤ cap := by
  have before : (scanState st i).alias.size ≤ cap := by rwa [scan_state_alias]
  have emit (h : (emitInstruction ctx i (scanState st i) >>= fun e =>
      pure (e.scan block i (scanState st i))) = .ok output) : output.state.alias.size ≤ cap := by
    cases he : emitInstruction ctx i (scanState st i) with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok e =>
      simp only [he, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact emitted_bound payloads mapped before he
  unfold scanInstruction at h
  dsimp only at h
  generalize hm : (if i == ti then true else ctx.insts[i]!.clif.any mustLower) = mandatory at h
  split at h
  · cases h; exact bound
  · split at h
    · cases h; exact before
    · split at h
      · cases h; exact before
      · split at h
        · cases hc : commitOpportunistic ctx block i (scanState st i) with
          | error e => simp only [hc, bind, Except.bind] at h; cases h
          | ok result =>
            simp only [hc, bind, Except.bind] at h
            cases result with
            | none => exact emit h
            | some q => cases h; exact commit_bound mapped before hc
        · exact emit h

/-- The actual tail-recursive block scan preserves the alias cap across every
instruction, without restrictions on selected rules or scan length. -/
theorem stock_scanBlock_aliasBelow {ctx : Ctx} {block ti : Nat} {branch : Bool}
    {indices : List Nat} {st : State} {output : BlockScan} {cap : Nat}
    (payloads : ∀ r ∈ ctx.tryRegs.2, ∃ n, r = .vreg n .int ∧ n < cap)
    (mapped : ∀ x r, ctx.valueReg? x = some r → ∃ n, r = .vreg n .int ∧ n < cap)
    (bound : st.alias.size ≤ cap)
    (h : scanBlock ctx block ti branch indices st = .ok output) :
    output.state.alias.size ≤ cap := by
  have cert := runScans_spec h
  clear h
  induction cert with
  | nil st => exact bound
  | cons head rest ih => exact ih (stock_scan_aliasBelow payloads mapped bound head)

private def opportunityCtx : Ctx :=
  { sinkCtx with insts := #[⟨.op .unit, [0], [.int 8], some (.iconst .i8 9)⟩] }
private def opportunity : State :=
  { sinkState with
    demand := #[1, 0]
    entryColor := #[0]
    alias := #[some 0]
    opportunistic := #[some ⟨0, [.vreg 197 .int], 1⟩, none] }
private def committed : State :=
  { scanState opportunity 0 with
    alias := (opportunity.alias ++ Array.replicate 192 none).set! 192 (some 197),
    opportunistic := #[none, none] }
private def committedScan : Scan :=
  ⟨committed, some ⟨0, 0, .opportunistic, scanState opportunity 0, committed, [], [], #[]⟩, #[]⟩
private theorem maps :
    ∀ x r, opportunityCtx.valueReg? x = some r → ∃ n, r = .vreg n .int ∧ n < 194 := by
  intro x r h
  cases x with
  | zero => cases h; exact ⟨192, rfl, by decide⟩
  | succ x =>
    cases x with
    | zero => cases h; exact ⟨193, rfl, by decide⟩
    | succ x => simp [opportunityCtx, sinkCtx, Ctx.valueReg?] at h
private theorem payloads :
    ∀ r ∈ opportunityCtx.tryRegs.2, ∃ n, r = .vreg n .int ∧ n < 194 := by
  simp [opportunityCtx, sinkCtx]

set_option maxHeartbeats 2000000 in
/-- An actual opportunistic scan grows the alias array below the cap while
pointing at a temporary above it; the cap bounds destinations, not targets. -/
theorem stock_scan_aliasBelow_witness :
    scanInstruction opportunityCtx 0 0 1 false opportunity = .ok committedScan ∧
      committedScan.state.alias[192]? = some (some 197) ∧
      committedScan.state.alias.size = 193 ∧ committedScan.state.alias.size ≤ 194 := by
  have run : scanInstruction opportunityCtx 0 0 1 false opportunity = .ok committedScan := rfl
  exact ⟨run, rfl, rfl, stock_scan_aliasBelow payloads maps (by decide) run⟩

private def committedBlock : BlockScan := ⟨committed, [⟨0, opportunity, committedScan⟩], #[]⟩

set_option maxHeartbeats 2000000 in
theorem stock_scanBlock_aliasBelow_witness :
    scanBlock opportunityCtx 0 1 false [0] opportunity = .ok committedBlock ∧
      committedBlock.state.alias[192]? = some (some 197) ∧
      committedBlock.state.alias.size ≤ 194 := by
  have run : scanBlock opportunityCtx 0 1 false [0] opportunity = .ok committedBlock := rfl
  exact ⟨run, rfl, stock_scanBlock_aliasBelow payloads maps (by decide) run⟩

end Backend.Stock.Proof

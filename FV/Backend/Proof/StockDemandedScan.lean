module

public import FV.Backend.Proof.StockDemandedUnsunk

@[expose] public section

/-! Demand protection through real result binding, opportunistic aliases and
complete scans. Kept separate from helper interpretation to bound elaboration. -/
namespace Backend.Stock.Proof
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
attribute [local irreducible] Isle.Aarch64.program

private def stableFields (st : State) := (st.demand,st.sunk)
private theorem stableFields_rel {ctx : Ctx} {st next : State}
    (same : stableFields next = stableFields st) : DemandedUnsunkLe ctx st next := by
  have demand := congrArg Prod.fst same
  have sunk := congrArg Prod.snd same
  change next.demand = st.demand at demand
  change next.sunk = st.sunk at sunk
  refine ⟨?_,?_⟩
  · intro x; rw [demand]; exact Nat.le_refl _
  · intro i x result used safe; rw [sunk]; exact safe

private theorem setAlias_stableFields {st next : State} {dst src : Reg}
    (h : st.setAlias dst src = .ok next) : stableFields next = stableFields st := by
  cases dst <;> cases src <;>
    simp only [State.setAlias,bind,Except.bind,pure,Except.pure,
      throw,throwThe,MonadExceptOf.throw] at h
  all_goals repeat' first | (solve | cases h) | (solve | cases h; rfl) | split at h
private theorem fold_fields_eq {α β γ : Type} (field : α → γ)
    (step : α → β → Except String α)
    (hs : ∀ a b next, step a b = .ok next → field next = field a)
    (xs : List β) {a next : α} (h : xs.foldlM step a = .ok next) :
    field next = field a := by
  induction xs generalizing a with
  | nil => cases h; rfl
  | cons x xs ih =>
    rw [List.foldlM_cons] at h
    cases he : step a x with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok middle =>
      simp only [he, bind, Except.bind] at h
      exact (ih h).trans (hs a x middle he)

private theorem binding_stableFields {ctx : Ctx} {pairs : List (Nat × List Reg)}
    {st next : State} {copies : Array MInst}
    (h : bindResults ctx pairs st = .ok (next, copies)) : stableFields next = stableFields st := by
  unfold bindResults at h
  apply fold_fields_eq (fun a : State × Array MInst => stableFields a.1) _ ?_ pairs h
  intro acc pair next he
  rcases acc with ⟨s, code⟩
  rcases pair with ⟨v, rs⟩
  dsimp only at he
  cases hm : ctx.valueReg? v with
  | none => simp only [hm] at he; cases he
  | some r =>
    simp only [hm] at he
    split at he
    · rename_i _ n cls
      cases ha : s.setAlias r (.vreg n cls) with
      | error e => simp only [ha, bind, Except.bind] at he; cases he
      | ok q =>
        simp only [ha, bind, Except.bind, pure, Except.pure] at he
        cases he
        exact setAlias_stableFields ha
    · cases he; rfl
    · cases he

private theorem commit_stableFields {ctx : Ctx} {block i : Nat} {st next : State}
    (h : commitOpportunistic ctx block i st = .ok (some next)) : stableFields next = stableFields st := by
  have values {values : List Nat} {a b : State}
      (h : commitOpportunisticValues ctx values a = .ok b) : stableFields b = stableFields a := by
    unfold commitOpportunisticValues at h
    apply fold_fields_eq stableFields _ ?_ values h
    intro a v b he
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
            exact setAlias_stableFields (next := q) hs
        · cases he
      · cases he
    · cases he; rfl
  unfold commitOpportunistic at h
  dsimp only at h
  split at h
  · cases h
  · cases hv : commitOpportunisticValues ctx (ctx.insts[i]!.results) st with
    | error e => simp only [hv, bind, Except.bind] at h; cases h
    | ok q =>
      simp only [hv, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact values hv

private theorem scan_state_stableFields (st : State) (i : Nat) : stableFields (scanState st i) = stableFields st := by
  unfold scanState
  dsimp only
  split <;> rfl

private theorem emitted_demanded_unsunk {ctx : Ctx} {i : Nat} {st : State}
    {emission : Emission}
    (h : emitInstruction ctx i st = .ok emission) : DemandedUnsunkLe ctx st emission.state := by
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
          exact DemandedUnsunkLe.trans (stock_named_demanded_unsunk hr) (stableFields_rel (binding_stableFields hb))


/-- Every actual scan decision preserves demanded colored definitions. -/
theorem stock_scan_demanded_unsunk {ctx : Ctx} {block i ti : Nat} {branch : Bool}
    {st : State} {output : Scan}
    (h : scanInstruction ctx block i ti branch st = .ok output) : DemandedUnsunkLe ctx st output.state := by
  have refl : DemandedUnsunkLe ctx st (scanState st i) := stableFields_rel (scan_state_stableFields st i)
  have emit (h : (emitInstruction ctx i (scanState st i) >>= fun e =>
      pure (e.scan block i (scanState st i))) = .ok output) : DemandedUnsunkLe ctx st output.state := by
    cases he : emitInstruction ctx i (scanState st i) with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok e =>
      simp only [he, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact DemandedUnsunkLe.trans refl (emitted_demanded_unsunk he)
  unfold scanInstruction at h
  dsimp only at h
  generalize hm : (if i == ti then true else ctx.insts[i]!.clif.any mustLower) = mandatory at h
  split at h
  · cases h; exact DemandedUnsunkLe.refl _ _
  · split at h
    · cases h; exact refl
    · split at h
      · cases h; exact refl
      · split at h
        · cases hc : commitOpportunistic ctx block i (scanState st i) with
          | error e => simp only [hc, bind, Except.bind] at h; cases h
          | ok result =>
            simp only [hc, bind, Except.bind] at h
            cases result with
            | none => exact emit h
            | some q =>
              cases h
              exact DemandedUnsunkLe.trans refl (stableFields_rel (commit_stableFields hc))
        · exact emit h

/-- Complete tail-recursive scans transport the demanded colored unsunk invariant. -/
theorem stock_scanBlock_demanded_unsunk {ctx : Ctx} {block ti : Nat} {branch : Bool}
    {indices : List Nat} {st : State} {output : BlockScan}
    (h : scanBlock ctx block ti branch indices st = .ok output) : DemandedUnsunkLe ctx st output.state := by
  have cert := runScans_spec h
  clear h
  induction cert with
  | nil st => exact DemandedUnsunkLe.refl _ _
  | cons head rest ih => exact DemandedUnsunkLe.trans (stock_scan_demanded_unsunk head) ih




/-- Preserve the invariant at every real retained-record boundary, including
intermediate records rather than only the final scan state. -/
theorem stock_scans_demanded_unsunk {ctx : Ctx} {block ti : Nat} {branch : Bool}
    {indices : List Nat} {st : State} {output : BlockScan}
    (cert : ScansSpec (fun i => scanInstruction ctx block i ti branch) indices st output) :
    DemandedUnsunkLe ctx st output.state ∧
      ∀ r ∈ output.records, DemandedUnsunkLe ctx st r.input ∧ DemandedUnsunkLe ctx st r.output.state := by
  induction cert with
  | nil st => exact ⟨DemandedUnsunkLe.refl _ _,by simp⟩
  | cons head rest ih =>
    have step := stock_scan_demanded_unsunk head
    refine ⟨DemandedUnsunkLe.trans step ih.1,?_⟩
    intro r member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨DemandedUnsunkLe.refl _ _,step⟩
    · obtain ⟨pre,post⟩ := ih.2 r member
      exact ⟨DemandedUnsunkLe.trans step pre,DemandedUnsunkLe.trans step post⟩


private def skipCtx : Ctx :=
  {sinkCtx with insts := #[{sinkCtx.insts[0]! with results := [0]},{sinkCtx.insts[0]! with results := [1]}]}
private def skipState : State :=
  {sinkState with entryColor := #[1,2],color := some 3,demand := #[1,0],sunk := #[false,false]}
private def skipped : Scan := ⟨scanState skipState 1,none,#[]⟩
private def scanned : BlockScan := ⟨skipped.state,[⟨1,skipState,skipped⟩],#[]⟩

/-- A real branch slot produces a nonempty scan while a demanded colored
neighbor remains protected. The helper sink witnesses cover changed sunk bits. -/
theorem stock_scan_demanded_unsunk_witness :
    scanInstruction skipCtx 0 1 1 true skipState = .ok skipped ∧
    skipState.entryColor[0]! ≠ 0 ∧ skipState.demand[0]! ≠ 0 ∧
    DemandedUnsunkLe skipCtx skipState skipped.state := by
  have run : scanInstruction skipCtx 0 1 1 true skipState = .ok skipped := rfl
  exact ⟨run,by decide,by decide,stock_scan_demanded_unsunk run⟩

/-- A complete nonempty scan inhabits the block invariant. -/
theorem stock_scanBlock_demanded_unsunk_witness :
    scanBlock skipCtx 0 1 true [1] skipState = .ok scanned ∧
    scanned.records.length = 1 ∧ DemandedUnsunkLe skipCtx skipState scanned.state := by
  have run : scanBlock skipCtx 0 1 true [1] skipState = .ok scanned := rfl
  exact ⟨run,rfl,stock_scanBlock_demanded_unsunk run⟩

/-- Actual retained input/output boundaries inhabit the complete scan relation. -/
theorem stock_scans_demanded_unsunk_witness :
    ScansSpec (fun i => scanInstruction skipCtx 0 i 1 true) [1] skipState scanned ∧
    scanned.records.length = 1 ∧ DemandedUnsunkLe skipCtx skipState scanned.state ∧
    ∀ r ∈ scanned.records,DemandedUnsunkLe skipCtx skipState r.input ∧
      DemandedUnsunkLe skipCtx skipState r.output.state := by
  have run : scanBlock skipCtx 0 1 true [1] skipState = .ok scanned := rfl
  have cert := runScans_spec run
  obtain ⟨last,records⟩ := stock_scans_demanded_unsunk cert
  exact ⟨cert,rfl,last,records⟩

end Backend.Stock.Proof

import FV.Backend.Proof.StockNoLoadSink

/-! Complete sunk-array preservation through actual binding, opportunistic aliases
and retained scan records, derived from the generated-program invariant. -/
namespace Backend.Stock.Proof.SinkRules
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

structure SunkEq (st next : State) : Prop where
  sunk : next.sunk = st.sunk
private theorem SunkEq.refl (st : State) : SunkEq st st := ⟨rfl⟩
private theorem SunkEq.trans {a b c : State} (ab : SunkEq a b) (bc : SunkEq b c) : SunkEq a c := ⟨Eq.trans bc.sunk ab.sunk⟩
private def stableFields (st : State) := st.sunk
private theorem stableFields_rel {st next : State}
    (same : stableFields next = stableFields st) : SunkEq st next := ⟨same⟩

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

private def emitDecoded (ctx : Ctx) (i : Nat)
    (root : Except String (Option V × State × List RuleId)) : Except String Emission := do
  let info := ctx.insts[i]!
  let (out,next,fired) ← root
  let some (.regsVec rss) := out | throw s!"no lowering rule for instruction {i}"
  if rss.length != info.results.length && !info.results.isEmpty then
    throw "lowering produced a wrong number of results"
  let (st,extra) ← bindResults ctx (info.results.zip rss) next
  pure ⟨st,st.base.emitted ++ extra,rss,fired⟩

private theorem decoded_preserves {ctx : Ctx} {i : Nat} {st : State}
    {root : Except String (Option V × State × List RuleId)} {emission : Emission}
    (keeps : ∀ {out next trace}, root = .ok (out,next,trace) → next.sunk = st.sunk)
    (h : emitDecoded ctx i root = .ok emission) : SunkEq st emission.state := by
  unfold emitDecoded at h
  cases hr : root with
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
          exact SunkEq.trans ⟨keeps hr⟩ (stableFields_rel (binding_stableFields hb))


private theorem emitted_no_load_unsunk {ctx : Ctx} (noLoads : NoLoadData ctx) {i : Nat} {st : State}
    {emission : Emission}
    (h : emitInstruction ctx i st = .ok emission) : SunkEq st emission.state := by
  unfold emitInstruction at h
  exact decoded_preserves (ctx := ctx) (i := i)
    (root := Stock.runTerm ctx "lower" [.inst i] st)
    (fun run => no_load_lower noLoads run) h


private theorem emission_scan_preserves {block i : Nat} {before initial : State}
    {result : Except String Emission} {output : Scan}
    (keeps : ∀ e, result = .ok e → SunkEq initial e.state)
    (h : (result >>= fun e => pure (e.scan block i before)) = .ok output) :
    SunkEq initial output.state := by
  cases result with
  | error message => cases h
  | ok e =>
    simp only [bind,Except.bind,pure,Except.pure] at h
    cases h
    exact keeps e rfl

private def decideScan (ctx : Ctx) (block i ti : Nat) (branch : Bool) (input : State)
    (emission : Except String Emission) (committed : Except String (Option State)) : Except String Scan := do
  if input.sunk[i]! then
    return ⟨input,some ⟨block,i,.sunk,input,input,[],[],#[]⟩,#[]⟩
  let before := scanState input i
  if i == ti && branch then return ⟨before,none,#[]⟩
  let info := ctx.insts[i]!
  let mandatory := if i == ti then true else info.clif.any mustLower
  if !mandatory && !info.results.any (fun v => before.demand[v]! != 0) then
    return ⟨before,some ⟨block,i,.omitted,before,before,[],[],#[]⟩,#[]⟩
  if before.entryColor[i]! == 0 && !mandatory then
    if let some next ← committed then
      return ⟨next,some ⟨block,i,.opportunistic,before,next,[],[],#[]⟩,#[]⟩
  let emission ← emission
  pure (emission.scan block i before)

private theorem decoded_scan_preserves {ctx : Ctx} {block i ti : Nat} {branch : Bool}
    {st : State} {output : Scan} {emission : Except String Emission}
    {committed : Except String (Option State)}
    (emitKeeps : ∀ e, emission = .ok e → SunkEq (scanState st i) e.state)
    (commitKeeps : ∀ q, committed = .ok (some q) → SunkEq (scanState st i) q)
    (h : decideScan ctx block i ti branch st emission committed = .ok output) :
    SunkEq st output.state := by
  have refl : SunkEq st (scanState st i) := stableFields_rel (scan_state_stableFields st i)
  have emit (h : (emission >>= fun e =>
      pure (e.scan block i (scanState st i))) = .ok output) : SunkEq st output.state :=
    emission_scan_preserves (fun e he => SunkEq.trans refl (emitKeeps e he)) h
  unfold decideScan at h
  dsimp only at h
  generalize hm : (if i == ti then true else ctx.insts[i]!.clif.any mustLower) = mandatory at h
  split at h
  · cases h; exact SunkEq.refl _
  · split at h
    · cases h; exact refl
    · split at h
      · cases h; exact refl
      · split at h
        · cases hc : committed with
          | error e => simp only [hc, bind, Except.bind] at h; cases h
          | ok result =>
            simp only [hc, bind, Except.bind] at h
            cases result with
            | none => exact emit h
            | some q =>
              cases h
              exact SunkEq.trans refl (commitKeeps q hc)
        · exact emit h

/-- Every actual scan decision preserves the complete sunk array. -/
theorem scan_no_load_unsunk {ctx : Ctx} (noLoads : NoLoadData ctx) {block i ti : Nat} {branch : Bool}
    {st : State} {output : Scan}
    (h : scanInstruction ctx block i ti branch st = .ok output) : SunkEq st output.state := by
  exact decoded_scan_preserves (fun e he => emitted_no_load_unsunk noLoads he)
    (fun q hc => stableFields_rel (commit_stableFields hc)) h

/-- Complete tail-recursive scans preserve the complete sunk array. -/
theorem scan_block_no_load_unsunk {ctx : Ctx} (noLoads : NoLoadData ctx) {block ti : Nat} {branch : Bool}
    {indices : List Nat} {st : State} {output : BlockScan}
    (h : scanBlock ctx block ti branch indices st = .ok output) : SunkEq st output.state := by
  have cert := runScans_spec h
  clear h
  induction cert with
  | nil st => exact SunkEq.refl _
  | cons head rest ih => exact SunkEq.trans (scan_no_load_unsunk noLoads head) ih




/-- Preserve the invariant at every real retained-record boundary, including
intermediate records rather than only the final scan state. -/
theorem scans_no_load_unsunk {ctx : Ctx} (noLoads : NoLoadData ctx) {block ti : Nat} {branch : Bool}
    {indices : List Nat} {st : State} {output : BlockScan}
    (cert : ScansSpec (fun i => scanInstruction ctx block i ti branch) indices st output) :
    SunkEq st output.state ∧
      ∀ r ∈ output.records, SunkEq st r.input ∧ SunkEq st r.output.state := by
  induction cert with
  | nil st => exact ⟨SunkEq.refl _,by simp⟩
  | cons head rest ih =>
    have step := scan_no_load_unsunk noLoads head
    refine ⟨SunkEq.trans step ih.1,?_⟩
    intro r member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨SunkEq.refl _,step⟩
    · obtain ⟨pre,post⟩ := ih.2 r member
      exact ⟨SunkEq.trans step pre,SunkEq.trans step post⟩


attribute [local irreducible] commitOpportunistic scanState

/-- A slot-preserving actual lower helper lifts through result binding and every
scan decision. The helper contract can permit sinking at other source slots. -/
theorem scan_sunk_at_of_lower {ctx : Ctx} {slot : Nat}
    (keeps : ∀ {vs st next out trace},
      Stock.runTerm ctx "lower" vs st = .ok (out,next,trace) →
        next.sunk[slot]! = st.sunk[slot]!)
    {block i ti : Nat} {branch : Bool} {st : State} {output : Scan}
    (run : scanInstruction ctx block i ti branch st = .ok output) :
    output.state.sunk[slot]! = st.sunk[slot]! := by
  have emitted {i : Nat} {st : State} {emission : Emission}
      (h : emitInstruction ctx i st = .ok emission) :
      emission.state.sunk[slot]! = st.sunk[slot]! := by
    unfold emitInstruction at h
    change emitDecoded ctx i (Stock.runTerm ctx "lower" [.inst i] st) = .ok emission at h
    unfold emitDecoded at h
    cases hr : Stock.runTerm ctx "lower" [.inst i] st with
    | error e => simp only [hr,bind,Except.bind] at h; cases h
    | ok root =>
      rcases root with ⟨out,next,trace⟩
      simp only [hr,bind,Except.bind] at h
      cases out with
      | none => cases h
      | some out =>
        cases out <;> try cases h
        rename_i rss
        dsimp only at h
        split at h
        · cases h
        · cases hb : bindResults ctx (ctx.insts[i]!.results.zip rss) next with
          | error e => simp only [hb] at h; cases h
          | ok result =>
            rcases result with ⟨final,copies⟩
            simp only [hb,pure,Except.pure] at h
            cases h
            exact (congrArg (fun bits => bits[slot]!) (binding_stableFields hb)).trans (keeps hr)
  have scanned : (scanState st i).sunk[slot]! = st.sunk[slot]! :=
    congrArg (fun bits => bits[slot]!) (scan_state_stableFields st i)
  have emit (h : (emitInstruction ctx i (scanState st i) >>= fun e =>
      pure (e.scan block i (scanState st i))) = .ok output) :
      output.state.sunk[slot]! = st.sunk[slot]! := by
    cases call : emitInstruction ctx i (scanState st i) with
    | error e => simp only [call,bind,Except.bind] at h; cases h
    | ok e =>
      simp only [call,bind,Except.bind,pure,Except.pure] at h
      cases h
      exact (emitted call).trans scanned
  change decideScan ctx block i ti branch st
    (emitInstruction ctx i (scanState st i))
    (commitOpportunistic ctx block i (scanState st i)) = .ok output at run
  unfold decideScan at run
  dsimp only at run
  generalize hm : (if i == ti then true else ctx.insts[i]!.clif.any mustLower) = mandatory at run
  split at run
  · cases run; rfl
  · split at run
    · cases run; exact scanned
    · split at run
      · cases run; exact scanned
      · split at run
        · cases hc : commitOpportunistic ctx block i (scanState st i) with
          | error e => simp only [hc,bind,Except.bind] at run; cases run
          | ok result =>
            simp only [hc,bind,Except.bind] at run
            cases result with
            | none => exact emit run
            | some q =>
              cases run
              exact (congrArg (fun bits => bits[slot]!) (commit_stableFields hc)).trans scanned
        · exact emit run

/-- The same actual helper contract reaches every retained record boundary. -/
theorem scans_sunk_at_of_lower {ctx : Ctx} {slot : Nat}
    (keeps : ∀ {vs st next out trace},
      Stock.runTerm ctx "lower" vs st = .ok (out,next,trace) →
        next.sunk[slot]! = st.sunk[slot]!)
    {block ti : Nat} {branch : Bool} {indices : List Nat} {st : State} {output : BlockScan}
    (cert : ScansSpec (fun i => scanInstruction ctx block i ti branch) indices st output) :
    output.state.sunk[slot]! = st.sunk[slot]! ∧
      ∀ r ∈ output.records,r.input.sunk[slot]! = st.sunk[slot]! ∧
        r.output.state.sunk[slot]! = st.sunk[slot]! := by
  induction cert with
  | nil st => exact ⟨rfl,by simp⟩
  | cons head rest ih =>
    have step := scan_sunk_at_of_lower keeps head
    refine ⟨ih.1.trans step,?_⟩
    intro r member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨rfl,step⟩
    · obtain ⟨pre,post⟩ := ih.2 r member
      exact ⟨pre.trans step,post.trans step⟩

end Backend.Stock.Proof.SinkRules

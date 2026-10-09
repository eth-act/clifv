import FV.Backend.Proof.StockScanBounds
import FV.Backend.Proof.IselFlowExt

/-! Actual stock evaluation preserves preallocated exception reservations and
never moves the fresh-register frontier backwards. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
attribute [local irreducible] Isle.Aarch64.program
set_option maxRecDepth 4096

/-- The allocation frontier grows, while reserved exception registers stay fixed. -/
def AllocationLe (st next : State) : Prop :=
  st.base.nextVreg ≤ next.base.nextVreg ∧ next.tryRegs = st.tryRegs
private theorem allocation_refl (st : State) : AllocationLe st st := ⟨Nat.le_refl _, rfl⟩
private theorem allocation_trans {a b c : State} (ab : AllocationLe a b) (bc : AllocationLe b c) :
    AllocationLe a c := ⟨Nat.le_trans ab.1 bc.1, bc.2.trans ab.2⟩
private def fields (st : State) := (st.base.nextVreg, st.tryRegs)
private theorem fields_rel {st next : State} (h : fields next = fields st) :
    AllocationLe st next := by
  have base := congrArg Prod.fst h
  change next.base.nextVreg = st.base.nextVreg at base
  have reservations := congrArg Prod.snd h
  exact ⟨by change st.base.nextVreg ≤ next.base.nextVreg; rw [base]; exact Nat.le_refl _, reservations⟩
private theorem marks_fields (st : State) (vs : List Nat) :
    fields (vs.foldl State.mark st) = fields st := by
  induction vs generalizing st with
  | nil => rfl
  | cons v vs ih => exact ih (st.mark v)

private theorem setAlias_fields {st next : State} {dst src : Reg}
    (h : st.setAlias dst src = .ok next) : fields next = fields st := by
  cases dst <;> cases src <;>
    simp only [State.setAlias, bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at h
  all_goals repeat' first | (solve | cases h) | (solve | cases h; rfl) | split at h

private def tryAliasStep (ps rets : List Reg) (acc : Except String (State × List Reg))
    (pair : Reg × Reg) : Except String (State × List Reg) := do
  let (s, regs) ← acc
  let (p, r) := pair
  if let some i := ps.idxOf? p then
    let some ret := rets[i]? | throw "try_call return register"
    pure (← s.setAlias r ret, regs ++ [ret])
  else pure (s, regs ++ [r])

private theorem try_fold_error (ps rets : List Reg) (pairs : List (Reg × Reg)) (e : String) :
    pairs.foldl (tryAliasStep ps rets) (.error e) = .error e := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih => exact ih

private theorem try_fold_fields (ps rets : List Reg) (pairs : List (Reg × Reg))
    (st : State) (regs : List Reg) {next : State} {out : List Reg}
    (h : pairs.foldl (tryAliasStep ps rets) (.ok (st, regs)) = .ok (next, out)) :
    fields next = fields st := by
  induction pairs generalizing st regs with
  | nil => cases h; rfl
  | cons pair pairs ih =>
    rw [List.foldl_cons] at h
    cases hs : tryAliasStep ps rets (.ok (st, regs)) pair with
    | error e => rw [hs, try_fold_error] at h; cases h
    | ok result =>
      rcases result with ⟨middle, rs⟩
      rw [hs] at h
      have hm : fields middle = fields st := by
        unfold tryAliasStep at hs
        simp only [bind, Except.bind] at hs
        cases hi : ps.idxOf? pair.1 with
        | none => simp only [hi, pure, Except.pure] at hs; cases hs; rfl
        | some i =>
          simp only [hi] at hs
          cases hr : rets[i]? with
          | none => simp only [hr] at hs; cases hs
          | some r =>
            simp only [hr] at hs
            cases ha : st.setAlias pair.2 r with
            | error e => rw [ha] at hs; cases hs
            | ok q =>
              rw [ha] at hs
              simp only [pure, Except.pure] at hs
              cases hs
              exact setAlias_fields ha
      exact (ih middle rs h).trans hm


private theorem delegate_alloc {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V}
    (h : (match Backend.externCtor ctx t args st.base with
      | .ok (v, base) => ExtResult.ok (v, { st with base })
      | .fail => ExtResult.fail
      | .unmodeled e => ExtResult.unmodeled e) = ExtResult.ok (v, next)) :
    AllocationLe st next := by
  cases call : Backend.externCtor ctx t args st.base with
  | fail => rw [call] at h; cases h
  | unmodeled e => rw [call] at h; cases h
  | ok pair =>
    rcases pair with ⟨value, base⟩
    rw [call] at h
    cases h
    exact ⟨(externCtor_ok ctx t args st.base _ _ call).vreg, rfl⟩

private theorem output_frontier (returns : List Clif.AbiParam) (regs : List (List Reg))
    (base : LState) :
    base.nextVreg ≤ (returns.foldl (fun (rs, base) _ =>
      let (r, next) := base.fresh .int
      (rs ++ [[r]], next)) (regs, base)).2.nextVreg := by
  induction returns generalizing regs base with
  | nil => exact Nat.le_refl _
  | cons ret returns ih =>
    exact Nat.le_trans (by simp [LState.fresh]) (ih _ (base.fresh .int).2)

/-- All successful actual constructors preserve reservations and increase the
fresh frontier, including try-call alias installation and explicit call outputs. -/
theorem stock_ctor_allocationLe {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V}
    (h : Stock.externCtor ctx t args st = .ok (v, next)) : AllocationLe st next := by
  unfold Stock.externCtor at h
  split at h
  all_goals dsimp only at h
  all_goals try solve | exact delegate_alloc h
  all_goals repeat' first
    | (solve | cases h <;> exact allocation_refl st)
    | (solve | exact allocation_trans (show AllocationLe st (st.mark _) from ⟨Nat.le_refl _, rfl⟩) (delegate_alloc h))
    | (solve | exact allocation_trans (fields_rel (marks_fields st _)) (delegate_alloc h))
    | (solve | cases h; exact ⟨Nat.le_refl _, rfl⟩)
    | split at h
  case h_10 =>
    cases h
    exact ⟨output_frontier _ [] st.base, rfl⟩
  all_goals
    rename_i _ _ sig _ _ ps _ _ s regs step
    cases h
    exact fields_rel (try_fold_fields ps ctx.tryRegs.1
      ((payloadRegs sig.callConv).zip ctx.tryRegs.2) st [] step)

/-- Full actual term evaluation preserves reservations and a monotone frontier. -/
theorem stock_apply_allocationLe {p : Program} {ctx : Ctx} {cfg : Config}
    {n ty t : Nat} {args : List V} {st next : State} {tr tr' : Array RuleId} {out : Option V}
    (h : (applyTerm p (Stock.sem ctx) cfg n ty t args).run (st, tr) =
      .ok (out, next, tr')) : AllocationLe st next :=
  (presAt allocation_refl (fun _ _ _ => allocation_trans)
    (fun _ _ _ _ _ => stock_ctor_allocationLe) n).apply ty t args st tr out next tr' h

private theorem named_alloc {ctx : Ctx} {term : String} {args : List V}
    {st next : State} {out : Option V} {trace : List RuleId}
    (h : Stock.runTerm ctx term args st = .ok (out, next, trace)) :
    AllocationLe st next := by
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
        exact stock_apply_allocationLe ha

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

private theorem binding_fields {ctx : Ctx} {pairs : List (Nat × List Reg)}
    {st next : State} {copies : Array MInst}
    (h : bindResults ctx pairs st = .ok (next, copies)) : fields next = fields st := by
  unfold bindResults at h
  apply fold_fields_eq (fun a : State × Array MInst => fields a.1) _ ?_ pairs h
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
        exact setAlias_fields ha
    · cases he; rfl
    · cases he

private theorem emitted_alloc {ctx : Ctx} {i : Nat} {st : State}
    {emission : Emission}
    (h : emitInstruction ctx i st = .ok emission) : AllocationLe st emission.state := by
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
          exact allocation_trans (named_alloc hr) (fields_rel (binding_fields hb))


private theorem commit_fields {ctx : Ctx} {block i : Nat} {st next : State}
    (h : commitOpportunistic ctx block i st = .ok (some next)) : fields next = fields st := by
  have values {values : List Nat} {a b : State}
      (h : commitOpportunisticValues ctx values a = .ok b) : fields b = fields a := by
    unfold commitOpportunisticValues at h
    apply fold_fields_eq fields _ ?_ values h
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
            exact setAlias_fields (next := q) hs
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

private theorem scan_state_fields (st : State) (i : Nat) : fields (scanState st i) = fields st := by
  unfold scanState
  dsimp only
  split <;> rfl

/-- Actual scans preserve reservations and a monotone allocation frontier. -/
theorem stock_scan_allocationLe {ctx : Ctx} {block i ti : Nat} {branch : Bool}
    {st : State} {output : Scan}
    (h : scanInstruction ctx block i ti branch st = .ok output) : AllocationLe st output.state := by
  have refl : AllocationLe st (scanState st i) := fields_rel (scan_state_fields st i)
  have emit (h : (emitInstruction ctx i (scanState st i) >>= fun e =>
      pure (e.scan block i (scanState st i))) = .ok output) : AllocationLe st output.state := by
    cases he : emitInstruction ctx i (scanState st i) with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok e =>
      simp only [he, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact allocation_trans refl (emitted_alloc he)
  unfold scanInstruction at h
  dsimp only at h
  generalize hm : (if i == ti then true else ctx.insts[i]!.clif.any mustLower) = mandatory at h
  split at h
  · cases h; exact allocation_refl _
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
              exact allocation_trans refl (fields_rel (commit_fields hc))
        · exact emit h

/-- Complete tail-recursive scans preserve the allocation invariants. -/
theorem stock_scanBlock_allocationLe {ctx : Ctx} {block ti : Nat} {branch : Bool}
    {indices : List Nat} {st : State} {output : BlockScan}
    (h : scanBlock ctx block ti branch indices st = .ok output) : AllocationLe st output.state := by
  have cert := runScans_spec h
  clear h
  induction cert with
  | nil st => exact allocation_refl _
  | cons head rest ih => exact allocation_trans (stock_scan_allocationLe head) ih


private def outputSig : Clif.Signature :=
  { returns := [⟨.i64, .none, .normal⟩, ⟨.i64, .none, .normal⟩] }
private def outputState : State :=
  { sinkState with tryRegs := #[([.vreg 192 .int], [.vreg 193 .int])] }
private def outputNext : State :=
  { outputState with base := ((outputState.base.fresh .int).2.fresh .int).2 }
private def outputValue : V := .regsVec [[.vreg 194 .int], [.vreg 195 .int]]
private theorem output_run :
    Stock.externCtor sinkCtx T.gen_call_output [.op (.sig outputSig)] outputState =
      .ok (outputValue, outputNext) := rfl

/-- Actual call-output generation allocates two fresh registers while keeping
nonempty exception reservations. -/
theorem stock_ctor_allocationLe_witness :
    Stock.externCtor sinkCtx T.gen_call_output [.op (.sig outputSig)] outputState =
      .ok (outputValue, outputNext) ∧ AllocationLe outputState outputNext ∧
      outputNext.base.nextVreg = outputState.base.nextVreg + 2 ∧
      outputNext.tryRegs[0]? = some ([.vreg 192 .int], [.vreg 193 .int]) :=
  ⟨output_run, stock_ctor_allocationLe output_run, rfl, rfl⟩

private def outputProgram : Program := { (default : Program) with terms := #[T.gen_call_output] }

theorem stock_apply_allocationLe_witness :
    (applyTerm outputProgram (Stock.sem sinkCtx) {} 1 T.gen_call_output.ret 0
      [.op (.sig outputSig)]).run (outputState, #[]) =
        .ok (some outputValue, outputNext, #[]) ∧ AllocationLe outputState outputNext ∧
      outputNext.base.nextVreg = outputState.base.nextVreg + 2 := by
  have run : (applyTerm outputProgram (Stock.sem sinkCtx) {} 1 T.gen_call_output.ret 0
      [.op (.sig outputSig)]).run (outputState, #[]) =
        .ok (some outputValue, outputNext, #[]) := rfl
  exact ⟨run, stock_apply_allocationLe run, rfl⟩

/-- A complete opportunistic scan installs an alias without moving the frontier. -/
theorem stock_scan_allocationLe_witness :
    ∃ ctx st output, scanInstruction ctx 0 0 1 false st = .ok output ∧
      AllocationLe st output.state ∧ output.state.alias[192]? = some (some 197) ∧
      output.state.base.nextVreg = 194 := by
  obtain ⟨run, alias, _, _⟩ := stock_scan_aliasBelow_witness
  exact ⟨_, _, _, run, stock_scan_allocationLe run, alias, rfl⟩

/-- A real tail-recursive block scan also retains its allocation frontier. -/
theorem stock_scanBlock_allocationLe_witness :
    ∃ ctx st output, scanBlock ctx 0 1 false [0] st = .ok output ∧
      AllocationLe st output.state ∧ output.state.alias[192]? = some (some 197) ∧
      output.state.base.nextVreg = 194 := by
  obtain ⟨run, alias, _⟩ := stock_scanBlock_aliasBelow_witness
  exact ⟨_, _, _, run, stock_scanBlock_allocationLe run, alias, rfl⟩

end Backend.Stock.Proof


module

public import FV.Backend.Proof.StockAllocationFlow

@[expose] public section

/-! Constructor frame needed by the non-sink constructor coverage model.
The fold proof reuses the reservation traversal from StockAllocationFlow. -/
namespace Backend.Stock.Proof
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 4096

private def fields (st : State) := st.sunk

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


private theorem delegate_fields {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V}
    (h : (match Backend.externCtor ctx t args st.base with
      | .ok (v, base) => ExtResult.ok (v, { st with base })
      | .fail => ExtResult.fail
      | .unmodeled e => ExtResult.unmodeled e) = ExtResult.ok (v, next)) :
    fields next = fields st := by
  cases call : Backend.externCtor ctx t args st.base with
  | fail => rw [call] at h; cases h
  | unmodeled e => rw [call] at h; cases h
  | ok pair =>
    rcases pair with ⟨value, base⟩
    rw [call] at h
    cases h
    rfl

/-- Every actual helper other than sink_inst retains the complete
sunk-bit array, including payload aliasing and demand updates. -/
theorem stock_ctor_noSink {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V} (notSink : t.id ≠ TId.sink_inst)
    (h : Stock.externCtor ctx t args st = .ok (v, next)) :
    next.sunk = st.sunk := by
  change fields next = fields st
  unfold Stock.externCtor at h
  split at h
  all_goals dsimp only at h
  all_goals try solve | exact delegate_fields h
  all_goals repeat' first
    | (solve | cases h <;> rfl)
    | (solve | exact (delegate_fields h).trans (by rfl))
    | (solve | exact (delegate_fields h).trans (marks_fields st _))
    | (solve | exfalso; apply notSink; assumption)
    | split at h
  all_goals
    rename_i _ _ sig _ _ ps _ _ s regs step
    cases h
    exact try_fold_fields ps ctx.tryRegs.1
      ((payloadRegs sig.callConv).zip ctx.tryRegs.2) st [] step

/-- Actual call-output allocation inhabits the non-sink frame theorem. -/
theorem stock_ctor_noSink_witness :
    ∃ (ctx : Ctx) (st next : State) (t : Term) (args : List V) (out : V),
      t.id ≠ TId.sink_inst ∧ Stock.externCtor ctx t args st = .ok (out,next) ∧
      next.base.nextVreg = st.base.nextVreg+2 ∧ next.sunk = st.sunk := by
  obtain ⟨run,allocation,grows,slots⟩ := stock_ctor_allocationLe_witness
  exact ⟨_,_,_,_,_,_,by decide,run,grows,stock_ctor_noSink (by decide) run⟩
end Backend.Stock.Proof

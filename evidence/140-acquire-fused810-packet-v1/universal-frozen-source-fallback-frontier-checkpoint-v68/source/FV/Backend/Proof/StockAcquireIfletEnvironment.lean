import FV.Backend.Proof.StockAcquireRootArgumentFields

namespace Backend.Stock.Proof
open Backend.Proof Isle Isle.Interp Isle.Aarch64
attribute [local irreducible] Isle.Aarch64.program

/-- The real eligibility match preserves every argument except its instruction binding. -/
theorem stock_sink_iflet_environment {ctx : Ctx} {st next : State} {tr tr' : Array RuleId}
    {env bound : Isle.Interp.Env V} {x k v n : Nat}
    (hv : env[x]? = some (some (.value v)))
    (h : (matchIfLets program (Stock.sem ctx) {} (n + 4)
      [⟨.bind 18 k (.wildcard 18), .term 18 221 [.var 15 x]⟩] env).run (st, tr) =
        .ok (some bound, next, tr')) :
    ∃ i, Stock.externCtor ctx T.is_sinkable_inst [.value v] st = .ok (.inst i, st) ∧
      next = st ∧ tr' = tr ∧ bound = env.setIfInBounds k (some (.inst i)) := by
  simp only [matchIfLets.eq_3, evalExpr.eq_7, evalArgs.eq_3, evalExpr.eq_2,
    evalArgs.eq_2, hv, isel_monad] at h
  simp only [applyTerm.eq_2, data_program.t221, T.is_sinkable_inst,
    Stock.sem, Stock.externCtor, isel_monad] at h
  cases he : source ctx st v with
  | none => simp only [he, isel_monad] at h; cases h
  | some pair =>
    obtain ⟨i, eligible⟩ := pair
    cases eligible with
    | false => simp only [he, isel_monad] at h; cases h
    | true =>
      simp only [he, isel_monad, matchPat] at h
      split at h
      · rename_i hk
        simp only [isel_monad, matchIfLets.eq_2,
          Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨i, ?_, rfl, rfl, ?_⟩
        · change (match source ctx st v with
            | some (j, true) => ExtResult.ok (V.inst j, st)
            | _ => ExtResult.fail) = ExtResult.ok (V.inst i, st)
          rw [he]
        · rfl
      · cases h


end Backend.Stock.Proof

import FV.Backend.Proof.StockSinkProvenance

/-! Matching preserves environment slots which are not bound by the pattern.
This supports provenance of instruction variables used by load-sinking RHSs. -/
namespace Backend.Stock.Proof
open Backend.Proof Isle Isle.Interp Isle.Aarch64

mutual
private def avoids (k : Nat) : Pattern → Bool
  | .bind _ x sub => x != k && avoids k sub
  | .and _ ps | .term _ _ ps => avoidsList k ps
  | _ => true
private def avoidsList (k : Nat) : List Pattern → Bool
  | [] => true
  | q :: qs => avoids k q && avoidsList k qs
end

private theorem avoidsList_eq (k : Nat) (ps : List Pattern) :
    avoidsList k ps = true ↔ ∀ q ∈ ps, avoids k q = true := by
  induction ps with
  | nil => simp [avoidsList]
  | cons q qs ih => simp [avoidsList, ih]

section
variable {V σ : Type} {p : Program} {sem : Isle.Sem V σ} {st : σ} {k : Nat}

mutual
private theorem pat_keeps {pat : Pattern} {v : V} {env bound : Isle.Interp.Env V}
    (ha : avoids k pat = true)
    (hm : matchPat p sem st pat v env = .ok (some bound)) : bound[k]? = env[k]? := by
  cases pat with
  | bind ty x sub =>
    simp only [avoids, Bool.and_eq_true, bne_iff_ne] at ha
    obtain ⟨_, hm⟩ := matchPat_bind_inv hm
    have h := pat_keeps ha.2 hm
    exact h.trans (by simp [ha.1])
  | wildcard ty => simp only [matchPat, pure, Except.pure] at hm; cases hm; rfl
  | var ty x =>
    rw [matchPat.eq_2] at hm
    split at hm
    · split at hm <;> simp_all only [pure, Except.pure, Except.ok.injEq,
        Option.some.injEq, reduceCtorEq]
    · cases hm
  | constBool ty b =>
    rw [matchPat.eq_3] at hm
    split at hm <;> simp_all only [pure, Except.pure, Except.ok.injEq,
      Option.some.injEq, reduceCtorEq]
  | constInt ty i =>
    rw [matchPat.eq_4] at hm
    split at hm <;> simp_all only [pure, Except.pure, Except.ok.injEq,
      Option.some.injEq, reduceCtorEq]
  | constPrim ty name =>
    rw [matchPat.eq_5] at hm
    split at hm
    · split at hm <;> simp_all only [pure, Except.pure, Except.ok.injEq,
        Option.some.injEq, reduceCtorEq]
    · cases hm
  | and ty ps => exact all_keeps (by simpa only [avoids, avoidsList_eq] using ha) hm
  | term ty t ps =>
    have ha : ∀ q ∈ ps, avoids k q = true := by simpa only [avoids, avoidsList_eq] using ha
    rw [matchPat.eq_8] at hm
    cases ht : termOf p t with
    | error e => rw [ht] at hm; cases hm
    | ok term =>
      rw [ht] at hm
      simp only [bind, Except.bind] at hm
      split at hm
      · split at hm
        · split at hm
          · exact args_keeps ha hm
          · cases hm
        · cases hm
      · split at hm
        · exact args_keeps ha hm
        · cases hm
      · split at hm
        · cases hm
        · split at hm
          · exact args_keeps ha hm
          · split at hm <;> cases hm
          · cases hm
      · cases hm

termination_by sizeOf pat

private theorem all_keeps {ps : List Pattern} {v : V} {env bound : Isle.Interp.Env V}
    (ha : ∀ q ∈ ps, avoids k q = true)
    (hm : matchAll p sem st ps v env = .ok (some bound)) : bound[k]? = env[k]? := by
  cases ps with
  | nil => simp only [matchAll, pure, Except.pure] at hm; cases hm; rfl
  | cons q qs =>
    rw [matchAll.eq_2] at hm
    cases hq : matchPat p sem st q v env with
    | error e => rw [hq] at hm; cases hm
    | ok value =>
      cases value with
      | none => rw [hq] at hm; cases hm
      | some middle =>
        rw [hq] at hm
        simp only [bind, Except.bind] at hm
        exact (all_keeps (fun q hq => ha q (List.mem_cons_of_mem _ hq)) hm).trans
          (pat_keeps (ha q (List.mem_cons_self ..)) hq)
termination_by sizeOf ps

private theorem args_keeps {ps : List Pattern} {vs : List V} {env bound : Isle.Interp.Env V}
    (ha : ∀ q ∈ ps, avoids k q = true)
    (hm : matchArgs p sem st ps vs env = .ok (some bound)) : bound[k]? = env[k]? := by
  cases ps with
  | nil =>
    cases vs <;> simp only [matchArgs, isel_monad] at hm <;> cases hm
    rfl
  | cons q qs =>
    cases vs with
    | nil => simp only [matchArgs] at hm; cases hm
    | cons v vs =>
      obtain ⟨middle, hq, ht⟩ := matchArgs_cons_inv hm
      exact (args_keeps (fun q hq => ha q (List.mem_cons_of_mem _ hq)) ht).trans
        (pat_keeps (ha q (List.mem_cons_self ..)) hq)
termination_by sizeOf ps
end
end

/-- Any successful match preserves a slot when every binding in the matched
pattern targets another slot. Applies to actual stock patterns and extractors. -/
theorem stock_pattern_keeps {ctx : Ctx} {st : State} {pat : Pattern} {v : Backend.V}
    {env bound : Isle.Interp.Env Backend.V} {k : Nat}
    (ha : avoids k pat = true)
    (hm : matchPat program (Stock.sem ctx) st pat v env = .ok (some bound)) :
    bound[k]? = env[k]? := pat_keeps ha hm

/-- An actual binding at slot0 preserves the producer instruction at slot1. -/
theorem stock_pattern_keeps_witness :
    ∃ env bound : Isle.Interp.Env Backend.V,
      env[1]? = some (some (.inst 7)) ∧
      avoids 1 (.bind 15 0 (.wildcard 15)) = true ∧
      matchPat program (Stock.sem sinkCtx) sinkState
        (.bind 15 0 (.wildcard 15)) (.value 1) env = .ok (some bound) ∧
      bound[1]? = some (some (.inst 7)) := by
  let env : Isle.Interp.Env Backend.V := #[none, some (.inst 7)]
  let bound := env.set! 0 (some (.value 1))
  have hm : matchPat program (Stock.sem sinkCtx) sinkState
      (.bind 15 0 (.wildcard 15)) (.value 1) env = .ok (some bound) := rfl
  exact ⟨env, bound, rfl, rfl, hm, stock_pattern_keeps rfl hm⟩

end Backend.Stock.Proof

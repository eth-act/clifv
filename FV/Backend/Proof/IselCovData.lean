import FV.Backend.Proof.IselCovSound

/-!
# Form coverage of the ISLE lowering (V3): the instruction data holds no `MInst`

`instData`, `termData` and `tryCallData` build `InstructionData` values without `MInst` data
(`covV`), as `IselFlowData` shows they hold no register.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Aarch64

theorem covVL_nil : covVL [] = true := rfl

theorem covVL_cons {v : V} {vs : List V} (h1 : covV v = true) (h2 : covVL vs = true) :
    covVL (v :: vs) = true := by simp [covVL, h1, h2]

theorem covV_data_ne {ty : TypeId} {k : Nat} {fs : List V} (hty : ty ≠ tyMInst)
    (h : covVL fs = true) : covV (.data ty k fs) = true := by
  rw [covV_data]
  simp [hty, h]

theorem covV_mkVariant {ty : TypeId} {name : String} {fs : List V} (hty : ty ≠ tyMInst)
    (h : covVL fs = true) : covV (mkVariant ty name fs) = true := by
  unfold mkVariant
  split
  · exact covV_data_ne hty h
  · rfl

theorem covV_int {i : Int} : covV (.int i) = true := rfl
theorem covV_value {x : Nat} : covV (.value x) = true := rfl
theorem covV_values {xs : List Nat} : covV (.values xs) = true := rfl
theorem covV_op {o : Opnd} : covV (.op o) = true := rfl
theorem covV_blockCalls {bs : List Nat} : covV (.blockCalls bs) = true := rfl

/-- Build `covV` of an `instDataV` term. -/
macro "cov_data" : tactic => `(tactic| (
  unfold instDataV opcodeV
  repeat' first
    | with_reducible apply covV_mkVariant (by decide)
    | with_reducible exact covVL_nil
    | with_reducible apply covVL_cons
    | with_reducible exact covV_int
    | with_reducible exact covV_value
    | with_reducible exact covV_values
    | with_reducible exact covV_op
    | with_reducible exact covV_blockCalls))

set_option maxRecDepth 20000 in
/-- The data of a statement holds no `MInst`. -/
theorem instData_covV {f : Clif.Function} {c : Clif.Inst} {d : V} (h : instData f c = .ok d) :
    covV d = true := by
  cases c <;> simp only [instData] at h
  all_goals (repeat' split at h)
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h)
    | (simp only [pure, Except.pure, Except.ok.injEq] at h
       subst h
       cov_data)

/-- The data of a terminator holds no `MInst`. -/
theorem termData_covV {t : Clif.Terminator} {d : V} (h : termData t = .ok d) : covV d = true := by
  cases t <;> simp only [termData] at h
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h)
    | (simp only [pure, Except.pure, Except.ok.injEq] at h
       subst h
       cov_data)

set_option maxRecDepth 20000 in
/-- The data of a `try_call` holds no `MInst`. -/
theorem tryCallData_covV {f : Clif.Function} {t : Clif.Terminator} {d : V}
    (h : tryCallData f t = .ok d) : covV d = true := by
  cases t <;> simp only [tryCallData] at h
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
    | skip
  all_goals
    rename_i et
    cases he : exnTableOpnd f et with
    | error e => rw [he] at h; cases h
    | ok q =>
      rw [he] at h
      obtain ⟨sig, items⟩ := q
      simp only [bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
        | (simp only [pure, Except.pure, Except.ok.injEq] at h
           subst h
           cov_data)

end Backend.Proof.Cov

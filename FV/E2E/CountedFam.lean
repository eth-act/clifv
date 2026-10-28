import FV.E2E.RegLevelCorrectI
import FV.Backend.Proof.VCodeSemICall
import FV.Backend.Proof.DeadCleanupAdapter

/-!
# Counted semantics of a family (SEM1, `docs/plans/uninit.md` §5.9)

`ISem.counted sem` for a family `sem : Nat → Sem` whose non-calls do not depend on the index
(`NoncallIndep sem`): the facts `IselSimI`/`IselSimITry` use of `csemI`, for any such family
(`csemI` is `ISem.counted (csem F ctx (X.at ·))`, `csemI_eq_counted`):

* `counted_noncall`, `counted_call`;
* `ProbeOf semB sem`: `semB n` agrees with `sem n` on non-calls and its calls fail;
  `counted_probe_proj`: such a probe projects into the counted semantics at any fixed counter;
* `seqRun_counted_le1`: a straight-line run with at most one call under `ISem.counted sem` from
  counter `n` is the run of `sem n`, the counter counting the calls (`SeqEnd.liftI`).
-/

namespace Backend.Proof

open Backend

/-- The non-calls of `sem n` do not depend on `n`. -/
def NoncallIndep (sem : Nat → Sem) : Prop :=
  ∀ i : MInst, i.isCallI = false → ∀ m m', sem m i = sem m' i

/-- `semB n` is `sem n` on non-calls, and its calls fail. -/
structure ProbeOf (semB sem : Nat → Sem) : Prop where
  noncall : ∀ n (i : MInst), i.isCallI = false → semB n i = sem n i
  call : ∀ n (i : MInst), i.isCallI = true → ∀ uses w, semB n i uses w = none

section
variable {sem : Nat → Sem}

theorem counted_noncall (hni : NoncallIndep sem) {i : MInst} (h : i.isCallI = false)
    (uses : List CV) (w : Arm.ArmState) (n n' : Nat) :
    ISem.counted sem i uses (w, n) = (sem n' i uses w).map fun r => (r.1, (r.2.1, n), r.2.2) := by
  simp only [ISem.counted, h, Bool.false_eq_true, ↓reduceIte]
  rw [hni i h n n']

theorem counted_call {i : MInst} (h : i.isCallI = true) (uses : List CV) (w : Arm.ArmState)
    (n : Nat) :
    ISem.counted sem i uses (w, n) = (sem n i uses w).map fun r => (r.1, (r.2.1, n + 1), r.2.2) := by
  simp only [ISem.counted, h, ↓reduceIte]

/-- **A probe projects into the counted semantics at any fixed counter.** -/
theorem counted_probe_proj {semB : Nat → Sem} (hB : ProbeOf semB sem) (n : Nat) :
    ISem.ProjW (fun w => (w, n)) (semB n) (ISem.counted sem) := by
  intro i uses w outs w' ctl h
  cases hc : i.isCallI with
  | false =>
    rw [hB.noncall n i hc] at h
    simp only [ISem.counted, hc, Bool.false_eq_true, ↓reduceIte, h, Option.map_some]
  | true => rw [hB.call n i hc] at h; cases h

/-- The general form: `sem m`, which a call of the sequence (at most one) reads at the world's
counter `n` (`m = n`). -/
theorem seqRun_counted_le1_at (hni : NoncallIndep sem) :
    ∀ (ms : List MInst) (m n : Nat), callsI ms ≤ 1 → (callsI ms = 1 → m = n) →
      ∀ (ρ : Nat → CV) (w : Arm.ArmState),
        seqRun (ISem.counted sem) ms ρ (w, n) =
          (seqRun (sem m) ms ρ w).map (SeqEnd.liftI ms n)
  | [], _, n, _, _, ρ, w => by simp [seqRun, SeqEnd.liftI]
  | i :: ms, m, n, hle, hmn, ρ, w => by
    simp only [seqRun]
    cases ho : i.operands with
    | error _ => rfl
    | ok ops =>
      simp only
      cases hc : i.isCallI with
      | false =>
        have hle' : callsI ms ≤ 1 := by rw [callsI_cons, hc] at hle; simpa using hle
        have hmn' : callsI ms = 1 → m = n := fun h => hmn (by rw [callsI_cons, hc]; simpa using h)
        rw [counted_noncall hni hc _ w n m]
        cases hs : sem m i (vuses ops ρ) w with
        | none => rfl
        | some r =>
          obtain ⟨outs, w', ctl⟩ := r
          simp only [Option.map_some]
          by_cases hl : outs.length = (ops.toList.filter Operand.isDef).length
          · simp only [hl, ↓reduceIte]
            cases ctl with
            | next =>
              simp only
              rw [seqRun_counted_le1_at hni ms m n hle' hmn' _ w']
              cases seqRun (sem m) ms (vdefUpd ops outs ρ) w' with
              | none => rfl
              | some e => simp only [Option.map_some, SeqEnd.liftI_noncall hc]
            | goto j => simp [SeqEnd.liftI, hc]
            | ret => simp [SeqEnd.liftI, hc]
            | halt => simp [SeqEnd.liftI, hc]
          · simp only [hl, ↓reduceIte]; rfl
      | true =>
        have h1 : callsI (i :: ms) = callsI ms + 1 := by rw [callsI_cons, hc]; rfl
        have h0 : callsI ms = 0 := by omega
        have e : m = n := hmn (by omega)
        subst e
        rw [counted_call hc _ w m]
        cases hs : sem m i (vuses ops ρ) w with
        | none => rfl
        | some r =>
          obtain ⟨outs, w', ctl⟩ := r
          simp only [Option.map_some]
          by_cases hl : outs.length = (ops.toList.filter Operand.isDef).length
          · simp only [hl, ↓reduceIte]
            cases ctl with
            | next =>
              simp only
              rw [seqRun_counted_le1_at hni ms m (m + 1) (by omega) (by omega) _ w']
              cases seqRun (sem m) ms (vdefUpd ops outs ρ) w' with
              | none => rfl
              | some e => simp only [Option.map_some, SeqEnd.liftI_call hc h0]
            | goto j => simp [SeqEnd.liftI, hc]
            | ret => simp [SeqEnd.liftI, hc]
            | halt => simp [SeqEnd.liftI, hc]
          · simp only [hl, ↓reduceIte]; rfl

/-- **A straight-line run with at most one call under `ISem.counted sem`** from counter `n` is
the run of `sem n`, the counter counting the calls executed (`SeqEnd.liftI`). -/
theorem seqRun_counted_le1 (hni : NoncallIndep sem) {ms : List MInst} (hle : callsI ms ≤ 1)
    (ρ : Nat → CV) (w : Arm.ArmState) (n : Nat) :
    seqRun (ISem.counted sem) ms ρ (w, n) = (seqRun (sem n) ms ρ w).map (SeqEnd.liftI ms n) :=
  seqRun_counted_le1_at hni ms n n hle (fun _ => rfl) ρ w

end

/-! ## Instances: `csem`, `valueSem` -/

theorem noncallIndep_csem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) :
    NoncallIndep fun n => csem F ctx (X.at n) :=
  fun _ h n n' => csem_at_noncall F ctx X h n n'

theorem probeOf_csem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) :
    ProbeOf (fun n => csem F ctx { X.at n with call := fun _ _ _ => none })
      (fun n => csem F ctx (X.at n)) where
  noncall _ _ h := csem_call_congr F ctx _ _ h
  call _ i h _ _ := by cases i <;> simp_all [MInst.isCallI, csem]

theorem valueSem_call_congr (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    (c : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState))
    {i : MInst} (h : i.isCallI = false) :
    DeadCleanup.valueSem F ctx { X with call := c } i = DeadCleanup.valueSem F ctx X i := by
  funext us w
  simp only [DeadCleanup.valueSem]
  rw [csem_call_congr F ctx X c h]

theorem noncallIndep_valueSem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) :
    NoncallIndep fun n => DeadCleanup.valueSem F ctx (X.at n) :=
  fun _ h n n' => valueSem_call_congr F ctx (X.at n') (X.call n) h

theorem probeOf_valueSem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) :
    ProbeOf (fun n => DeadCleanup.valueSem F ctx { X.at n with call := fun _ _ _ => none })
      (fun n => DeadCleanup.valueSem F ctx (X.at n)) where
  noncall _ _ h := valueSem_call_congr F ctx _ _ h
  call _ i h _ _ := by
    simp only [DeadCleanup.valueSem]
    split
    · cases i <;> simp_all [MInst.isCallI, DeadCleanup.specForm, DeadCleanup.pureForm,
        DeadCleanup.cmpForm]
    · cases i <;> simp_all [MInst.isCallI, csem]

end Backend.Proof

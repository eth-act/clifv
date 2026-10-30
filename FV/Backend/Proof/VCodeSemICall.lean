import FV.Backend.Proof.VCodeSemI

/-!
# Straight-line runs with one call under the counted semantics (SEM1 step 2, `docs/plans/uninit.md` §5.3)

A CLIF call lowers to a straight-line sequence with one VCode call (the argument moves, the
`call`, the result moves). Under `csemI` its call is number `n` of the activation (the world's
counter) and every instruction after it runs at counter `n + 1`; the non-calls do not read the
index (`csem_at_noncall`). So a sequence with at most one call runs under `csemI` from counter
`n` exactly as under `csem` at index `n`, the counter counting the calls executed:

* `SeqEnd.liftI ms n`: a `csem` run's end with the counters of `csemI` (`n` plus the calls of
  `ms` before the stop, plus one for the world after a stopping call);
* `seqRun_csemI_le1`: `seqRun (csemI F ctx X) ms ρ (w, n) = (seqRun (csem F ctx (X.at n)) ms ρ
  w).map (SeqEnd.liftI ms n)` when `ms` has at most one call;
* `LowerInstOk.csemI_le1`: a lowering with at most one call that is correct for `csem` at every
  index is correct for `csemI` with the memory relation on the Arm world and a counter invariant
  `Q` that advances by the lowering's calls over the CLIF instruction (for a call: the callee
  contract's part, `Q cm n → Q cm' (n + 1)`).
-/

namespace Backend.Proof

open Backend

/-- The number of calls (`MInst.isCallI`) of a sequence. -/
def callsI (ms : List MInst) : Nat := ms.countP (·.isCallI)

@[simp] theorem callsI_nil : callsI [] = 0 := rfl

theorem callsI_cons (i : MInst) (ms : List MInst) :
    callsI (i :: ms) = callsI ms + (if i.isCallI then 1 else 0) := by
  unfold callsI
  by_cases h : i.isCallI = true <;> simp [List.countP_cons, h]

theorem callsI_take_zero {ms : List MInst} (h : callsI ms = 0) (k : Nat) : callsI (ms.take k) = 0 := by
  unfold callsI at h ⊢
  rw [List.countP_eq_zero] at h ⊢
  exact fun a ha => h a (List.mem_of_mem_take ha)

/-- A `csem` run's end with the counters of the `csemI` run from counter `n`: the calls of `ms`
before the stopping instruction, and one more for the world after a stopping call. -/
def SeqEnd.liftI (ms : List MInst) (n : Nat) : SeqEnd CV Arm.ArmState → SeqEnd CV (Arm.ArmState × Nat)
  | .fall ρ w => .fall ρ (w, n + callsI ms)
  | .stop k i ops ρ w outs w' ctl =>
    .stop k i ops ρ (w, n + callsI (ms.take k)) outs
      (w', n + callsI (ms.take k) + if i.isCallI then 1 else 0) ctl

theorem SeqEnd.liftI_noncall {i : MInst} (hi : i.isCallI = false) (ms : List MInst) (n : Nat)
    (e : SeqEnd CV Arm.ArmState) : (SeqEnd.liftI ms n e).succ = SeqEnd.liftI (i :: ms) n e.succ := by
  cases e with
  | fall ρ w => simp [SeqEnd.liftI, SeqEnd.succ, callsI_cons, hi]
  | stop k j ops ρ w outs w' ctl =>
    simp [SeqEnd.liftI, SeqEnd.succ, List.take_succ_cons, callsI_cons, hi]

theorem SeqEnd.liftI_call {i : MInst} (hi : i.isCallI = true) {ms : List MInst}
    (h0 : callsI ms = 0) (n : Nat) (e : SeqEnd CV Arm.ArmState) :
    (SeqEnd.liftI ms (n + 1) e).succ = SeqEnd.liftI (i :: ms) n e.succ := by
  cases e with
  | fall ρ w => simp [SeqEnd.liftI, SeqEnd.succ, callsI_cons, hi, h0]
  | stop k j ops ρ w outs w' ctl =>
    simp [SeqEnd.liftI, SeqEnd.succ, List.take_succ_cons, callsI_cons, hi, callsI_take_zero h0,
      Nat.add_assoc, Nat.add_comm 1]

/-- The general form: `csem` at index `m`, which a call of the sequence (at most one) reads at
the world's counter `n` (`m = n`). -/
theorem seqRun_csemI_le1_at (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) :
    ∀ (ms : List MInst) (m n : Nat), callsI ms ≤ 1 → (callsI ms = 1 → m = n) →
      ∀ (ρ : Nat → CV) (w : Arm.ArmState),
        seqRun (csemI F ctx X) ms ρ (w, n) =
          (seqRun (csem F ctx (X.at m)) ms ρ w).map (SeqEnd.liftI ms n)
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
        rw [csemI_noncall F ctx X hc _ w n m]
        cases hs : csem F ctx (X.at m) i (vuses ops ρ) w with
        | none => rfl
        | some r =>
          obtain ⟨outs, w', ctl⟩ := r
          simp only [Option.map_some]
          by_cases hl : outs.length = (ops.toList.filter Operand.isDef).length
          · simp only [hl, ↓reduceIte]
            cases ctl with
            | next =>
              simp only
              rw [seqRun_csemI_le1_at F ctx X ms m n hle' hmn' _ w']
              cases seqRun (csem F ctx (X.at m)) ms (vdefUpd ops outs ρ) w' with
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
        rw [csemI_call F ctx X hc _ w m]
        cases hs : csem F ctx (X.at m) i (vuses ops ρ) w with
        | none => rfl
        | some r =>
          obtain ⟨outs, w', ctl⟩ := r
          simp only [Option.map_some]
          by_cases hl : outs.length = (ops.toList.filter Operand.isDef).length
          · simp only [hl, ↓reduceIte]
            cases ctl with
            | next =>
              simp only
              rw [seqRun_csemI_le1_at F ctx X ms m (m + 1) (by omega) (by omega) _ w']
              cases seqRun (csem F ctx (X.at m)) ms (vdefUpd ops outs ρ) w' with
              | none => rfl
              | some e => simp only [Option.map_some, SeqEnd.liftI_call hc h0]
            | goto j => simp [SeqEnd.liftI, hc]
            | ret => simp [SeqEnd.liftI, hc]
            | halt => simp [SeqEnd.liftI, hc]
          · simp only [hl, ↓reduceIte]; rfl

/-- **A straight-line run with at most one call under `csemI`** from counter `n` is the `csem`
run at index `n`, the counter counting the calls executed (`SeqEnd.liftI`). -/
theorem seqRun_csemI_le1 (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) {ms : List MInst}
    (hle : callsI ms ≤ 1) (ρ : Nat → CV) (w : Arm.ArmState) (n : Nat) :
    seqRun (csemI F ctx X) ms ρ (w, n) =
      (seqRun (csem F ctx (X.at n)) ms ρ w).map (SeqEnd.liftI ms n) :=
  seqRun_csemI_le1_at F ctx X ms n n hle (fun _ => rfl) ρ w

/-- **A lowering with at most one call, correct for `csem` at every call index, is correct for
`csemI`**, with the memory relation `MR` on the Arm world and a counter invariant `Q` that the
CLIF instruction advances by the lowering's calls. -/
theorem LowerInstOk.csemI_le1 {F : BitVec 64 → Prop} {fctx : FnCtx} {X : ExtSemI}
    {MR : MemRelT} {Q : Clif.Mem → Nat → Prop} {env : Clif.Env} {p : Clif.Program} {ctx : Ctx}
    {inst : Clif.Inst} {results : List Nat} {st : LState} {rss : List (List Reg)} {st' : LState}
    {ms : List MInst}
    (h : ∀ n, LowerInstOk (csem F fctx (X.at n)) MR env p ctx inst results st rss st' ms)
    (hle : callsI ms ≤ 1)
    (hQ : ∀ fr cm vals cm' n, instOutcome env p fr cm inst = .ok (vals, cm') → Q cm n →
      Q cm' (n + callsI ms)) :
    LowerInstOk (Backend.Proof.csemI F fctx X) (fun sl cm w => MR sl cm w.1 ∧ Q cm w.2) env p ctx
      inst results
      st rss st' ms := by
  refine ⟨(h 0).mono, (h 0).defs, fun fr cm ρ ⟨w, n⟩ hf hv hd ⟨hmr, hq⟩ => ?_⟩
  have hr := (h n).run fr cm ρ w hf hv hd hmr
  have hseq := seqRun_csemI_le1 F fctx X hle ρ w n
  cases ho : instOutcome env p fr cm inst with
  | ok r =>
    obtain ⟨vals, cm'⟩ := r
    simp only [ho] at hr ⊢
    obtain ⟨hu, ρ', w', hs, hres, hmr'⟩ := hr
    refine ⟨hu, ρ', (w', n + callsI ms), ?_, hres, hmr', hQ fr cm vals cm' n ho hq⟩
    rw [hseq, hs]; rfl
  | trap c =>
    simp only [ho] at hr ⊢
    intro he
    obtain ⟨hu, k, i, ops, ρ₁, w₁, outs, w₂, hs, htc⟩ := hr he
    refine ⟨hu, k, i, ops, ρ₁, (w₁, n + callsI (ms.take k)), outs,
      (w₂, n + callsI (ms.take k) + if i.isCallI then 1 else 0), ?_, htc⟩
    rw [hseq, hs]; rfl
  | stuck _ => simp only [ho]

end Backend.Proof

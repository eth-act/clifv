module

public import FV.Backend.Proof.IselFlowExt

@[expose] public section

/-!
# The outgoing area under the extern constructors (S10g, #404)

Only `gen_call_info` and `gen_call_ind_info` change the lowering state's outgoing area (they
raise it to the callee's stack-argument size). **`externCtor_out`**: every other successful
extern constructor call keeps it.
-/

namespace Backend.Proof.OutBound

open Backend Isle Isle.Aarch64 Backend.Proof.Flow

/-- A successful result of extern constructor `id` keeps the outgoing area of `st`, unless `id`
is `gen_call_info` or `gen_call_ind_info`. -/
def OutP (st : LState) (id : TermId) (_args : List V) (r : ExtResult (V × LState)) : Prop :=
  id ≠ TId.gen_call_info → id ≠ TId.gen_call_ind_info →
    ∀ v st', r = .ok (v, st') → st'.outgoing = st.outgoing

/-- A fold whose steps keep the outgoing area keeps it. -/
theorem foldl_out_eq {α β : Type} (l : List α) (F : β × LState → α → β × LState)
    (hF : ∀ q a, (F q a).2.outgoing = q.2.outgoing) :
    ∀ q, (l.foldl F q).2.outgoing = q.2.outgoing := by
  induction l with
  | nil => intro q; rfl
  | cons a l ih => intro q; rw [List.foldl_cons, ih, hF]

set_option maxHeartbeats 4000000 in
/-- **Every extern constructor but `gen_call_info`/`gen_call_ind_info` keeps the outgoing
area.** -/
theorem externCtor_out (ctx : Ctx) (t : Term) (args : List V) (st : LState) :
    OutP st t.id args (externCtor ctx t args st) := by
  unfold externCtor
  split
  · intro _ _ v st' h
    split at h
    · cases h; rfl
    · cases h
  · apply externCtor_split _ (OutP st)
    all_goals
      intros
      unfold OutP
      intro hn1 hn2 v st' h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals cases h
    all_goals first
      | rfl
      | exact absurd rfl hn1
      | exact absurd rfl hn2
      | (simp only [LState.fresh, LState.emit]; done)
      | exact (loadConstantFull_ok _ _ _ _ _).2.2.1
      | exact foldl_out_eq _ _ (fun _ _ => by first | rfl | (split <;> rfl)) _

/-- `externCtor_out`, unfolded. -/
theorem externCtor_out_eq {ctx : Ctx} {t : Term} {args : List V} {st : LState} {v : V}
    {st' : LState} (h1 : t.id ≠ TId.gen_call_info) (h2 : t.id ≠ TId.gen_call_ind_info)
    (h : externCtor ctx t args st = .ok (v, st')) : st'.outgoing = st.outgoing :=
  externCtor_out ctx t args st h1 h2 v st' h

end Backend.Proof.OutBound

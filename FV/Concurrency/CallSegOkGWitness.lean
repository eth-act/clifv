import FV.Concurrency.CallSegOkG
import FV.Concurrency.CallLoadWitness
import FV.Concurrency.CallSegTWitness
import FV.Concurrency.IselCallWitness

/-!
# Witnesses for `CallSegOkG` (#473, step (4))

* `partsOk_trap`: `PartsOk` from a state at a `trap` terminator (no CLIF step from it), on the
  byte partition `Loc1`;
* `seg_end_trap`: `seg_end` from that state with the empty segment;
* `call_next_C`: `call_next` for the caller of `atomic_load` (`CallSeg.WitnessC.csC`) at its call;
* `segW_nil`, `liftW_nil`: `realizedT_segW`/`realizedT_liftW` on the empty segment.
-/

namespace Concurrency.CallSegOkG.Witness

open Prog ClifThread ClifThreadI ThreadRefine CallComposeT PrivCohT.Witness ArmThread
  ArmAllocThread PrepThread CallSegT CallSegT.Witness ClifLift CallSegLift

/-- The byte partition. -/
def Loc1 : Nat → Nat → Prop := fun _ n => n = 1

theorem partDisj_loc1 : PartDisj Loc1 := fun a n b m _ hm h1 h2 => by
  simp only [Loc1] at hm; omega

/-- `s` at a `trap` terminator. -/
def sTrap (s : Clif.State) (c : Clif.TrapCode) : Clif.State :=
  { s with frame := { s.frame with body := [], term := .trap c } }

theorem step_trap (env : Clif.Env) (p : Clif.Program) {s : Clif.State} {c : Clif.TrapCode}
    (hb : s.frame.body = []) (ht : s.frame.term = .trap c) : Clif.step env p s = .trapped c := by
  unfold Clif.step; rw [hb]; simp only; rw [ht]; rfl

/-- The states with the frame of `sTrap s c`: no CLIF step. -/
theorem reach_trap {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {c : Clif.TrapCode} :
    ∀ {t : TState}, RReach env p (.run (sTrap s c)) t →
      ∃ s', t = .run s' ∧ s'.frame.body = [] ∧ s'.frame.term = .trap c := by
  have hno : ∀ (s' : Clif.State), s'.frame.body = [] → s'.frame.term = .trap c →
      ∀ B, res (Clif.step env p (withBytes s' B)) = none := fun s' hb ht B => by
    rw [step_trap env p (s := withBytes s' B) hb ht]; rfl
  intro t h
  induction h with
  | base => exact ⟨_, rfl, rfl, rfl⟩
  | step _ hs ih =>
    obtain ⟨s', rfl, hb, ht⟩ := ih
    obtain ⟨-, ⟨B, hB⟩, hf⟩ := hs
    obtain ⟨t'', h1, -⟩ := hf B hB
    rw [hno _ hb ht] at h1; cases h1
  | stepS _ hs ih =>
    obtain ⟨s', rfl, hb, ht⟩ := ih
    obtain ⟨-, ⟨B, hB⟩, -, hf⟩ := hs
    obtain ⟨t'', h1, -⟩ := hf B hB
    rw [hno _ hb ht] at h1; cases h1
  | @strip t t' _ he ih =>
    obtain ⟨s', rfl, hb, ht⟩ := ih
    cases t' with
    | ret v => cases he
    | run s2 =>
      simp only [strip, TState.run.injEq] at he
      have hf := congrArg Clif.State.frame he
      simp only [withBytes] at hf
      exact ⟨s2, rfl, hf ▸ hb, hf ▸ ht⟩

/-- **`PartsOk` from a trap**: no CLIF step from a reachable state. -/
theorem partsOk_trap (env : Clif.Env) (p : Clif.Program) (s : Clif.State) (c : Clif.TrapCode) :
    PartsOk env p (.run (sTrap s c)) Loc1 := fun t evs t' hR hs => by
  obtain ⟨s', rfl, hb, ht⟩ := reach_trap hR
  obtain ⟨-, ⟨B, hB⟩, hf⟩ := hs
  obtain ⟨t'', h1, -⟩ := hf B hB
  rw [step_trap env p (s := withBytes s' B) hb ht] at h1; cases h1

/-- **Non-vacuity of `seg_end`**: the empty segment of the trap state, below no callers. -/
theorem seg_end_trap (env : Clif.Env) (p : Clif.Program) (s : Clif.State) (c : Clif.TrapCode)
    (R : Backend.Proof.RL) (ls : List Lab) (u : Arm.ArmState × Mon)
    (hr : PRun Policy.arm id (fun _ _ => True) u ls u) :
    ∃ k' d', RealT env p (fun _ => True) ls k' (encT U100 (.run (pushC [] (sTrap s c))),
        fun _ => False) d' ∧
      (k' = ls.length ∨ EndT env p 0 (ls.take k') d' ∨
        (k' = 0 ∧ ∃ s' M DE, True ∧ (.run (sTrap s c) : TState) = .run s' ∧
          d' = (encT M (.run (pushC [] s')), DE) ∧
          (∀ a, M a → U100 a) ∧ (∀ a, DE a → PrivA R a ∨ M a ∨ (¬ ∃ n, Loc1 a n) ∨ False) ∧
          RReach env p (.run (sTrap s c)) (.run (pushC [] s')))) := by
  have href : Refines Maps (PrivA R) (MonPair (evTr (ls.take 0)))
      ([] : List (List (Ev SKind BVal))) (conv (evTr (ls.take 0))) id := by
    simpa [evTr] using refines_privW (MK := Maps) (Priv := PrivA R) (T := [])
      (fun q y hy => by simp [evAt] at hy)
  have hR0 : RReach env p (.run (sTrap s c)) (.run (pushC [] (sTrap s c))) := by
    simpa [pushC] using (RReach.base : RReach env p (.run (sTrap s c)) _)
  exact seg_end (Bnd := fun _ => True) (fun _ _ => trivial) (Dcap := 0)
    (partsOk_trap env p s c) partDisj_loc1 hr (Nat.zero_le _) [] hR0 .nil
    (by simpa [evTr] using CallCompose.xClosed_nil) href (D := fun _ => False) (N := fun _ => False)
    (fun _ h => h.elim) (fun q x h => by rw [evAt_nil] at h; cases h) (Pz := fun _ => True)
    (.inr (.inr ⟨_, rfl, trivial⟩))

/-- **Non-vacuity of `realizedT_segW`**: the empty segment. -/
theorem segW_nil (env : Clif.Env) (p : Clif.Program) (s : Clif.State) (ls : List Lab) :
    RealizedT env p (fun _ => True) ls 0 (encT U100 (.run s)) (encT (maskAfter U100 []) (.run s))
      U100 (DirtyEnd U100 (fun _ => False) ([] : List (List (Ev SKind BVal)))) := by
  have href : Refines Maps (fun _ => False) (MonPair (evTr (ls.take 0)))
      ([] : List (List (Ev SKind BVal))) (conv (evTr (ls.take 0))) id := by
    simpa [evTr] using refines_privW (MK := Maps) (Priv := fun _ => False) (T := [])
      (fun q y hy => by simp [evAt] at hy)
  exact realizedT_segW (NS := fun _ => False) (Nat.zero_le _) .nil
    (by simpa [evTr] using CallCompose.xClosed_nil) href trivial (fun a h => .inr (.inl h))
    (fun _ _ _ _ h => by rw [evAt_nil] at h; cases h) (fun q x h => by rw [evAt_nil] at h; cases h)
    (fun q x h => by rw [evAt_nil] at h; cases h) (fun _ _ => trivial)

/-- **Non-vacuity of `realizedT_liftW`**: the empty segment below a suspended frame. -/
theorem liftW_nil (env : Clif.Env) (p : Clif.Program) (s : Clif.State) (fr : Clif.Frame)
    (rs : List Clif.ValueId) (u : Arm.ArmState × Mon) :
    ∃ (trS' : List (List (Ev SKind BVal))) (s1 : Clif.State),
      RealizedT env p (fun _ => True) [] 0 (encT U100 (.run (pushC [(fr, rs)] s)))
        (encT (maskAfter U100 trS') (.run (pushC [(fr, rs)] s1))) U100
        (DirtyEnd U100 (fun _ => False) trS') ∧ s1 = s := by
  have href : Refines Maps (fun _ => False) (MonPair (evTr (([] : List Lab).take 0)))
      ([] : List (List (Ev SKind BVal))) (conv (evTr (([] : List Lab).take 0))) id := by
    simpa [evTr] using refines_privW (MK := Maps) (Priv := fun _ => False) (T := [])
      (fun q y hy => by simp [evAt] at hy)
  rcases realizedT_liftW (Bnd := fun _ => True) (f := id)
      (ok := fun _ _ => True) (u := u) (PRun.nil) (Nat.zero_le _) [(fr, rs)]
      (s := s) (t := .run s) .nil (by simpa [evTr] using CallCompose.xClosed_nil) href
      (NS := fun _ => False) (fun a h => .inr (.inl h))
      (fun _ _ _ _ h => by rw [evAt_nil] at h; cases h) (fun q x h => by rw [evAt_nil] at h; cases h)
      (fun q x h => by rw [evAt_nil] at h; cases h) (fun _ _ => trivial) with
    ⟨trS', s1, -, hR, hs, -⟩ | ⟨k', hk', trS', j, evs, hp, hj, -⟩
  · exact ⟨trS', s1, hR, hs s rfl⟩
  · obtain rfl : trS' = [] := List.eq_nil_of_prefix_nil hp
    cases hj

open CallSeg.WitnessC in
/-- **Non-vacuity of `call_next`**: the caller of `atomic_load` at its call. -/
theorem call_next_C {env : Clif.Env} (henv : env.extern "ld" = none) (B : Bytes) :
    ∃ e vals callee, (withBytes csC B).frame.func.extern? 0 = some e ∧
      (withBytes csC B).frame.getMany [0] = .ok vals ∧
      vals.map (·.ty) = Clif.AbiParam.tys e.sig.params ∧ pCL.func? e.name = some callee ∧
      Clif.AbiParam.tys callee.sig.params = Clif.AbiParam.tys e.sig.params ∧
      Clif.AbiParam.tys callee.sig.returns = Clif.AbiParam.tys e.sig.returns := by
  obtain ⟨hb, -⟩ := clifC
  obtain ⟨-, -, -, hnames, -⟩ := IselCall.Witness.checksFC
  refine call_next (ext := []) (rest := []) (results := [1]) hb (fun e he => ?_) (s1 := _)
    (by simpa [pushC] using stepC env B)
  have : e.2.name ∈ fC.externs.map (·.2.name) := List.mem_map_of_mem he
  rw [hnames, List.mem_singleton] at this
  rw [this]; exact henv

end Concurrency.CallSegOkG.Witness

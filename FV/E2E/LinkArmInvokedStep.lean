import FV.E2E.LinkArmProphThm
import FV.E2E.LinkPlaceBReach

/-!
# The step of an invoking state, the calling states of a path, the machine's call indices
(SEM1 #537, #680 (3), stage 2 glue)

* **`invoked_step`**: a state that invokes the extern `nm` with `vals` at `m` and steps to `s1`
  without entering a frame got `s1`'s memory back from `nm`'s extern;
* **`reachN_call_at`**: a state reached after `n` calls passes a calling state of every count
  `j < n`, which steps to a state reached after `j + 1` calls;
* **`callIdx_unique`**: two call states of a machine run with the same number of calls before
  them are the same step.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

theorem lstep_next_of_invoked {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {nm : String}
    {vals : List Clif.Val} {m : Clif.Mem} (hinv : Clif.Invoked env p s nm vals m)
    (hci : Opt.HeadNoCI s.frame) {fr1 : Clif.Frame} {m1 : Clif.Mem} :
    Opt.lstep s.frame s.mem ≠ .next fr1 m1 := by
  intro hl
  obtain ⟨-, hinv⟩ := hinv
  revert hinv
  cases hb : s.frame.body with
  | cons st rest =>
    dsimp only
    cases hi : st.inst with
    | call fn args => exact fun _ => (Opt.lstep_call_of_call hb hi).1 fr1 m1 hl
    | callIndirect sig callee args => exact fun _ => hci.1 st rest hb sig callee args hi
    | _ => exact fun h => h.elim
  | nil =>
    dsimp only
    cases ht : s.frame.term with
    | tryCall fn args et =>
      have := hci.2 hb; rw [ht] at this; cases this
    | tryCallIndirect c args et =>
      have := hci.2 hb; rw [ht] at this; cases this
    | returnCall fn args =>
      intro _
      rw [Opt.lstep_term hb, ht] at hl
      simp only [Opt.LRes.ofRes] at hl
      split at hl <;> cases hl
    | _ => exact fun h => h.elim

/-- **The step of an invoking state** (module doc). -/
theorem invoked_step {P : Clif.Program} (hP : ∀ g ∈ P.funcs, Clif.LinkFree g) {env : Clif.Env}
    {p : Clif.Program} {s s1 : Clif.State} (hI : Clif.LInv P s) {nm : String}
    {vals : List Clif.Val} {m : Clif.Mem} (hinv : Clif.Invoked env p s nm vals m)
    (hst : Clif.step env p s = .next s1) (hc : s1.callers = s.callers) :
    ∃ G rv, env.extern nm = some G ∧ G vals m = .returned rv s1.mem := by
  have hst' : Clif.step (env.only (Clif.Invoked env p s)) p s = .next s1 :=
    (Clif.step_only fun _ _ _ h => h).trans hst
  -- an answer of the restricted environment is the invocation's
  have hans : ∀ n g v rv, (env.only (Clif.Invoked env p s)).extern n = some g →
      g v s.mem = .returned rv s1.mem →
      ∃ G rv, env.extern nm = some G ∧ G vals m = .returned rv s1.mem := by
    intro n g v rv hg hr
    obtain ⟨G1, hG1, rfl⟩ := Clif.Env.only_extern_eq hg
    obtain ⟨hA, hr'⟩ := onlyFn_returned hr
    obtain ⟨rfl, rfl, rfl⟩ := invoked_unique hinv hA
    exact ⟨G1, rv, hG1, hr'⟩
  have hne : ∀ (fr : Clif.Frame) (rs : List Clif.ValueId), s1.callers ≠ (fr, rs) :: s.callers :=
    fun fr rs h => by
      have := congrArg List.length (hc.symm.trans h)
      simp at this
  rcases Clif.step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · rw [Clif.step_try _ p s hb ht] at hst'
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next hst'
    obtain ⟨⟨ext, v⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
    rcases Clif.callCont_cases h with ⟨hc1, -⟩ | ⟨-, -, n', g, rv, hg, hr⟩
    · exact absurd hc1 (hne _ _)
    · exact hans n' g v rv hg hr
  · rw [Clif.step_tryInd _ p s hb ht] at hst'
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next hst'
    obtain ⟨⟨d, a, v⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
    rcases Clif.indCont_next h with ⟨hc1, -⟩ | ⟨-, -, n', g, rv, hg, hr⟩
    · exact absurd hc1 (hne _ _)
    · exact hans n' g v rv hg hr
  · rw [Clif.step_ind _ p s hb hi] at hst'
    obtain ⟨⟨d, a, v⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next hst'
    rcases Clif.indCont_next h with ⟨hc1, -⟩ | ⟨-, -, n', g, rv, hg, hr⟩
    · exact absurd hc1 (hne _ _)
    · exact hans n' g v rv hg hr
  · rw [Opt.step_eq_lift _ p s hci] at hst'
    cases hl : Opt.lstep s.frame s.mem with
    | next fr1 m1 => exact absurd hl (lstep_next_of_invoked hinv hci)
    | call ext v rs rest =>
      rw [hl] at hst'
      rcases Clif.callCont_cases hst' with ⟨hc1, -⟩ | ⟨-, -, n', g, rv, hg, hr⟩
      · exact absurd hc1 (hne _ _)
      · exact hans n' g v rv hg hr
    | ret v =>
      rw [hl] at hst'
      obtain ⟨c, rs, cs, regs, hc', hc1, -⟩ := Clif.returnValues_next hst'
      have := congrArg List.length (hc.symm.trans hc1)
      rw [hc'] at this
      simp at this
    | tail ext v => exact absurd hl (Clif.lstep_ne_tail hP hI.1)
    | trap c => rw [hl] at hst'; cases hst'
    | stuck msg => rw [hl] at hst'; cases hst'

/-- **The calling states of a path** (module doc). -/
theorem reachN_call_at {env : Clif.Env} {p : Clif.Program} {cs t : Clif.State} {n : Nat}
    (hr : ReachN env p cs t n) : ∀ j < n, ∃ tj tj1, ReachN env p cs tj j ∧ callNum tj = 1 ∧
      Clif.step env p tj = .next tj1 ∧ ReachN env p cs tj1 (j + 1) := by
  induction hr with
  | refl => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | @snoc s s' m hs hst ih =>
    intro j hj
    by_cases hjm : j < m
    · exact ih j hjm
    · have hcn : callNum s = 1 := by
        rcases callNum_le_one s with h0 | h1
        · rw [h0] at hj; omega
        · exact h1
      have hjm' : j = m := by omega
      subst hjm'
      refine ⟨s, s', hs, hcn, hst, ?_⟩
      have := ReachN.snoc hs hst
      rwa [hcn] at this

/-- **One machine step per call count**: two call states of a run with the same number of call
states before them are the same step. -/
theorem callIdx_unique {Mm : Arm.ArmState → Arm.ArmState} {fa : FnAsm} {base : BitVec 64}
    {s : Arm.ArmState} {i j : Nat} (hi : CallPc fa base (Arm.r .PC (runX Mm i s)))
    (hj : CallPc fa base (Arm.r .PC (runX Mm j s)))
    (h : callsBefore Mm fa base s i = callsBefore Mm fa base s j) : i = j := by
  rcases Nat.lt_trichotomy i j with hlt | rfl | hlt
  · have := callsBefore_lt hi hlt; omega
  · rfl
  · have := callsBefore_lt hj hlt; omega

end E2E

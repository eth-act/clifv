module

public import FV.E2E.LinkPlaceBCount
public import FV.E2E.LinkArmEnvOfB
public import FV.E2E.InvokedN

@[expose] public section

/-! # The slot-byte counter after `k` calls of an activation (SEM1 #537, #680 (3), stage 2 (a))

`counter_at` (`LinkPlaceBCount`) adds up advances along given memories. Here the memories are
those of the activation's run itself: a bare activation (`q.bare`, no callers) reached from `cs`
after `k` extern calls (`ReachN`) has `cs`'s oracle with the counter advanced by
`Σ_{j<k} advAt env q.bare cs j`, `advAt … j` the advance of the step of call number `j`
(unique: the calling state of count `j` is unique, `reachN_call_unique`, and so is the advance,
`NextAdv.unique`).

* `step_bare_noCall_place`: a step that makes no call (`callNum s = 0`) keeps the oracle;
* `advAt`, `advAt_eq`: the advance of call number `j`;
* **`nextAdv_reachN`**: the counter along `ReachN`;
* **`LinkSys.counter_reachN`**: an activation entered placed at `c` with `ini` is placed at `c`
  with `ini.adv (Σ_{j<k} advAt … j)` after `k` calls; `envAdv_envOfB`; `initState_linv_only`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **A step of a bare activation that makes no call keeps the oracle.** -/
theorem step_bare_noCall_place {P q : Clif.Program} (hP : ∀ g ∈ P.funcs, Clif.LinkFree g)
    {env : Clif.Env} {s s1 : Clif.State} (hI : Clif.LInv P s) (hc : s.callers = [])
    (h0 : callNum s = 0) (h : Clif.step env q.bare s = .next s1) :
    s1.mem.place = s.mem.place := by
  rcases Clif.step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · simp [callNum, hb, ht, Clif.Terminator.isTry] at h0
  · simp [callNum, hb, ht, Clif.Terminator.isTry] at h0
  · simp [callNum, hb, hi, Clif.Inst.isCallLike] at h0
  · rw [Opt.step_eq_lift env q.bare s hci] at h
    cases hl : Opt.lstep s.frame s.mem with
    | next fr1 m1 =>
      rw [hl] at h; cases h
      exact (Clif.lstep_next_place hl).1
    | call ext vals rs rest =>
      obtain ⟨st, fn, args, hb, hi, -, -⟩ := Opt.lstep_call_inv hl
      simp [callNum, hb, hi, Clif.Inst.isCallLike] at h0
    | ret vals =>
      rw [hl] at h
      obtain ⟨c, rs, cs, regs, hc', -, -⟩ := Clif.returnValues_next h
      rw [hc] at hc'; cases hc'
    | tail ext vals => exact absurd hl (Clif.lstep_ne_tail hP hI.1)
    | trap c => rw [hl] at h; cases h
    | stuck m => rw [hl] at h; cases h

theorem callNum_le_one (s : Clif.State) : callNum s = 0 ∨ callNum s = 1 := by
  unfold callNum
  split
  · split <;> simp
  · split <;> simp

open Classical in
/-- **The advance of call number `j`** of the run from `cs`: the slot-byte counter advance of the
step of the calling state reached after `j` calls. -/
noncomputable def advAt (env : Clif.Env) (p : Clif.Program) (cs : Clif.State) (j : Nat) : Nat :=
  Classical.epsilon fun e => ∃ s s1, ReachN env p cs s j ∧ callNum s = 1 ∧
    Clif.step env p s = .next s1 ∧ Clif.NextAdv s.mem s1.mem e

/-- `advAt` is the advance of the calling state's step (when its memory has an oracle). -/
theorem advAt_eq {env : Clif.Env} {p : Clif.Program} {cs s s1 : Clif.State} {j e : Nat}
    (hs : ReachN env p cs s j) (h1 : callNum s = 1) (hst : Clif.step env p s = .next s1)
    (hN : Clif.NextAdv s.mem s1.mem e) {pl : Clif.Place} {ini : Clif.SlotInit}
    (hp : s.mem.place = some pl) (hi : pl.init = some ini) : advAt env p cs j = e := by
  have hex : ∃ e, ∃ s s1, ReachN env p cs s j ∧ callNum s = 1 ∧
      Clif.step env p s = .next s1 ∧ Clif.NextAdv s.mem s1.mem e := ⟨e, s, s1, hs, h1, hst, hN⟩
  obtain ⟨t, t1, ht, ht1, htst, htN⟩ := Classical.epsilon_spec hex
  obtain rfl := reachN_call_unique ht ht1 hs h1
  rw [hst] at htst
  cases htst
  exact htN.unique hN hp hi

/-- **The counter along the run of a bare activation**: a state reached from `cs` after `k`
calls has `cs`'s oracle with the counter advanced by `Σ_{j<k} advAt … j`. -/
theorem nextAdv_reachN {P q : Clif.Program} (hP : ∀ g ∈ P.funcs, Clif.LinkFree g)
    {env : Clif.Env} (hk : Clif.EnvAdv env) {cs : Clif.State} (hI : Clif.LInv P cs)
    (hc : cs.callers = []) {pl : Clif.Place} {ini : Clif.SlotInit}
    (hp : cs.mem.place = some pl) (hin : pl.init = some ini) {s : Clif.State} {k : Nat}
    (hs : ReachN env q.bare cs s k) :
    Clif.LInv P s ∧ s.callers = [] ∧
      Clif.NextAdv cs.mem s.mem (Clif.sumTo (advAt env q.bare cs) k) := by
  induction hs with
  | refl => exact ⟨hI, hc, Clif.NextAdv.of_place rfl⟩
  | @snoc s s1 n hr hst ih =>
    obtain ⟨hIs, hcs, hN⟩ := ih
    have hI1 := (Clif.step_next_linv hP hIs hst (fun _ h => by simp at h)).1
    have hc1 := Clif.step_bare_callers hP hIs.1 hcs hst
    refine ⟨hI1, hc1, ?_⟩
    rcases callNum_le_one s with h0 | h1
    · rw [h0, Nat.add_zero]
      have := hN.trans (Clif.NextAdv.of_place (step_bare_noCall_place hP hIs hcs h0 hst))
      rwa [Nat.add_zero] at this
    · rw [h1]
      obtain ⟨e, he⟩ : ∃ e, Clif.NextAdv s.mem s1.mem e := by
        rcases Clif.step_next_cases hP hIs hst with ⟨-, -, ⟨hpl', -⟩ | ⟨n, G, vals, rv, hG, hr⟩⟩ |
          ⟨c, hc', -⟩ | ⟨c, hc', -⟩
        · exact ⟨0, Clif.NextAdv.of_place hpl'⟩
        · exact hk n G hG vals s.mem rv s1.mem hr
        · rw [hc1] at hc'; cases hc'
        · rw [hcs] at hc'; cases hc'
      have hA := advAt_eq hr h1 hst he (hN pl ini hp hin) rfl
      have := hN.trans he
      rwa [← hA] at this

namespace LinkSys

variable (L : LinkSys)

/-- **The counter of an activation after `k` calls**: `g`'s activation entered at `cs` placed at
`c` with `ini` (`WorldEntryB.place`), run bare under an environment that advances the counter
(`crun_adv`, `envAdv_envOfB`) to `s` after `k` calls: `s`'s memory is placed at `c` with
`ini.adv (Σ_{j<k} advAt … j)`. -/
theorem counter_reachN {env : Clif.Env} (hk : Clif.EnvAdv env) {g : Clif.Function}
    (hg : Clif.LinkFree g) {cs : Clif.State} (hI : Clif.LInv (L.P.only g) cs)
    (hc : cs.callers = []) {c : BitVec 64} {ini : Clif.SlotInit} (hpB : L.PlaceAtB cs.mem c ini)
    {s : Clif.State} {k : Nat} (hs : ReachN env L.P.bare cs s k) :
    L.PlaceAtB s.mem c (ini.adv (Clif.sumTo (advAt env L.P.bare cs) k)) := by
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hg
  obtain ⟨sps, hp⟩ := hpB
  exact PlaceAtB.adv ⟨sps, hp⟩ (nextAdv_reachN hPf hk hI hc hp rfl hs).2.2

/-- **`envOfB` advances the counter** when the linked environment does (its guard only adds
`stuck` answers). -/
theorem envAdv_envOfB {M : Nat} (hk : Clif.EnvAdv (Clif.linkEnvR L.P L.base (L.crun M)))
    (g : Clif.Function) (c : BitVec 64) : Clif.EnvAdv (L.envOfB M g c) := by
  intro n G hG vals m rv m' hr
  simp only [envOfB] at hG
  split at hG
  · cases hG
  · split at hG
    · cases he : (Clif.linkEnvR L.P L.base (L.crun M)).extern n with
      | none => rw [he] at hG; cases hG
      | some G0 =>
        rw [he] at hG; cases hG
        simp only at hr
        split at hr
        · exact hk n G0 he vals m rv m' hr
        · cases hr
    · exact hk n G hG vals m rv m' hr

end LinkSys

/-- An activation entered by `initState` runs `h` alone, without callers. -/
theorem initState_linv_only {P : Clif.Program} {n : String} {h : Clif.Function}
    (hpf : P.func? n = some h) {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State}
    (hi : Clif.initState P n vals cm = .ok cs) : Clif.LInv (P.only h) cs ∧ cs.callers = [] := by
  simp only [Clif.initState, hpf, Clif.Res.ofOption_some, Clif.Res.ok_bind] at hi
  cases he : Clif.enterFunc h vals cm with
  | ok r =>
    rw [he] at hi
    obtain ⟨fr, mem'⟩ := r
    simp only [Clif.Res.ok_bind, Clif.Res.pure_eq, Clif.Res.ok.injEq] at hi
    subst hi
    exact ⟨⟨Clif.LFrame.enterFunc (by simp [Clif.Program.only]) he, fun _ h => nomatch h⟩, rfl⟩
  | trap => rw [he] at hi; cases hi
  | stuck => rw [he] at hi; cases hi


end E2E

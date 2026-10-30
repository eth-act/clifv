import FV.E2E.LinkArmUEnv
import FV.E2E.LinkArmUClif

/-!
# The run with unwinding of an activation in the linked program (S10f, #233)

`LinkSys.ActInv`/`runLoop_envOf`/`trapsExplicit_envOf` (`FV/E2E/LinkArm.lean`) for the runs with
unwinding: the run of the program without functions from an activation of `g` stays in its frame
(no caller: an exception its frame does not catch ends the run) and its externs keep the
slot-placement oracle, also when they unwind (`LinkSysU.actInvX_step`); so its steps under the
activation's environment `envOfX` are those under `envRX` (`runLoopX_envOfX`), and the run
premises transfer (`trapsExplicitX_envOfX`).
-/

namespace E2E

open Backend Backend.Proof

namespace LinkSysU

variable (L : LinkSysU)

/-- **The run invariant with unwinding of an activation of `g` with stack pointer `c`**: its
frame is a frame of `g` with the pending tables aligned (`XInv (P.only g)`), it has no callers,
and the slot-placement oracle has `c` (when program callees have slots). -/
def ActInvX (g : Clif.Function) (c : BitVec 64) (xs : Clif.XState) : Prop :=
  Clif.XInv (L.P.only g) xs ∧ xs.s.callers = [] ∧ (L.NeedSlots → L.PlaceAt xs.s.mem c)

/-- The base environment with unwinding keeps the oracle (when program callees have slots). -/
theorem envX_keepsPlace (hL : L.Ok) (hU : L.OkU) (hN : L.NeedSlots) :
    Clif.XEnvKeepsPlace L.envX :=
  Clif.xEnvKeepsPlace_of (by rw [hU.envX]; exact hL.baseKeepsPlace hN) (hU.baseKeepsPlaceU hN)

/-- The base environment with unwinding creates no allocation (when program callees have slots
or a function of `P` has an outgoing-argument area). -/
theorem envX_keepsAllocs (hU : L.OkU) (hA : L.NeedSlots ∨
    ∃ g ∈ L.P.funcs, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase ≠ 0) :
    Clif.XEnvKeepsAllocs L.envX :=
  hU.baseKeepsAllocsU hA

/-- **The activation's environment keeps the oracle** without the slot-byte oracle (the linked
environment's externs: the base's, and the callee runs, whole-program runs with unwinding). -/
theorem envRX_keepsPlace0 (hL : L.Ok) (hU : L.OkU) [hR : L.CrunOkX] (hN : L.NeedSlots) (M : Nat)
    (g : Clif.Function) : Clif.XEnvKeepsPlace0 (L.envRX M g) := by
  have hk := Clif.linkEnvRX_keepsPlace0 (P := L.P) (env := L.envX) (R := L.crunX M)
    (fun s o h hc => hR.runs M s o h (by
      rcases hc with ⟨v, m, rfl⟩ | ⟨e, m, rfl⟩
      · exact .inl ⟨v, m, rfl⟩
      · exact .inr (.inr ⟨e, m, rfl⟩)))
    hL.free (L.envX_keepsPlace hL hU hN)
  intro n G hG
  rcases L.envRX_restricts (M := M) (g := g) n with h | h
  · rw [h] at hG; cases hG
  · rw [h] at hG; exact hk n G hG

/-- **The activation's environment keeps the oracle** (slot-byte oracle included) when the
program's functions have no stack slots (otherwise a callee with slots advances `init`). -/
theorem envRX_keepsPlace (hL : L.Ok) (hU : L.OkU) [hR : L.CrunOkX] (hN : L.NeedSlots) (M : Nat)
    (hS : ∀ f ∈ L.P.funcs, f.slots = [])
    (g : Clif.Function) : Clif.XEnvKeepsPlace (L.envRX M g) := by
  have hk := Clif.linkEnvRX_keepsPlace (P := L.P) (env := L.envX) (R := L.crunX M)
    (fun s o h hc => hR.runs M s o h (by
      rcases hc with ⟨v, m, rfl⟩ | ⟨e, m, rfl⟩
      · exact .inl ⟨v, m, rfl⟩
      · exact .inr (.inr ⟨e, m, rfl⟩)))
    hL.free hS (L.envX_keepsPlace hL hU hN)
  intro n G hG
  rcases L.envRX_restricts (M := M) (g := g) n with h | h
  · rw [h] at hG; cases hG
  · rw [h] at hG; exact hk n G hG

theorem only_linkFree (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs) :
    ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
  simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf; exact hL.free f hg

/-- **The run with unwinding of `P.bare` under `envRX` keeps `ActInvX`**: it stays in its frame
(an exception its frame does not catch ends the run) and its externs keep the oracle. -/
theorem actInvX_step (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] {M : Nat} {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {c : BitVec 64} {xs xs' : Clif.XState} (hJ : L.ActInvX g c xs)
    (hs : Clif.stepX (L.envRX M g) L.P.bare xs = .next xs') : L.ActInvX g c xs' := by
  obtain ⟨hI, hc, hpl⟩ := hJ
  have hPf := L.only_linkFree hL hg
  refine ⟨Clif.stepX_next_xinv hPf hI hs (fun _ h => by simp at h), ?_⟩
  unfold Clif.stepX at hs
  split at hs
  · rename_i e mem hr
    rcases Clif.raiseIn_cases hs with ⟨fr', rfl, -⟩ | h
    · refine ⟨hc, fun hN => ?_⟩
      obtain ⟨sps, hp⟩ := hpl hN
      obtain ⟨n, G, vals, hG, hu⟩ := Clif.raiseAt_extern hr
      refine ⟨sps, ?_⟩
      show mem.place = _
      rw [(L.envRX_keepsPlace0 hL hU hN M g n G hG vals xs.s.mem
        (fun pl h => by rw [hp] at h; cases h; rfl)).2 e mem hu, hp]
    · rw [hc] at h; simp [Clif.unwindFrom] at h
  · cases hst : Clif.step (L.envRX M g).toEnv L.P.bare xs.s with
    | next s1 =>
      rw [hst] at hs
      simp only [Clif.liftStep, Clif.XStepResult.next.injEq] at hs
      subst hs
      have hc1 := Clif.step_bare_callers hPf hI.1.1 hc hst
      refine ⟨hc1, fun hN => ?_⟩
      obtain ⟨sps, hp⟩ := hpl hN
      refine ⟨sps, ?_⟩
      rcases Clif.step_next_cases hPf hI.1 hst with ⟨-, -, ⟨hpl', -⟩ | ⟨n, G, vals, rv, hG, hr⟩⟩ |
        ⟨cc, hcc, -⟩ | ⟨cc, hcc, -⟩
      · show s1.mem.place = _
        rw [hpl', hp]
      · show s1.mem.place = _
        rw [(L.envRX_keepsPlace0 hL hU hN M g).toEnv n G hG vals xs.s.mem rv s1.mem
          (fun pl h => by rw [hp] at h; cases h; rfl) hr, hp]
      · rw [hc1] at hcc; cases hcc
      · rw [hc] at hcc; cases hcc
    | _ => rw [hst] at hs; simp [Clif.liftStep] at hs

/-- **The run with unwinding of an activation under `envOfX` is its run under `envRX`.** -/
theorem runLoopX_envOfX (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] {M : Nat} {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {c : BitVec 64} :
    ∀ (n : Nat) (xs : Clif.XState), L.ActInvX g c xs →
      Clif.runLoopX (L.envOfX M g c) L.P.bare n xs = Clif.runLoopX (L.envRX M g) L.P.bare n xs
  | 0, _, _ => rfl
  | n + 1, xs, hJ => by
    rw [Clif.runLoopX_succ', Clif.runLoopX_succ',
      L.stepX_envOfX (hL.free g hg) hJ.1.1.1 hJ.2.2]
    cases hs : Clif.stepX (L.envRX M g) L.P.bare xs with
    | next xs' =>
      exact runLoopX_envOfX hL hU hg n xs' (L.actInvX_step hL hU hg hJ hs)
    | _ => rfl

theorem reachX_envOfX (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] {M : Nat} {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {c : BitVec 64} {xs0 xs : Clif.XState}
    (hr : ReachX (L.envOfX M g c) L.P.bare xs0 xs) (hJ : L.ActInvX g c xs0) :
    ReachX (L.envRX M g) L.P.bare xs0 xs ∧ L.ActInvX g c xs := by
  induction hr with
  | refl => exact ⟨.refl _, hJ⟩
  | step hs _ ih =>
    rw [L.stepX_envOfX (hL.free g hg) hJ.1.1.1 hJ.2.2] at hs
    obtain ⟨h1, h2⟩ := ih (L.actInvX_step hL hU hg hJ hs)
    exact ⟨.step hs h1, h2⟩

/-- A step of an activation under `envOfX` is its step under `envRX`. -/
theorem step_envOfX {M : Nat} {g : Clif.Function} {c : BitVec 64} {s : Clif.State}
    (hP : Clif.LinkFree g) (hI : Clif.LFrame (L.P.only g) s.frame)
    (hpl : L.NeedSlots → L.PlaceAt s.mem c) :
    Clif.step (L.envOfX M g c).toEnv L.P.bare s = Clif.step (L.envRX M g).toEnv L.P.bare s :=
  step_agree hP hI rfl rfl (XAgreeAt.toEnv fun _ vals => L.envOfX_envRX vals hpl)

/-- **The run premises with unwinding of `P.bare` under `envRX` are those under `envOfX`.** -/
theorem trapsExplicitX_envOfX (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] {M : Nat}
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {c : BitVec 64} {cs : Clif.State}
    (hJ : L.ActInvX g c cs.toX) (h : TrapsExplicitX (L.envRX M g) L.P.bare cs) :
    TrapsExplicitX (L.envOfX M g c) L.P.bare cs where
  stmt := fun xs c' st rest hr hs hb => by
    obtain ⟨hr', hJs⟩ := L.reachX_envOfX hL hU hg hr hJ
    rw [L.step_envOfX (hL.free g hg) hJs.1.1.1 hJs.2.2] at hs
    exact h.stmt xs c' st rest hr' hs hb
  tryCall := fun xs c' fn args et hr hs hb ht => by
    obtain ⟨hr', hJs⟩ := L.reachX_envOfX hL hU hg hr hJ
    rw [L.step_envOfX (hL.free g hg) hJs.1.1.1 hJs.2.2] at hs
    exact h.tryCall xs c' fn args et hr' hs hb ht
  tryCallInd := fun xs c' callee args et hr hs hb ht => by
    obtain ⟨hr', hJs⟩ := L.reachX_envOfX hL hU hg hr hJ
    rw [L.step_envOfX (hL.free g hg) hJs.1.1.1 hJs.2.2] at hs
    exact h.tryCallInd xs c' callee args et hr' hs hb ht
  indirect := fun _ _ _ _ _ _ _ _ _ _ _ _ g' hg' => by simp at hg'
  tryIndirect := fun _ _ _ _ _ _ _ _ _ _ g' hg' => by simp at hg'

end LinkSysU

end E2E

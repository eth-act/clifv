import FV.E2E.LinkPlaceBReach
import FV.E2E.LinkArmThmPRBROf
import FV.E2E.LinkArmStage2Zero

/-!
# The counter advance of a returning activation, and `CountPRB κ 0` (SEM1 #537, #680 (3))

* `reachN_cons`, `reaches_reachN`: a run (`Reaches`) is a counted run (`ReachN`);
* `step_done_mem_q`: `step_done_mem` for a run of another program (`P.bare`) with the invariant
  of `P`;
* **`returned_nextAdv_leave`**: a returning run of a bare activation advances the popped entry's
  counter by `Σ_{j<k} advAt … j`, `k` the calls of the run (`nextAdv_reachN` up to the last
  state; the return frees the slots and pops the stack pointer);
* `place_reachN_keeps`, `returned_keeps_leave`: under an environment keeping the oracle the
  activation keeps it, and gives back the popped entry's;
* `envR_zero_keeps`: at depth `0` the activation's environment keeps the oracle under
  `NeedSlots` (base externs: `Ok.baseKeepsPlace`; program callees never return,
  `CrunOk.zero`);
* **`countPRB_zero`**: `CountPRB κ 0` (the machine's count at depth `0` is `0`, `TabUpTo`);
* **`thmPRBRL_zero`**: `ThmPRBRL κ 0` from `RetOkPRB κ 0` alone.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

theorem reachN_cons {env : Clif.Env} {p : Clif.Program} {s s' a : Clif.State} {k : Nat}
    (h : ReachN env p s' a k) (hs : Clif.step env p s = .next s') :
    ReachN env p s a (callNum s + k) := by
  induction h with
  | refl => simpa using ReachN.snoc (ReachN.refl (env := env) (p := p) (cs := s)) hs
  | @snoc t a m _ hst ih =>
    have := ReachN.snoc ih hst
    rwa [Nat.add_assoc] at this

theorem reaches_reachN {env : Clif.Env} {p : Clif.Program} {s u : Clif.State}
    (h : Clif.Reaches env p s u) : ∃ k, ReachN env p s u k := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | next hs _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨_, reachN_cons hk hs⟩

/-- `step_done_mem` for a run of the program `q` from a state with `P`'s invariant. -/
theorem step_done_mem_q {P q : Clif.Program} (hP : ∀ g ∈ P.funcs, Clif.LinkFree g)
    {env : Clif.Env} {s : Clif.State} {v : List Clif.Val} {m : Clif.Mem} (hI : Clif.LInv P s)
    (h : Clif.step env q s = .done v m) :
    m = (s.mem.free (s.frame.slots.map (·.2))).leave := by
  rcases Clif.step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · rw [Clif.step_try env q s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := Clif.ofRes_eq_done h
    obtain ⟨⟨ext, vals⟩, -, h⟩ := Clif.ofRes_eq_done h
    exact absurd h Clif.callCont_ne_done
  · rw [Clif.step_tryInd env q s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := Clif.ofRes_eq_done h
    obtain ⟨⟨d, a, w⟩, -, h⟩ := Clif.ofRes_eq_done h
    exact absurd h Clif.indCont_ne_done
  · rw [Clif.step_ind env q s hb hi] at h
    obtain ⟨⟨d, a, w⟩, -, h⟩ := Clif.ofRes_eq_done h
    exact absurd h Clif.indCont_ne_done
  · rw [Opt.step_eq_lift env q s hci] at h
    cases hl : Opt.lstep s.frame s.mem with
    | ret vals => rw [hl] at h; exact Clif.returnValues_mem.2 v m h
    | call ext vals rs rest => rw [hl] at h; exact absurd h Clif.callCont_ne_done
    | tail ext vals => exact absurd hl (Clif.lstep_ne_tail hP hI.1)
    | next fr1 m1 => rw [hl] at h; cases h
    | trap c => rw [hl] at h; cases h
    | stuck m => rw [hl] at h; cases h

/-- **A returning bare activation advances the popped entry's counter** by the advances of its
`k` calls. -/
theorem returned_nextAdv_leave {P q : Clif.Program} (hP : ∀ g ∈ P.funcs, Clif.LinkFree g)
    {env : Clif.Env} (hk : Clif.EnvAdv env) {cs : Clif.State} (hI : Clif.LInv P cs)
    (hc : cs.callers = []) {pl : Clif.Place} {ini : Clif.SlotInit}
    (hp : cs.mem.place = some pl) (hin : pl.init = some ini) {N : Nat} {v : List Clif.Val}
    {m : Clif.Mem} (hrun : Clif.runLoop env q.bare N cs = .returned v m) :
    ∃ k, (∃ u, ReachN env q.bare cs u k ∧ Clif.step env q.bare u = .done v m) ∧
      Clif.NextAdv cs.mem.leave m (Clif.sumTo (advAt env q.bare cs) k) := by
  obtain ⟨u, hu, hd⟩ := Clif.runLoop_returned_reaches env q.bare N cs v m hrun
  obtain ⟨k, hk'⟩ := reaches_reachN hu
  obtain ⟨hIu, -, hN⟩ := nextAdv_reachN hP hk hI hc hp hin hk'
  refine ⟨k, ⟨u, hk', hd⟩, ?_⟩
  rw [step_done_mem_q hP hIu hd]
  intro pl' ini' hp' hi'
  have hu := hN pl ini hp hin
  simp only [Clif.Mem.leave, hp, Option.some.injEq] at hp'
  subst hp'
  simp only at hi'
  rw [hin, Option.some.injEq] at hi'
  subst hi'
  simp only [Clif.Mem.leave, Clif.Mem.free, hu]

/-- **Under an environment keeping the oracle a bare activation keeps it.** -/
theorem place_reachN_keeps {P q : Clif.Program} (hP : ∀ g ∈ P.funcs, Clif.LinkFree g)
    {env : Clif.Env} (hk : Clif.EnvKeepsPlace env) {cs : Clif.State} (hI : Clif.LInv P cs)
    (hc : cs.callers = []) {s : Clif.State} {k : Nat} (hs : ReachN env q.bare cs s k) :
    Clif.LInv P s ∧ s.callers = [] ∧ s.mem.place = cs.mem.place := by
  induction hs with
  | refl => exact ⟨hI, hc, rfl⟩
  | @snoc s s1 n hr hst ih =>
    obtain ⟨hIs, hcs, hN⟩ := ih
    have hI1 := (Clif.step_next_linv hP hIs hst (fun _ h => by simp at h)).1
    have hc1 := Clif.step_bare_callers hP hIs.1 hcs hst
    refine ⟨hI1, hc1, ?_⟩
    rw [← hN]
    rcases callNum_le_one s with h0 | h1
    · exact step_bare_noCall_place hP hIs hcs h0 hst
    · rcases Clif.step_next_cases hP hIs hst with ⟨-, -, ⟨hpl', -⟩ | ⟨n, G, vals, rv, hG, hr⟩⟩ |
          ⟨c, hc', -⟩ | ⟨c, hc', -⟩
      · exact hpl'
      · exact hk n G hG vals s.mem rv s1.mem hr
      · rw [hc1] at hc'; cases hc'
      · rw [hcs] at hc'; cases hc'

/-- **A returning bare activation under an environment keeping the oracle gives back the popped
entry's oracle.** -/
theorem returned_keeps_leave {P q : Clif.Program} (hP : ∀ g ∈ P.funcs, Clif.LinkFree g)
    {env : Clif.Env} (hk : Clif.EnvKeepsPlace env) {cs : Clif.State} (hI : Clif.LInv P cs)
    (hc : cs.callers = []) {N : Nat} {v : List Clif.Val} {m : Clif.Mem}
    (hrun : Clif.runLoop env q.bare N cs = .returned v m) : Clif.NextAdv cs.mem.leave m 0 := by
  obtain ⟨u, hu, hd⟩ := Clif.runLoop_returned_reaches env q.bare N cs v m hrun
  obtain ⟨k, hk'⟩ := reaches_reachN hu
  obtain ⟨hIu, -, hN⟩ := place_reachN_keeps hP hk hI hc hk'
  refine Clif.NextAdv.of_place ?_
  rw [step_done_mem_q hP hIu hd]
  simp only [Clif.Mem.leave, Clif.Mem.free, hN]
  cases hp : cs.mem.place <;> simp [hp]

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **At depth `0` the activation's environment keeps the oracle** (with program callees with
slots: the base externs keep it, `Ok.baseKeepsPlace`; program callees never return). -/
theorem envR_zero_keeps (hL : L.Ok) [hR : L.CrunOk] (hN : L.NeedSlots) (g : Clif.Function) :
    Clif.EnvKeepsPlace (L.envR 0 g) := by
  intro n G hG vals m rvals m' hr
  simp only [envR] at hG
  split at hG
  · cases hG
  · cases hpf : L.P.func? n with
    | none =>
      rw [Clif.linkEnvR_none hpf] at hG
      exact hL.baseKeepsPlace hN n G hG vals m rvals m' hr
    | some h =>
      rw [Clif.linkEnvR_some hpf] at hG
      cases hG
      exfalso
      simp only at hr
      split at hr
      · exact hR.zero _ _ _ hr
      · cases hr
      · cases hr

/-- **`CountPRB κ 0`**: at depth `0` the machine enters no placed activation (`TabUpTo 0`: count
`0`) and the CLIF run keeps the oracle. -/
theorem countPRB_zero (hL : L.Ok) [L.CrunOk] : L.CountPRB κ 0 := by
  intro g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE _ _ _ hrun _ _ _ n e _ _ hte hN
  obtain ⟨rfl, -⟩ := hte
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hL.free f hg
  exact returned_keeps_leave hPf (L.envR_zero_keeps hL hN g) hI hWE.clif.callers hrun

/-- **`ThmPRBRL κ 0` up to `RetOkPRB κ 0`** (`thmPRBRL_of` with `stage2PRB_zero`,
`countPRB_zero`; no induction hypothesis at depth `0`). -/
theorem thmPRBRL_zero (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) (hret : L.RetOkPRB κ 0) :
    L.ThmPRBRL κ 0 :=
  L.thmPRBRL_of hL hκ (fun h => absurd h (Nat.lt_irrefl 0)) (fun h => absurd h (Nat.lt_irrefl 0))
    hret (L.stage2PRB_zero hL) (L.countPRB_zero hL)

end LinkSys

end E2E

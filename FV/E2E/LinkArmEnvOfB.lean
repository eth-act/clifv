module

public import FV.E2E.LinkArmPlaceB

@[expose] public section

/-!
# The activation's environment under the slot-byte oracle (SEM1 #537, #680 (3), `thmPRB_of`)

`envOf` (`LinkArm`) guards the program callees of an activation by `PlaceAt` (oracle `none`); the
induction step of `ThmPRB` runs the activation from a memory placed with an oracle
(`WorldEntryB.place`). `envOfB`: the guard `PlacedB cm c` (placed at `c` with *some* oracle; the
counter advances along the run). `ActInvB`: `ActInv` with `PlacedB`; `actInvB_step`: the run of
`P.bare` under `linkEnvR` keeps it (its externs advance the counter, `crun_adv`);
`step_envOfB`, **`runLoop_envOfB`**: under `ActInvB` the run under `envOfB` is the run under
`envR`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)

/-- The memory is placed at `c` with some slot-byte oracle. -/
def PlacedB (cm : Clif.Mem) (c : BitVec 64) : Prop := ∃ ini, L.PlaceAtB cm c ini

open Classical in
/-- **The CLIF environment of an activation of `g` at depth `M` under the slot-byte oracle**:
`envOf` with `PlacedB` for `PlaceAt`. -/
noncomputable def envOfB (M : Nat) (g : Clif.Function) (c : BitVec 64) : Clif.Env where
  extern n := if (L.P.func? n).isSome ∧ ¬ L.MayCall g n then none
    else if (L.P.func? n).isSome then ((Clif.linkEnvR L.P L.base (L.crun M)).extern n).map
      fun G vals cm => if L.NeedSlots → L.PlacedB cm c then G vals cm else .stuck "slot placement"
    else (Clif.linkEnvR L.P L.base (L.crun M)).extern n
  names := (Clif.linkEnvR L.P L.base (L.crun M)).names
  sigOf := (Clif.linkEnvR L.P L.base (L.crun M)).sigOf

theorem envOfB_envR {M : Nat} {g : Clif.Function} {c : BitVec 64} {n : String}
    (vals : List Clif.Val) {cm : Clif.Mem} (hpl : L.NeedSlots → L.PlacedB cm c) :
    ((L.envOfB M g c).extern n).map (· vals cm) = ((L.envR M g).extern n).map (· vals cm) := by
  simp only [envOfB, envR]
  split
  · rfl
  · split
    · cases (Clif.linkEnvR L.P L.base (L.crun M)).extern n with
      | none => rfl
      | some G0 => simp only [Option.map_some, if_pos hpl]
    · rfl

/-- **The activation invariant under the slot-byte oracle.** -/
def ActInvB (g : Clif.Function) (c : BitVec 64) (s : Clif.State) : Prop :=
  Clif.LInv (L.P.only g) s ∧ s.callers = [] ∧ (L.NeedSlots → L.PlacedB s.mem c)

/-- **The run of `P.bare` under `linkEnvR` keeps `ActInvB`**: it stays in its frame and its
externs advance the counter. -/
theorem actInvB_step (hL : L.Ok) [hR : L.CrunOk] {M : Nat} {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {c : BitVec 64} {s s1 : Clif.State} (hJ : L.ActInvB g c s)
    (hs : Clif.step (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare s = .next s1) :
    L.ActInvB g c s1 := by
  obtain ⟨hI, hc, hpl⟩ := hJ
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hL.free f hg
  have hc1 := Clif.step_bare_callers hPf hI.1 hc hs
  refine ⟨(Clif.step_next_linv hPf hI hs (fun _ h => by simp at h)).1, hc1, fun hN => ?_⟩
  obtain ⟨ini, hp⟩ := hpl hN
  rcases Clif.step_next_cases hPf hI hs with ⟨-, -, ⟨hpl', -⟩ | ⟨n, G, vals, rv, hG, hr⟩⟩ |
    ⟨cc, hcc, -⟩ | ⟨cc, hcc, -⟩
  · obtain ⟨sps, hp⟩ := hp
    exact ⟨ini, sps, by rw [hpl', hp]⟩
  · obtain ⟨e, he⟩ := L.crun_adv hL hN M n G hG vals s.mem rv s1.mem hr
    exact ⟨ini.adv e, hp.adv he⟩
  · rw [hc1] at hcc; cases hcc
  · rw [hc] at hcc; cases hcc

/-- Under `PlacedB` the steps under `envOfB` and `envR` are the same. -/
theorem step_envOfB {M : Nat} {g : Clif.Function} {c : BitVec 64} {s : Clif.State}
    (hP : Clif.LinkFree g) (hI : Clif.LFrame (L.P.only g) s.frame)
    (hpl : L.NeedSlots → L.PlacedB s.mem c) :
    Clif.step (L.envOfB M g c) L.P.bare s = Clif.step (L.envR M g) L.P.bare s := by
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hP
  have hx : ∀ (t : Clif.State) n vals, t.mem = s.mem →
      ((L.envOfB M g c).extern n).map (· vals t.mem) = ((L.envR M g).extern n).map (· vals t.mem) :=
    fun t n vals htm => L.envOfB_envR vals (by rw [htm]; exact hpl)
  have hcall : ∀ (t : Clif.State) ext vals rest rs, t.mem = s.mem →
      Opt.callCont (L.envOfB M g c) L.P.bare t rest rs ext vals =
        Opt.callCont (L.envR M g) L.P.bare t rest rs ext vals :=
    fun t ext vals rest rs htm => callCont_envEq fun _ => hx t ext.name vals htm
  have hind : ∀ (t : Clif.State) rest rs sig d a v, t.mem = s.mem →
      Clif.indCont (L.envOfB M g c) L.P.bare t rest rs sig d a v =
        Clif.indCont (L.envR M g) L.P.bare t rest rs sig d a v :=
    fun t rest rs sig d a v htm => indCont_envEq rfl rfl fun _ n _ _ => hx t n v htm
  rcases Clif.step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · rw [Clif.step_try _ _ s hb ht, Clif.step_try _ _ s hb ht]
    exact ofRes_congr fun ⟨n, b, bc⟩ _ => ofRes_congr fun ⟨ext, vals⟩ _ =>
      hcall _ ext vals _ _ rfl
  · rw [Clif.step_tryInd _ _ s hb ht, Clif.step_tryInd _ _ s hb ht]
    exact ofRes_congr fun ⟨n, b, bc⟩ _ => ofRes_congr fun ⟨d, a, v⟩ _ => hind _ _ _ _ d a v rfl
  · rw [Clif.step_ind _ _ s hb hi, Clif.step_ind _ _ s hb hi]
    exact ofRes_congr fun ⟨d, a, v⟩ _ => hind _ _ _ _ d a v rfl
  · rw [Opt.step_eq_lift _ _ s hci, Opt.step_eq_lift _ _ s hci]
    cases hl : Opt.lstep s.frame s.mem with
    | call ext vals rs rest => exact hcall s ext vals rest rs rfl
    | tail ext vals => exact absurd hl (Clif.lstep_ne_tail hPf hI)
    | _ => rfl

/-- A step under `envOfB` that is not stuck is its step under `linkEnvR`. -/
theorem step_envOfB_link (hL : L.Ok) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} {s : Clif.State} (hJ : L.ActInvB g c s) {r : Clif.StepResult}
    (hs : Clif.step (L.envOfB M g c) L.P.bare s = r) (hr : ∀ m, r ≠ .stuck m) :
    Clif.step (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare s = r := by
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hL.free f hg
  rw [L.step_envOfB (hL.free g hg) hJ.1.1 hJ.2.2] at hs
  exact step_of_restrict L.envR_restricts hPf hJ.1.1 hs hr

/-- **Under `ActInvB` the run under `envOfB` is the run under `envR`.** -/
theorem runLoop_envOfB (hL : L.Ok) [L.CrunOk] {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} :
    ∀ (n : Nat) (s : Clif.State), L.ActInvB g c s →
      Clif.runLoop (L.envOfB M g c) L.P.bare n s = Clif.runLoop (L.envR M g) L.P.bare n s
  | 0, _, _ => rfl
  | n + 1, s, hJ => by
    rw [Clif.runLoop_succ', Clif.runLoop_succ', L.step_envOfB (hL.free g hg) hJ.1.1 hJ.2.2]
    cases hs : Clif.step (L.envR M g) L.P.bare s with
    | next s1 =>
      have hs' := L.step_envOfB_link hL hg hJ
        ((L.step_envOfB (hL.free g hg) hJ.1.1 hJ.2.2).trans hs) (fun _ h => nomatch h)
      exact runLoop_envOfB hL hg n s1 (L.actInvB_step hL hg hJ hs')
    | _ => rfl

end LinkSys

end E2E

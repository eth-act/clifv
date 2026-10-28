import FV.E2E.LinkPlace

/-! # The slot-byte oracle on whole-program runs (SEM1, `docs/plans/uninit.md` §5.5)

`LinkPlace.lean` tracks the slot-placement oracle with the slot-byte oracle off
(`Place.init = none`: `PlaceInv`, `runLoop_place`, `EnvKeepsPlace0`). With the oracle on
(`init = some ini`), every activation with slots that the oracle places advances `ini.next` by
one (`Clif.initSlots`), and the byte table `ini.bytes` never changes. So a returning run gives
back the oracle with its counter advanced by some `e`, the number of placed activations with
slots it entered, nested callees included (`NextAdv`). This is the CLIF side of the count
correspondence: a caller's local call `k` advances the global counter by the callee run's `e`.

* `SlotInit.adv`, `NextAdv m m' e`: `m'`'s oracle is `m`'s with the counter advanced by `e`;
* `EnvAdv env`: every returning extern advances the counter by some `e`
  (`envAdv_of_keepsPlace`: `e = 0` for externs that keep the oracle);
* `enterSlots_adv`: entering a function advances it by `0` or `1`;
* `PlaceInvB`, `placeInvB_step`, `runLoop_placeB`, `initState_placeB`: the invariant along a run;
* `linkEnvR_adv`/`linkEnvN_adv`: the linked environment advances it (program callees by their
  runs' counts) when the base externs do.

Existing statements (`PlaceInv`, `EnvKeepsPlace0`, …, all at `init = none`) are unchanged. -/

namespace Clif
open Opt

/-- The slot-byte oracle after `e` more placed activations with slots. -/
def SlotInit.adv (ini : SlotInit) (e : Nat) : SlotInit := { ini with next := ini.next + e }

@[simp] theorem SlotInit.adv_zero (ini : SlotInit) : ini.adv 0 = ini := rfl

theorem SlotInit.adv_adv (ini : SlotInit) (e e' : Nat) : (ini.adv e).adv e' = ini.adv (e + e') := by
  simp only [SlotInit.adv, Nat.add_assoc]

theorem SlotInit.succ_eq_adv (ini : SlotInit) : ini.succ = ini.adv 1 := rfl

/-- **The memory `m'` has `m`'s slot-placement oracle with the slot-byte counter advanced by
`e`** (stack pointers, frames and byte table kept), when `m` has a slot-byte oracle. -/
def NextAdv (m m' : Mem) (e : Nat) : Prop :=
  ∀ pl ini, m.place = some pl → pl.init = some ini →
    m'.place = some { pl with init := some (ini.adv e) }

theorem NextAdv.trans {m m' m'' : Mem} {e e' : Nat} (h : NextAdv m m' e) (h' : NextAdv m' m'' e') :
    NextAdv m m'' (e + e') := by
  intro pl ini hp hi
  rw [h' _ (ini.adv e) (h pl ini hp hi) rfl, SlotInit.adv_adv]

theorem NextAdv.of_place {m m' : Mem} (h : m'.place = m.place) : NextAdv m m' 0 := by
  intro pl ini hp hi
  rw [h, hp]
  obtain ⟨sps, fr, i⟩ := pl
  cases hi
  rfl

/-- **The externs advance the slot-byte counter**: every returning extern call does, by some
count. -/
def EnvAdv (env : Env) : Prop :=
  ∀ n g, env.extern n = some g → ∀ vals m rvals m', g vals m = .returned rvals m' →
    ∃ e, NextAdv m m' e

/-- Externs that keep the oracle advance the counter by `0`. -/
theorem envAdv_of_keepsPlace {env : Env} (hk : EnvKeepsPlace env) : EnvAdv env :=
  fun n g hg vals m rvals m' hr => ⟨0, NextAdv.of_place (hk n g hg vals m rvals m' hr)⟩

/-- **Entering a function under the slot-byte oracle** pushes a stack pointer and advances the
counter by `0` or `1` (`1` exactly for a placed activation with slots). -/
theorem enterSlots_adv (f : Function) (mem : Mem) {pl : Place} {ini : SlotInit}
    (h : mem.place = some pl) (hi : pl.init = some ini) :
    ∃ sp e, (enterSlots f mem).2.place =
      some { pl with sps := sp :: pl.sps, init := some (ini.adv e) } ∧ e ≤ 1 := by
  cases hf : pl.frame f.name with
  | none =>
    simp only [enterSlots, h, hf]
    refine ⟨pl.sps.headD 0, 0, ?_, by omega⟩
    refine (bumpSlots_facts f.slots _).1.trans ?_
    obtain ⟨sps, frm, i⟩ := pl
    cases hi
    rfl
  | some p =>
    obtain ⟨d, off⟩ := p
    have e : ∀ m0 : Mem,
        (placeSlots f.slots (pl.sps.headD 0 - BitVec.ofNat 64 d) off m0).2.place = m0.place :=
      fun m0 => (placeSlots_facts _ _ f.slots ([], m0)).1
    simp only [enterSlots, h, hf, initSlots_place, e]
    obtain ⟨sps, frm, i⟩ := pl
    cases hi
    by_cases hs : f.slots.isEmpty
    · refine ⟨sps.headD 0 - BitVec.ofNat 64 d, 0, ?_, by omega⟩
      simp only [initPlace, hs, ↓reduceIte]
      rfl
    · refine ⟨sps.headD 0 - BitVec.ofNat 64 d, 1, ?_, Nat.le_refl _⟩
      simp only [initPlace, hs, Option.map_some, Place.advance]
      rfl

/-- The oracle of a state of a run from an activation entered with stack pointers `sps` and
slot-byte oracle `ini`: one stack pointer per frame on top of them, the counter advanced. -/
def PlaceInvB (sps : List (BitVec 64)) (fr : String → Option (Nat × (SlotId → Nat)))
    (ini : SlotInit) (s : State) : Prop :=
  ∃ l e, s.mem.place = some ⟨l ++ sps, fr, some (ini.adv e)⟩ ∧ l.length = s.callers.length + 1

theorem placeInvB_step {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (hk : EnvAdv env) {sps : List (BitVec 64)} {fr : String → Option (Nat × (SlotId → Nat))}
    {ini : SlotInit} {s : State} (hI : LInv P s) (hp : PlaceInvB sps fr ini s) :
    (∀ s1, step env P s = .next s1 → PlaceInvB sps fr ini s1) ∧
    (∀ v m, step env P s = .done v m → ∃ e, m.place = some ⟨sps, fr, some (ini.adv e)⟩) := by
  obtain ⟨l, e, hl, hlen⟩ := hp
  refine ⟨fun s1 h => ?_, fun v m h => ?_⟩
  · rcases step_next_cases hP hI h with ⟨hc, -, ⟨hpl, -⟩ | ⟨n, g, vals, rv, hg, hr⟩⟩ |
      ⟨c, hc, -, g, vals, he⟩ | ⟨c, hc, -, hm⟩
    · exact ⟨l, e, by rw [hpl, hl], by rw [hc, hlen]⟩
    · obtain ⟨e', he'⟩ := hk n g hg vals s.mem rv s1.mem hr
      refine ⟨l, e + e', ?_, by rw [hc, hlen]⟩
      rw [he' _ _ hl rfl, SlotInit.adv_adv]
    · obtain ⟨_, _, _, _, _, _, hal, -⟩ := Opt.enterFunc_ok he
      obtain ⟨sp, e', hsp, -⟩ := enterSlots_adv g s.mem hl rfl
      rw [hal] at hsp
      refine ⟨sp :: l, e + e', ?_, by rw [hc]; simp [hlen]⟩
      rw [hsp, SlotInit.adv_adv]
      rfl
    · rw [hc] at hlen
      cases l with
      | nil => simp at hlen
      | cons y l' =>
        refine ⟨l', e, ?_, by simpa using hlen⟩
        rw [hm]
        simp only [Mem.leave, Mem.free, hl]
        rfl
  · obtain ⟨hc, hm⟩ := step_done_mem hP hI h
    rw [hc] at hlen
    cases l with
    | nil => simp at hlen
    | cons y l' =>
      cases l' with
      | cons => simp at hlen
      | nil =>
        refine ⟨e, ?_⟩
        rw [hm]
        simp only [Mem.leave, Mem.free, hl]
        rfl

/-- **A returning run gives back the oracle with the counter advanced.** -/
theorem runLoop_placeB {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (hk : EnvAdv env) {sps : List (BitVec 64)} {fr : String → Option (Nat × (SlotId → Nat))}
    {ini : SlotInit} :
    ∀ (N : Nat) (s : State) (vals : List Val) (mem : Mem), LInv P s → PlaceInvB sps fr ini s →
      runLoop env P N s = .returned vals mem → ∃ e, mem.place = some ⟨sps, fr, some (ini.adv e)⟩
  | 0, _, _, _, _, _, h => by simp at h
  | N + 1, s, vals, mem, hI, hp, h => by
    rw [runLoop_succ'] at h
    have hs := placeInvB_step hP hk hI hp
    cases hst : step env P s with
    | next s1 =>
      rw [hst] at h
      exact runLoop_placeB hP hk N s1 vals mem (step_next_linv hP hI hst).1 (hs.1 s1 hst) h
    | done v m =>
      rw [hst] at h
      simp only [afterStep, Outcome.returned.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hs.2 v m hst
    | trapped c => rw [hst] at h; cases h
    | stuck m => rw [hst] at h; cases h

/-- The entry state of an activation under the slot-byte oracle. -/
theorem initState_placeB {P : Program} {n : String} {vals : List Val} {cm : Mem} {cs : State}
    (hi : initState P n vals cm = .ok cs) {pl : Place} {ini : SlotInit} (hp : cm.place = some pl)
    (hi0 : pl.init = some ini) : PlaceInvB pl.sps pl.frame ini cs := by
  simp only [initState, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.pure_eq_ok] at hi
  obtain ⟨g, -, ⟨fr, mem'⟩, he, rfl⟩ := hi
  obtain ⟨_, _, _, _, _, _, hal, -⟩ := Opt.enterFunc_ok he
  obtain ⟨sp, e, hsp, -⟩ := enterSlots_adv g cm hp hi0
  rw [hal] at hsp
  obtain ⟨sps, frm, i⟩ := pl
  exact ⟨[sp], e, hsp, rfl⟩

/-- **The linked environment advances the slot-byte counter** (a program callee by its run's
count of placed activations with slots) when the base externs do. -/
theorem linkEnvR_adv {P : Program} {base : Env} {R : State → Outcome}
    (hR : RunsOf base P R) (hP : ∀ g ∈ P.funcs, LinkFree g)
    (hk : EnvAdv base) : EnvAdv (linkEnvR P base R) := by
  intro n gsem hg vals m rvals m' hr
  cases hpf : P.func? n with
  | none => rw [linkEnvR_none hpf] at hg; exact hk n gsem hg vals m rvals m' hr
  | some g =>
    rw [linkEnvR_some hpf] at hg
    cases hg
    simp only at hr
    cases hi : initState P n vals m with
    | ok s =>
      rw [hi] at hr
      simp only at hr
      obtain ⟨M, hr⟩ := hR s _ hr (.inl ⟨_, _, rfl⟩)
      have hI : LInv P s := by
        simp only [initState, hpf, Res.ofOption_some, Res.ok_bind] at hi
        cases he : enterFunc g vals m with
        | ok r =>
          rw [he] at hi
          obtain ⟨fr, mem'⟩ := r
          simp only [Res.ok_bind, Res.pure_eq, Res.ok.injEq] at hi
          subst hi
          exact ⟨LFrame.enterFunc (Program.func?_some hpf).1 he, fun _ h => nomatch h⟩
        | trap => rw [he] at hi; cases hi
        | stuck => rw [he] at hi; cases hi
      cases hmp : m.place with
      | none => exact ⟨0, fun pl ini h => by rw [hmp] at h; cases h⟩
      | some pl =>
        cases hin : pl.init with
        | none => exact ⟨0, fun pl' ini h hi' => by rw [hmp] at h; cases h; rw [hin] at hi'; cases hi'⟩
        | some ini =>
          obtain ⟨e, he⟩ := runLoop_placeB hP hk M s rvals m' hI (initState_placeB hi hmp hin) hr
          refine ⟨e, fun pl' ini' h hi' => ?_⟩
          rw [hmp] at h
          cases h
          rw [hin] at hi'
          cases hi'
          rw [he]
    | trap c => rw [hi] at hr; cases hr
    | stuck msg => rw [hi] at hr; cases hr

theorem linkEnvN_adv {P : Program} {base : Env} {M : Nat} (hP : ∀ g ∈ P.funcs, LinkFree g)
    (hk : EnvAdv base) : EnvAdv (linkEnvN P base M) :=
  linkEnvR_adv (runsOf_runLoop base P M) hP hk

end Clif

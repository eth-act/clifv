import FV.Concurrency.ArmAllocLS

/-!
# Layer 4b pausing at calls and returns (T2j follow-up, #473, calls)

A caller's activation in a linked thread runs its own code only up to its calls and its return:
at a call the callee's code runs (its own contract, `CallCompose.link_compose`), after the `ret`
the caller's. Layer 4b for such an activation therefore **pauses** at the `call` and `rets` items
instead of stepping them, at a configuration related to the Arm state the run reached there:

* `refA_runQ`, **`refines_of_itemSimQ`**: `refines_of_itemSim` that, where the source terminates,
  also gives the Arm run up to the realized prefix's end and the relation of its last state to
  the source's configuration;
* `AtCall`, `AtRets`, `Pause` (the allocated code `Done`, or at a `call`/`rets` item);
  `MemScopeLSC` (`MemScopeLS` with `call` items);
* **`itemSim_lsC`**: the per-item obligation of the scope with calls, terminating at `Pause`;
* **`arm_alloc_refines_lsC`**: every precise run under `OkPriv` from a `Q`-related state realizes
  a run of the allocated code, its whole run or a prefix whose last Arm state is related (`RelQ`)
  to a configuration where the code is done or pauses at a call or a return.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot ArmPrecise VCodeThread Backend Backend.Proof AllocThread
open PrepThread (conv)
open Code VCodeEvents VCodeAddr

/-! ## The run level, with the state where the source terminates -/

section run
variable {P : Policy} {f : ArmState → ArmState} {ok : ArmState → Lab → Prop} {C : Type}
  {S : C → List Ev → C → Prop} {Rel : ArmState × Mon → C → Prop} {Term : C → Prop}
  {μ : C → Nat} {Priv : Nat → Prop}

/-- `refA_run` with the Arm run up to the source's termination (module doc). -/
theorem refA_runQ (hsim : ItemSim P f ok S Rel Term μ Priv) :
    ∀ N M (ls : List Lab) t t' c, ls.length ≤ N → μ c ≤ M → PRun P f ok t ls t' → Rel t c →
      ∃ n trS cE ψ, n ≤ ls.length ∧ SRun S c trS cE ∧ RefA Priv trS (evTr (ls.take n)) ψ ∧
        (n = ls.length ∨ ∃ tE, PRun P f ok t (ls.take n) tE ∧ Rel tE cE ∧ Term cE) := by
  intro N
  induction N with
  | zero =>
    intro M
    induction M with
    | zero =>
      intro ls t t' c hN hM hr hR
      rcases hsim t c hR ls t' hr with hT | ⟨n, evs, c', t1, φ, hn, hpos, hs, -, -, hi⟩ |
          ⟨evs, c', φ, hs, hi⟩ | hp
      · exact ⟨0, [], c, fun _ => (0, 0), Nat.zero_le _, .nil,
          refA_nil (fun p y hy => by simp [evTr] at hy; rw [evAt_nil] at hy; cases hy) _,
          .inr ⟨t, .nil, hR, hT⟩⟩
      · omega
      · have hl : ls = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hl
        have := RefA.cons hi (refA_nil (Priv := Priv) (trT := []) (fun p y hy => by
          rw [evAt_nil] at hy; cases hy) (fun _ => (0, 0)))
        exact ⟨0, [evs], c', _, Nat.le_refl _, .cons hs .nil, by simpa [evTr] using this, .inl rfl⟩
      · exact ⟨ls.length, [], c, fun _ => (0, 0), Nat.le_refl _, .nil,
          refA_nil (by rw [take_take_self]; exact hp) _, .inl rfl⟩
    | succ M ihM =>
      intro ls t t' c hN hM hr hR
      rcases hsim t c hR ls t' hr with hT | ⟨n, evs, c', t1, φ, hn, hpos, hs, hr1, hR1, hi⟩ |
          ⟨evs, c', φ, hs, hi⟩ | hp
      · exact ⟨0, [], c, fun _ => (0, 0), Nat.zero_le _, .nil,
          refA_nil (fun p y hy => by simp [evTr] at hy; rw [evAt_nil] at hy; cases hy) _,
          .inr ⟨t, .nil, hR, hT⟩⟩
      · have hn0 : n = 0 := by omega
        subst hn0
        have hl : ls = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hl
        obtain ⟨n', trS, cE, ψ, hn', hsr, href, hend⟩ :=
          ihM [] t1 t1 c' (by simp) (by omega) .nil hR1
        refine ⟨0, evs :: trS, cE, consMap 0 φ ψ, Nat.le_refl _, .cons hs hsr, ?_, .inl rfl⟩
        have := RefA.cons hi href
        simpa [evTr] using this
      · have hl : ls = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hl
        have := RefA.cons hi (refA_nil (Priv := Priv) (trT := []) (fun p y hy => by
          rw [evAt_nil] at hy; cases hy) (fun _ => (0, 0)))
        exact ⟨0, [evs], c', _, Nat.le_refl _, .cons hs .nil, by simpa [evTr] using this, .inl rfl⟩
      · exact ⟨ls.length, [], c, fun _ => (0, 0), Nat.le_refl _, .nil,
          refA_nil (by rw [take_take_self]; exact hp) _, .inl rfl⟩
  | succ N ihN =>
    intro M
    induction M with
    | zero =>
      intro ls t t' c hN hM hr hR
      rcases hsim t c hR ls t' hr with hT | ⟨n, evs, c', t1, φ, hn, hpos, hs, hr1, hR1, hi⟩ |
          ⟨evs, c', φ, hs, hi⟩ | hp
      · exact ⟨0, [], c, fun _ => (0, 0), Nat.zero_le _, .nil,
          refA_nil (fun p y hy => by simp [evTr] at hy; rw [evAt_nil] at hy; cases hy) _,
          .inr ⟨t, .nil, hR, hT⟩⟩
      · have hn0 : 0 < n := by omega
        obtain ⟨t1', r1, r2⟩ := PRun.split (ls.take n) (ls.drop n)
          (by rw [List.take_append_drop]; exact hr)
        rw [PRun.det r1 hr1] at r2
        obtain ⟨n', trS, cE, ψ, hn', hsr, href, hend⟩ :=
          ihN (μ c') (ls.drop n) t1 t' c' (by simp; omega) (Nat.le_refl _) r2 hR1
        have htk : ls.take n ++ (ls.drop n).take n' = ls.take (n + n') := by rw [List.take_add]
        refine ⟨n + n', evs :: trS, cE, consMap n φ ψ, by simp at hn'; omega, .cons hs hsr,
          ?_, ?_⟩
        · have := RefA.cons hi href
          rw [← evTr_append, evTr_length, List.length_take, Nat.min_eq_left hn] at this
          rwa [htk] at this
        · rcases hend with h | ⟨tE, hrE, hRE, hTE⟩
          · left; simp at h; omega
          · exact .inr ⟨tE, htk ▸ hr1.append hrE, hRE, hTE⟩
      · exact ⟨ls.length, [evs], c', _, Nat.le_refl _, .cons hs .nil, by
          rw [take_take_self]
          have := RefA.cons hi (refA_nil (Priv := Priv) (trT := []) (fun p y hy => by
            rw [evAt_nil] at hy; cases hy) (fun _ => (0, 0)))
          simpa [evTr] using this, .inl rfl⟩
      · exact ⟨ls.length, [], c, fun _ => (0, 0), Nat.le_refl _, .nil,
          refA_nil (by rw [take_take_self]; exact hp) _, .inl rfl⟩
    | succ M ihM =>
      intro ls t t' c hN hM hr hR
      rcases hsim t c hR ls t' hr with hT | ⟨n, evs, c', t1, φ, hn, hpos, hs, hr1, hR1, hi⟩ |
          ⟨evs, c', φ, hs, hi⟩ | hp
      · exact ⟨0, [], c, fun _ => (0, 0), Nat.zero_le _, .nil,
          refA_nil (fun p y hy => by simp [evTr] at hy; rw [evAt_nil] at hy; cases hy) _,
          .inr ⟨t, .nil, hR, hT⟩⟩
      · obtain ⟨t1', r1, r2⟩ := PRun.split (ls.take n) (ls.drop n)
          (by rw [List.take_append_drop]; exact hr)
        rw [PRun.det r1 hr1] at r2
        obtain ⟨n', trS, cE, ψ, hn', hsr, href, hend⟩ : ∃ n' trS cE ψ, n' ≤ (ls.drop n).length ∧
            SRun S c' trS cE ∧ RefA Priv trS (evTr ((ls.drop n).take n')) ψ ∧
            (n' = (ls.drop n).length ∨ ∃ tE, PRun P f ok t1 ((ls.drop n).take n') tE ∧
              Rel tE cE ∧ Term cE) := by
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0
            exact ihM (ls.drop 0) t1 t' c' (by simp; omega) (by omega) r2 hR1
          · exact ihN (μ c') (ls.drop n) t1 t' c' (by simp; omega) (Nat.le_refl _) r2 hR1
        have htk : ls.take n ++ (ls.drop n).take n' = ls.take (n + n') := by rw [List.take_add]
        refine ⟨n + n', evs :: trS, cE, consMap n φ ψ, by simp at hn'; omega, .cons hs hsr,
          ?_, ?_⟩
        · have := RefA.cons hi href
          rw [← evTr_append, evTr_length, List.length_take, Nat.min_eq_left hn] at this
          rwa [htk] at this
        · rcases hend with h | ⟨tE, hrE, hRE, hTE⟩
          · left; simp at h; omega
          · exact .inr ⟨tE, htk ▸ hr1.append hrE, hRE, hTE⟩
      · exact ⟨ls.length, [evs], c', _, Nat.le_refl _, .cons hs .nil, by
          rw [take_take_self]
          have := RefA.cons hi (refA_nil (Priv := Priv) (trT := []) (fun p y hy => by
            rw [evAt_nil] at hy; cases hy) (fun _ => (0, 0)))
          simpa [evTr] using this, .inl rfl⟩
      · exact ⟨ls.length, [], c, fun _ => (0, 0), Nat.le_refl _, .nil,
          refA_nil (by rw [take_take_self]; exact hp) _, .inl rfl⟩

/-- **`refines_of_itemSim` with the state where the source terminates** (module doc): the realized
prefix is the whole run, or the Arm run up to its end reaches a state related to the source's
terminated configuration. -/
theorem refines_of_itemSimQ (hsim : ItemSim P f ok S Rel Term μ Priv) {ls : List Lab}
    {t t' : ArmState × Mon} {c : C} (hr : PRun P f ok t ls t') (hR : Rel t c) :
    ∃ n trS cE ψ, n ≤ ls.length ∧ SRun S c trS cE ∧
      ThreadRefine.Refines (· = ·) Priv (MonPair (evTr (ls.take n))) (conv trS) (conv (evTr (ls.take n))) ψ ∧
      (n = ls.length ∨ ∃ tE, PRun P f ok t (ls.take n) tE ∧ Rel tE cE ∧ Term cE) := by
  obtain ⟨n, trS, cE, ψ, hn, hs, href, hend⟩ :=
    refA_runQ hsim ls.length (μ c) ls t t' c (Nat.le_refl _) (Nat.le_refl _) hr hR
  exact ⟨n, trS, cE, ψ, hn, hs, href.refines, hend⟩

/-- **`refines_of_itemSimQ` with the realized prefix exclusive-closed** (`RefA.xClosed`: every
`relXW` of the prefix follows an `acqXR` of it). -/
theorem refines_of_itemSimQX (hsim : ItemSim P f ok S Rel Term μ Priv) {ls : List Lab}
    {t t' : ArmState × Mon} {c : C} (hr : PRun P f ok t ls t') (hR : Rel t c) :
    ∃ n trS cE ψ, n ≤ ls.length ∧ SRun S c trS cE ∧
      ThreadRefine.Refines (· = ·) Priv (MonPair (evTr (ls.take n))) (conv trS) (conv (evTr (ls.take n))) ψ ∧
      (n = ls.length ∨ ∃ tE, PRun P f ok t (ls.take n) tE ∧ Rel tE cE ∧ Term cE) ∧
      ∀ b y, ThreadRefine.evAt (evTr (ls.take n)) b = some y → y.k = .relXW →
        ∃ a x, ThreadRefine.evAt (evTr (ls.take n)) a = some x ∧ x.k = .acqXR ∧ ThreadRefine.Lt a b := by
  obtain ⟨n, trS, cE, ψ, hn, hs, href, hend⟩ :=
    refA_runQ hsim ls.length (μ c) ls t t' c (Nat.le_refl _) (Nat.le_refl _) hr hR
  exact ⟨n, trS, cE, ψ, hn, hs, href.refines, hend, href.xClosed⟩

end run

/-! ## Pausing at calls and returns -/

/-- The allocated code is at a `call` item. -/
def AtCall (R : RL) (c : MConf CV ArmState) : Prop :=
  ∃ b k allocs its m w vb info, c = OpC b k allocs its m w ∧ R.vc.blocks[b]? = some vb ∧
    vb.insts[k]? = some (.call info)

/-- The allocated code is at a `rets` item (before its epilogue). -/
def AtRets (R : RL) (c : MConf CV ArmState) : Prop :=
  ∃ b k allocs its m w vb us, c = OpC b k allocs its m w ∧ R.vc.blocks[b]? = some vb ∧
    vb.insts[k]? = some (.rets us)

/-- **Where layer 4b of a caller pauses**: the allocated code is done, or at a call or a return. -/
def Pause (R : RL) (c : MConf CV ArmState) : Prop := Done R c ∨ AtCall R c ∨ AtRets R c

/-- **The scope with calls**: every instruction is in `MemScopeLS`'s forms or a call. -/
def MemScopeLSC (R : RL) : Prop :=
  ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), R.vc.blocks[b]? = some vb →
    vb.insts[k]? = some i → MemFormL R.ctx i ∨ BrForm i ∨ LSForm R.ctx i ∨ ∃ info, i = .call info

theorem memScopeLSC_of_ls {R : RL} (h : MemScopeLS R) : MemScopeLSC R :=
  fun b vb k i hb hi => (h b vb k i hb hi).elim .inl fun h => .inr (h.elim .inl fun h => .inr (.inl h))

/-- `Pause` of a ranked configuration. -/
abbrev PauseR (R : RL) (c : RConf) : Prop := Pause R c.1

/-- **The per-item obligation of the scope with calls, pausing at calls and returns** (module
doc; `itemSim_ls` off the pauses), on ranked configurations (`μR`; the statement before #553
used a measure of the configuration only, which `MachBuffer`'s layout falsifies:
`ArmAllocBranch` module doc). -/
theorem itemSim_lsC {R : RL} (hR : R.Wf) (hsc : MemScopeLSC R) :
    ItemSim Policy.arm R.step (OkPriv R) (SrcStepR R) (RelQR R) (PauseR R) (μR R) (PrivA R) := by
  rintro ⟨s, mon⟩ ⟨c, r⟩ ⟨hqa, hk⟩ ls t' hr
  match c, hqa, hk with
  | .ret vals m w, _, _ => exact .inl (.inl (.inl ⟨vals, m, w, rfl⟩))
  | .halt w, _, _ => exact .inl (.inl (.inr (.inl ⟨w, rfl⟩)))
  | .run ⟨b, its, m, w⟩, hqa, hk =>
  by_cases hP : AtCall R (.run ⟨b, its, m, w⟩) ∨ AtRets R (.run ⟨b, its, m, w⟩)
  case pos => exact .inl (.inr hP)
  by_cases hS : ∃ evs c', SrcStep R (.run ⟨b, its, m, w⟩) evs c'
  case neg => exact .inl (.inl (.inr (.inr fun evs c' h => hS ⟨evs, c', h⟩)))
  obtain ⟨evs0, c0, hs0⟩ := hS
  cases hs0 with
  | @move _ src dst its' =>
    rcases move_op hR hqa hr with h | h
    · exact .inr (.inl (isOut_μR noGotoAt_move hk h))
    · exact .inr (.inr (.inr h))
  | @op _ k allocs its' _ _ vb i ops _ _ hvb hi hops hevs hfoot hst =>
    have hs : SrcStep R (OpC b k allocs its' m w) _ _ := .op hvb hi hops hevs hfoot hst
    rcases RelQ.op' hqa hs with ⟨hq, hA⟩ | ⟨rfl, vals, m', w', rfl⟩
    case inr => exact .inr (.inl (itemSimOut_retR hs (RkC.pos hk)))
    have uniq : ∀ vb' i', R.vc.blocks[b]? = some vb' → vb'.insts[k]? = some i' → i' = i :=
      fun vb' i' h1 h2 => by rw [hvb] at h1; cases h1; rw [hi] at h2; cases h2; rfl
    rcases hsc b vb k i hvb hi with hl | hbr | hls | ⟨info, rfl⟩
    · refine Or.imp_left Or.inl (opOutR_of (noGotoAt_op hvb hi (noGoto_memFormL hl)) hk ?_)
      rcases hl with (h | h | ⟨ty, rt, rn, fl, rfl, hfo⟩ | ⟨ty, rt, rn, fl, rfl, hfo⟩) | hl | hl
      · exact opOut_okPriv (fun ls t' hr => noev_op hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ h) hr) hr
      · exact opOut_okPriv (fun ls t' hr => fence_op hR hq hA hs
          (fun vb' i' h1 h2 => (uniq vb' i' h1 h2).trans h) hr) hr
      · exact opOut_okPriv (fun ls t' hr => oneEv_op hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ ldar_form hfo) hr) hr
      · exact opOut_okPriv (fun ls t' hr => oneEv_op hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ stlr_form hfo) hr) hr
      · exact rmw_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hl) hr
      · exact cas_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hl) hr
    · exact Or.imp_left Or.inl
        (goto_op hR hq hA hk hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hbr) hr)
    · exact Or.imp_left Or.inl (opOutR_of (noGotoAt_op hvb hi (noGoto_ls hls)) hk
        (opOut_okPriv (fun ls t' hr => oneEv_op hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ lsForm_oneEv hls) hr) hr))
    · exact absurd (.inl ⟨b, k, allocs, its', m, w, vb, info, rfl, hvb, hi⟩) hP

/-- **Layer 4b of a caller, pausing at its calls and its return** (module doc): every precise
run under `OkPriv` from a `Q`-related state realizes a run of the allocated code (`MTRun`) with
`Refines`, on the whole run or on a prefix whose Arm run ends in a state related (`RelQ`) to a
configuration where the allocated code is done, at a `call` or at a `rets` item. -/
theorem arm_alloc_refines_lsC {R : RL} (hR : R.Wf) (hsc : MemScopeLSC R)
    {s : ArmState} {mon : Mon} {c : MConf CV ArmState} (hq : Q R s c) (hA : AInv R c)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step (OkPriv R) (s, mon) ls t') :
    ∃ n trS cE ψ, n ≤ ls.length ∧ MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) c trS cE ∧
      ThreadRefine.Refines (· = ·) (PrivA R) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧
      (n = ls.length ∨ ∃ tE, PRun Policy.arm R.step (OkPriv R) (s, mon) (ls.take n) tE ∧
        RelQ R tE cE ∧ Pause R cE) := by
  obtain ⟨r, hrel⟩ := RelQR.of (t := (s, mon)) hq hA
  obtain ⟨n, trS, cE, ψ, hn, hs, href, hend⟩ :=
    refines_of_itemSimQ (itemSim_lsC hR hsc) hr hrel
  exact ⟨n, trS, cE.1, ψ, hn, mtrun_of_srun (SRun.fst hs), href,
    hend.imp_right fun ⟨tE, h1, h2, h3⟩ => ⟨tE, h1, h2.1, h3⟩⟩

end Concurrency.ArmAllocThread

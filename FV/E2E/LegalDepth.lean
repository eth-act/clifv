module

public import FV.E2E.LegalProgram

@[expose] public section

/-!
# The `i128` legalisation keeps the call depth (S3 with L1d)

`E2E.LegalProgram.legalProg_refines` matches a returning or trapping whole-program run of the
source program `P` with one of the legalised program `legalProg P`. Here the same with the
**call depth**: if no state the source run reaches has more than `d` callers (`Clif.DepthLe`),
neither has any state the legalised run reaches (`legalProg_refines_depth`). The legalisation
keeps the call structure (a call of a function of `P` is a call of its legalisation, the
`__*ti3` helpers are externs), so the peak-depth executable theorem
(`Link.compileExe_correct_peak`) applies to the legalised run with the source run's depth.

The proof is `legalProg_refines`'s induction on the fuel, at every depth: its environments carry
the depth.

* Source: the guarded environment `guardEnvD` runs a callee only from an entry that is good and
  whose run has call depth at most `d - 1` (`DepthCall`); `guard_runD`: every callee the source
  run enters is such an entry (`Clif.DepthLe.callee`).
* Target: `tgtEnvD` runs a callee of `legalProg P` (its whole-program run, unbounded) only from an
  entry whose run has call depth at most `d - 1`, else the call is stuck; the induction hypothesis
  at depth `d - 1` gives that for every callee the target run enters (`prog_callD`).
* `Clif.unlink_depth`: a per-function run that returns or traps under an environment whose
  program callees return or trap only from entries of depth at most `d - 1` (`Clif.UnlinkD`) is a
  whole-program run of depth at most `d`: the per-function states have no callers, a callee's
  states are below one caller (`Clif.Reaches.below_cases`).
-/

namespace Clif

theorem StepsTo.reaches {env : Env} {p : Program} :
    ∀ {k : Nat} {s s1 : State}, StepsTo env p k s s1 → Reaches env p s s1
  | 0, s, s1, h => by simp only [StepsTo] at h; subst h; exact .refl _
  | _ + 1, _, _, ⟨_, hs, h⟩ => .next hs (StepsTo.reaches h)

theorem Reaches.stepsTo {env : Env} {p : Program} {s s1 : State} (h : Reaches env p s s1) :
    ∃ k, StepsTo env p k s s1 := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | next hs _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, _, hs, hk⟩

/-- A state that a run which ends reaches, whose step finishes the run's bottom activation:
the run returns there. -/
theorem Reaches.done_outcome {env : Env} {p : Program} {x v : State} (h : Reaches env p x v)
    {a : List Val} {b : Mem} (hv : step env p v = .done a b) {N : Nat}
    (hN : runLoop env p N x ≠ .outOfFuel) : runLoop env p N x = .returned a b := by
  obtain ⟨k, hk⟩ := h.stepsTo
  have e1 := hk.runLoop (N + 1)
  rw [runLoop_succ', hv] at e1
  rw [← runLoop_add env p N x hN (1 + k), ← Nat.add_assoc]
  exact e1

/-- **The states reached below the callers `K`**: the bottom activation's states with `K` below,
until it returns to `K` (`resumeStep`), after which the run continues from the resumed state. -/
theorem Reaches.below_cases {env : Env} {p : Program} {K : List (Frame × List ValueId)}
    {x u : State} (h : Reaches env p (x.below K) u) :
    (∃ v, Reaches env p x v ∧ u = v.below K) ∨
    (∃ v a b s1, Reaches env p x v ∧ step env p v = .done a b ∧ resumeStep K a b = .next s1 ∧
      Reaches env p s1 u) := by
  generalize hy : x.below K = y at h
  induction h generalizing x with
  | refl => exact .inl ⟨x, .refl _, hy.symm⟩
  | next hs hr ih =>
    subst hy
    rw [step_below] at hs
    cases hx : step env p x with
    | next x' =>
      rw [hx] at hs
      simp only [StepResult.below, StepResult.next.injEq] at hs
      rcases ih hs with ⟨v, hv, rfl⟩ | ⟨v, a, b, s1, hv, hd, hres, hr'⟩
      · exact .inl ⟨v, .next hx hv, rfl⟩
      · exact .inr ⟨v, a, b, s1, .next hx hv, hd, hres, hr'⟩
    | done a b =>
      rw [hx] at hs
      exact .inr ⟨x, a, b, _, .refl _, hx, hs, hr⟩
    | trapped c => rw [hx] at hs; cases hs
    | stuck m => rw [hx] at hs; cases hs

/-- **`E`'s program callees run within call depth `d - 1`**: a call of a function `h` of `P`
returns or traps only from an entry whose whole-program run has positive `d` and call depth at
most `d - 1`. -/
def UnlinkD (E : Env) (P : Program) (base : Env) (d : Nat) : Prop :=
  ∀ h ∈ P.funcs, ∀ hs, E.extern h.name = some hs → ∀ vals mem,
    ((∃ rv m', hs vals mem = .returned rv m') ∨ (∃ c, hs vals mem = .trapped c)) →
    ∀ fr' mem', enterFunc h vals mem = .ok (fr', mem') →
      0 < d ∧ DepthLe base P (d - 1) ⟨fr', [], mem'⟩

/-- **Unlinking keeps the call depth**: a per-function run of `P.bare` under an environment that
unlinks `P` (`Unlink`) whose program callees return or trap only from entries of call depth at
most `d - 1` (`UnlinkD`) that returns or traps is from a state whose whole-program run has call
depth at most `d`. -/
theorem unlink_depth {E base : Env} {P : Program} {syms : String → Option Nat} {d : Nat}
    (hU : Unlink E P base) (hD : UnlinkD E P base d) {f : Function} (hf : f ∈ P.funcs)
    (hio : ¬ IndFree f → UnlinkInd E P base syms) :
    ∀ (n : Nat) (s : State), UInv P f syms s →
      ((∃ v m, Clif.runLoop E P.bare n s = .returned v m) ∨
        (∃ c, Clif.runLoop E P.bare n s = .trapped c)) →
      DepthLe base P d s := by
  intro n
  induction n with
  | zero =>
    intro s _ h
    rcases h with ⟨_, _, h⟩ | ⟨_, h⟩ <;> simp at h
  | succ n ih =>
  intro s hI hout
  rw [runLoop_succ'] at hout
  have nostuck : ∀ msg, step E P.bare s ≠ .stuck msg := by
    intro msg hm
    rw [hm] at hout
    rcases hout with ⟨_, _, h⟩ | ⟨_, h⟩ <;> simp [afterStep] at h
  intro u hu
  cases hu with
  | refl => rw [hI.callers]; exact Nat.zero_le _
  | next hs1 hr =>
    rcases unlink_step hU hf hio hI.callers hI.frame hI.syms with
      ⟨-, hn, hd, ht⟩ | ⟨g, hgP, vals, c, hW, hCL⟩ | hS
    · cases hst : step E P.bare s with
      | next s1 =>
        rw [hn s1 hst] at hs1
        cases hs1
        rw [hst] at hout
        exact ih _ (hI.next hU hf hio hst) hout u hr
      | done v m => rw [hd v m hst] at hs1; cases hs1
      | trapped c => rw [ht c hst] at hs1; cases hs1
      | stuck m => exact absurd hst (nostuck m)
    · obtain ⟨hs, he, hprog⟩ := hU.prog g hgP
      have CL := hCL E (EnvAgree.refl P E) hs he
      rcases CL.2.2 with ⟨msg, hm⟩ | ⟨rv, m2, ho, -, hr'⟩ | ⟨c', ho, hr'⟩
      · exact absurd hm (nostuck msg)
      · obtain ⟨fr', mem', hent, N, hrun⟩ := (hprog vals s.mem).1 rv m2 ho
        obtain ⟨hd0, hdc⟩ := hD g hgP hs he vals s.mem (.inl ⟨rv, m2, ho⟩) fr' mem' hent
        have hW' : step base P s = .next ((⟨fr', [], mem'⟩ : State).below [c]) := by
          rw [hW, hent]; rfl
        rw [hW'] at hs1
        cases hs1
        rcases hr.below_cases with ⟨v, hv, rfl⟩ | ⟨v, a, b, s1, hv, hdone, hres, hr1⟩
        · have := hdc v hv
          simp only [State.below_callers, List.length_append, List.length_singleton]
          omega
        · have e := hv.done_outcome hdone (N := N) (by rw [hrun]; exact fun h => nomatch h)
          rw [hrun] at e
          cases e
          have hst : step E P.bare s = .next s1 := by rw [hr', hres]
          rw [hst] at hout
          exact ih s1 (hI.next hU hf hio hst) hout u hr1
      · obtain ⟨fr', mem', hent, N, hrun⟩ := (hprog vals s.mem).2 c' ho
        obtain ⟨hd0, hdc⟩ := hD g hgP hs he vals s.mem (.inr ⟨c', ho⟩) fr' mem' hent
        have hW' : step base P s = .next ((⟨fr', [], mem'⟩ : State).below [c]) := by
          rw [hW, hent]; rfl
        rw [hW'] at hs1
        cases hs1
        rcases hr.below_cases with ⟨v, hv, rfl⟩ | ⟨v, a, b, s1, hv, hdone, -, -⟩
        · have := hdc v hv
          simp only [State.below_callers, List.length_append, List.length_singleton]
          omega
        · have e := hv.done_outcome hdone (N := N) (by rw [hrun]; exact fun h => nomatch h)
          rw [hrun] at e
          cases e
    · obtain ⟨msg, hm⟩ := hS E (EnvAgree.refl P E)
      exact absurd hm (nostuck msg)

end Clif

namespace E2E.LegalProgram

open Clif Opt.Legal Opt.Legalize128

/-! ## The source environment with the call depth -/

/-- A call of `h` on `vals` from memory `mem` enters a run of call depth at most `d - 1`, `d`
positive. -/
def DepthCall (B : Env) (P : Program) (d : Nat) (h : Function) (vals : List Val) (mem : Mem) :
    Prop :=
  ∀ fr' mem', enterFunc h vals mem = .ok (fr', mem') → 0 < d ∧ DepthLe B P (d - 1) ⟨fr', [], mem'⟩

open Classical in
/-- The callee run of the guarded environment at call depth `d`: the linked environment's from a
good entry of depth at most `d - 1`. -/
noncomputable def guardFunD (B : Env) (P : Program) (G : Prop) (syms : String → Option Nat)
    (M d : Nat) (h : Function) (n : String) : List Val → Mem → Outcome :=
  fun vals mem => if GoodCall B P G syms h vals mem ∧ DepthCall B P d h vals mem then
      linkFun B P M n vals mem
    else .stuck "outside the source run"

theorem guardFunD_good {B : Env} {P : Program} {G : Prop} {syms : String → Option Nat}
    {M d : Nat} {h : Function} {n : String} {vals : List Val} {mem : Mem}
    (hg : GoodCall B P G syms h vals mem) (hd : DepthCall B P d h vals mem) :
    guardFunD B P G syms M d h n vals mem = linkFun B P M n vals mem := by
  simp [guardFunD, hg, hd]

theorem guardFunD_cases {B : Env} {P : Program} {G : Prop} {syms : String → Option Nat}
    {M d : Nat} {h : Function} {n : String} {vals : List Val} {mem : Mem} {o : Outcome}
    (ho : guardFunD B P G syms M d h n vals mem = o) (hs : ∀ msg, o ≠ .stuck msg) :
    (GoodCall B P G syms h vals mem ∧ DepthCall B P d h vals mem) ∧
      linkFun B P M n vals mem = o := by
  unfold guardFunD at ho
  split at ho
  · exact ⟨‹_›, ho⟩
  · exact absurd ho.symm (hs _)

/-- **The guarded linked environment at call depth `d`** (`guardEnv` whose callees are entered
only at depth at most `d - 1`). -/
noncomputable def guardEnvD (B : Env) (P : Program) (G : Prop) (syms : String → Option Nat)
    (M d : Nat) : Env where
  extern n := match P.func? n with
    | some h => some (guardFunD B P G syms M d h n)
    | none => B.extern n
  names := (linkEnvN P B M).names
  sigOf := (linkEnvN P B M).sigOf

theorem guardEnvD_none {B : Env} {P : Program} {G : Prop} {syms : String → Option Nat}
    {M d : Nat} {n : String} (hn : P.func? n = none) :
    (guardEnvD B P G syms M d).extern n = B.extern n := by
  simp [guardEnvD, hn]

theorem guardEnvD_some {B : Env} {P : Program} {G : Prop} {syms : String → Option Nat}
    {M d : Nat} {n : String} {h : Function} (hn : P.func? n = some h) :
    (guardEnvD B P G syms M d).extern n = some (guardFunD B P G syms M d h n) := by
  simp [guardEnvD, hn]

theorem agree_guardD (B : Env) (P : Program) (G : Prop) (syms : String → Option Nat)
    (M d : Nat) : EnvAgree P (linkEnvN P B M) (guardEnvD B P G syms M d) :=
  ⟨rfl, rfl, fun n hn => by rw [guardEnvD_none hn, linkEnvN_none hn]⟩

theorem unlink_guardD {B : Env} {P : Program} {G : Prop} {syms : String → Option Nat}
    (hF : ProgFacts P) (M d : Nat) : Unlink (guardEnvD B P G syms M d) P B where
  nd := hF.nd
  free := hF.free
  decl := hF.decl
  prog h hh := by
    have hp := func?_name hF.nd hh
    refine ⟨_, guardEnvD_some hp, fun vals mem => ⟨fun rv m' hr => ?_, fun c hr => ?_⟩⟩
    · obtain ⟨-, hl⟩ := guardFunD_cases hr (fun _ h => by cases h)
      exact (linkFun_prog hp vals mem).1 rv m' hl
    · obtain ⟨-, hl⟩ := guardFunD_cases hr (fun _ h => by cases h)
      exact (linkFun_prog hp vals mem).2 c hl
  base _ hn := guardEnvD_none hn
  sigOf _ := rfl

/-- **The guarded run at call depth `d`**: a per-function run of `f` under the linked
environment from a state all of whose whole-program successors are good and whose run has call
depth at most `d` returns or traps as under `guardEnvD` (every callee is entered at a good state
of depth at most `d - 1`: the whole program enters it there with one more caller). -/
theorem guard_runD {B : Env} {P : Program} {G : Prop} {syms : String → Option Nat}
    (hF : ProgFacts P) (M d : Nat) {f : Function} (hf : f ∈ P.funcs)
    (hio : ¬ IndFree f → UnlinkInd (linkEnvN P B M) P B syms) :
    ∀ (n : Nat) (s : State), UInv P f syms s → GoodFrom B P G syms s → DepthLe B P d s →
      (∀ v m, Clif.runLoop (linkEnvN P B M) P.bare n s = .returned v m →
        Clif.runLoop (guardEnvD B P G syms M d) P.bare n s = .returned v m) ∧
      (∀ c, Clif.runLoop (linkEnvN P B M) P.bare n s = .trapped c →
        Clif.runLoop (guardEnvD B P G syms M d) P.bare n s = .trapped c) := by
  have hU := unlink_linkN (B := B) hF M
  have hA := agree_guardD B P G syms M d
  intro n
  induction n with
  | zero => exact fun _ _ _ _ => ⟨fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
  | succ n ih =>
  intro s hI hG hD
  rw [runLoop_succ', runLoop_succ']
  have cont : ∀ s1, step (linkEnvN P B M) P.bare s = .next s1 →
      step (guardEnvD B P G syms M d) P.bare s = .next s1 →
      (∀ v m, afterStep (linkEnvN P B M) P.bare n (.next s1) = .returned v m →
        afterStep (guardEnvD B P G syms M d) P.bare n (.next s1) = .returned v m) ∧
      (∀ c, afterStep (linkEnvN P B M) P.bare n (.next s1) = .trapped c →
        afterStep (guardEnvD B P G syms M d) P.bare n (.next s1) = .trapped c) := by
    intro s1 h1 _
    obtain ⟨k, hk⟩ := unlink_next hU hf hio hI h1
    exact ih s1 (hI.next hU hf hio h1) (hG.of_reach hk.sreach)
      fun u hu => hD u (hk.reaches.trans hu)
  rcases unlink_step hU hf hio hI.callers hI.frame hI.syms with
    ⟨heq, -, -, -⟩ | ⟨h, hhP, vals, c, hW, hCL⟩ | hS
  · rw [heq _ hA]
    cases hst : step (linkEnvN P B M) P.bare s with
    | next s1 => exact cont s1 hst (by rw [heq _ hA, hst])
    | done v m => exact ⟨fun _ _ h => h, fun _ h => h⟩
    | trapped c => exact ⟨fun _ _ h => h, fun _ h => h⟩
    | stuck m => exact ⟨fun _ _ h => h, fun _ h => h⟩
  · have hp := func?_name hF.nd hhP
    have CE := hCL _ (EnvAgree.refl _ _) _ (linkEnvN_some' hp)
    have CG := hCL _ hA _ (guardEnvD_some (G := G) (syms := syms) (M := M) (d := d) hp)
    have hgood : GoodCall B P G syms h vals s.mem := by
      intro fr' mem' hent s' hs'
      have hW' : step B P s = .next ((⟨fr', [], mem'⟩ : State).below [c]) := by rw [hW, hent]; rfl
      have := hG (s'.below [c]) (.step hW' (hs'.belowK [c]))
      exact ⟨this.1, memTrapFree_below [c] this.2.1, this.2.2⟩
    have hdep : DepthCall B P d h vals s.mem := by
      intro fr' mem' hent
      have hW' : step B P s = .next ((⟨fr', [], mem'⟩ : State).below [c]) := by rw [hW, hent]; rfl
      exact DepthLe.callee (K := [c]) (by simp) hD (.next hW' (.refl _))
    have heqF : guardFunD B P G syms M d h h.name vals s.mem = linkFun B P M h.name vals s.mem :=
      guardFunD_good hgood hdep
    rw [heqF] at CG
    cases hst : step (linkEnvN P B M) P.bare s with
    | next s1 =>
      rw [hst] at CE
      rcases CE.2.2 with ⟨msg, hm⟩ | ⟨rv, m2, ho, hty, hr⟩ | ⟨t, ho, hr⟩
      · cases hm
      · have hG2 := CG.1 rv m2 ho hty s1 hr.symm
        rw [hG2]
        exact cont s1 hst hG2
      · cases hr
    | trapped t =>
      rw [hst] at CE
      rcases CE.2.2 with ⟨msg, hm⟩ | ⟨rv, m2, ho, hty, hr⟩ | ⟨t', ho, hr⟩
      · cases hm
      · exact absurd hr.symm resumeStep_ne_trapped
      · cases hr
        rw [CG.2.1 t ho]
        exact ⟨fun _ _ h => h, fun _ h => h⟩
    | done v m =>
      refine ⟨fun _ _ _ => ?_, fun _ h => (by cases h)⟩
      rw [hst] at CE
      rcases CE.2.2 with ⟨msg, hm⟩ | ⟨rv, m2, -, -, hr⟩ | ⟨t', -, hr⟩
      · cases hm
      · exact absurd hr.symm resumeStep_ne_done
      · cases hr
    | stuck m => exact ⟨fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
  · obtain ⟨msg, hm⟩ := hS _ (EnvAgree.refl _ _)
    rw [hm]
    exact ⟨fun _ _ h => (by cases h), fun _ h => (by cases h)⟩

/-- `noMemTrap_guard` at call depth `d`. -/
theorem noMemTrap_guardD {B : Env} {P : Program} {G : Prop} {syms : String → Option Nat}
    (hF : ProgFacts P) (M d : Nat) {f : Function} (hf : f ∈ P.funcs)
    (hio : ¬ IndFree f → UnlinkInd (guardEnvD B P G syms M d) P B syms) {s : State}
    (hI : UInv P f syms s) (hG : GoodFrom B P G syms s) :
    NoMemTrap (guardEnvD B P G syms M d) P.bare s := by
  intro t ht c st rest htr hb
  obtain ⟨k, hk⟩ := ht.steps
  obtain ⟨k', hk'⟩ := unlink_steps (unlink_guardD hF M d) hf hio hI hk
  have hT := (hG t hk'.sreach).2.1
  have hloc : ∀ (hnc : ∀ fn args, st.inst ≠ .call fn args)
      (hnci : ∀ sig callee args, st.inst ≠ .callIndirect sig callee args),
      step (guardEnvD B P G syms M d) P.bare t = step B P t := fun hnc hnci => by
    rw [step_inst _ _ t st rest hb hnc hnci, step_inst _ _ t st rest hb hnc hnci]
  refine ⟨fun op ty fl a o hi => ?_, fun op ty fl x a o hi => ?_⟩
  · have e := hloc (fun _ _ h => by rw [hi] at h; cases h) (fun _ _ _ h => by rw [hi] at h; cases h)
    exact (hT c st rest (e.symm.trans htr) hb).1 op ty fl a o hi
  · have e := hloc (fun _ _ h => by rw [hi] at h; cases h) (fun _ _ _ h => by rw [hi] at h; cases h)
    exact (hT c st rest (e.symm.trans htr) hb).2 op ty fl x a o hi

/-- `keep_guard` at call depth `d`. -/
theorem keep_guardD {B : Env} {P : Program} {G : Prop} {syms : String → Option Nat}
    {M d : Nat} (hF : ProgFacts P) (hb : EnvKeepsBounded B) :
    EnvKeepsBounded (guardEnvD B P G syms M d) := by
  intro name g hg vals m rv m' hr hM
  cases hpn : P.func? name with
  | none => rw [guardEnvD_none hpn] at hg; exact hb name g hg vals m rv m' hr hM
  | some h2 =>
    rw [guardEnvD_some hpn] at hg
    cases hg
    obtain ⟨hh2, rfl⟩ := Program.func?_some hpn
    obtain ⟨⟨hgood, -⟩, hl⟩ := guardFunD_cases hr (fun _ h => by cases h)
    obtain ⟨fr', mem', he, N, hN⟩ := (linkFun_prog hpn vals m).1 rv m' hl
    obtain ⟨k, t, hst, hdone⟩ := runLoop_returned_steps N _ rv m' hN
    have hGt := hgood fr' mem' he t hst.sreach
    have hLt : LInv P t := LInv.steps hF.free hst ⟨LFrame.enterFunc hh2 he, fun _ h => nomatch h⟩
    exact fun a n hv => hGt.1 a n (step_done_valid hF.free hLt hdone a n hv)

/-! ## The target environment with the call depth -/

open Classical in
/-- The callee run of the target's environment at call depth `d`: the whole-program run of the
legalised program (unbounded) from an entry of call depth at most `d - 1`, `d` positive; else
stuck. -/
noncomputable def tgtFunD (B : Env) (P' : Program) (d : Nat) (n : String) :
    List Val → Mem → Outcome :=
  fun vals mem => match initState P' n vals mem with
    | .ok s => if 0 < d ∧ DepthLe B P' (d - 1) s then runLim B P' s
      else .stuck "deeper than the source run"
    | .trap c => .trapped c
    | .stuck m => .stuck m

/-- **The target's linked environment at call depth `d`** (`tgtEnv` whose callees run only from
entries of depth at most `d - 1`). -/
noncomputable def tgtEnvD (B : Env) (P P' : Program) (d : Nat) : Env where
  extern n := match P'.func? n with
    | some _ => some (tgtFunD B P' d n)
    | none => B.extern n
  names := P.names ++ B.names
  sigOf n := (P'.func? n).map (·.sig)

theorem tgtEnvD_some {B : Env} {P P' : Program} {d : Nat} {n : String} {h : Function}
    (hn : P'.func? n = some h) : (tgtEnvD B P P' d).extern n = some (tgtFunD B P' d n) := by
  simp [tgtEnvD, hn]

theorem tgtEnvD_none {B : Env} {P P' : Program} {d : Nat} {n : String}
    (hn : P'.func? n = none) : (tgtEnvD B P P' d).extern n = B.extern n := by
  simp [tgtEnvD, hn]

/-- A callee run of `tgtEnvD` that does not get stuck: an entry state of call depth at most
`d - 1`, `d` positive, and the whole-program run there. -/
theorem tgtFunD_cases {B : Env} {P' : Program} {d : Nat} {h : Function}
    (hp : P'.func? h.name = some h) {vals : List Val} {mem : Mem} {o : Outcome}
    (ho : tgtFunD B P' d h.name vals mem = o) (hs : ∀ msg, o ≠ .stuck msg) :
    ∃ fr mem', enterFunc h vals mem = .ok (fr, mem') ∧ 0 < d ∧
      DepthLe B P' (d - 1) ⟨fr, [], mem'⟩ ∧ runLim B P' ⟨fr, [], mem'⟩ = o := by
  unfold tgtFunD at ho
  cases hi : initState P' h.name vals mem with
  | ok s =>
    rw [hi] at ho
    obtain ⟨fr, mem', he, rfl⟩ := (initState_ok_iff hp).mp hi
    dsimp only at ho
    by_cases hc : 0 < d ∧ DepthLe B P' (d - 1) ⟨fr, [], mem'⟩
    · simp only [hc, and_self, ↓reduceIte] at ho
      exact ⟨fr, mem', he, hc.1, hc.2, ho⟩
    · simp only [hc, ↓reduceIte] at ho
      exact absurd ho.symm (hs _)
  | trap c => exact absurd hi (initState_not_trap P' h.name vals mem c)
  | stuck m => rw [hi] at ho; exact absurd ho.symm (hs _)

theorem unlink_tgtD {B : Env} {P P' : Program} {d : Nat} (hF : ProgFacts P') :
    Unlink (tgtEnvD B P P' d) P' B where
  nd := hF.nd
  free := hF.free
  decl := hF.decl
  prog h hh := by
    have hp := func?_name hF.nd hh
    refine ⟨_, tgtEnvD_some hp, fun vals mem => ⟨fun rv m' hr => ?_, fun c hr => ?_⟩⟩
    · obtain ⟨fr, mem', he, -, -, hl⟩ := tgtFunD_cases hp hr (fun _ h => by cases h)
      obtain ⟨N, hN⟩ := runLim_ok hl (fun h => by cases h)
      exact ⟨fr, mem', he, N, hN⟩
    · obtain ⟨fr, mem', he, -, -, hl⟩ := tgtFunD_cases hp hr (fun _ h => by cases h)
      obtain ⟨N, hN⟩ := runLim_ok hl (fun h => by cases h)
      exact ⟨fr, mem', he, N, hN⟩
  base _ hn := tgtEnvD_none hn
  sigOf _ := rfl

theorem unlinkD_tgtD {B : Env} {P P' : Program} {d : Nat} (hF : ProgFacts P') :
    UnlinkD (tgtEnvD B P P' d) P' B d := by
  intro h hh hs he vals mem hout fr' mem' hent
  have hp := func?_name hF.nd hh
  rw [tgtEnvD_some hp] at he
  cases he
  have hns : ∀ msg, tgtFunD B P' d h.name vals mem ≠ .stuck msg := by
    rintro msg hm
    rcases hout with ⟨_, _, h⟩ | ⟨_, h⟩ <;> rw [hm] at h <;> cases h
  obtain ⟨fr, mem1, he1, hd0, hdl, -⟩ := tgtFunD_cases hp rfl hns
  rw [hent] at he1
  cases he1
  exact ⟨hd0, hdl⟩

theorem unlinkInd_tgtD {B : Env} {P P' : Program} {d : Nat} {syms : String → Option Nat}
    (hS : IndScope P' B syms) (hb : ∀ n, B.sigOf n = none)
    (hnames : P'.funcs.map (·.name) = P.funcs.map (·.name))
    (hext : ∀ n ∈ P.externNames, n ∈ P'.externNames) :
    UnlinkInd (tgtEnvD B P P' d) P' B syms :=
  ⟨hS, hb, P.externNames ++ B.names, by
    simp only [tgtEnvD, Program.names, hnames, List.append_assoc], fun n hn => by
    rcases List.mem_append.mp hn with h | h
    · exact List.mem_append_left _ (hext n h)
    · exact List.mem_append_right _ h⟩

/-! ## The induction with the call depth -/

/-- **The refinement at fuel `M`, at every call depth**: `Refines`, and a source run of call
depth at most `d` (`DepthLe`) is matched by a target run of call depth at most `d`. -/
def RefinesD (B : Env) (P : Program) (syms : String → Option Nat) (M : Nat) : Prop :=
  ∀ d, ∀ h ∈ P.funcs, ∀ vals vals' m fr m1 fr', enterFunc h vals m = .ok (fr, m1) →
    enterFunc (legalize h) vals' m = .ok (fr', m1) →
    ExpRel ((groups h.sig.params).getD []) vals vals' →
    GoodFrom B P (SomeInd (legalProg P)) syms ⟨fr, [], m1⟩ →
    DepthLe B P d ⟨fr, [], m1⟩ →
    (∀ rv m2, Clif.runLoop B P M ⟨fr, [], m1⟩ = .returned rv m2 →
      ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
        (∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .returned rv' m2) ∧
        DepthLe B (legalProg P) d ⟨fr', [], m1⟩) ∧
    (∀ c, Clif.runLoop B P M ⟨fr, [], m1⟩ = .trapped c →
      (∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .trapped c) ∧
        DepthLe B (legalProg P) d ⟨fr', [], m1⟩)

section Induction

variable {P : Program} {B : Env} {syms : String → Option Nat} (hC : ProgCtx P B syms)
  {M : Nat} (ih : RefinesD B P syms M) (d : Nat)
include hC ih

/-- A callee run of the guarded environment at depth `d` and the target's: related by the
induction hypothesis at depth `d - 1`. -/
theorem prog_callD {n : String} {h2 : Function} (hp : P.func? n = some h2)
    {vals vals' : List Val} {m : Mem}
    (hexp : ExpRel ((groups h2.sig.params).getD []) vals vals') :
    (∀ rv m', guardFunD B P (SomeInd (legalProg P)) syms M d h2 n vals m = .returned rv m' →
      ∃ rv', ExpRel ((groups h2.sig.returns).getD []) rv rv' ∧
        tgtFunD B (legalProg P) d n vals' m = .returned rv' m') ∧
    (∀ c, guardFunD B P (SomeInd (legalProg P)) syms M d h2 n vals m = .trapped c →
      tgtFunD B (legalProg P) d n vals' m = .trapped c) := by
  obtain ⟨hh2, rfl⟩ := Program.func?_some hp
  have hp' := hC.func?_some hp
  have key : ∀ o, guardFunD B P (SomeInd (legalProg P)) syms M d h2 h2.name vals m = o →
      (∀ msg, o ≠ .stuck msg) → ∃ fr m1 fr', enterFunc h2 vals m = .ok (fr, m1) ∧
        enterFunc (legalize h2) vals' m = .ok (fr', m1) ∧
        GoodFrom B P (SomeInd (legalProg P)) syms ⟨fr, [], m1⟩ ∧ 0 < d ∧
        DepthLe B P (d - 1) ⟨fr, [], m1⟩ ∧ Clif.runLoop B P M ⟨fr, [], m1⟩ = o := by
    intro o ho hs
    obtain ⟨⟨hgood, hdep⟩, hl⟩ := guardFunD_cases ho hs
    unfold linkFun at hl
    cases hi : initState P h2.name vals m with
    | ok s =>
      rw [hi] at hl
      obtain ⟨fr, m1, he, rfl⟩ := (initState_ok_iff hp).mp hi
      obtain ⟨fr', he'⟩ := enterFunc_legal (hC.ok h2 hh2) he hexp
      obtain ⟨hd0, hdl⟩ := hdep fr m1 he
      exact ⟨fr, m1, fr', he, he', hgood fr m1 he, hd0, hdl, hl⟩
    | trap c => exact absurd hi (initState_not_trap P h2.name vals m c)
    | stuck msg => rw [hi] at hl; exact absurd hl.symm (hs msg)
  have tgt : ∀ fr' m1 o k, enterFunc (legalize h2) vals' m = .ok (fr', m1) →
      Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = o → o ≠ .outOfFuel → 0 < d →
      DepthLe B (legalProg P) (d - 1) ⟨fr', [], m1⟩ →
      tgtFunD B (legalProg P) d h2.name vals' m = o := by
    intro fr' m1 o k he' hr ho hd0 hdl
    unfold tgtFunD
    rw [(initState_ok_iff hp').mpr ⟨fr', m1, he', rfl⟩]
    dsimp only
    simp only [hd0, hdl, and_self, ↓reduceIte]
    rw [runLim_eq (by rw [hr]; exact ho), hr]
  refine ⟨fun rv m' ho => ?_, fun c ho => ?_⟩
  · obtain ⟨fr, m1, fr', he, he', hG, hd0, hdl, hr⟩ := key _ ho (fun _ h => by cases h)
    obtain ⟨rv', hrel, ⟨k, hk⟩, hdt⟩ :=
      (ih (d - 1) h2 hh2 vals vals' m fr m1 fr' he he' hexp hG hdl).1 rv m' hr
    exact ⟨rv', hrel, tgt fr' m1 _ k he' hk (fun h => by cases h) hd0 hdt⟩
  · obtain ⟨fr, m1, fr', he, he', hG, hd0, hdl, hr⟩ := key _ ho (fun _ h => by cases h)
    obtain ⟨⟨k, hk⟩, hdt⟩ := (ih (d - 1) h2 hh2 vals vals' m fr m1 fr' he he' hexp hG hdl).2 c hr
    exact tgt fr' m1 _ k he' hk (fun h => by cases h) hd0 hdt

/-- `extRel_prog` at call depth `d`. -/
theorem extRel_progD {n : String} {h2 : Function} (hp : P.func? n = some h2) {sig : Signature}
    (hsig : h2.sig = sig) :
    ExtRelAt (guardEnvD B P (SomeInd (legalProg P)) syms M d) (tgtEnvD B P (legalProg P) d) n
      sig := by
  intro hs he
  rw [guardEnvD_some hp] at he
  cases he
  refine ⟨_, tgtEnvD_some (hC.func?_some hp), fun gs rg hgs hrg vals vals' m hty hexp => ?_⟩
  have hexp' : ExpRel ((groups h2.sig.params).getD []) vals vals' := by
    rw [hsig, hgs]; exact hexp
  obtain ⟨h1, h2'⟩ := prog_callD hC ih d hp hexp'
  refine ⟨fun rv m' ho _ => ?_, fun c ho => h2' c ho⟩
  obtain ⟨rv', hrel, ht⟩ := h1 rv m' ho
  refine ⟨rv', ht, ?_⟩
  rw [hsig, hrg] at hrel
  exact hrel

/-- `sameAt_link` at call depth `d`. -/
theorem sameAt_linkD {n : String} {sig : Signature} (hd : sig128 sig = false)
    (hdecl : ∀ h2, P.func? n = some h2 → h2.sig = sig) :
    SameAt (guardEnvD B P (SomeInd (legalProg P)) syms M d) (tgtEnvD B P (legalProg P) d) n
      sig := by
  intro hs he
  cases hpn : P.func? n with
  | some h2 =>
    rw [guardEnvD_some hpn] at he
    cases he
    have hs2 := hdecl h2 hpn
    have hd2 : sig128 h2.sig = false := by rw [hs2]; exact hd
    refine ⟨_, tgtEnvD_some (hC.func?_some hpn), fun vals m hv => ?_⟩
    obtain ⟨gs, hgs, hG⟩ := groups_plain (sig128_params hd2)
    have hexp : ExpRel ((groups h2.sig.params).getD []) vals vals := by
      rw [hgs, Option.getD_some]
      refine expRel_refl_plain hG (sig128_params hd2) ?_
      have := congrArg List.length hv
      rw [hs2]
      simpa [AbiParam.tys] using this
    obtain ⟨h1, h2'⟩ := prog_callD hC ih d hpn hexp
    refine ⟨fun rv m' ho _ => ?_, fun c ho => h2' c ho⟩
    obtain ⟨rv', hrel, ht⟩ := h1 rv m' ho
    obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns hd2)
    rw [hrg, Option.getD_some] at hrel
    rw [← expRel_val hR (sig128_returns hd2) hrel]
    exact ht
  | none =>
    rw [guardEnvD_none hpn] at he
    exact ⟨hs, by rw [tgtEnvD_none (hC.func?_none hpn)]; exact he,
      fun vals m _ => ⟨fun rv m' ho _ => ho, fun c ho => ho⟩⟩

/-- `callIndRel_link` at call depth `d`. -/
theorem callIndRel_linkD {dsig : Signature} (hd : sig128 dsig = false) :
    CallIndRel (guardEnvD B P (SomeInd (legalProg P)) syms M d) (tgtEnvD B P (legalProg P) d)
      P.bare (legalProg P).bare dsig := by
  intro mem a vals
  have hnames : ((guardEnvD B P (SomeInd (legalProg P)) syms M d).names ++ P.bare.externNames) =
      ((tgtEnvD B P (legalProg P) d).names ++ (legalProg P).bare.externNames) := by
    simp [guardEnvD, tgtEnvD, linkEnvN_names]
  have hfun : ∀ n h2, P.func? n = some h2 →
      ((guardEnvD B P (SomeInd (legalProg P)) syms M d).sigOf n).all dsig.abiMatch = true →
      ((tgtEnvD B P (legalProg P) d).sigOf n).all dsig.abiMatch = true ∧ sig128 h2.sig = false ∧
        AbiParam.tys dsig.params = AbiParam.tys h2.sig.params := by
    intro n h2 hpn hs
    have hs' : dsig.abiMatch h2.sig = true := by
      simpa [guardEnvD, linkEnvN_sigOf, hpn] using hs
    have hm := Signature.abiMatch_eq_true.mp hs'
    have h2p : sig128 h2.sig = false := sig128_of_tys hd hm.1 hm.2.2
    have hl2 : (legalize h2).sig = h2.sig := by
      have := (legalFacts (hC.ok h2 (Program.func?_some hpn).1)).sig
      rw [Complete.sigExp_plain h2p] at this
      exact (Option.some.inj this).symm
    refine ⟨?_, h2p, hm.1⟩
    simp [tgtEnvD, hC.func?_some hpn, hl2, hs']
  have hexpOf : ∀ n h2, P.func? n = some h2 → sig128 h2.sig = false →
      AbiParam.tys dsig.params = AbiParam.tys h2.sig.params →
      vals.map (·.ty) = AbiParam.tys dsig.params →
      ExpRel ((groups h2.sig.params).getD []) vals vals := by
    intro n h2 _ h2p htp hv
    obtain ⟨gs, hgs, hG⟩ := groups_plain (sig128_params h2p)
    rw [hgs, Option.getD_some]
    refine expRel_refl_plain hG (sig128_params h2p) ?_
    have := congrArg List.length (hv.trans htp)
    simpa [AbiParam.tys] using this
  constructor
  · intro r hr
    obtain ⟨n, g, h1, hg, hs, hv, rv, m', ho, hrt, rfl⟩ := callExternAt_ok_iff.mp hr
    rw [hnames] at h1
    cases hpn : P.func? n with
    | some h2 =>
      rw [guardEnvD_some hpn] at hg
      cases hg
      obtain ⟨hs', h2p, htp⟩ := hfun n h2 hpn hs
      obtain ⟨h1', -⟩ := prog_callD hC ih d hpn (hexpOf n h2 hpn h2p htp hv)
      obtain ⟨rv', hrel, ht⟩ := h1' rv m' ho
      obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns h2p)
      rw [hrg, Option.getD_some] at hrel
      rw [expRel_val hR (sig128_returns h2p) hrel] at ht
      exact callExternAt_ok_iff.mpr ⟨n, _, h1, tgtEnvD_some (hC.func?_some hpn), hs', hv, rv, m',
        ht, hrt, rfl⟩
    | none =>
      rw [guardEnvD_none hpn] at hg
      have hsN : (tgtEnvD B P (legalProg P) d).sigOf n = none := by
        simp [tgtEnvD, hC.func?_none hpn]
      exact callExternAt_ok_iff.mpr ⟨n, g, h1, by rw [tgtEnvD_none (hC.func?_none hpn)]; exact hg,
        by rw [hsN]; rfl, hv, rv, m', ho, hrt, rfl⟩
  · intro c hr
    obtain ⟨n, g, h1, hg, hs, hv, ho⟩ := callExternAt_trap_iff.mp hr
    rw [hnames] at h1
    cases hpn : P.func? n with
    | some h2 =>
      rw [guardEnvD_some hpn] at hg
      cases hg
      obtain ⟨hs', h2p, htp⟩ := hfun n h2 hpn hs
      obtain ⟨-, h2'⟩ := prog_callD hC ih d hpn (hexpOf n h2 hpn h2p htp hv)
      exact callExternAt_trap_iff.mpr ⟨n, _, h1, tgtEnvD_some (hC.func?_some hpn), hs', hv,
        h2' c ho⟩
    | none =>
      rw [guardEnvD_none hpn] at hg
      have hsN : (tgtEnvD B P (legalProg P) d).sigOf n = none := by
        simp [tgtEnvD, hC.func?_none hpn]
      exact callExternAt_trap_iff.mpr ⟨n, g, h1, by rw [tgtEnvD_none (hC.func?_none hpn)]; exact hg,
        by rw [hsN]; rfl, hv, ho⟩

end Induction

/-- **The refinement of one activation at fuel `M + 1` and call depth `d`** (`root_refines` with
the call depth): the callees related at fuel `M` and every depth (`RefinesD`). -/
theorem root_refinesD {P : Program} {B : Env} {syms : String → Option Nat}
    (hC : ProgCtx P B syms) {M : Nat} (ih : RefinesD B P syms M) (d : Nat) {h : Function}
    (hh : h ∈ P.funcs) {args args' : List Val} {fr fr' : Frame} {m1 : Mem}
    (hE : EntryRel h args args' fr fr')
    (hG : GoodFrom B P (SomeInd (legalProg P)) syms ⟨fr, [], m1⟩)
    (hd : DepthLe B P d ⟨fr, [], m1⟩) :
    (∀ rv m2, Clif.runLoop B P (M + 1) ⟨fr, [], m1⟩ = .returned rv m2 →
      ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
        (∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .returned rv' m2) ∧
        DepthLe B (legalProg P) d ⟨fr', [], m1⟩) ∧
    (∀ c, Clif.runLoop B P (M + 1) ⟨fr, [], m1⟩ = .trapped c →
      (∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .trapped c) ∧
        DepthLe B (legalProg P) d ⟨fr', [], m1⟩) := by
  have hF := hC.facts
  have hF' := hC.facts'
  have hhP' : legalize h ∈ (legalProg P).funcs := List.mem_map_of_mem hh
  have hio : ¬ IndFree h → SomeInd (legalProg P) := fun hn => hC.someInd hh hn
  have hLe : LInv P ⟨fr, [], m1⟩ := ⟨hE.lframe hh, fun _ h => nomatch h⟩
  have hLeh : LInv (P.only h) ⟨fr, [], m1⟩ :=
    ⟨hE.lframe (by simp [Program.only]), fun _ h => nomatch h⟩
  have hsym : ¬ IndFree h → m1.symbols = syms := fun hn => (hG _ (.refl _)).2.2 (hio hn)
  have hUI : UInv P h syms ⟨fr, [], m1⟩ := ⟨rfl, hLeh.1, hsym⟩
  have hioE : ¬ IndFree h → UnlinkInd (linkEnvN P B M) P B syms := fun hn =>
    unlinkInd_linked (hC.indSrc (hio hn)) (hC.ind (hio hn)).2 rfl
  have hioG : ¬ IndFree h →
      UnlinkInd (guardEnvD B P (SomeInd (legalProg P)) syms M d) P B syms := fun hn =>
    unlinkInd_linked (hC.indSrc (hio hn)) (hC.ind (hio hn)).2 rfl
  -- the source run is a per-function run under the guarded linked environment
  have hlink : ∀ o, Clif.runLoop B P (M + 1) ⟨fr, [], m1⟩ = o → (∀ msg, o ≠ .stuck msg) →
      o ≠ .outOfFuel → ∃ n, Clif.runLoop (linkEnvN P B M) P.bare n ⟨fr, [], m1⟩ = o := by
    intro o ho hs hof
    obtain ⟨n, hn⟩ := runLoop_linkN (P := P) (base := B) (f := h) (syms := syms) M hC.nd hh
      hC.free (fun hn => hC.indSrc (hio hn)) (E := linkEnvN P B M) rfl rfl (fun _ _ => rfl)
      (fun _ _ _ => rfl) (M + 1) ⟨fr, [], m1⟩ (Nat.le_refl _) hLe hLeh hsym
      (by rw [ho]; exact hs) (by rw [ho]; exact hof)
    exact ⟨n, hn.trans ho⟩
  have hguard := guard_runD (G := SomeInd (legalProg P)) hF M d hh hioE
  -- the target's per-function run is a whole-program run of call depth at most `d`
  have hUIt : UInv (legalProg P) (legalize h) syms ⟨fr', [], m1⟩ :=
    ⟨rfl, hE.lframe' (by simp [Program.only]), fun hn => (hG _ (.refl _)).2.2 ⟨_, hhP', hn⟩⟩
  have hioT : ¬ IndFree (legalize h) →
      UnlinkInd (tgtEnvD B P (legalProg P) d) (legalProg P) B syms :=
    fun hn => unlinkInd_tgtD (hC.ind ⟨_, hhP', hn⟩).1 (hC.ind ⟨_, hhP', hn⟩).2 hC.names
      (fun _ h => hC.externNames h)
  have hwhole := fun n =>
    unlink_run (unlink_tgtD (B := B) (P := P) (d := d) hF') hhP' hioT (n := n) hUIt
  have hdepth := fun n => unlink_depth (unlink_tgtD (B := B) (P := P) (d := d) hF')
    (unlinkD_tgtD hF') hhP' hioT n _ hUIt
  -- the per-activation refinement under the two environments
  have hact : (∀ n rv m2, Clif.runLoop (guardEnvD B P (SomeInd (legalProg P)) syms M d) P.bare n
        ⟨fr, [], m1⟩ = .returned rv m2 → rv.map (·.ty) = AbiParam.tys h.sig.returns →
        ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
          ∃ k, Clif.runLoop (tgtEnvD B P (legalProg P) d) (legalProg P).bare k ⟨fr', [], m1⟩ =
            .returned rv' m2) ∧
      (∀ n c, Clif.runLoop (guardEnvD B P (SomeInd (legalProg P)) syms M d) P.bare n
        ⟨fr, [], m1⟩ = .trapped c →
        ∃ k, Clif.runLoop (tgtEnvD B P (legalProg P) d) (legalProg P).bare k ⟨fr', [], m1⟩ =
          .trapped c) := by
    obtain ⟨b, hb, h2, h3, h4, h5⟩ := hE.entry
    obtain ⟨b', hb', h2', h3', h5'⟩ := hE.entry'
    rcases Complete.legalOkB_cases (hC.ok h hh) with ⟨hm, -, hl⟩ | ⟨hp, cert, hc⟩
    · -- the identity: the same code, related environments
      obtain ⟨hs, hes, hds⟩ := not_mentions hm
      obtain ⟨gs, hgs, hGs⟩ := groups_plain (sig128_params hs)
      have hexp := hE.exp
      rw [hgs, Option.getD_some] at hexp
      have hvv : args' = args := expRel_val hGs (sig128_params hs) hexp
      have hfe : fr' = fr := by
        rw [hl] at hb'
        rw [hb] at hb'
        cases hb'
        obtain ⟨func, regs, slots, body, term⟩ := fr
        obtain ⟨func', regs', slots', body', term'⟩ := fr'
        have e1 : func' = func := by
          have := hE.func'; have := hE.func; simp_all
        simp only at h2 h3 h5 h2' h3' h5' e1
        rw [hvv, h5] at h5'
        cases h5'
        have e2 := hE.slots
        simp only at e2
        subst e1 e2
        rw [h2, h2', h3, h3']
      subst hfe
      have hrun := ident_run (E := guardEnvD B P (SomeInd (legalProg P)) syms M d)
        (E' := tgtEnvD B P (legalProg P) d) (P := P) (P' := legalProg P) (f := h)
        (fun fn ex hfe => sameAt_linkD hC ih d (by
          obtain ⟨fn', hmem⟩ := lookup_mem hfe
          exact hes _ hmem) (fun h2 hpn => hC.decl h hh fn ex hfe h2 hpn))
        (fun i dsig hd => callIndRel_linkD hC ih d (by
          obtain ⟨i', hmem⟩ := lookup_mem hd
          exact hds _ hmem))
        (hC.free h hh)
      refine ⟨fun n rv m2 hr hty => ⟨rv, ?_, n, (hrun n _ rfl hLeh.1).1 rv m2 hr⟩,
        fun n c hr => ⟨n, (hrun n _ rfl hLeh.1).2 c hr⟩⟩
      obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns hs)
      rw [hrg, Option.getD_some]
      refine expRel_refl_plain hR (sig128_returns hs) ?_
      have := congrArg List.length hty
      simpa [AbiParam.tys] using this
    · -- a legalisation: `legalize_refines2` with the two environments
      have hbase := hC.base ⟨h, hh, hp.mentions⟩
      have hE2 : EnvOk2 (guardEnvD B P (SomeInd (legalProg P)) syms M d)
          (tgtEnvD B P (legalProg P) d) ⟨h, legalize h, cert⟩ P.bare (legalProg P).bare :=
        { src := fun _ _ _ => rfl
          tgt := fun _ _ _ => rfl
          helper := fun op => by
            obtain ⟨hf, hB, hsem⟩ := hbase.1 op
            exact ⟨hf, by rw [tgtEnvD_none (hC.func?_none (hC.helpers op))]; exact hB, hsem⟩
          ext := fun fn ex hfe => by
            cases hpn : P.func? ex.name with
            | some h2 => exact extRel_progD hC ih d hpn (hC.decl h hh fn ex hfe h2 hpn)
            | none =>
              intro hs he
              rw [guardEnvD_none hpn] at he
              obtain ⟨h', hb', hrel⟩ := hbase.2.1.at ex.name ex.sig hs he
              exact ⟨h', by rw [tgtEnvD_none (hC.func?_none hpn)]; exact hb', hrel⟩
          keep := keep_guardD hF hbase.2.2
          ind := fun _ => ⟨rfl, fun sig dsig hs hd =>
            have hd128 := pre_indSite hp hs hd
            callIndRel2_of_plain hd128 (callIndRel_linkD hC ih d hd128)⟩ }
      have hT := noMemTrap_guardD hF M d hh hioG hUI hG
      have hI : NoIndInternal (guardEnvD B P (SomeInd (legalProg P)) syms M d) P.bare h
          ⟨fr, [], m1⟩ := fun _ _ => ⟨(fun _ _ _ _ _ _ _ _ _ _ g hg => nomatch hg),
            (fun _ _ _ _ _ _ _ _ g hg => nomatch hg)⟩
      have href := fun n => legalize_refines2 hp hc hE2 hb hb' hE.func h2 h3 h4 h5 hE.func' h2'
        h3' h5' hE.slots hE.exp (hG _ (.refl _)).1 hT hI n
      exact ⟨fun n rv m2 hr _ => (href n).1 rv m2 hr, fun n c hr => (href n).2 c hr⟩
  refine ⟨fun rv m2 hr => ?_, fun c hr => ?_⟩
  · obtain ⟨n, hn⟩ := hlink _ hr (fun _ h => by cases h) (fun h => by cases h)
    have hn'' := (hguard n _ hUI hG hd).1 rv m2 hn
    have hty : rv.map (·.ty) = AbiParam.tys h.sig.returns := by
      have := runLoop_returned_tys hC.free (M + 1) _ rv m2 hLe hr
      simpa [State.bottom, hE.func] using this
    obtain ⟨rv', hrel, k, hk⟩ := hact.1 n rv m2 hn'' hty
    obtain ⟨k', hk'⟩ := (hwhole k).1 rv' m2 hk
    exact ⟨rv', hrel, ⟨k', hk'⟩, hdepth k (.inl ⟨rv', m2, hk⟩)⟩
  · obtain ⟨n, hn⟩ := hlink _ hr (fun _ h => by cases h) (fun h => by cases h)
    have hn'' := (hguard n _ hUI hG hd).2 c hn
    obtain ⟨k, hk⟩ := hact.2 n c hn''
    exact ⟨(hwhole k).2 c hk, hdepth k (.inr ⟨c, hk⟩)⟩

/-- **The callees are related at every fuel and call depth** (by induction on the fuel). -/
theorem prog_refinesD {P : Program} {B : Env} {syms : String → Option Nat}
    (hC : ProgCtx P B syms) : ∀ M, RefinesD B P syms M := by
  intro M
  induction M with
  | zero =>
    intro _ h _ vals vals' m fr m1 fr' _ _ _ _ _
    exact ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩
  | succ M ih =>
    intro d h hh vals vals' m fr m1 fr' hent hent' hexp hG hd
    have hfacts := legalFacts (hC.ok h hh)
    exact root_refinesD hC ih d hh
      (EntryRel.of_enter ⟨hfacts.name, hfacts.slots⟩ hent hent' hexp) hG hd

/-- **Whole-program refinement of the original program keeping the call depth** (S3, L1d):
`legalProg_refines`, and if the source run from `h`'s entry has call depth at most `d`
(`Clif.DepthLe`: no state it reaches has more than `d` callers), so has the legalised program's
run from the entry with the ABI-split arguments. -/
theorem legalProg_refines_depth {P : Program} {B : Env} {syms : String → Option Nat}
    (hC : ProgCtx P B syms) {h : Function} (hh : h ∈ P.funcs) {args args' : List Val}
    {fr fr' : Frame} {m1 : Mem} (hE : EntryRel h args args' fr fr')
    (hG : GoodFrom B P (SomeInd (legalProg P)) syms ⟨fr, [], m1⟩) {d : Nat}
    (hd : DepthLe B P d ⟨fr, [], m1⟩) (M : Nat) :
    (∀ rv m2, Clif.runLoop B P M ⟨fr, [], m1⟩ = .returned rv m2 →
      ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
        (∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .returned rv' m2) ∧
        DepthLe B (legalProg P) d ⟨fr', [], m1⟩) ∧
    (∀ c, Clif.runLoop B P M ⟨fr, [], m1⟩ = .trapped c →
      (∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .trapped c) ∧
        DepthLe B (legalProg P) d ⟨fr', [], m1⟩) := by
  cases M with
  | zero => exact ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩
  | succ M => exact root_refinesD hC (prog_refinesD hC M) d hh hE hG hd

end E2E.LegalProgram

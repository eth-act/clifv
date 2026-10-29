import FV.Concurrency.ArmAllocPause
import FV.Concurrency.ArmProgram

/-!
# Layer 4b on a linked machine (T2j follow-up, #473, calls)

A thread whose activations call compiled callees runs a **linked machine**: the caller's `R.step`
on the caller's program, the callee's on the callee's, and at a callee's `ret` line a step that
also switches back to the caller's program (`CallSeg.WitnessC.MC2`). Such a machine agrees with
`R.step` on the states holding `R`'s program at every line other than `ret` (`AgreesAt`). Layer
4b of the caller holds for it, because a run of the allocated code reaches a `ret` line only at a
`rets` item, where layer 4b pauses:

* `ItemSimN`: the per-item obligation `ItemSim` whose runs ending inside an item end in a state
  satisfying `G` (here `AtNonRet R`: at an instruction line other than `ret`);
* `prun_splitN`: a precise run of a machine `g` agreeing with `f` at the `G` states of a program
  `π` is a run of `f` up to its first state outside `G`;
* **`ItemSimN.transfer`**: `ItemSimN` for `f` gives `ItemSim` for every such `g`;
* `itemSim_lsCN`: the per-item obligation of the scope with calls (`itemSim_lsC`) with the pc
  invariant, from the item lemmas' `…R` versions (`noev_opR`, `fence_opR`, `oneEv_opR`,
  `rmw_opR`, `cas_opR`, `goto_opR`, `move_opR`);
* **`arm_alloc_refines_lsCL`**: `arm_alloc_refines_lsC` for every machine agreeing with `R.step`
  at `R`'s lines other than `ret`.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot ArmPrecise VCodeThread Backend Backend.Proof AllocThread
open Code VCodeEvents VCodeAddr

/-! ## The per-item obligation with a condition on the states inside items -/

section linked
variable {P : Policy} {f g : ArmState → ArmState} {ok : ArmState → Lab → Prop} {C : Type}
  {S : C → List Ev → C → Prop} {Rel : ArmState × Mon → C → Prop} {Term : C → Prop}
  {μ : C → Nat} {Priv : Nat → Prop} {G : ArmState → Prop} {π : Arm.Program}

/-- **The per-item obligation whose runs ending inside an item end in a `G` state** (`ItemSim`
with `G t'.1` in its two cases of runs ending inside the item). -/
def ItemSimN (P : Policy) (f : ArmState → ArmState) (ok : ArmState → Lab → Prop) {C : Type}
    (S : C → List Ev → C → Prop) (Rel : ArmState × Mon → C → Prop) (Term : C → Prop)
    (μ : C → Nat) (Priv : Nat → Prop) (G : ArmState → Prop) : Prop :=
  ∀ t c, Rel t c → ∀ ls t', PRun P f ok t ls t' →
    Term c ∨
    (∃ n evs c' t1 φ, n ≤ ls.length ∧ (0 < n ∨ μ c' < μ c) ∧ S c evs c' ∧
      PRun P f ok t (ls.take n) t1 ∧ Rel t1 c' ∧ Img Priv evs (evTr (ls.take n)) φ) ∨
    ((∃ evs c' φ, S c evs c' ∧ Img Priv evs (evTr ls) φ) ∧ G t'.1) ∨
    (PrivW Priv (evTr ls) ∧ G t'.1)

theorem ItemSimN.itemSim (h : ItemSimN P f ok S Rel Term μ Priv G) :
    ItemSim P f ok S Rel Term μ Priv :=
  fun t c hR ls t' hr => (h t c hR ls t' hr).imp_right (Or.imp_right (Or.imp And.left And.left))

theorem failState_program' (rs : BitVec 5) (s : ArmState) :
    (failState rs s).program = s.program := by
  simp only [failState, write_pc, write_gpr_zr]
  split <;> simp [write_gpr, w_program]

/-- A thread step of `f` is one of `g` where they agree on the state with any memory. -/
theorem tstep_swap {s : ArmState} {mon : Mon} {l : Lab} {t1 : ArmState × Mon}
    (hag : ∀ m, f (setMem m s) = g (setMem m s)) (hs : TStep P f (s, mon) l t1) :
    TStep P g (s, mon) l t1 := by
  cases hs with
  | @exec _ _ evs hk hagr hfp hsucc =>
    have hfp' : Footprint g s evs := fun m hm => by rw [← hag, ← hag]; exact hfp m hm
    have h := TStep.exec (f := g) (P := P) (mon := mon) hk hagr hfp' hsucc
    rwa [← hag] at h
  | xfail hc hfail herr hsp => exact .xfail hc hfail herr hsp

/-- **A run of a machine `g` agreeing with `f` at the `G` states of the program `π`** is a run
of `f` up to its first state outside `G` (`u`), the prefixes of that part runs of both. -/
theorem prun_splitN (hag : ∀ s, s.program = π → G s → ∀ m, g (setMem m s) = f (setMem m s))
    (hf : ∀ s, s.program = π → G s → ∀ m, (f (setMem m s)).program = π) :
    ∀ {t t' : ArmState × Mon} {ls : List Lab}, t.1.program = π → PRun P g ok t ls t' →
      ∃ ls1 ls2 u, ls = ls1 ++ ls2 ∧ PRun P f ok t ls1 u ∧ PRun P g ok u ls2 t' ∧
        (∀ k v, PRun P f ok t (ls1.take k) v → PRun P g ok t (ls1.take k) v) ∧
        (ls2 = [] ∨ ¬ G u.1)
  | _, _, _, _, .nil => ⟨[], [], _, rfl, .nil, .nil, fun k v h => by
    simp only [List.take_nil] at h ⊢; cases h; exact .nil, .inl rfl⟩
  | (s, mon), t', _, hπ, .cons (t1 := t1) (l := l) (ls := ls) hs hp ho hr => by
    by_cases hG : G s
    · have hs' : TStep P f (s, mon) l t1 := tstep_swap (fun m => hag s hπ hG m) hs
      have hπ1 : t1.1.program = π := by
        cases hs' with
        | exec => exact hf s hπ hG _
        | xfail => rw [failState_program']; exact hπ
      obtain ⟨ls1, ls2, u, rfl, h1, h2, h3, h4⟩ := prun_splitN hag hf hπ1 hr
      refine ⟨l :: ls1, ls2, u, rfl, .cons hs' hp ho h1, h2, fun k v hv => ?_, h4⟩
      cases k with
      | zero => cases hv; exact .nil
      | succ k =>
        cases hv with
        | cons hs1 hp1 ho1 hr1 =>
          obtain rfl := tstep_det hs1 hs'
          exact .cons hs hp ho (h3 k v hr1)
    · exact ⟨[], l :: ls, (s, mon), rfl, .nil, .cons hs hp ho hr, fun k v h => by
        simp only [List.take_nil] at h ⊢; cases h; exact .nil, .inr hG⟩

/-- **The per-item obligation on a linked machine** (module doc): `ItemSimN` for `f` gives
`ItemSim` for every machine `g` agreeing with `f` at the `G` states of the program `π` that the
related, non-terminated states hold (`f` keeping `π` at the `G` states). -/
theorem ItemSimN.transfer (hsim : ItemSimN P f ok S Rel Term μ Priv G)
    (hag : ∀ s, s.program = π → G s → ∀ m, g (setMem m s) = f (setMem m s))
    (hf : ∀ s, s.program = π → G s → ∀ m, (f (setMem m s)).program = π)
    (hπ : ∀ t c, Rel t c → ¬ Term c → t.1.program = π) :
    ItemSim P g ok S Rel Term μ Priv := by
  intro t c hR ls t' hr
  by_cases hT : Term c
  · exact .inl hT
  obtain ⟨ls1, ls2, u, rfl, h1, -, h3, h4⟩ := prun_splitN hag hf (hπ t c hR hT) hr
  rcases hsim t c hR ls1 u h1 with hT' | ⟨n, evs, c', t1, φ, hn, hpos, hs, hr1, hR1, hi⟩ |
      ⟨h, hG⟩ | ⟨h, hG⟩
  · exact .inl hT'
  · have e : (ls1 ++ ls2).take n = ls1.take n := List.take_append_of_le_length hn
    refine .inr (.inl ⟨n, evs, c', t1, φ, by simp; omega, hpos, hs, ?_, hR1, ?_⟩)
    · rw [e]; exact h3 n t1 hr1
    · rw [e]; exact hi
  · rcases h4 with rfl | hng
    · rw [List.append_nil]; exact .inr (.inr (.inl h))
    · exact absurd hG hng
  · rcases h4 with rfl | hng
    · rw [List.append_nil]; exact .inr (.inr (.inr h))
    · exact absurd hG hng

end linked

/-! ## The machine at the lines other than `ret` -/

/-- **A machine agreeing with `R.step` at `R`'s lines other than `ret`** (on the states holding
`R`'s program): e.g. a linked machine running `R`'s callees on their programs and switching back
to `R`'s program at their `ret` lines. -/
def AgreesAt (R : RL) (g : ArmState → ArmState) : Prop :=
  ∀ s, s.program = R.fb.program R.base → AtNonRet R s → g s = R.step s

theorem atNonRet_setMem {R : RL} {s : ArmState} (m : Memory) (h : AtNonRet R s) :
    AtNonRet R (setMem m s) := by
  obtain ⟨j, x, t, hj, hx, hh, hpc⟩ := h
  exact ⟨j, x, t, hj, hx, hh, by rw [r_setMem]; exact hpc⟩

/-- **At an unhooked line the machine is the plain step** (`armStepX_ins` without the error
premise). -/
theorem step_atNonRet {R : RL} (hR : R.Wf) {s : ArmState} (hπ : s.program = R.fb.program R.base)
    (h : AtNonRet R s) : R.step s = Arm.stepi s := by
  obtain ⟨j, x, t, hj, -, hh, hpc⟩ := h
  obtain ⟨_, w, hw, hk⟩ := FnAsm.layout_word hR.layout hR.lm hj rfl
  have hne : R.fb.words.toList ≠ [] := by
    intro h
    have : R.fb.words.size = 0 := by simpa using congrArg List.length h
    simp [this] at hk
  have hb : progBase s = R.base := progBase_eq (by rw [hπ]; rfl) hne
  have hsum := layout_sum hR.layout
  have hins : insnAt R.fa (progBase s) (Arm.r .PC s) = some x := by
    rw [hb, hpc]; exact insnAt_line (by have := hR.fit; omega) hj
  show ArmStepX R.X R.H R.fa s = Arm.stepi s
  unfold ArmStepX
  simp only [hins]
  cases x <;> simp_all [Insn.hooked]

theorem step_program_atNonRet {R : RL} (hR : R.Wf) {s : ArmState}
    (hπ : s.program = R.fb.program R.base) (h : AtNonRet R s) :
    (R.step s).program = R.fb.program R.base := by
  rw [step_atNonRet hR hπ h, ArmFoot.stepi_program, hπ]

/-! ## Layer 4b of the scope with calls on a linked machine -/

/-- `OpOutN` under `OkPriv` from runs under any condition (`opOut_okPriv`). -/
theorem opOutN_okPriv {R : RL} {s : ArmState} {mon : Mon} {c : MConf CV ArmState}
    (h : ∀ ls t', PRun Policy.arm R.step (fun _ _ => True) (s, mon) ls t' →
      OpOutN R (fun _ _ => True) (fun c => c.measure) (s, mon) c ls t')
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step (OkPriv R) (s, mon) ls t') :
    OpOutN R (OkPriv R) (fun c => c.measure) (s, mon) c ls t' := by
  rcases h ls t' (PRun.mono (fun _ _ _ => trivial) hr) with
    h | ⟨n, evs, c', t1, φ, hn, hpos, hs, hr1, hR1, hi'⟩ | h | h
  · exact .inl h
  · obtain ⟨t1', r1, -⟩ := PRun.split (ls.take n) (ls.drop n)
      (by rw [List.take_append_drop]; exact hr)
    obtain rfl := PRun.det (PRun.mono (fun _ _ _ => trivial) r1) hr1
    exact .inr (.inl ⟨n, evs, c', t1', φ, hn, hpos, hs, r1, hR1, hi'⟩)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

/-- **The per-item obligation of the scope with calls with the pc invariant** (`itemSim_lsC`):
a run ending inside an item ends at an unhooked line other than `ret`. On ranked configurations
(`μR`; the statement before #553 used a measure of the configuration only, which `MachBuffer`'s
layout falsifies: `ArmAllocBranch` module doc). -/
theorem itemSim_lsCN {R : RL} (hR : R.Wf) (hsc : MemScopeLSC R) :
    ItemSimN Policy.arm R.step (OkPriv R) (SrcStepR R) (RelQR R) (PauseR R) (μR R) (PrivA R)
      (AtNonRet R) := by
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
    rcases move_opR hR hqa hr with h | h
    · exact .inr (.inl (isOut_μR noGotoAt_move hk h))
    · exact .inr (.inr (.inr h))
  | @op _ k allocs its' _ _ vb i ops _ _ hvb hi hops hevs hfoot hst =>
    have hs : SrcStep R (OpC b k allocs its' m w) _ _ := .op hvb hi hops hevs hfoot hst
    rcases RelQ.op' hqa hs with ⟨hq, hA⟩ | ⟨rfl, vals, m', w', rfl⟩
    case inr => exact .inr (.inl (itemSimOut_retR hs (RkC.pos hk)))
    have uniq : ∀ vb' i', R.vc.blocks[b]? = some vb' → vb'.insts[k]? = some i' → i' = i :=
      fun vb' i' h1 h2 => by rw [hvb] at h1; cases h1; rw [hi] at h2; cases h2; rfl
    rcases hsc b vb k i hvb hi with hl | hbr | hls | ⟨info, rfl⟩
    · refine Or.imp_left Or.inl (opOutNR_of (noGotoAt_op hvb hi (noGoto_memFormL hl)) hk ?_)
      rcases hl with (h | h | ⟨ty, rt, rn, fl, rfl, hfo⟩ | ⟨ty, rt, rn, fl, rfl, hfo⟩) | hl | hl
      · exact opOutN_okPriv (fun ls t' hr => noev_opR hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ h) hr) hr
      · exact opOutN_okPriv (fun ls t' hr => fence_opR hR hq hA hs
          (fun vb' i' h1 h2 => (uniq vb' i' h1 h2).trans h) hr) hr
      · exact opOutN_okPriv (fun ls t' hr => oneEv_opR hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ ldar_form hfo) hr) hr
      · exact opOutN_okPriv (fun ls t' hr => oneEv_opR hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ stlr_form hfo) hr) hr
      · exact rmw_opR hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hl) hr
      · exact cas_opR hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hl) hr
    · exact Or.imp_left Or.inl
        (goto_opR hR hq hA hk hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hbr) hr)
    · exact Or.imp_left Or.inl (opOutNR_of (noGotoAt_op hvb hi (noGoto_ls hls)) hk
        (opOutN_okPriv (fun ls t' hr => oneEv_opR hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ lsForm_oneEv hls) hr) hr))
    · exact absurd (.inl ⟨b, k, allocs, its', m, w, vb, info, rfl, hvb, hi⟩) hP

/-- **The per-item obligation of the scope with calls on a machine agreeing with `R.step` at
`R`'s lines other than `ret`** (`ItemSimN.transfer`). -/
theorem itemSim_lsCL {R : RL} (hR : R.Wf) (hsc : MemScopeLSC R) {g : ArmState → ArmState}
    (hg : AgreesAt R g) :
    ItemSim Policy.arm g (OkPriv R) (SrcStepR R) (RelQR R) (PauseR R) (μR R) (PrivA R) := by
  refine (itemSim_lsCN hR hsc).transfer (π := R.fb.program R.base)
    (fun s hπ hn m => hg _ (by rw [setMem_program]; exact hπ) (atNonRet_setMem m hn))
    (fun s hπ hn m => step_program_atNonRet hR (by rw [setMem_program]; exact hπ)
      (atNonRet_setMem m hn)) ?_
  rintro ⟨s, mon⟩ ⟨c, r⟩ ⟨hqa, -⟩ hT
  match c, hqa, hT with
  | .ret vals m w, _, hT => exact absurd (.inl (.inl ⟨vals, m, w, rfl⟩)) hT
  | .halt w, _, hT => exact absurd (.inl (.inr (.inl ⟨w, rfl⟩))) hT
  | .run ⟨b, its, m, w⟩, hqa, _ =>
    obtain ⟨mt, hq⟩ := RelQ.q hqa
    exact (q_stRel hq).prog

/-- **Layer 4b of a caller on a linked machine** (module doc; `arm_alloc_refines_lsC` for every
machine `g` agreeing with `R.step` at `R`'s lines other than `ret`): every precise run of `g`
under `OkPriv` from a `Q`-related state realizes a run of the allocated code, its whole run or a
prefix whose last Arm state is related (`RelQ`) to a configuration where the code is done or
pauses at a call or a return. -/
theorem arm_alloc_refines_lsCL {R : RL} (hR : R.Wf) (hsc : MemScopeLSC R)
    {g : ArmState → ArmState} (hg : AgreesAt R g)
    {s : ArmState} {mon : Mon} {c : MConf CV ArmState} (hq : Q R s c) (hA : AInv R c)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm g (OkPriv R) (s, mon) ls t') :
    ∃ n trS cE ψ, n ≤ ls.length ∧ MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) c trS cE ∧
      ThreadRefine.Refines (· = ·) (PrivA R) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧
      (n = ls.length ∨ ∃ tE, PRun Policy.arm g (OkPriv R) (s, mon) (ls.take n) tE ∧
        RelQ R tE cE ∧ Pause R cE) := by
  obtain ⟨r, hrel⟩ := RelQR.of (t := (s, mon)) hq hA
  obtain ⟨n, trS, cE, ψ, hn, hs, href, hend⟩ :=
    refines_of_itemSimQ (itemSim_lsCL hR hsc hg) hr hrel
  exact ⟨n, trS, cE.1, ψ, hn, mtrun_of_srun (SRun.fst hs), href,
    hend.imp_right fun ⟨tE, h1, h2, h3⟩ => ⟨tE, h1, h2.1, h3⟩⟩

end Concurrency.ArmAllocThread

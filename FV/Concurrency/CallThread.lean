import FV.Concurrency.ArmAllocEntry
import FV.Concurrency.RealizeCompiled
import FV.Concurrency.CallCompose
import FV.Concurrency.ClifLift

/-!
# One compiled activation from its ABI entry, as a thread (T2h, #311, calls)

`RealizeCompiled.thread_compiledB` starts the Arm run after the prologue. For calls the callee's
activation starts at its ABI entry (the state after the caller's `bl`), so:

* `CompiledE env p RA cs`: the activation `RA` of a compiled CLIF function (`R.Wf`, the widest
  layer-4b scope `MemScopeLS`, no GOT-pinned calls), entered at its ABI entry `RA.s0`
  (`AbiCall`), with the pipeline facts (`Front`) at the state after the prologue, its stack
  probes writing outside the world (`ProbeF`, #581);
* **`thread_compiled_entry`**: every precise Arm run under `OkPriv` from the ABI entry realizes,
  on a prefix, a CLIF thread run from `cs` (`Refines Maps`, private set `PrivA RA`, the prefix's
  monitor pairs atomic), the prefix being the whole run, or ending where the CLIF thread stops,
  or ending where **the prefix itself drives the allocated code to its end** (`DoneBy`: a run of
  the allocated code from its entry configuration to `Done`, refined by exactly that Arm prefix;
  through `ThreadCompose.arm_isel_refinesE'`, which keeps the prefix length at layer 4b's end).
-/

namespace Concurrency.CallThread

open Arm ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine
  ArmAllocThread ThreadCompose RealizeCompiled E2E

/-- **A compiled activation entered at its ABI entry** (module doc). -/
structure CompiledE (env : Clif.Env) (p : Clif.Program) (RA : RL) (cs : Clif.State) : Prop where
  wf : RA.Wf
  scope : MemScopeLS RA
  gv : RA.gv = fun _ _ => False
  abi : ∃ ra, AbiCall RA.fb RA.base ra RA.s0
  front : Front env p RA cs (iterN RA.step (prologueLines RA.af.saves RA.af.frameSize RA.af.isCaller).length RA.s0)
  /-- the prologue's stack probes write outside the world (#581: new; holds for a frame below
  4 KiB, `ProbeF.of_small`) -/
  probe : ProbeF RA

/-- **The Arm prefix `P` drives the activation's allocated code to its end**: a run of the
allocated code from an entry configuration to `Done`, refined by `P`'s events. -/
def DoneBy (RA : RL) (P : List Lab) : Prop :=
  ∃ m₀ w₀ trM cE ψ, MTRun RA.vc RA.rf RA.sem ckeep (cEvs RA.F RA.ctx) (MConf.init RA.rf m₀ w₀)
    trM cE ∧ Done RA cE ∧
    Refines (· = ·) (PrivA RA) (MonPair (evTr P)) (conv trM) (conv (evTr P)) ψ

/-- **One compiled activation from its ABI entry** (module doc). -/
theorem thread_compiled_entry {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    (hc : CompiledE env p RA cs) {mon : Mon} {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm RA.step (OkPriv RA) (RA.s0, mon) ls t') :
    ∃ (k : Nat) (trS : List (List (Ev SKind BVal))) (t : TState) (ψ : Nat × Nat → Nat × Nat),
      k ≤ ls.length ∧ CRun env p (.run cs) trS t ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨ DoneBy RA (ls.take k)) := by
  obtain ⟨ra, hent⟩ := hc.abi
  obtain ⟨f, vc, ctx, st0, R, gn, bl, A, MR, slots, sb, syms, B0, args, m₀, w₀, H, hchk, hMR,
    hMRw, hX, hMem, hMRs, hreg, hprep, halloc, hB0, hcall, hfunc, hslots, hbody, hterm, hregs, hty,
    hsig, hmr, hargs, hq, hA⟩ := hc.front
  obtain ⟨nA, trM, cE, ψA, hnA, hM, hAr, hend⟩ :=
    arm_alloc_refines_entryQ hc.wf hc.scope hent hc.probe hq hA hr
  obtain ⟨k, trS, t, ψ, hk, hrun, href, hendk⟩ :=
    arm_isel_refinesE' (E := Done RA cE) hc.gv H hchk hMR hMRw hX hMem hMRs hreg hprep halloc hB0
      hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs hr hM hAr hend hnA
  have href' : Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS
      (conv (evTr (ls.take k))) ψ := by
    refine Refines.pairT_congr href fun a b _ hb => monPair_take hk ?_
    obtain ⟨hb1, -⟩ := evAt_isSome (show (evAt (conv (evTr (ls.take k))) (b.1, b.2)).isSome from hb)
    have := hb1; simp [conv, evTr] at this; omega
  refine ⟨k, trS, t, ψ, by omega, hrun, href', ?_⟩
  rcases hendk with h | ⟨rfl, h⟩ | h
  · exact .inl h
  · exact .inr (.inr ⟨m₀, w₀, trM, cE, ψA, hM, h, hAr⟩)
  · exact .inr (.inl h)


/-! ## The callee's contract in a linked thread -/

section linked
variable {α : Type}

/-- A source trace extended by event-free steps has the same events. -/
theorem evAt_prefix_nil {trS trS' : List (List α)} (hp : trS' <+: trS)
    (hd : ∀ e ∈ trS.drop trS'.length, e = []) (q : Nat × Nat) : evAt trS' q = evAt trS q := by
  obtain ⟨u, rfl⟩ := hp
  simp only [evAt]
  by_cases h : q.1 < trS'.length
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_append_right (by omega)]
    cases hu : u[q.1 - trS'.length]? with
    | none => rfl
    | some e =>
      have : e = [] := hd e (by simpa using List.mem_of_getElem? hu)
      subst this; rfl

end linked

/-- **A refinement of a trace refines its prefixes that drop only event-free steps.** -/
theorem refines_prefix_nil {K K' V : Type} {MK : K → K' → Prop} {P : Nat → Prop}
    {pairT : Nat × Nat → Nat × Nat → Prop} {trS trS' : List (List (Ev K V))}
    {trT : List (List (Ev K' V))} {ψ : Nat × Nat → Nat × Nat} (h : Refines MK P pairT trS trT ψ)
    (hp : trS' <+: trS) (hd : ∀ e ∈ trS.drop trS'.length, e = []) :
    Refines MK P pairT trS' trT ψ := by
  have e := evAt_prefix_nil hp hd
  have hj : ∀ j (hj : j < trS'.length), ∃ hj' : j < trS.length, trS'[j] = trS[j] := by
    intro j hj
    obtain ⟨u, rfl⟩ := hp
    exact ⟨by simp; omega, by rw [List.getElem_append_left hj]⟩
  exact {
    ev := fun p x hx => h.ev p x (by rw [← e]; exact hx)
    mono := fun p q hp hq hl => h.mono p q (by rw [← e]; exact hp) (by rw [← e]; exact hq) hl
    shared := fun p x hx => h.shared p x (by rw [← e]; exact hx)
    priv := fun p y hy hW hn => h.priv p y hy hW fun q hq => hn q (by rw [e]; exact hq)
    len := fun j hj' => by obtain ⟨h1, h2⟩ := hj j hj'; rw [h2]; exact h.len j h1
    pair := fun j hj' h2 => by
      obtain ⟨h1, h3⟩ := hj j hj'
      rw [h3] at h2
      exact h.pair j h1 h2
    pair_inv := fun p q hp hq hpq => h.pair_inv p q (by rw [← e]; exact hp) (by rw [← e]; exact hq) hpq }

theorem failState_program (rs : BitVec 5) (s : ArmState) : (failState rs s).program = s.program := by
  simp only [failState, write_pc, write_gpr_zr]
  split <;> simp [write_gpr, w_program]

/-- **Machines agreeing on the states holding a program `π`**: a precise run of `f` from such a
state, `g` keeping `π`, is a run of `g`. -/
theorem prun_transfer {P : Policy} {f g : ArmState → ArmState} {ok : ArmState → Lab → Prop}
    {π : Arm.Program} (hfg : ∀ s, s.program = π → f s = g s)
    (hg : ∀ s, s.program = π → (g s).program = π) :
    ∀ {t t' : ArmState × Mon} {ls : List Lab}, t.1.program = π → PRun P f ok t ls t' →
      PRun P g ok t ls t'
  | _, _, _, _, .nil => .nil
  | (s, mon), _, _, hπ, .cons hs hpr ho hr => by
    simp only at hπ
    have hm : ∀ m, (ArmFoot.setMem m s).program = π := fun m => by rw [ArmFoot.setMem_program]; exact hπ
    cases hs with
    | @exec _ _ evs hk hag hfp hsucc =>
      have hfp' : Footprint g s evs := fun m hm' => by
        rw [← hfg _ (hm m), ← hfg _ (hm _)]; exact hfp m hm'
      have hstep := TStep.exec (f := g) (P := P) (mon := mon) hk hag hfp' hsucc
      rw [← hfg _ (hm _)] at hstep
      exact .cons hstep hpr ho (prun_transfer hfg hg (by
        simp only; rw [hfg _ (hm _)]; exact hg _ (hm _)) hr)
    | xfail hc hfail herr hsp =>
      exact .cons (TStep.xfail hc hfail herr hsp) hpr ho (prun_transfer hfg hg (by
        simp only; rw [failState_program]; exact hπ) hr)

/-- **Runs without store-exclusive-release instructions are exclusive-closed**: when no state
holding the program `π` is at a store exclusive with release, and the machine keeps `π`, no
precise run from such a state has a `relXW` event. -/
theorem xClosed_noStx {P : Policy} {f : ArmState → ArmState} {ok : ArmState → Lab → Prop}
    {π : Arm.Program} (hf : ∀ s, s.program = π → (f s).program = π)
    (hx : ∀ s, s.program = π → ∀ rs rn, cls s ≠ .stx true rs rn) :
    ∀ {t t' : ArmState × Mon} {ls : List Lab}, t.1.program = π → PRun P f ok t ls t' →
      ∀ l ∈ ls, ∀ e ∈ l.evs, e.k ≠ .relXW
  | _, _, _, _, .nil => fun _ h => absurd h List.not_mem_nil
  | (s, mon), _, _, hπ, .cons (t1 := t1) hs _ _ hr => by
    simp only at hπ
    have hm : ∀ m, (ArmFoot.setMem m s).program = π := fun m => by rw [ArmFoot.setMem_program]; exact hπ
    intro l hl e he hk
    rcases List.mem_cons.mp hl with rfl | hl'
    · cases hs with
      | exec hk' =>
        have := hk'.1 e he
        rw [hk] at this
        cases hc : cls s <;> rw [hc] at this <;> simp [Cls.kind, AKind.dir] at this
        rename_i rel rs rn
        cases rel
        · simp [Cls.kind, AKind.dir] at this
        · exact hx s hπ rs rn hc
      | xfail => exact absurd he List.not_mem_nil
    · have hπ1 : t1.1.program = π := by
        cases hs with
        | exec => simp only; exact hf _ (hm _)
        | xfail => simp only; rw [failState_program]; exact hπ
      exact xClosed_noStx hf hx hπ1 hr l hl' e he hk

/-- Runs without `relXW` events are exclusive-closed. -/
theorem xClosed_runs {ls : List Lab} (h : ∀ l ∈ ls, ∀ e ∈ l.evs, e.k ≠ .relXW) :
    CallCompose.XClosed (evTr ls) := CallCompose.xClosed_of fun b y hy => by
  simp only [evAt, evTr, List.getElem?_map] at hy
  cases hb : ls[b.1]? with
  | none => rw [hb] at hy; cases hy
  | some l =>
    rw [hb] at hy
    simp only [Option.map_some, Option.bind_some] at hy
    exact h l (List.mem_of_getElem? hb) y (List.mem_of_getElem? hy)

/-- **The end of a callee's realized prefix** (in the caller's thread, the extra suspended callers
`ext`): the prefix drives the callee's allocated code to its end (`DoneBy`), or the CLIF thread is
in the callee's activation, lifted, where it stops or returns. -/
def CalleeEnd (env : Clif.Env) (p : Clif.Program) (RA : RL)
    (ext : List (Clif.Frame × List Clif.ValueId)) (P : List Lab) (d : TState) : Prop :=
  DoneBy RA P ∨ ∃ s, d = .run (ClifLift.pushC ext s) ∧
    (Stop env p (.run s) ∨ ∃ v, CStep env p (.run s) [] (.ret v))

/-- **The function contract of a compiled callee in a linked thread**: the thread's machine `M` is
the activation's `RA.step` on the states holding its program (which `RA.step` keeps); entered at
the ABI entry `RA.s0` with the CLIF state of its entry under the caller's suspended frames `ext`,
every precise run under `OkPriv` realizes, through the callee's compiled-code refinement
(`thread_compiled_entry`, lifted by `ClifLift.crun_pushC`), a prefix that is the whole run or ends
at `CalleeEnd`; the callee's precise runs exclusive-closed (`hX`; e.g. `xClosed_noStx`). -/
theorem funReal_callee {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    (hc : CompiledE env p RA cs) (ext : List (Clif.Frame × List Clif.ValueId))
    {M : ArmState → ArmState} (hM : ∀ s, s.program = RA.s0.program → M s = RA.step s)
    (hP : ∀ s, s.program = RA.s0.program → (RA.step s).program = RA.s0.program)
    (hX : ∀ mon ls t', PRun Policy.arm RA.step (OkPriv RA) (RA.s0, mon) ls t' →
      CallCompose.XClosed (evTr ls)) (mon : Mon) :
    CallCompose.FunReal env p (PrivA RA) M (OkPriv RA) (fun _ _ _ _ => False)
      (CalleeEnd env p RA ext) (RA.s0, mon) (.run (ClifLift.pushC ext cs)) := by
  intro ls t' hr
  have hr' := prun_transfer (π := RA.s0.program) hM hP rfl hr
  obtain ⟨k, trS, t, ψ, hk, hrun, href, hend⟩ := thread_compiled_entry hc hr'
  obtain ⟨trS', t2, hrun2, hpre, hdrop, -, hrunE, hretE⟩ := ClifLift.crun_pushC (ext := ext) hrun
  obtain ⟨v, hv, -⟩ := CallCompose.take_prun hr' k
  refine ⟨k, t2, ⟨hk, trS', ψ, hrun2, hX mon _ _ hv, refines_prefix_nil href hpre hdrop⟩, ?_⟩
  rcases hend with h | h | h
  · exact .inl h
  · right; left; right
    cases t with
    | run s' =>
      obtain ⟨rfl, -⟩ := hrunE s' rfl
      exact ⟨s', rfl, .inl h⟩
    | ret w =>
      obtain ⟨s', rfl, hc'⟩ := hretE w rfl
      exact ⟨s', rfl, .inr ⟨w, hc'⟩⟩
  · exact .inr (.inl (.inl h))

end Concurrency.CallThread

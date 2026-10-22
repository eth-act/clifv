import FV.Concurrency.ThreadCompose
import FV.Concurrency.ArmAllocMove
import FV.Concurrency.PrivCoh
import FV.Concurrency.ArmAllocBranch
import FV.Concurrency.ArmAllocLS

/-!
# The program-level contract for compiled code (T2k, #311)

`ProgE2E.Realizes` (the CLIF threads' traces are realized by the Arm threads' traces) for Arm
threads running **compiled** functions, from the per-thread layers:

* `crun_states`: a CLIF thread run (`CRun`) as a state function (the shape of
  `ThreadRefine.realizes_of_threads`);
* `Refines.pairT_congr`, `monPair_take`: the atomic pairs of a refinement only matter at the
  images; the monitor pairs of a prefix of an Arm trace are those of the trace there;
* `Compiled`: what the pipeline gives one thread (`RA` the activation of a compiled function:
  register level `RL.Wf`, the memory scope, no GOT-pinned calls;
  layer 2's driver hypothesis and checks for the CLIF function; the CLIF entry state `cs` related
  to the entry world, and `Q ∧ AInv` at the allocated code's entry configuration for the Arm state
  `s`);
* `thread_compiled`: every precise Arm run from `s` under `OkPriv` (the thread's private reads
  return its own bytes) realizes, on a prefix, a CLIF thread run from `cs`: layer 4b with moves
  (`arm_alloc_refines_mv`) composed with layers 2, 3, 4a (`arm_isel_refinesE`), the target's
  atomic pairs its own monitor pairs; the prefix is all of the run, or the CLIF thread stops, or
  the allocated code is done (returned, trapped, undefined);
* **`realizes_compiled`**: for `n` such threads, every execution of the Arm traces (the prefixes
  of `thread_compiled`) whose `rmw` is the threads' monitor pairs and in which no thread accesses
  another's private set (its frame) is `Realizes`d by CLIF threads from the `cs i` running
  `CStep` (`PrivCoh.realizes_of_threads_priv`, a private set per thread);
* `CompiledLS`, `thread_compiledLS`, `realizes_compiledLS`: the same for functions with LL/SC
  loops, block-ending branches and plain loads/stores (`MemScopeLS`, `arm_alloc_refines_ls`);
  the `Compiled` and `CompiledB` versions are corollaries.
-/

namespace Concurrency.RealizeCompiled

open Arm ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine
  ArmAllocThread ThreadCompose

/-! ## Runs as state functions -/

/-- **A CLIF thread run as a state function.** -/
theorem crun_states {env : Clif.Env} {p : Clif.Program} :
    ∀ {t t' : TState} {tr : List (List (Ev SKind BVal))}, CRun env p t tr t' →
      ∃ st : Nat → TState, st 0 = t ∧
        (∀ j (h : j < tr.length), CStep env p (st j) tr[j] (st (j + 1))) ∧ st tr.length = t'
  | t, _, _, .nil => ⟨fun _ => t, rfl, fun j h => absurd h (Nat.not_lt_zero _), rfl⟩
  | t, _, _, .cons (t' := t1) hs hr => by
    obtain ⟨st, h0, hst, hend⟩ := crun_states hr
    refine ⟨fun j => if j = 0 then t else st (j - 1), by simp, fun j h => ?_, by simpa using hend⟩
    cases j with
    | zero => simpa [h0] using hs
    | succ j => simpa using hst j (by simpa using h)

/-! ## Atomic pairs -/

variable {K K' V : Type}

/-- **The atomic pairs of a refinement matter only at the target's events.** -/
theorem Refines.pairT_congr {MK : K → K' → Prop} {P : Nat → Prop}
    {pairT pairT' : Nat × Nat → Nat × Nat → Prop} {trS : List (List (Ev K V))}
    {trT : List (List (Ev K' V))} {ψ : Nat × Nat → Nat × Nat} (h : Refines MK P pairT trS trT ψ)
    (hp : ∀ a b, (evAt trT a).isSome → (evAt trT b).isSome → (pairT a b ↔ pairT' a b)) :
    Refines MK P pairT' trS trT ψ where
  ev := h.ev
  mono := h.mono
  shared := h.shared
  priv := h.priv
  len := h.len
  pair j hj h2 := by
    have h0 : (evAt trS (j, 0)).isSome := by
      simp only [evAt, List.getElem?_eq_getElem hj, Option.bind_some]
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    have h1 : (evAt trS (j, 1)).isSome := by
      simp only [evAt, List.getElem?_eq_getElem hj, Option.bind_some]
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    exact (hp _ _ (h.img h0) (h.img h1)).1 (h.pair j hj h2)
  pair_inv p q hp' hq hpr :=
    h.pair_inv p q hp' hq ((hp _ _ (h.img hp') (h.img hq)).2 hpr)

theorem evTr_take (ls : List Lab) (n : Nat) : evTr (ls.take n) = (evTr ls).take n := by
  simp [evTr, List.map_take]

/-- **The monitor pairs of a prefix of an Arm trace** ending inside a shorter prefix are the
shorter prefix's. -/
theorem monPair_take {ls : List Lab} {n k : Nat} (hk : k ≤ n) {a b : Nat × Nat} (hb : b.1 < k) :
    MonPair (evTr (ls.take n)) a b ↔ MonPair (evTr (ls.take k)) a b := by
  have e : ∀ q : Nat × Nat, q.1 < k →
      evAt (evTr (ls.take n)) q = evAt (evTr (ls.take k)) q := fun q hq => by
    rw [evTr_take, evTr_take, evAt_take_of_lt (by omega), evAt_take_of_lt hq]
  have hlt : ∀ q : Nat × Nat, Lt q b → q.1 < k := fun q h => by
    rcases h with h | ⟨h, -⟩ <;> omega
  constructor
  · rintro ⟨⟨x, hx, hxk⟩, ⟨y, hy, hyk⟩, hab, hbt⟩
    refine ⟨⟨x, by rw [← e a (hlt a hab)]; exact hx, hxk⟩, ⟨y, by rw [← e b hb]; exact hy, hyk⟩, hab,
      fun q z h1 h2 hz => hbt q z h1 h2 (by rw [e q (hlt q h2)]; exact hz)⟩
  · rintro ⟨⟨x, hx, hxk⟩, ⟨y, hy, hyk⟩, hab, hbt⟩
    refine ⟨⟨x, by rw [e a (hlt a hab)]; exact hx, hxk⟩, ⟨y, by rw [e b hb]; exact hy, hyk⟩, hab,
      fun q z h1 h2 hz => hbt q z h1 h2 (by rw [← e q (hlt q h2)]; exact hz)⟩

/-! ## One compiled thread -/

/-- The pipeline facts of one compiled thread (`Compiled.front`): the CLIF function `f`
(lowering `vc`, `prepare`d to `RA.vc`, allocated as `RA.rf`), layer 2's driver hypothesis and
checks, the CLIF entry state `cs` (block 0, arguments `args`, related by `MR` to the entry world
`w₀`), and `Q ∧ AInv` at the allocated code's entry configuration for the Arm state `s`. -/
abbrev Front (env : Clif.Env) (p : Clif.Program) (RA : RL) (cs : Clif.State) (s : ArmState) :
    Prop :=
  ∃ (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (R : Reg → Reg)
    (gn : Nat → Nat) (bl : List BLow) (A : Nat → Nat → List Clif.ValueId) (MR : MemRelT)
    (slots : List (Clif.SlotId × Nat)) (sb : Nat) (syms : String → Option Nat)
    (B0 : Clif.Block) (args : List Clif.Val) (m₀ : Loc → CV) (w₀ : ArmState),
    DriverHyp f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) MR env p ∧
    threadCheckBl f bl = true ∧ MemRelOk RA.F sb syms f MR ∧
    (∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w) ∧
    TlsMemFree RA.X ∧ MemRefines RA.F sb syms (csem RA.F RA.ctx RA.X) ∧ MRStable RA.F MR ∧
    (∀ off, ArgLoc.stack off ∉ locsOf f.sig) ∧ prepCheck vc RA.vc = true ∧
    checkAlloc RA.vc RA.rf = .ok () ∧
    f.blocks[0]? = some B0 ∧ cs.callers = [] ∧ cs.frame.func = f ∧ cs.frame.slots = slots ∧
    cs.frame.body = B0.body ∧ cs.frame.term = B0.term ∧
    Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs ∧
    args.map (·.ty) = B0.params.map (·.2) ∧ args.map (·.ty) = f.sig.params.map (·.ty) ∧
    MR slots cs.mem w₀ ∧ ArgsAtEntry RA.F f.sig args w₀ ∧
    Q RA s (MConf.init RA.rf m₀ w₀) ∧ AInv RA (MConf.init RA.rf m₀ w₀)

/-- **What the pipeline gives one thread** (module doc): the activation `RA` of the compiled
CLIF function, whose instructions are memory forms (`MemScope`), and its pipeline facts
(`Front`). -/
structure Compiled (env : Clif.Env) (p : Clif.Program) (RA : RL) (cs : Clif.State)
    (s : ArmState) : Prop where
  wf : RA.Wf
  scope : MemScope RA
  gv : RA.gv = fun _ _ => False
  front : Front env p RA cs s

/-- `Compiled` for functions with LL/SC loops and block-ending branches (`MemScopeB`, layer 4b
`arm_alloc_refines_br`). -/
structure CompiledB (env : Clif.Env) (p : Clif.Program) (RA : RL) (cs : Clif.State)
    (s : ArmState) : Prop where
  wf : RA.Wf
  scope : MemScopeB RA
  gv : RA.gv = fun _ _ => False
  front : Front env p RA cs s

/-- `Compiled` for functions with LL/SC loops, block-ending branches and plain loads/stores
(`MemScopeLS`, layer 4b `arm_alloc_refines_ls`). -/
structure CompiledLS (env : Clif.Env) (p : Clif.Program) (RA : RL) (cs : Clif.State)
    (s : ArmState) : Prop where
  wf : RA.Wf
  scope : MemScopeLS RA
  gv : RA.gv = fun _ _ => False
  front : Front env p RA cs s

theorem CompiledB.toLS {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    {s : ArmState} (hc : CompiledB env p RA cs s) : CompiledLS env p RA cs s :=
  ⟨hc.wf, memScopeLS_of_memScopeB hc.scope, hc.gv, hc.front⟩

theorem Compiled.toB {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    {s : ArmState} (hc : Compiled env p RA cs s) : CompiledB env p RA cs s :=
  ⟨hc.wf, memScopeB_of_memScopeL (memScopeL_of_memScope hc.scope), hc.gv, hc.front⟩

/-- **One compiled thread, with loops, branches and plain loads/stores** (as `thread_compiled`,
for `CompiledLS`). -/
theorem thread_compiledLS {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    {s : ArmState} (hc : CompiledLS env p RA cs s) {mon : Mon} {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm RA.step (OkPriv RA) (s, mon) ls t') :
    ∃ (k : Nat) (trS : List (List (Ev SKind BVal))) (st : Nat → TState) (ψ : Nat × Nat → Nat × Nat),
      k ≤ ls.length ∧ st 0 = .run cs ∧
      (∀ j (h : j < trS.length), CStep env p (st j) trS[j] (st (j + 1))) ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p (st trS.length) ∨
        ∃ m₀ w₀ trM cE, MTRun RA.vc RA.rf RA.sem ckeep (cEvs RA.F RA.ctx) (MConf.init RA.rf m₀ w₀)
          trM cE ∧ Done RA cE) := by
  obtain ⟨f, vc, ctx, st0, R, gn, bl, A, MR, slots, sb, syms, B0, args, m₀, w₀, H, hchk, hMR,
    hMRw, hX, hMem, hMRs, hreg, hprep, halloc, hB0, hcall, hfunc, hslots, hbody, hterm, hregs, hty,
    hsig, hmr, hargs, hq, hA⟩ := hc.front
  obtain ⟨nA, trM, cE, ψA, hnA, hM, hAr, hend⟩ := arm_alloc_refines_ls hc.wf hc.scope hq hA hr
  obtain ⟨k, trS, t, ψ, hk, hrun, href, hendk⟩ :=
    arm_isel_refinesE (E := Done RA cE) hc.gv H hchk hMR hMRw hX hMem hMRs hreg hprep halloc hB0
      hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs hr hM hAr hend hnA
  obtain ⟨st, h0, hst, hlast⟩ := crun_states hrun
  have href' : Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS
      (conv (evTr (ls.take k))) ψ := by
    refine Refines.pairT_congr href fun a b _ hb => monPair_take hk ?_
    obtain ⟨hb1, -⟩ := evAt_isSome (show (evAt (conv (evTr (ls.take k))) (b.1, b.2)).isSome from hb)
    have := hb1; simp [conv, evTr] at this; omega
  refine ⟨k, trS, st, ψ, by omega, h0, hst, href', ?_⟩
  rcases hendk with h | h | h
  · exact .inl h
  · exact .inr (.inr ⟨m₀, w₀, trM, cE, hM, h⟩)
  · exact .inr (.inl (hlast ▸ h))

/-- **One compiled thread, with loops and branches** (as `thread_compiled`, for `CompiledB`). -/
theorem thread_compiledB {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    {s : ArmState} (hc : CompiledB env p RA cs s) {mon : Mon} {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm RA.step (OkPriv RA) (s, mon) ls t') :
    ∃ (k : Nat) (trS : List (List (Ev SKind BVal))) (st : Nat → TState) (ψ : Nat × Nat → Nat × Nat),
      k ≤ ls.length ∧ st 0 = .run cs ∧
      (∀ j (h : j < trS.length), CStep env p (st j) trS[j] (st (j + 1))) ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p (st trS.length) ∨
        ∃ m₀ w₀ trM cE, MTRun RA.vc RA.rf RA.sem ckeep (cEvs RA.F RA.ctx) (MConf.init RA.rf m₀ w₀)
          trM cE ∧ Done RA cE) :=
  thread_compiledLS hc.toLS hr

/-- **One compiled thread** (module doc): a precise Arm run under `OkPriv` from `s` realizes, on
its first `k` steps, a CLIF thread run from `cs`, with `Refines Maps` (private set `PrivA RA`,
the Arm prefix's monitor pairs atomic); the prefix is the whole run, or the CLIF thread stops, or
the allocated code is done. -/
theorem thread_compiled {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    {s : ArmState} (hc : Compiled env p RA cs s) {mon : Mon} {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm RA.step (OkPriv RA) (s, mon) ls t') :
    ∃ (k : Nat) (trS : List (List (Ev SKind BVal))) (st : Nat → TState) (ψ : Nat × Nat → Nat × Nat),
      k ≤ ls.length ∧ st 0 = .run cs ∧
      (∀ j (h : j < trS.length), CStep env p (st j) trS[j] (st (j + 1))) ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p (st trS.length) ∨
        ∃ m₀ w₀ trM cE, MTRun RA.vc RA.rf RA.sem ckeep (cEvs RA.F RA.ctx) (MConf.init RA.rf m₀ w₀)
          trM cE ∧ Done RA cE) :=
  thread_compiledB hc.toB hr

/-! ## The program -/

/-- The private set of thread `i` of `n` compiled threads: its activation's (`PrivA`). -/
def PrivN (n : Nat) (RA : Nat → RL) (i l : Nat) : Prop := i < n ∧ PrivA (RA i) l

/-- **The contract for `n` compiled threads, with loops, branches and plain loads/stores** (as
`realizes_compiled`, for `CompiledLS`). -/
theorem realizes_compiledLS {n : Nat} {env : Clif.Env} {p : Clif.Program} {RA : Nat → RL}
    {cs : Nat → Clif.State} {sA : Nat → ArmState}
    (hc : ∀ i < n, CompiledLS env p (RA i) (cs i) (sA i))
    {mon : Nat → Mon} {ls : Nat → List Lab} {t' : Nat → ArmState × Mon}
    (hr : ∀ i < n, PRun Policy.arm (RA i).step (OkPriv (RA i)) (sA i, mon i) (ls i) (t' i)) :
    ∃ k : Nat → Nat, (∀ i < n, k i ≤ (ls i).length) ∧
      ∀ (PA : Traces ProgE2E.AState AKind BVal) (locsA locsC : List (Nat × Nat)) (MA0 MC0 : Bytes)
        (rfA coA rmwA : Rel PEv), PA.n = n →
        (∀ i < n, PA.tr i = conv (evTr ((ls i).take (k i)))) →
        (PA.exec locsA rfA coA rmwA).Wf →
        (∀ i < n, ∀ a b, rmwA (.thr i a.1 a.2) (.thr i b.1 b.2) ↔
          MonPair (evTr ((ls i).take (k i))) a b) →
        locsC <+: locsA →
        (∀ q (h : q < locsA.length), locsC.length ≤ q → ∃ j, PrivN n RA j (locsA[q]).1) →
        (∀ q (h : q < locsC.length),
          bytesI.get MA0 (locsC[q]).1 (locsC[q]).2 = bytesI.get MC0 (locsC[q]).1 (locsC[q]).2) →
        (∀ i < n, ∀ j < n, j ≠ i → ∀ q x, evAt (PA.tr i) q = some x → x.dir ≠ .F →
          ¬ PrivA (RA j) x.loc) →
        ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = n ∧
          (∀ i < n, PC.st i 0 = .run (cs i)) ∧ PC.Runs (CStep env p) ∧
          Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ (fun _ _ _ => True) := by
  classical
  have hth : ∀ i (hi : i < n), ∃ (k : Nat) (trS : List (List (Ev SKind BVal))) (st : Nat → TState)
      (ψ : Nat × Nat → Nat × Nat), k ≤ (ls i).length ∧
      st 0 = .run (cs i) ∧ (∀ j (h : j < trS.length), CStep env p (st j) trS[j] (st (j + 1))) ∧
      Refines Maps (PrivA (RA i)) (MonPair (evTr ((ls i).take k))) trS
        (conv (evTr ((ls i).take k))) ψ := fun i hi => by
    obtain ⟨k, trS, st, ψ, hk, h0, hst, href, -⟩ := thread_compiledLS (hc i hi) (hr i hi)
    exact ⟨k, trS, st, ψ, hk, h0, hst, href⟩
  let k : Nat → Nat := fun i => if hi : i < n then Classical.choose (hth i hi) else 0
  have hk : ∀ i (hi : i < n), ∃ (trS : List (List (Ev SKind BVal))) (st : Nat → TState)
      (ψ : Nat × Nat → Nat × Nat), k i ≤ (ls i).length ∧
      st 0 = .run (cs i) ∧ (∀ j (h : j < trS.length), CStep env p (st j) trS[j] (st (j + 1))) ∧
      Refines Maps (PrivA (RA i)) (MonPair (evTr ((ls i).take (k i)))) trS
        (conv (evTr ((ls i).take (k i)))) ψ := fun i hi => by
    simp only [k, hi, dite_true]
    exact Classical.choose_spec (hth i hi)
  refine ⟨k, fun i hi => by obtain ⟨_, _, _, h, -⟩ := hk i hi; exact h, ?_⟩
  intro PA locsA locsC MA0 MC0 rfA coA rmwA hn htr hwf hrmw hlocs hpriv0 hval0 hdisj
  obtain ⟨PC, φ, hPn, hs0, hruns, hreal⟩ := PrivCoh.realizes_of_threads_priv (T := CStep env p)
    (s0 := fun i => .run (cs i)) (PrivT := PrivN n RA)
    (pairT := fun i => MonPair (evTr ((ls i).take (k i)))) (Obs := fun _ _ _ => True)
    hwf (fun i hi => hrmw i (hn ▸ hi)) hlocs hpriv0 hval0 (fun i hi => by
      have hi' : i < n := hn ▸ hi
      obtain ⟨trS, st, ψ, -, h0, hst, href⟩ := hk i hi'
      refine ⟨trS, st, ψ, h0, hst, ?_, ?_, trivial⟩
      · rw [htr i hi']
        exact Refines.congr href (fun _ _ h => h) fun l => ⟨fun h => ⟨hi', h⟩, fun h => h.2⟩
      · intro q x hx hF j ⟨hj, hP⟩
        by_cases e : j = i
        · subst e; exact href.shared q x hx hF hP
        · obtain ⟨y, hy, -, hd, hl, -⟩ := href.ev q x hx
          rw [← htr i hi'] at hy
          exact hdisj i hi' j hj e _ y hy (by rw [hd]; exact hF) (hl ▸ hP))
  exact ⟨PC, φ, hPn.trans hn, fun i _ => hs0 i, hruns, hreal⟩

/-- **The contract for `n` compiled threads, with loops and branches** (as `realizes_compiled`,
for `CompiledB`). -/
theorem realizes_compiledB {n : Nat} {env : Clif.Env} {p : Clif.Program} {RA : Nat → RL}
    {cs : Nat → Clif.State} {sA : Nat → ArmState}
    (hc : ∀ i < n, CompiledB env p (RA i) (cs i) (sA i))
    {mon : Nat → Mon} {ls : Nat → List Lab} {t' : Nat → ArmState × Mon}
    (hr : ∀ i < n, PRun Policy.arm (RA i).step (OkPriv (RA i)) (sA i, mon i) (ls i) (t' i)) :
    ∃ k : Nat → Nat, (∀ i < n, k i ≤ (ls i).length) ∧
      ∀ (PA : Traces ProgE2E.AState AKind BVal) (locsA locsC : List (Nat × Nat)) (MA0 MC0 : Bytes)
        (rfA coA rmwA : Rel PEv), PA.n = n →
        (∀ i < n, PA.tr i = conv (evTr ((ls i).take (k i)))) →
        (PA.exec locsA rfA coA rmwA).Wf →
        (∀ i < n, ∀ a b, rmwA (.thr i a.1 a.2) (.thr i b.1 b.2) ↔
          MonPair (evTr ((ls i).take (k i))) a b) →
        locsC <+: locsA →
        (∀ q (h : q < locsA.length), locsC.length ≤ q → ∃ j, PrivN n RA j (locsA[q]).1) →
        (∀ q (h : q < locsC.length),
          bytesI.get MA0 (locsC[q]).1 (locsC[q]).2 = bytesI.get MC0 (locsC[q]).1 (locsC[q]).2) →
        (∀ i < n, ∀ j < n, j ≠ i → ∀ q x, evAt (PA.tr i) q = some x → x.dir ≠ .F →
          ¬ PrivA (RA j) x.loc) →
        ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = n ∧
          (∀ i < n, PC.st i 0 = .run (cs i)) ∧ PC.Runs (CStep env p) ∧
          Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ (fun _ _ _ => True) :=
  realizes_compiledLS (fun i hi => (hc i hi).toLS) hr

/-- **The contract for `n` compiled threads** (module doc). Each thread `i` runs the compiled code
of `Compiled env p (RA i) (cs i) (sA i)` with a precise Arm run `ls i` under `OkPriv`; `k i` is
the prefix `thread_compiled` realizes. Every execution of these prefixes (well formed, its `rmw`
the threads' monitor pairs, its initial locations beyond the CLIF ones private to some thread,
the CLIF ones with the same initial bytes) in which no thread's events touch another thread's
private set is realized by CLIF threads from the `cs i` (`Realizes`, any outcome). -/
theorem realizes_compiled {n : Nat} {env : Clif.Env} {p : Clif.Program} {RA : Nat → RL}
    {cs : Nat → Clif.State} {sA : Nat → ArmState} (hc : ∀ i < n, Compiled env p (RA i) (cs i) (sA i))
    {mon : Nat → Mon} {ls : Nat → List Lab} {t' : Nat → ArmState × Mon}
    (hr : ∀ i < n, PRun Policy.arm (RA i).step (OkPriv (RA i)) (sA i, mon i) (ls i) (t' i)) :
    ∃ k : Nat → Nat, (∀ i < n, k i ≤ (ls i).length) ∧
      ∀ (PA : Traces ProgE2E.AState AKind BVal) (locsA locsC : List (Nat × Nat)) (MA0 MC0 : Bytes)
        (rfA coA rmwA : Rel PEv), PA.n = n →
        (∀ i < n, PA.tr i = conv (evTr ((ls i).take (k i)))) →
        (PA.exec locsA rfA coA rmwA).Wf →
        (∀ i < n, ∀ a b, rmwA (.thr i a.1 a.2) (.thr i b.1 b.2) ↔
          MonPair (evTr ((ls i).take (k i))) a b) →
        locsC <+: locsA →
        (∀ q (h : q < locsA.length), locsC.length ≤ q → ∃ j, PrivN n RA j (locsA[q]).1) →
        (∀ q (h : q < locsC.length),
          bytesI.get MA0 (locsC[q]).1 (locsC[q]).2 = bytesI.get MC0 (locsC[q]).1 (locsC[q]).2) →
        (∀ i < n, ∀ j < n, j ≠ i → ∀ q x, evAt (PA.tr i) q = some x → x.dir ≠ .F →
          ¬ PrivA (RA j) x.loc) →
        ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = n ∧
          (∀ i < n, PC.st i 0 = .run (cs i)) ∧ PC.Runs (CStep env p) ∧
          Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ (fun _ _ _ => True) :=
  realizes_compiledB (fun i hi => (hc i hi).toB) hr

/-! ## Executions without reads -/

/-- A strict total order on program events (initial writes first, then thread, step, event). -/
def PEvLt : PEv → PEv → Prop
  | .init q, .init q' => q < q'
  | .init _, .thr .. => True
  | .thr .., .init _ => False
  | .thr i j k, .thr i' j' k' => i < i' ∨ (i = i' ∧ (j < j' ∨ (j = j' ∧ k < k')))

/-- Coherence of an execution of `P` without initial locations: the writes of a location in
`PEvLt` order. -/
def coW {σ K : Type} (P : Traces σ K BVal) (a b : PEv) : Prop :=
  (P.exec [] (fun _ _ => False) (fun _ _ => False) (fun _ _ => False)).dir a = .W ∧
  (P.exec [] (fun _ _ => False) (fun _ _ => False) (fun _ _ => False)).dir b = .W ∧
  (P.exec [] (fun _ _ => False) (fun _ _ => False) (fun _ _ => False)).loc a =
    (P.exec [] (fun _ _ => False) (fun _ _ => False) (fun _ _ => False)).loc b ∧ PEvLt a b

/-- **Traces without reads have a well-formed execution**: no initial locations, no `rf`, no
`rmw`, the writes of each location in `PEvLt` order. -/
theorem wf_noReads {σ K : Type} (P : Traces σ K BVal)
    (hR : ∀ e x, P.evAt e = some x → x.dir ≠ .R) :
    (P.exec [] (fun _ _ => False) (coW P) (fun _ _ => False)).Wf where
  po_irrefl a := PEv.po_irrefl a
  po_trans _ _ _ := PEv.po_trans
  po_tid _ _ := PEv.po_tid
  po_total _ _ := PEv.po_total
  rf_dir _ _ h := h.elim
  rf_loc _ _ h := h.elim
  rf_func _ _ _ h := h.elim
  rf_total b h := by
    exfalso
    cases b with
    | init q => simp [Traces.exec] at h
    | thr i j k =>
      simp only [Traces.exec] at h
      split at h
      · exact hR _ _ (by assumption) h
      · cases h
  co_dir _ _ h := ⟨h.1, h.2.1⟩
  co_loc _ _ h := h.2.2.1
  co_irrefl a h := by
    have := h.2.2.2
    cases a <;> simp [PEvLt] at this
  co_trans a b c h1 h2 := ⟨h1.1, h2.2.1, h1.2.2.1.trans h2.2.2.1, by
    have e1 := h1.2.2.2
    have e2 := h2.2.2.2
    cases a <;> cases b <;> cases c <;> simp only [PEvLt] at e1 e2 ⊢ <;> omega⟩
  co_total a b ha hb hl hne := by
    have : PEvLt a b ∨ PEvLt b a := by
      cases a <;> cases b <;> simp only [PEvLt, ne_eq, PEv.init.injEq, PEv.thr.injEq,
        reduceCtorEq, not_false_eq_true, true_or, or_true] at hne ⊢ <;> omega
    rcases this with h | h
    · exact .inl ⟨ha, hb, hl, h⟩
    · exact .inr ⟨hb, ha, hl.symm, h⟩
  rmw_dir _ _ h := h.elim
  rmw_loc _ _ h := h.elim
  rmw_po _ _ h := h.elim
  rmw_imm _ _ _ h := h.elim

end Concurrency.RealizeCompiled

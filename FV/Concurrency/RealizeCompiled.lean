import FV.Concurrency.ThreadCompose
import FV.Concurrency.ArmAllocMove
import FV.Concurrency.PrivCoh
import FV.Concurrency.ArmAllocBranch
import FV.Concurrency.ArmAllocLS
import FV.Concurrency.ThreadProgress
import FV.Concurrency.ArmAllocPause

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
* **The whole run** (T2j, #473): `thread_compiledLS_full`, **`realizes_compiledLS_full`** (and
  the `B`/plain versions): the realized prefix of each thread is its whole Arm run, or a CLIF
  thread run from `cs` realizes it and stops there (`Covers`; `IselThread.Stop`: no step —
  returned, trapped, undefined behaviour — or an `atomic_cas` on read-only data): the allocated
  code is never `Done` without the CLIF thread stopping (`ThreadProgress.arm_isel_refines_full`).
  `thread_full_of_sim` is the one-thread statement for any layer-4b scope with covered code.
-/

namespace Concurrency.RealizeCompiled

open Arm ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine ThreadProgress
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

/-- **One compiled thread, its realized prefix the whole run or ending where the CLIF thread
stops**, for any layer-4b scope (`hsim`, the per-item obligation of `R`'s code, on ranked
configurations: `ArmAllocBranch.RConf`; before #553 on configurations with a measure of the
configuration only, which `MachBuffer`'s layout falsifies) whose code is covered
(`ThreadProgress.CoveredCode`). -/
theorem thread_full_of_sim {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    {s : ArmState} (hgv : RA.gv = fun _ _ => False) (hfront : Front env p RA cs s)
    (hsim : ItemSim Policy.arm RA.step (OkPriv RA) (SrcStepR RA) (RelQR RA) (DoneR RA) (μR RA)
      (PrivA RA)) (hcov : CoveredCode RA)
    {mon : Mon} {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm RA.step (OkPriv RA) (s, mon) ls t') :
    ∃ (k : Nat) (trS : List (List (Ev SKind BVal))) (st : Nat → TState) (ψ : Nat × Nat → Nat × Nat),
      k ≤ ls.length ∧ st 0 = .run cs ∧
      (∀ j (h : j < trS.length), CStep env p (st j) trS[j] (st (j + 1))) ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p (st trS.length)) := by
  obtain ⟨f, vc, ctx, st0, R, gn, bl, A, MR, slots, sb, syms, B0, args, m₀, w₀, H, hchk, hMR,
    hMRw, hX, hMem, hMRs, hreg, hprep, halloc, hB0, hcall, hfunc, hslots, hbody, hterm, hregs, hty,
    hsig, hmr, hargs, hq, hA⟩ := hfront
  obtain ⟨nA, trM, cE, ψA, hnA, hM, hAr, hend⟩ := arm_alloc_refinesQ hsim hq hA hr
  obtain ⟨k, trS, t, ψ, hk, hrun, href, hendk⟩ :=
    arm_isel_refines_full hgv hcov H hchk hMR hMRw hX hMem hMRs hreg hprep halloc hB0
      hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs hr hM hAr hend hnA
  obtain ⟨st, h0, hst, hlast⟩ := crun_states hrun
  have href' : Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS
      (conv (evTr (ls.take k))) ψ := by
    refine Refines.pairT_congr href fun a b _ hb => monPair_take hk ?_
    obtain ⟨hb1, -⟩ := evAt_isSome (show (evAt (conv (evTr (ls.take k))) (b.1, b.2)).isSome from hb)
    have := hb1; simp [conv, evTr] at this; omega
  exact ⟨k, trS, st, ψ, by omega, h0, hst, href', hendk.imp_right (hlast ▸ ·)⟩

/-- **One compiled thread with loops, branches and plain loads/stores, its realized prefix the
whole run or ending where the CLIF thread stops** (`thread_full_of_sim` for `MemScopeLS`). -/
theorem thread_compiledLS_full {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    {s : ArmState} (hc : CompiledLS env p RA cs s) {mon : Mon} {ls : List Lab}
    {t' : ArmState × Mon} (hr : PRun Policy.arm RA.step (OkPriv RA) (s, mon) ls t') :
    ∃ (k : Nat) (trS : List (List (Ev SKind BVal))) (st : Nat → TState) (ψ : Nat × Nat → Nat × Nat),
      k ≤ ls.length ∧ st 0 = .run cs ∧
      (∀ j (h : j < trS.length), CStep env p (st j) trS[j] (st (j + 1))) ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p (st trS.length)) :=
  thread_full_of_sim hc.gv hc.front (itemSim_ls hc.wf hc.scope) (coveredCode_of_ls hc.scope) hr

/-- **`thread_full_of_sim` with the return covered** (T2j follow-up; `refines_of_itemSimQ`,
`ThreadProgress.arm_isel_refines_fullR`): where the CLIF thread has returned, the realized prefix is
the whole run or the Arm run up to its end reaches a state related to the allocated code's end. -/
theorem thread_full_of_simR {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    {s : ArmState} (hgv : RA.gv = fun _ _ => False) (hfront : Front env p RA cs s)
    (hsim : ItemSim Policy.arm RA.step (OkPriv RA) (SrcStepR RA) (RelQR RA) (DoneR RA) (μR RA)
      (PrivA RA)) (hcov : CoveredCode RA)
    {mon : Mon} {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm RA.step (OkPriv RA) (s, mon) ls t') :
    ∃ (k : Nat) (trS : List (List (Ev SKind BVal))) (st : Nat → TState) (ψ : Nat × Nat → Nat × Nat),
      k ≤ ls.length ∧ st 0 = .run cs ∧
      (∀ j (h : j < trS.length), CStep env p (st j) trS[j] (st (j + 1))) ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p (st trS.length)) ∧
      ∀ v, st trS.length = .ret v → k = ls.length ∨
        ∃ tE cE, PRun Policy.arm RA.step (OkPriv RA) (s, mon) (ls.take k) tE ∧ RelQ RA tE cE ∧
          Done RA cE := by
  obtain ⟨f, vc, ctx, st0, R, gn, bl, A, MR, slots, sb, syms, B0, args, m₀, w₀, H, hchk, hMR,
    hMRw, hX, hMem, hMRs, hreg, hprep, halloc, hB0, hcall, hfunc, hslots, hbody, hterm, hregs, hty,
    hsig, hmr, hargs, hq, hA⟩ := hfront
  obtain ⟨r, hrel⟩ := RelQR.of (t := (s, mon)) hq hA
  obtain ⟨nA, trM, cE, ψA, hnA, hs, hAr, hendQ⟩ := refines_of_itemSimQ hsim hr hrel
  have hend : nA = ls.length ∨ (Done RA cE.1 ∧ ∃ t, RelQ RA t cE.1) :=
    hendQ.imp_right fun ⟨tE, _, hRE, hDE⟩ => ⟨hDE, tE, hRE.1⟩
  obtain ⟨k, trS, t, ψ, hk, hrun, href, hendk, hretk⟩ :=
    arm_isel_refines_fullR hgv hcov H hchk hMR hMRw hX hMem hMRs hreg hprep halloc hB0
      hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs hr (mtrun_of_srun (SRun.fst hs)) hAr
      hend hnA
  obtain ⟨st, h0, hst, hlast⟩ := crun_states hrun
  have href' : Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS
      (conv (evTr (ls.take k))) ψ := by
    refine Refines.pairT_congr href fun a b _ hb => monPair_take hk ?_
    obtain ⟨hb1, -⟩ := evAt_isSome (show (evAt (conv (evTr (ls.take k))) (b.1, b.2)).isSome from hb)
    have := hb1; simp [conv, evTr] at this; omega
  refine ⟨k, trS, st, ψ, by omega, h0, hst, href', hendk.imp_right (hlast ▸ ·), fun v hv => ?_⟩
  have hkA := hretk v (hlast ▸ hv)
  subst hkA
  rcases hendQ with h | ⟨tE, hrE, hRE, hDE⟩
  · exact .inl h
  · exact .inr ⟨tE, cE.1, hrE, hRE.1, hDE⟩

/-- **One compiled thread with loops, branches and plain loads/stores, on the whole run, with the
return covered** (`thread_full_of_simR` for `MemScopeLS`). -/
theorem thread_compiledLS_fullR {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    {s : ArmState} (hc : CompiledLS env p RA cs s) {mon : Mon} {ls : List Lab}
    {t' : ArmState × Mon} (hr : PRun Policy.arm RA.step (OkPriv RA) (s, mon) ls t') :
    ∃ (k : Nat) (trS : List (List (Ev SKind BVal))) (st : Nat → TState) (ψ : Nat × Nat → Nat × Nat),
      k ≤ ls.length ∧ st 0 = .run cs ∧
      (∀ j (h : j < trS.length), CStep env p (st j) trS[j] (st (j + 1))) ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p (st trS.length)) ∧
      ∀ v, st trS.length = .ret v → k = ls.length ∨
        ∃ tE cE, PRun Policy.arm RA.step (OkPriv RA) (s, mon) (ls.take k) tE ∧ RelQ RA tE cE ∧
          Done RA cE :=
  thread_full_of_simR hc.gv hc.front (itemSim_ls hc.wf hc.scope) (coveredCode_of_ls hc.scope) hr

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

/-- **One compiled thread with loops and branches, its realized prefix the whole run or ending
where the CLIF thread stops.** -/
theorem thread_compiledB_full {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    {s : ArmState} (hc : CompiledB env p RA cs s) {mon : Mon} {ls : List Lab}
    {t' : ArmState × Mon} (hr : PRun Policy.arm RA.step (OkPriv RA) (s, mon) ls t') :
    ∃ (k : Nat) (trS : List (List (Ev SKind BVal))) (st : Nat → TState) (ψ : Nat × Nat → Nat × Nat),
      k ≤ ls.length ∧ st 0 = .run cs ∧
      (∀ j (h : j < trS.length), CStep env p (st j) trS[j] (st (j + 1))) ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p (st trS.length)) :=
  thread_compiledLS_full hc.toLS hr

/-- **One compiled thread, its realized prefix the whole run or ending where the CLIF thread
stops.** -/
theorem thread_compiled_full {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    {s : ArmState} (hc : Compiled env p RA cs s) {mon : Mon} {ls : List Lab}
    {t' : ArmState × Mon} (hr : PRun Policy.arm RA.step (OkPriv RA) (s, mon) ls t') :
    ∃ (k : Nat) (trS : List (List (Ev SKind BVal))) (st : Nat → TState) (ψ : Nat × Nat → Nat × Nat),
      k ≤ ls.length ∧ st 0 = .run cs ∧
      (∀ j (h : j < trS.length), CStep env p (st j) trS[j] (st (j + 1))) ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p (st trS.length)) :=
  thread_compiledB_full hc.toB hr

/-! ## The program -/

/-- The private set of thread `i` of `n` compiled threads: its activation's (`PrivA`). -/
def PrivN (n : Nat) (RA : Nat → RL) (i l : Nat) : Prop := i < n ∧ PrivA (RA i) l

/-- **The realized prefix `k` of the Arm run `ls` covers it** (T2j): it is the whole run, or a
CLIF thread run from `cs` realizes it (`Refines Maps`, private set `PrivA RA`, the prefix's monitor
pairs atomic) and then stops (`IselThread.Stop`). -/
def Covers (env : Clif.Env) (p : Clif.Program) (RA : RL) (cs : Clif.State) (ls : List Lab)
    (k : Nat) : Prop :=
  k = ls.length ∨ ∃ (trS : List (List (Ev SKind BVal))) (st : Nat → TState)
    (ψ : Nat × Nat → Nat × Nat), st 0 = .run cs ∧
    (∀ j (h : j < trS.length), CStep env p (st j) trS[j] (st (j + 1))) ∧
    Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
    Stop env p (st trS.length)

/-- **The contract for `n` compiled threads, with loops, branches and plain loads/stores, on
realized prefixes that cover the runs** (T2j): `realizes_compiledLS`, and each thread's realized
prefix `k i` is its whole Arm run or ends where a CLIF thread realizing it stops (`Covers`). -/
theorem realizes_compiledLS_full {n : Nat} {env : Clif.Env} {p : Clif.Program} {RA : Nat → RL}
    {cs : Nat → Clif.State} {sA : Nat → ArmState}
    (hc : ∀ i < n, CompiledLS env p (RA i) (cs i) (sA i))
    {mon : Nat → Mon} {ls : Nat → List Lab} {t' : Nat → ArmState × Mon}
    (hr : ∀ i < n, PRun Policy.arm (RA i).step (OkPriv (RA i)) (sA i, mon i) (ls i) (t' i)) :
    ∃ k : Nat → Nat, (∀ i < n, k i ≤ (ls i).length) ∧
      (∀ i < n, Covers env p (RA i) (cs i) (ls i) (k i)) ∧
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
        (conv (evTr ((ls i).take k))) ψ ∧ (k = (ls i).length ∨ Stop env p (st trS.length)) :=
    fun i hi => thread_compiledLS_full (hc i hi) (hr i hi)
  let k : Nat → Nat := fun i => if hi : i < n then Classical.choose (hth i hi) else 0
  have hk : ∀ i (hi : i < n), ∃ (trS : List (List (Ev SKind BVal))) (st : Nat → TState)
      (ψ : Nat × Nat → Nat × Nat), k i ≤ (ls i).length ∧
      st 0 = .run (cs i) ∧ (∀ j (h : j < trS.length), CStep env p (st j) trS[j] (st (j + 1))) ∧
      Refines Maps (PrivA (RA i)) (MonPair (evTr ((ls i).take (k i)))) trS
        (conv (evTr ((ls i).take (k i)))) ψ ∧
      (k i = (ls i).length ∨ Stop env p (st trS.length)) := fun i hi => by
    simp only [k, hi, dite_true]
    exact Classical.choose_spec (hth i hi)
  refine ⟨k, fun i hi => by obtain ⟨_, _, _, h, -⟩ := hk i hi; exact h, fun i hi => ?_, ?_⟩
  · obtain ⟨trS, st, ψ, -, h0, hst, href, hend⟩ := hk i hi
    exact hend.imp_right fun h => ⟨trS, st, ψ, h0, hst, href, h⟩
  intro PA locsA locsC MA0 MC0 rfA coA rmwA hn htr hwf hrmw hlocs hpriv0 hval0 hdisj
  obtain ⟨PC, φ, hPn, hs0, hruns, hreal⟩ := PrivCoh.realizes_of_threads_priv (T := CStep env p)
    (s0 := fun i => .run (cs i)) (PrivT := PrivN n RA)
    (pairT := fun i => MonPair (evTr ((ls i).take (k i)))) (Obs := fun _ _ _ => True)
    hwf (fun i hi => hrmw i (hn ▸ hi)) hlocs hpriv0 hval0 (fun i hi => by
      have hi' : i < n := hn ▸ hi
      obtain ⟨trS, st, ψ, -, h0, hst, href, -⟩ := hk i hi'
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
  obtain ⟨k, hk, -, h⟩ := realizes_compiledLS_full hc hr
  exact ⟨k, hk, h⟩

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

/-- **The contract for `n` compiled threads with loops and branches, on realized prefixes that
cover the runs** (`realizes_compiledLS_full` for `CompiledB`). -/
theorem realizes_compiledB_full {n : Nat} {env : Clif.Env} {p : Clif.Program} {RA : Nat → RL}
    {cs : Nat → Clif.State} {sA : Nat → ArmState}
    (hc : ∀ i < n, CompiledB env p (RA i) (cs i) (sA i))
    {mon : Nat → Mon} {ls : Nat → List Lab} {t' : Nat → ArmState × Mon}
    (hr : ∀ i < n, PRun Policy.arm (RA i).step (OkPriv (RA i)) (sA i, mon i) (ls i) (t' i)) :
    ∃ k : Nat → Nat, (∀ i < n, k i ≤ (ls i).length) ∧
      (∀ i < n, Covers env p (RA i) (cs i) (ls i) (k i)) ∧
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
  realizes_compiledLS_full (fun i hi => (hc i hi).toLS) hr

/-- **The contract for `n` compiled threads, on realized prefixes that cover the runs**
(`realizes_compiledLS_full` for `Compiled`). -/
theorem realizes_compiled_full {n : Nat} {env : Clif.Env} {p : Clif.Program} {RA : Nat → RL}
    {cs : Nat → Clif.State} {sA : Nat → ArmState} (hc : ∀ i < n, Compiled env p (RA i) (cs i) (sA i))
    {mon : Nat → Mon} {ls : Nat → List Lab} {t' : Nat → ArmState × Mon}
    (hr : ∀ i < n, PRun Policy.arm (RA i).step (OkPriv (RA i)) (sA i, mon i) (ls i) (t' i)) :
    ∃ k : Nat → Nat, (∀ i < n, k i ≤ (ls i).length) ∧
      (∀ i < n, Covers env p (RA i) (cs i) (ls i) (k i)) ∧
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
  realizes_compiledB_full (fun i hi => (hc i hi).toB) hr

/-! ## When the realized prefix is the whole run -/

/-- **A covering prefix is the whole run** when the CLIF thread cannot stop at its start and no
first step of it has its events (the non-fence ones shared, at distinct positions) in a strict
prefix of the run: then the realizing CLIF run of `Covers` has no step, and stops at its start. -/
theorem covers_full {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    {ls : List Lab} {k : Nat} (hcov : Covers env p RA cs ls k) (hk : k ≤ ls.length)
    (hgo : ¬ Stop env p (.run cs))
    (hstep : ∀ evs t', CStep env p (.run cs) evs t' → ∀ k' < ls.length,
      ∀ ψ : Nat × Nat → Nat × Nat,
      (∀ i (hi : i < evs.length), evs[i].dir ≠ .F → ¬ PrivA RA evs[i].loc ∧
        ∃ y, evAt (conv (evTr (ls.take k'))) (ψ (0, i)) = some y ∧ y.dir = evs[i].dir ∧
          y.loc = evs[i].loc) →
      (∀ i j (hi : i < evs.length) (hj : j < evs.length), i ≠ j → ψ (0, i) ≠ ψ (0, j)) → False) :
    k = ls.length := by
  rcases hcov with h | ⟨trS, st, ψ, h0, hst, href, hstop⟩
  · exact h
  refine Classical.byContradiction fun hne => ?_
  cases trS with
  | nil => exact hgo (by simpa [h0] using hstop)
  | cons evs rest =>
    have hs := hst 0 (by simp)
    simp only [List.getElem_cons_zero, h0] at hs
    have hat : ∀ i (hi : i < evs.length), evAt (evs :: rest) (0, i) = some evs[i] := fun i hi =>
      evAt_of (by simp) (by simpa using hi)
    refine hstep evs _ hs k (by omega) ψ (fun i hi hF => ?_) (fun i j hi hj hij e => ?_)
    · obtain ⟨y, hy, -, hd, hl, -⟩ := href.ev _ _ (hat i hi)
      exact ⟨href.shared _ _ (hat i hi) hF, y, hy, hd, hl⟩
    · have := href.inj (by rw [hat i hi]; rfl) (by rw [hat j hj]; rfl) e
      simp only [Prod.mk.injEq, true_and] at this
      exact hij this

/-- A non-call statement steps the same in every environment and program. -/
theorem step_next_of_check {env : Clif.Env} {p : Clif.Program} {s : Clif.State}
    {st : Clif.Stmt} {rest : List Clif.Stmt} (hb : s.frame.body = st :: rest)
    (hc : ∀ fn args, st.inst ≠ .call fn args)
    (hci : ∀ sig callee args, st.inst ≠ .callIndirect sig callee args)
    (env0 : Clif.Env) (p0 : Clif.Program)
    (h : (match Clif.step env0 p0 s with | .next _ => true | _ => false) = true) :
    ∃ s', Clif.step env p s = .next s' := by
  have e : Clif.step env p s = Clif.step env0 p0 s := by
    rw [Clif.step_inst env p s st rest hb hc hci, Clif.step_inst env0 p0 s st rest hb hc hci]
  rw [e]
  cases h' : Clif.step env0 p0 s with
  | next s' => exact ⟨s', rfl⟩
  | _ => rw [h'] at h; cases h

/-- A thread whose first statement is no `atomic_cas` is not at one on read-only data. -/
theorem not_casRO {s : Clif.State} {st : Clif.Stmt} {rest : List Clif.Stmt}
    (hb : s.frame.body = st :: rest) (hi : ∀ ty fl pp ex x, st.inst ≠ .atomicCas ty fl pp ex x) :
    ¬ CasRO (.run s) := by
  rintro ⟨s', stm, rest', ty, fl, pp, ex, x, a, n, he, hb', hi', -, -⟩
  cases he
  rw [hb] at hb'
  cases hb'
  exact hi _ _ _ _ _ hi'

/-- **A thread whose step shape is one event of a non-fence kind** steps with a non-fence
event. -/
theorem nonFence_one {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {kd : SKind} {n : Nat}
    (hsh : evShape s = [[(kd, n)]]) (hk : kd.dir ≠ .F) {evs : List (Ev SKind BVal)}
    {t' : TState} (hs : CStep env p (.run s) evs t') : ∃ i, ∃ hi : i < evs.length, evs[i].dir ≠ .F := by
  obtain ⟨⟨hm, hd⟩, -⟩ := hs
  rw [hsh] at hm
  simp only [List.mem_singleton] at hm
  match evs, hm with
  | [x], hm =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at hm
    refine ⟨0, by simp, ?_⟩
    rw [List.getElem_cons_zero, (hd x (by simp)).1, hm.1]
    exact hk

/-- **A thread whose step shape is two events of non-fence kinds** steps with two non-fence
events. -/
theorem nonFence_two {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {k1 k2 : SKind}
    {n1 n2 : Nat} (hsh : evShape s = [[(k1, n1), (k2, n2)]]) (hk1 : k1.dir ≠ .F)
    (hk2 : k2.dir ≠ .F) {evs : List (Ev SKind BVal)} {t' : TState}
    (hs : CStep env p (.run s) evs t') :
    ∃ hl : 1 < evs.length, evs[0].dir ≠ .F ∧ evs[1].dir ≠ .F := by
  obtain ⟨⟨hm, hd⟩, -⟩ := hs
  rw [hsh] at hm
  simp only [List.mem_singleton] at hm
  match evs, hm with
  | [x, y], hm =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at hm
    refine ⟨by simp, ?_, ?_⟩
    · rw [List.getElem_cons_zero, (hd x (by simp)).1, hm.1.1]; exact hk1
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero]
      rw [(hd y (by simp)).1, hm.2.1]; exact hk2

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

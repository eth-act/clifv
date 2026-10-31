import FV.Concurrency.CallRetT
import FV.Concurrency.CallSegLift
import FV.Concurrency.CallStepT
import FV.Concurrency.CallEnterArm
import FV.Concurrency.CallArgsEntry
import FV.Concurrency.CallSegAbi

/-!
# `SegOkG` for compiled activations: the segment ends (#473, step (4))

The pieces an activation's segment needs on the thread, before the activation data:

* `RReach`: the CLIF thread states reachable from `c0` by `CStep`/`CStepS` steps (up to the
  thread's own bytes); **`PartsOk`**: the program's accesses from reachable states lie on a
  location partition `Loc` (uniform sizes), its reads nonempty — the thread-wide partition the
  start-dirty sets need (`CallComposeT.Refines.toT_parts`);
* `OkB`: the thread's run condition (reads of its bound `Bnd` return its own bytes), giving every
  activation's `OkPriv` (`okPriv_of_okB`);
* `EndT`: the ends of a realized prefix short of the whole run (the innermost frame stops, the next
  CLIF step reads a masked byte, or a return with masked bytes);
* **`seg_end`**: a chain segment (`arm_isel_refines_abiCRNX`/`arm_isel_refinesCRNX`'s
  conclusion) of an activation below its callers `ext` is a `RealT` prefix: the whole run, an
  `EndT`, or the activation's pause (call or return) with the lifted pause state reachable.
-/

namespace Concurrency.CallSegOkG

open Arm ArmThread ArmFoot Prog ClifThread ClifThreadI ThreadRefine PrivCohT CallComposeT
  ArmAllocThread PrepThread ClifCStepTerm CallSegT ClifLift CallSegLift

variable {env : Clif.Env} {p : Clif.Program} {Loc : Nat → Nat → Prop}

/-! ## Reachable CLIF states and the location partition -/

/-- **The CLIF thread states reachable from `c0`** by `CStep` or `CStepS` steps, up to the
thread's own bytes. -/
inductive RReach (env : Clif.Env) (p : Clif.Program) (c0 : TState) : TState → Prop
  | base : RReach env p c0 c0
  | step {t evs t'} : RReach env p c0 t → CStep env p t evs t' → RReach env p c0 t'
  | stepS {t evs t'} : RReach env p c0 t → CStepS env p t evs t' → RReach env p c0 t'
  | strip {t t'} : RReach env p c0 t → strip t = strip t' → RReach env p c0 t'

/-- An access on the partition `Loc`, a read nonempty. -/
def AccOk (Loc : Nat → Nat → Prop) (e : Ev SKind BVal) : Prop :=
  (e.dir ≠ .F → Loc e.loc e.n) ∧ (e.dir = .R → 0 < e.n)

/-- **The program's accesses lie on the location partition `Loc`** (module doc): every `CStep`
from a state reachable from `c0`. -/
def PartsOk (env : Clif.Env) (p : Clif.Program) (c0 : TState) (Loc : Nat → Nat → Prop) : Prop :=
  ∀ t evs t', RReach env p c0 t → CStep env p t evs t' → ∀ e ∈ evs, AccOk Loc e

theorem RReach.crun {c0 : TState} (hP : PartsOk env p c0 Loc) :
    ∀ {t t' : TState} {tr : List (List (Ev SKind BVal))}, RReach env p c0 t → CRun env p t tr t' →
      (∀ evs ∈ tr, ∀ e ∈ evs, AccOk Loc e) ∧ RReach env p c0 t'
  | _, _, _, h, .nil => ⟨by simp, h⟩
  | _, _, _, h, .cons hs r => by
    obtain ⟨h1, h2⟩ := RReach.crun hP (h.step hs) r
    refine ⟨fun evs hm e he => ?_, h2⟩
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hP _ _ _ h hs e he
    · exact h1 evs hm e he

theorem RReach.crunS {c0 : TState} :
    ∀ {t t' : TState} {tr : List (List (Ev SKind BVal))}, RReach env p c0 t →
      CRunS env p t tr t' → RReach env p c0 t'
  | _, _, _, h, .nil => h
  | _, _, _, h, .cons hs r => RReach.crunS (h.stepS hs) r

theorem mem_of_evAt {α : Type} {tr : List (List α)} {q : Nat × Nat} {x : α}
    (h : evAt tr q = some x) : ∃ evs ∈ tr, x ∈ evs := by
  unfold evAt at h
  cases hq : tr[q.1]? with
  | none => rw [hq] at h; cases h
  | some evs =>
    rw [hq] at h
    exact ⟨evs, List.mem_of_getElem? hq, List.mem_of_getElem? h⟩

/-- **A segment's accesses lie on the partition** (module doc): the activation's own CLIF run
from `s`, lifted below `ext` to a reachable state. -/
theorem seg_parts {c0 : TState} {Loc : Nat → Nat → Prop} (hP : PartsOk env p c0 Loc)
    {ext : List (Clif.Frame × List Clif.ValueId)} {s : Clif.State}
    (hR : RReach env p c0 (.run (pushC ext s))) {trS : List (List (Ev SKind BVal))} {t : TState}
    (hrun : CRun env p (.run s) trS t) :
    (∀ q x, evAt trS q = some x → AccOk Loc x) ∧
      ∀ s', t = .run s' → RReach env p c0 (.run (pushC ext s')) := by
  obtain ⟨trS', t1, hrun', hp, hd, -, hrunE, -⟩ := crun_pushC (ext := ext) hrun
  obtain ⟨hacc, hR1⟩ := RReach.crun hP hR hrun'
  refine ⟨fun q x hx => ?_, fun s' e => ?_⟩
  · rw [← evAt_prefix_nil hp hd] at hx
    obtain ⟨evs, hm, he⟩ := mem_of_evAt hx
    exact hacc evs hm x he
  · obtain ⟨h1, -⟩ := hrunE s' e
    exact h1 ▸ hR1

/-! ## The run condition -/

/-- **The thread's run condition**: reads of its bound `Bnd` return its own bytes. -/
def OkB (Bnd : Nat → Prop) (s : ArmState) (l : Lab) : Prop :=
  ∀ e ∈ l.evs, e.k.dir = .R → Bnd e.addr.toNat → readM e.n e.addr s.mem = e.val

theorem okPriv_of_okB {R : Backend.Proof.RL} {Bnd : Nat → Prop} (h : ∀ a, PrivA R a → Bnd a)
    {s : ArmState} {l : Lab} (ho : OkB Bnd s l) : OkPriv R s l :=
  fun e he hd hp => ho e he hd (h _ hp)

theorem prun_okPriv {R : Backend.Proof.RL} {Bnd : Nat → Prop} (h : ∀ a, PrivA R a → Bnd a)
    {f : ArmState → ArmState} {t t' : ArmState × Mon} {ls : List Lab}
    (hr : PRun Policy.arm f (OkB Bnd) t ls t') : PRun Policy.arm f (OkPriv R) t ls t' :=
  PRun.mono (fun _ _ => okPriv_of_okB h) hr

/-! ## CLIF returns below callers -/

/-- A CLIF step returning from the bottom frame: the state has no callers. -/
theorem callers_nil_of_done {s : Clif.State} {v : List Clif.Val} {m : Clif.Mem}
    (h : Clif.step env p s = .done v m) : s.callers = [] := by
  rcases hc : s.callers with _ | ⟨c, cs⟩
  · rfl
  · exfalso
    have e : s = pushC (c :: cs) { s with callers := [] } := by
      cases s; simp only [pushC, List.nil_append] at hc ⊢; rw [hc]
    rw [e, step_pushC] at h
    cases hs : Clif.step env p { s with callers := [] } with
    | next s2 => rw [hs] at h; cases h
    | done v' m' =>
      rw [hs] at h
      simp only [push] at h
      split at h <;> cases h
    | trapped c' => rw [hs] at h; cases h
    | stuck msg => rw [hs] at h; cases h

/-- **A return whose results do not fit the caller's registers is stuck below the caller.** -/
theorem step_pushC_stuck {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (h : Clif.step env p s = .done vals cm) {caller : Clif.Frame} {results : List Clif.ValueId}
    {cs : List (Clif.Frame × List Clif.ValueId)} (hn : caller.regs.setMany results vals = none) :
    ∃ msg, Clif.step env p (pushC ((caller, results) :: cs) s) = .stuck msg := by
  rw [step_pushC, h]
  exact ⟨"call result arity mismatch", by simp only [push, hn]⟩

/-! ## The ends of a realized prefix -/

/-- **The ends of a realized prefix short of the whole run** (module doc): the innermost frame
`s` of the CLIF thread (below callers `ext`) stops (`IselThread.Stop`: no step, or an
`atomic_cas` on read-only data), is at an event-free return the prefix did not realize, or the
thread's CLIF step from it is stuck or traps (e.g. a return whose results do not fit the
caller), or it is at a call at CLIF call depth `Dcap` or more (the thread's stack budget covers
`Dcap` nested activations); or the next CLIF step reads a masked byte; or the thread returns
with masked bytes. -/
def EndT (env : Clif.Env) (p : Clif.Program) (Dcap : Nat) (_P : List Lab)
    (d : TState × (Nat → Prop)) : Prop :=
  (∃ ext s, strip d.1 = strip (.run (pushC ext s)) ∧
    (IselThread.Stop env p (.run s) ∨ (∃ v, CStep env p (.run s) [] (.ret v)) ∨
      (∃ msg, Clif.step env p (pushC ext s) = .stuck msg) ∨
      (∃ c, Clif.step env p (pushC ext s) = .trapped c) ∨
      (IselCall.AtCallS s ∧ Dcap ≤ ext.length))) ∨
  (∃ evs t'', CStep env p d.1 evs t'' ∧ ReadsMasked (maskOf d.1) evs) ∨
  (∃ v, CStep env p d.1 [] (.ret v) ∧ ∃ a, maskOf d.1 a)

theorem EndT.app {Dcap : Nat} {A B : List Lab} {d : TState × (Nat → Prop)}
    (h : EndT env p Dcap B d) : EndT env p Dcap (A ++ B) d := h

/-! ## End-dirty sets on the partition -/

theorem maskAfter_sub : ∀ {U : Nat → Prop} {tr : List (List (Ev SKind BVal))} {a : Nat},
    maskAfter U tr a → U a
  | _, [], _, h => h
  | U, evs :: tr, _, h => (maskAfter_sub (U := fun b => U b ∧ ¬ writes evs b) (tr := tr) h).1

theorem maskAfter_of : ∀ {U : Nat → Prop} {tr : List (List (Ev SKind BVal))} {a : Nat},
    U a → (∀ evs ∈ tr, ¬ writes evs a) → maskAfter U tr a
  | _, [], _, h, _ => h
  | U, evs :: tr, _, h, hw =>
    maskAfter_of (U := fun b => U b ∧ ¬ writes evs b) (tr := tr)
      ⟨h, hw evs (List.mem_cons_self ..)⟩ fun e he => hw e (List.mem_cons_of_mem _ he)

theorem evAt_of_mem {α : Type} {tr : List (List α)} {evs : List α} (h : evs ∈ tr) {x : α}
    (hx : x ∈ evs) : ∃ q, evAt tr q = some x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  exact ⟨(i, j), by simp [evAt, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]⟩

theorem evAt_of_prefix {α : Type} {A B : List (List α)} (h : A <+: B) {q : Nat × Nat} {x : α}
    (hx : evAt A q = some x) : evAt B q = some x := by
  obtain ⟨C, rfl⟩ := h
  rw [evAt_append_lt _ _ (evAt_lt hx)]; exact hx

/-- **The end-dirty set of a segment on the partition** lies in its private set, its end mask and
the addresses starting no location or in `N`: a masked location start no source write starts at
is written by none (writes covering a location start start there). -/
theorem dirtyEnd_sub (hdisj : PartDisj Loc) {tr : List (List (Ev SKind BVal))}
    (ho : ∀ q x, evAt tr q = some x → x.dir ≠ .F → Loc x.loc x.n) {D P U N : Nat → Prop}
    (hD : ∀ a, D a → P a ∨ U a ∨ (¬ ∃ n, Loc a n) ∨ N a) {a : Nat} (h : DirtyEnd D P tr a) :
    P a ∨ maskAfter U tr a ∨ (¬ ∃ n, Loc a n) ∨ N a := by
  rcases h with h | ⟨hd, hw⟩
  · exact .inl h
  rcases hD a hd with h | h | h
  · exact .inl h
  · by_cases hl : ∃ n, Loc a n
    · obtain ⟨n, hl⟩ := hl
      refine .inr (.inl (maskAfter_of h fun evs he ⟨e, hee, hW, hle, hlt⟩ => hw ?_))
      obtain ⟨q, hq⟩ := evAt_of_mem he hee
      exact ⟨q, e, hq, hW, hdisj a n e.loc e.n hl (ho q e hq (by rw [hW]; decide)) hle hlt⟩
    · exact .inr (.inr (.inl hl))
  · exact .inr (.inr h)

/-! ## A chain segment on the thread -/

/-- **A chain segment below its callers is a realized prefix** (module doc): an own CLIF run
from `s` refining a prefix of a precise run with private set `P`, started below `ext` at a
reachable state with mask `U` and a start-dirty set within `P`, the mask, the addresses starting
no location and a set `N` no read of the run starts at, ending as the chain theorems end (whole
run, `Stop`, or a pause `Pz`). -/
theorem seg_endP {Bnd : Nat → Prop} {P : Nat → Prop} (hb : ∀ a, P a → Bnd a)
    {Dcap : Nat}
    {c0 : TState} (hP : PartsOk env p c0 Loc) (hdisj : PartDisj Loc)
    {f : ArmState → ArmState} {ok : ArmState → Lab → Prop} {u t' : ArmState × Mon}
    {ls : List Lab} (hr : PRun Policy.arm f ok u ls t') {k : Nat} (hk : k ≤ ls.length)
    (ext : List (Clif.Frame × List Clif.ValueId)) {s : Clif.State}
    (hR : RReach env p c0 (.run (pushC ext s))) {trS : List (List (Ev SKind BVal))} {t : TState}
    {ψ : Nat × Nat → Nat × Nat} (hrun : CRun env p (.run s) trS t)
    (hx : CallCompose.XClosed (evTr (ls.take k)))
    (href : Refines Maps P (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ)
    {U D N : Nat → Prop} (hD : ∀ a, D a → P a ∨ U a ∨ (¬ ∃ n, Loc a n) ∨ N a)
    (hN : ∀ q x, evAt trS q = some x → x.dir = .R → ¬ N x.loc)
    {Pz : Clif.State → Prop}
    (hend : k = ls.length ∨ IselThread.Stop env p t ∨ ∃ s', t = .run s' ∧ Pz s') :
    ∃ k' d', RealT env p Bnd ls k' (encT U (.run (pushC ext s)), D) d' ∧
      (k' = ls.length ∨ EndT env p Dcap (ls.take k') d' ∨
        (k' = k ∧ ∃ s' M DE, Pz s' ∧ t = .run s' ∧ d' = (encT M (.run (pushC ext s')), DE) ∧
          (∀ a, M a → U a) ∧ (∀ a, DE a → P a ∨ M a ∨ (¬ ∃ n, Loc a n) ∨ N a) ∧
          RReach env p c0 (.run (pushC ext s')))) := by
  obtain ⟨hacc, hReachEnd⟩ := seg_parts hP hR hrun
  have hu : Uniform trS := uniform_of_parts hdisj fun q x hx hF => (hacc q x hx).1 hF
  have hpos : ∀ q x, evAt trS q = some x → x.dir = .R → 0 < x.n :=
    fun q x hx hRd => (hacc q x hx).2 hRd
  have hns : ∀ q x, evAt trS q = some x → x.dir = .R → ¬ ((¬ ∃ n, Loc x.loc n) ∨ N x.loc) :=
    fun q x hx hRd hn => hn.elim (fun hn => hn ⟨x.n, (hacc q x hx).1 (by rw [hRd]; decide)⟩)
      (hN q x hx hRd)
  rcases realizedT_liftW (Bnd := Bnd) hr hk ext hrun hx href hD hu hpos hns hb with
    ⟨trS', s1, hp, hRT, hs1, hret⟩ | ⟨k', -, trS', j, evs, -, -, sj, t'', hRT, hst, hm⟩
  · rcases hend with h | h | ⟨s', rfl, hz⟩
    · exact ⟨k, (encT (maskAfter U trS') (.run (pushC ext s1)), DirtyEnd D P trS'), hRT,
        .inl h⟩
    · refine ⟨k, (encT (maskAfter U trS') (.run (pushC ext s1)), DirtyEnd D P trS'), hRT,
        .inr (.inl (.inl ⟨ext, s1, by exact strip_encT (maskAfter U trS') (.run (pushC ext s1)),
          ?_⟩))⟩
      cases t with
      | run s' => obtain rfl := hs1 s' rfl; exact .inl h
      | ret v => exact .inr (.inl ⟨v, hret v rfl⟩)
    · obtain rfl := hs1 s' rfl
      exact ⟨k, (encT (maskAfter U trS') (.run (pushC ext s1)), DirtyEnd D P trS'), hRT,
        .inr (.inr ⟨rfl, s1, _, _, hz, rfl, rfl, fun _ => maskAfter_sub,
          fun a => dirtyEnd_sub hdisj (fun q x hx => (hacc q x (evAt_of_prefix hp hx)).1) hD,
          hReachEnd s1 rfl⟩)⟩
  · refine ⟨k', (encT (maskAfter U (trS'.take j)) (.run sj), DirtyEnd D P (trS'.take j)),
      hRT, .inr (.inl (.inr (.inl ⟨evs, t'', cstep_withBytes.mpr hst, ?_⟩)))⟩
    show ReadsMasked (maskOf (encT (maskAfter U (trS'.take j)) (.run sj))) evs
    rw [maskOf_encT]; exact hm

/-- **A chain segment of an activation below its callers is a realized prefix** (`seg_endP`
with the activation's private set `PrivA R`). -/
theorem seg_end {Bnd : Nat → Prop} {R : Backend.Proof.RL} (hb : ∀ a, PrivA R a → Bnd a)
    {Dcap : Nat}
    {c0 : TState} (hP : PartsOk env p c0 Loc) (hdisj : PartDisj Loc)
    {f : ArmState → ArmState} {ok : ArmState → Lab → Prop} {u t' : ArmState × Mon}
    {ls : List Lab} (hr : PRun Policy.arm f ok u ls t') {k : Nat} (hk : k ≤ ls.length)
    (ext : List (Clif.Frame × List Clif.ValueId)) {s : Clif.State}
    (hR : RReach env p c0 (.run (pushC ext s))) {trS : List (List (Ev SKind BVal))} {t : TState}
    {ψ : Nat × Nat → Nat × Nat} (hrun : CRun env p (.run s) trS t)
    (hx : CallCompose.XClosed (evTr (ls.take k)))
    (href : Refines Maps (PrivA R) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ)
    {U D N : Nat → Prop} (hD : ∀ a, D a → PrivA R a ∨ U a ∨ (¬ ∃ n, Loc a n) ∨ N a)
    (hN : ∀ q x, evAt trS q = some x → x.dir = .R → ¬ N x.loc)
    {Pz : Clif.State → Prop}
    (hend : k = ls.length ∨ IselThread.Stop env p t ∨ ∃ s', t = .run s' ∧ Pz s') :
    ∃ k' d', RealT env p Bnd ls k' (encT U (.run (pushC ext s)), D) d' ∧
      (k' = ls.length ∨ EndT env p Dcap (ls.take k') d' ∨
        (k' = k ∧ ∃ s' M DE, Pz s' ∧ t = .run s' ∧ d' = (encT M (.run (pushC ext s')), DE) ∧
          (∀ a, M a → U a) ∧ (∀ a, DE a → PrivA R a ∨ M a ∨ (¬ ∃ n, Loc a n) ∨ N a) ∧
          RReach env p c0 (.run (pushC ext s')))) :=
  seg_endP hb hP hdisj hr hk ext hR hrun hx href hD hN hend

end Concurrency.CallSegOkG

namespace Concurrency.CallSegOkG

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck ThreadRefine IselCall IselCallRet ArmAllocThread E2E
  ClifCStepTerm IselThread CallRetsEnd CallRetsN CallSegAbi LinkedMachine LinkedMachine.Link
  CallComposeT CallArgsL2 CallArgsEntry CallArgsAt CallResumeChecks

/-! ## Activations -/

/-- **An activation of a compiled function of the link** (module doc): the function `F` named
`nm`, the activation's entry state `s0`, callee budget `K`, kept addresses `G` and return address
`ra`; the CLIF function `f` and its lowering data (`DriverHypT`'s `vc ctx st0 R gn bl A`), the
memory relation `RelW Γ f c`, the prep and allocation facts' data, the activation's slots and its
CLIF callers `ext`. -/
structure Act where
  nm : String
  F : LFn
  s0 : ArmState
  K : Nat
  G : BitVec 64 → Prop
  ra : BitVec 64
  f : Clif.Function
  vc : VCode
  ctx : Ctx
  st0 : LState
  R : Reg → Reg
  gn : Nat → Nat
  bl : List BLow
  A : Nat → Nat → List Clif.ValueId
  Γ : E2E.Rel
  c : BitVec 64
  Lp : Nat → Prop
  ss : Array (Array Nat)
  ss' : Array (Array Nat)
  cc : CheckCtx
  ins : Array (Option AState)
  a0 : AState
  slots : List (Clif.SlotId × Nat)
  ext : List (Clif.Frame × List Clif.ValueId)
  /-- the caller's compiled function (the return address is in its code) -/
  caller : LFn
  /-- the open activations' CLIF memories at their calls and depths (`CallValid.AllocInvD`) -/
  opens : List (Clif.Mem × Nat)
  /-- addresses no CLIF read of the activation's segments starts at (its frame padding and the
  callers' private sets outside its slots) -/
  N : Nat → Prop := fun _ => False
  /-- the slot-placement oracle's stack pointers below the activation's (its callers') -/
  sps : List (BitVec 64) := []

/-- The activation's `RL` in the link. -/
abbrev Act.RL (L : Link) (g : Act) : Backend.Proof.RL := L.act g.F g.s0 g.K g.G

/-- The activation's callee-saved registers at its body entry (after the prologue). -/
noncomputable def Act.r0 (L : Link) (g : Act) : Reg → CV := fun r =>
  locVal (g.RL L).fr (iterN (g.RL L).step (prologueLines g.F.af.saves g.F.af.frameSize g.F.af.isCaller).length g.s0)
    (.reg r)

/-- **The static facts of an activation** (module doc): the premises of the chain theorems that do
not depend on the run. -/
structure StatOk (L : Link) (env : Clif.Env) (p : Clif.Program) (g : Act) : Prop where
  mem : (g.nm, g.F) ∈ L.fns
  wf : (g.RL L).Wf
  scope : MemScopeLSC (g.RL L)
  abi : AbiCall g.F.fb g.F.base g.ra g.s0
  H : DriverHypT g.f g.vc g.ctx g.st0 g.R g.gn g.bl g.A
    (csem (g.RL L).F (g.RL L).ctx (g.RL L).X) (RelW g.Γ g.f g.c) env p
  chk : threadCheckBlC g.f g.bl = true
  ΓF : g.Γ.F = (g.RL L).F
  align : g.c.toNat % 16 = 0
  tls : TlsMemFree g.F.X
  noCall : NoCall g.F.X
  H3 : PrepFacts g.vc g.F.vc g.Lp g.ss g.ss'
  checked : CheckedAt g.F.vc g.F.rf g.cc g.ins g.a0
  ok : L.Ok
  slot : (g.RL L).ctx.slotBase = g.Γ.slotOff
  sym : ∀ n b, g.Γ.syms n = some b → g.F.X.sym n 0 = BitVec.ofNat 64 b
  reg : ∀ off, ArgLoc.stack off ∉ locsOf g.f.sig
  pinit : ∀ (ρ₀ : Nat → CV) (w₀ : ArmState), PMatch g.vc g.F.vc
    (csem (g.RL L).F (g.RL L).ctx (g.RL L).X) (cEvs (g.RL L).F (g.RL L).ctx) g.Lp g.ss'
    (VConf.init ρ₀ w₀) (VConf.init ρ₀ w₀)
  minit : ∀ (m₀ : Loc → CV) (ρ₀ : Nat → CV) (w₀ : ArmState),
    Backend.Proof.Match g.cc g.ins ckeep (fun r => m₀ (.reg r)) (MConf.init g.F.rf m₀ w₀)
      (VConf.init ρ₀ w₀)
  res : callResLenB g.f = true
  cu : callUseRegsBl g.f g.bl = true
  ar : CallArity.callArityBl g.f g.bl = true
  low : lowerCheck g.f g.vc = true
  ind : indSigs g.f = []
  ver : verifiable g.f = true
  nt : g.f.blocks.all (fun B => !B.term.isTry) = true
  out0 : g.vc.outgoing = 0
  uv : CallUsesVirt g.F.vc
  dv : CallDefsVirt g.F.vc
  uniq : ∀ e ∈ g.f.externs, ∀ e' ∈ g.f.externs, e.2.name = e'.2.name → e.2 = e'.2
  envx : ∀ e ∈ g.f.externs, env.extern e.2.name = none
  sigs : ∀ e ∈ g.f.externs, ∀ callee, p.func? e.2.name = some callee → callee.sig = e.2.sig
  /-- the prologue's stack probes write outside the world (#581, `ProbeF`: new, for the entry
  form `chainP_entry`; holds for a frame below 4 KiB, `ProbeF.of_small`) -/
  probe : ProbeF (g.RL L)

/-- **The static facts of a compiled function of the link** (module doc): the lowering, prep and
allocation data of the CLIF function `f` compiled to `F` (named `nm`), its CLIF slots within its
frame's slot area, such that every activation of `F` (well formed, entered at an ABI call, its
body-entry stack pointer 16-aligned) has its `StatOk` with the memory relation of its world
(`Γ`: its private set, the link's symbols `syms`, its slot base). -/
def FnOk (L : Link) (env : Clif.Env) (p : Clif.Program) (syms : String → Option Nat)
    (nm : String) (F : LFn) (f : Clif.Function) : Prop :=
  F.Static ∧ F.af.frameSize % 16 = 0 ∧
  (∀ q ∈ f.slots, ∃ off, (slotLayout f.slots).1.lookup q.1 = some off ∧
    F.af.slotBase + off + q.2.size ≤ F.af.frameSize - clobberBytes F.af.saves) ∧
  ∃ (vc : VCode) (ctx : Ctx) (st0 : LState) (R : Reg → Reg) (gn : Nat → Nat) (bl : List BLow)
    (A : Nat → Nat → List Clif.ValueId) (Lp : Nat → Prop) (ss ss' : Array (Array Nat))
    (cc : CheckCtx) (ins : Array (Option AState)) (a0 : AState),
    ∀ (s0 : ArmState) (K : Nat) (G : BitVec 64 → Prop) (ra c : BitVec 64)
      (slots : List (Clif.SlotId × Nat)) (ext : List (Clif.Frame × List Clif.ValueId))
      (caller : LFn) (opens : List (Clif.Mem × Nat)) (N : Nat → Prop) (sps : List (BitVec 64)),
      (L.act F s0 K G).Wf → AbiCall F.fb F.base ra s0 → c.toNat % 16 = 0 →
      StatOk L env p ⟨nm, F, s0, K, G, ra, f, vc, ctx, st0, R, gn, bl, A,
        ⟨(L.act F s0 K G).F, syms, (L.act F s0 K G).ctx.slotBase, 0⟩, c, Lp, ss, ss', cc, ins, a0,
        slots, ext, caller, opens, N, sps⟩

/-- The pause of a chain segment at a call: the three relations and `Q` at the paused `call`. -/
def CallPz (L : Link) (g : Act) (r₀ : Reg → CV) (x0 : ArmState × Mon) (P : List Lab)
    (s' : Clif.State) : Prop :=
  ∃ tE vV' vP' cM', PRun Policy.arm L.M (OkPriv (g.RL L)) x0 P tE ∧
    RelQ (g.RL L) tE (.run cM') ∧ Pause (g.RL L) (.run cM') ∧ AtCallS s' ∧
    Match g.f g.ctx g.R g.gn g.bl g.A (RelW g.Γ g.f g.c) g.slots s' vV' ∧
    PMatch g.vc g.F.vc (csem (g.RL L).F (g.RL L).ctx (g.RL L).X) (cEvs (g.RL L).F (g.RL L).ctx)
      g.Lp g.ss' (.run vV') (.run vP') ∧
    MatchRun g.cc g.ins ckeep r₀ cM' vP'

/-- The pause of a chain segment at a done `return`, with its contract `RetEnd`. -/
def RetPz (L : Link) (env : Clif.Env) (p : Clif.Program) (g : Act) (r₀ : Reg → CV)
    (x0 : ArmState × Mon) (P : List Lab) (s' : Clif.State) : Prop :=
  ∃ tE, PRun Policy.arm L.M (OkPriv (g.RL L)) x0 P tE ∧ AtRetS s' ∧
    RetEnd (g.RL L) g.ra env p (RelW g.Γ g.f g.c) g.slots r₀ tE.1 s'

/-- **The chain property of an activation at `x0` with CLIF state `s`** (module doc): every
precise run of the link's machine from `x0` is realized on a prefix by the activation's own CLIF
run from `s`, up to the whole run, `Stop`, or a pause at a call or a done `return`. -/
def ChainP (L : Link) (env : Clif.Env) (p : Clif.Program) (g : Act) (r₀ : Reg → CV)
    (x0 : ArmState × Mon) (s : Clif.State) : Prop :=
  ∀ ls t', PRun Policy.arm L.M (OkPriv (g.RL L)) x0 ls t' →
    ∃ k trS t ψ, k ≤ ls.length ∧ CallCompose.XClosed (evTr (ls.take k)) ∧
      CRun env p (.run s) trS t ∧
      Refines Maps (PrivA (g.RL L)) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p t ∨ ∃ s', t = .run s' ∧
        (CallPz L g r₀ x0 (ls.take k) s' ∨ RetPz L env p g r₀ x0 (ls.take k) s'))

variable {L : Link} {env : Clif.Env} {p : Clif.Program} {g : Act}

/-- **The resume form** (`arm_isel_refinesCRNX`), with the checker's entry values of the saved
registers the ABI-entry ones (`hr₀`: Cranelift's epilogue pops them back; the save slots are not
`Q`'s locations). -/
theorem chainP_resume (hS : StatOk L env p g) {r₀ : Reg → CV} {s : Clif.State}
    {vV vP : VState CV ArmState} {cM : MState CV ArmState} {x : ArmState} {mon : Mon}
    (hr₀ : ∀ r ∈ (g.RL L).af.saves, ckeep r (r₀ r) = ckeep r (regVal (g.RL L).s0 r))
    (hm2 : Match g.f g.ctx g.R g.gn g.bl g.A (RelW g.Γ g.f g.c) g.slots s vV)
    (hm3 : PMatch g.vc g.F.vc (csem (g.RL L).F (g.RL L).ctx (g.RL L).X)
      (cEvs (g.RL L).F (g.RL L).ctx) g.Lp g.ss' (.run vV) (.run vP))
    (hm4 : MatchRun g.cc g.ins ckeep r₀ cM vP) (hq : Q (g.RL L) x (.run cM))
    (hA : AInv (g.RL L) (.run cM)) : ChainP L env p g r₀ (x, mon) s := fun ls t' hr => by
  obtain ⟨k, trS, t, ψ, hk, hx, hrun, href, hend⟩ := arm_isel_refinesCRNX hS.wf hS.scope rfl
    (agreesAt_M hS.ok hS.mem _ _ _) hS.abi hS.H hS.chk (hS.ΓF ▸ memRelOk_relW g.Γ g.f g.c)
    (IselRefines.Witness.relW_wf hS.align) hS.tls hS.noCall hS.H3 hS.checked hr₀ hm2 hm3 hm4 hq
    hA hr
  refine ⟨k, trS, t, ψ, hk, hx, hrun, href, ?_⟩
  rcases hend with h | h | ⟨tE, s', vV', vP', cM', h1, h2, h3, rfl, h4, h5, h6, h7⟩ |
    ⟨tE, s', h1, rfl, h2, h3⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨s', rfl, .inl ⟨tE, vV', vP', cM', h1, h2, h3, h4, h5, h6, h7⟩⟩)
  · exact .inr (.inr ⟨s', rfl, .inr ⟨tE, h1, h2, h3⟩⟩)

/-- **The entry form** (`arm_isel_refines_abiCRNX`): from the ABI entry, the CLIF entry state
`cs` of the activation's function. -/
theorem chainP_entry (hS : StatOk L env p g) {cs : Clif.State} {B0 : Clif.Block}
    (hB0 : g.f.blocks[0]? = some B0) (hcall : cs.callers = []) (hfunc : cs.frame.func = g.f)
    (hslots : cs.frame.slots = g.slots) (hbody : cs.frame.body = B0.body)
    (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = g.f.sig.params.map (·.ty))
    {m₀ : Loc → CV} {w₀ : Arm.ArmState} (hmr : RelW g.Γ g.f g.c g.slots cs.mem w₀)
    (hargs : ArgsAtEntry (g.RL L).F g.f.sig args w₀)
    (hq : Q (g.RL L) (iterN (g.RL L).step (prologueLines g.F.af.saves g.F.af.frameSize g.F.af.isCaller).length g.s0)
      (MConf.init g.F.rf m₀ w₀)) (hA : AInv (g.RL L) (MConf.init g.F.rf m₀ w₀)) {mon : Mon} :
    ChainP L env p g (fun r => m₀ (.reg r)) (g.s0, mon) cs := fun ls t' hr => by
  obtain ⟨k, trS, t, ψ, hk, hx, hrun, href, hend⟩ := arm_isel_refines_abiCRNX hS.wf hS.scope rfl
    (agreesAt_M hS.ok hS.mem _ _ _) hS.abi hS.probe hS.H hS.chk (hS.ΓF ▸ memRelOk_relW g.Γ g.f g.c)
    (IselRefines.Witness.relW_wf hS.align) hS.tls hS.noCall
    (memRefines_csem _ _ _ hS.slot (fun n b h => hS.sym n b h))
    (hS.ΓF ▸ mrStable_relW g.Γ g.f g.c)
    hS.reg hS.H3 hS.pinit hS.checked hS.minit hB0 hcall hfunc hslots hbody hterm hregs hty
    hsig hmr hargs hq hA hr
  refine ⟨k, trS, t, ψ, hk, hx, hrun, href, ?_⟩
  rcases hend with h | h | ⟨tE, s', vV', vP', cM', h1, h2, h3, rfl, h4, h5, h6, h7⟩ |
    ⟨tE, s', h1, rfl, h2, h3⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨s', rfl, .inl ⟨tE, vV', vP', cM', h1, h2, h3, h4, h5, h6, h7⟩⟩)
  · exact .inr (.inr ⟨s', rfl, .inr ⟨tE, h1, h2, h3⟩⟩)

/-! ## The return pause -/

/-- **A callee's return pause on the thread** (`CallRetT.realizedT_ret`): from the pause at its
done `return` (below its caller's frame), the epilogue and `ret` realize the CLIF return into the
caller: the whole run, the caller's result registers not fitting (no label realized), or the
return realized, ending at the caller's resumed frame on the caller's program. -/
theorem ret_seg {Bnd : Nat → Prop} (hok : L.Ok) (hmem : (g.nm, g.F) ∈ L.fns) (hwf : (g.RL L).Wf)
    (habi : AbiCall g.F.fb g.F.base g.ra g.s0) (hb : ∀ a, PrivA (g.RL L) a → Bnd a)
    {cnm : String} (hcA : (cnm, g.caller) ∈ L.fns) (hrA : g.caller.InRange g.ra)
    (hra : ∀ k < g.F.fb.words.size, g.ra ≠ g.F.base + BitVec.ofNat 64 (4 * k))
    {caller : Clif.Frame} {results : List Clif.ValueId} {cs : List (Clif.Frame × List Clif.ValueId)}
    (hext : g.ext = (caller, results) :: cs) {x : ArmState} {sR : Clif.State}
    (hret : RetEnd (g.RL L) g.ra env p (RelW g.Γ g.f g.c) g.slots (g.r0 L) x sR)
    (hat : AtRetS sR) (hcall : sR.callers = []) (U D : Nat → Prop) {mon : Mon} {ls : List Lab}
    {t' : ArmState × Mon} (hr : PRun Policy.arm L.M (OkPriv (g.RL L)) (x, mon) ls t') :
    ∃ k d', RealT env p Bnd ls k (encT U (.run (ClifLift.pushC g.ext sR)), D) d' ∧
      (k = ls.length ∨
        (∃ vals cm, Clif.step env p sR = .done vals cm ∧ caller.regs.setMany results vals = none ∧
          k = 0 ∧ d' = (encT U (.run (ClifLift.pushC g.ext sR)), D)) ∨
        ∃ vals cm regs v, Clif.step env p sR = .done vals cm ∧
          caller.regs.setMany results vals = some regs ∧
          RetC (g.RL L) g.ra (g.r0 L) (iterN (g.RL L).step k x) ∧
          PRun Policy.arm L.M (OkPriv (g.RL L)) (x, mon) (ls.take k) v ∧
          v.1 = set_program (iterN (g.RL L).step k x) (g.caller.fb.program g.caller.base) ∧
          d' = (encT U (.run ⟨{ caller with regs := regs }, cs, cm⟩),
            fun a => D a ∨ PrivA (g.RL L) a)) := by
  obtain ⟨n, vals, cm, -, hdone, hRC, -, hall⟩ :=
    CallRetT.realizedT_ret (Bnd := Bnd) hok hmem hwf habi hra hcA hrA hret hat hcall hb
  cases hreg : caller.regs.setMany results vals with
  | none =>
    exact ⟨0, (encT U (.run (ClifLift.pushC g.ext sR)), D), RealizedT.zero _ _ _,
      .inr (.inl ⟨vals, cm, hdone, hreg, rfl, rfl⟩)⟩
  | some regs =>
    obtain ⟨h1, h2⟩ := hall (cs := cs) hreg U D hr
    by_cases hlt : ls.length < n
    · refine ⟨ls.length, (encT U (.run (ClifLift.pushC g.ext sR)),
        fun a => D a ∨ PrivA (g.RL L) a), ?_, .inl rfl⟩
      show RealizedT env p Bnd ls ls.length _ _ _ _
      rw [hext]; exact h1 hlt
    · obtain ⟨v, hv, hv1, hRT⟩ := h2 (by omega)
      refine ⟨n, (encT U (.run ⟨{ caller with regs := regs }, cs, cm⟩),
        fun a => D a ∨ PrivA (g.RL L) a), ?_,
        .inr (.inr ⟨vals, cm, regs, v, hdone, hreg, hRC, hv, hv1, rfl⟩)⟩
      show RealizedT env p Bnd ls n _ _ _ _
      rw [hext]; exact hRT

/-! ## The call pause: the CLIF call -/

theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp at h
  | (x, y) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hx
      cases h
      have : a = x := by simpa using hx
      subst this; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- **A CLIF call that steps** (below any callers): the extern, its arguments of the declared
types, and a program function of matching signature types (no environment extern). -/
theorem call_next {ext : List (Clif.Frame × List Clif.ValueId)} {s : Clif.State}
    {results : List Clif.ValueId} {fn : Clif.FnRef} {args : List Clif.ValueId}
    {rest : List Clif.Stmt} (hb : s.frame.body = { results, inst := .call fn args } :: rest)
    (henv : ∀ e ∈ s.frame.func.externs, env.extern e.2.name = none) {s1 : Clif.State}
    (hs : Clif.step env p (ClifLift.pushC ext s) = .next s1) :
    ∃ e vals callee, s.frame.func.extern? fn = some e ∧ s.frame.getMany args = .ok vals ∧
      vals.map (·.ty) = Clif.AbiParam.tys e.sig.params ∧ p.func? e.name = some callee ∧
      Clif.AbiParam.tys callee.sig.params = Clif.AbiParam.tys e.sig.params ∧
      Clif.AbiParam.tys callee.sig.returns = Clif.AbiParam.tys e.sig.returns := by
  rw [Clif.step_call env p _ rest results fn args (by simpa [ClifLift.pushC] using hb)] at hs
  simp only [Clif.stepCall, ClifLift.pushC] at hs
  cases he : s.frame.func.extern? fn with
  | none => simp [he, Clif.StepResult.ofRes] at hs
  | some e =>
    cases hv : s.frame.getMany args with
    | trap c => simp [he, hv, Clif.StepResult.ofRes] at hs
    | stuck m => simp [he, hv, Clif.StepResult.ofRes] at hs
    | ok vals =>
      by_cases ht : vals.map (·.ty) = Clif.AbiParam.tys e.sig.params
      · cases hc : p.func? e.name with
        | none =>
          have := henv _ (mem_of_lookup he)
          simp [he, hv, ht, hc, this, Clif.StepResult.ofRes, Clif.checkTys, Clif.Res.check] at hs
        | some callee =>
          by_cases hsig : Clif.AbiParam.tys callee.sig.params = Clif.AbiParam.tys e.sig.params ∧
              Clif.AbiParam.tys callee.sig.returns = Clif.AbiParam.tys e.sig.returns
          · exact ⟨e, vals, callee, rfl, rfl, ht, hc, hsig.1, hsig.2⟩
          · exfalso
            simp [he, hv, ht, hc, Clif.StepResult.ofRes, Clif.checkTys, Clif.Res.check] at hs
            split at hs
            · exact absurd ‹_› hsig
            · cases hs
      · simp [he, hv, ht, Clif.StepResult.ofRes, Clif.checkTys, Clif.Res.check] at hs

end Concurrency.CallSegOkG

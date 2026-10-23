import FV.Concurrency.CallRetT
import FV.Concurrency.CallValid
import FV.Concurrency.CallSegLift
import FV.Concurrency.CallStepT
import FV.Concurrency.CallEntryLink
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

/-! ## The ends of a realized prefix -/

/-- **The ends of a realized prefix short of the whole run** (module doc): the innermost frame
`s` of the CLIF thread (below callers `ext`) stops (`IselThread.Stop`: no step, or an
`atomic_cas` on read-only data) or is at an event-free return the prefix did not realize; or
the next CLIF step reads a masked byte; or the thread returns with masked bytes. -/
def EndT (env : Clif.Env) (p : Clif.Program) (_P : List Lab) (d : TState × (Nat → Prop)) : Prop :=
  (∃ ext s, strip d.1 = strip (.run (pushC ext s)) ∧
    (IselThread.Stop env p (.run s) ∨ ∃ v, CStep env p (.run s) [] (.ret v))) ∨
  (∃ evs t'', CStep env p d.1 evs t'' ∧ ReadsMasked (maskOf d.1) evs) ∨
  (∃ v, CStep env p d.1 [] (.ret v) ∧ ∃ a, maskOf d.1 a)

theorem EndT.app {A B : List Lab} {d : TState × (Nat → Prop)} (h : EndT env p B d) :
    EndT env p (A ++ B) d := h

/-! ## A chain segment on the thread -/

/-- **A chain segment of an activation below its callers is a realized prefix** (module doc):
the activation `R`'s own CLIF run from `s` refining a prefix of a precise run with private set
`PrivA R`, started below `ext` at a reachable state with mask `U` and a start-dirty set within
`PrivA R`, the mask and the addresses starting no location, ending as the chain theorems end
(whole run, `Stop`, or a pause `Pz`). -/
theorem seg_end {Bnd : Nat → Prop} {R : Backend.Proof.RL} (hb : ∀ a, PrivA R a → Bnd a)
    {c0 : TState} (hP : PartsOk env p c0 Loc) (hdisj : PartDisj Loc)
    {f : ArmState → ArmState} {ok : ArmState → Lab → Prop} {u t' : ArmState × Mon}
    {ls : List Lab} (hr : PRun Policy.arm f ok u ls t') {k : Nat} (hk : k ≤ ls.length)
    (ext : List (Clif.Frame × List Clif.ValueId)) {s : Clif.State}
    (hR : RReach env p c0 (.run (pushC ext s))) {trS : List (List (Ev SKind BVal))} {t : TState}
    {ψ : Nat × Nat → Nat × Nat} (hrun : CRun env p (.run s) trS t)
    (hx : CallCompose.XClosed (evTr (ls.take k)))
    (href : Refines Maps (PrivA R) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ)
    {U D : Nat → Prop} (hD : ∀ a, D a → PrivA R a ∨ U a ∨ ¬ ∃ n, Loc a n)
    {Pz : Clif.State → Prop}
    (hend : k = ls.length ∨ IselThread.Stop env p t ∨ ∃ s', t = .run s' ∧ Pz s') :
    ∃ k' d', RealT env p Bnd ls k' (encT U (.run (pushC ext s)), D) d' ∧
      (k' = ls.length ∨ EndT env p (ls.take k') d' ∨
        (k' = k ∧ ∃ s' M, Pz s' ∧ t = .run s' ∧
          d' = (encT M (.run (pushC ext s')), fun a => D a ∨ PrivA R a) ∧
          RReach env p c0 (.run (pushC ext s')))) := by
  obtain ⟨hacc, hReachEnd⟩ := seg_parts hP hR hrun
  have hu : Uniform trS := uniform_of_parts hdisj fun q x hx hF => (hacc q x hx).1 hF
  have hpos : ∀ q x, evAt trS q = some x → x.dir = .R → 0 < x.n :=
    fun q x hx hRd => (hacc q x hx).2 hRd
  have hns : ∀ q x, evAt trS q = some x → x.dir = .R → ¬ ¬ ∃ n, Loc x.loc n :=
    fun q x hx hRd hn => hn ⟨x.n, (hacc q x hx).1 (by rw [hRd]; decide)⟩
  rcases realizedT_lift (Bnd := Bnd) hr hk ext hrun hx href hD hu hpos hns hb with
    ⟨trS', s1, -, hRT, hs1, hret⟩ | ⟨k', -, trS', j, evs, -, -, sj, t'', hRT, hst, hm⟩
  · rcases hend with h | h | ⟨s', rfl, hz⟩
    · exact ⟨k, (encT (maskAfter U trS') (.run (pushC ext s1)), fun a => D a ∨ PrivA R a), hRT,
        .inl h⟩
    · refine ⟨k, (encT (maskAfter U trS') (.run (pushC ext s1)), fun a => D a ∨ PrivA R a), hRT,
        .inr (.inl (.inl ⟨ext, s1, by exact strip_encT (maskAfter U trS') (.run (pushC ext s1)),
          ?_⟩))⟩
      cases t with
      | run s' => obtain rfl := hs1 s' rfl; exact .inl h
      | ret v => exact .inr ⟨v, hret v rfl⟩
    · obtain rfl := hs1 s' rfl
      exact ⟨k, (encT (maskAfter U trS') (.run (pushC ext s1)), fun a => D a ∨ PrivA R a), hRT,
        .inr (.inr ⟨rfl, s1, _, hz, rfl, rfl, hReachEnd s1 rfl⟩)⟩
  · refine ⟨k', (encT (maskAfter U (trS'.take j)) (.run sj), fun a => D a ∨ PrivA R a), hRT,
      .inr (.inl (.inr (.inl ⟨evs, t'', cstep_withBytes.mpr hst, ?_⟩)))⟩
    show ReadsMasked (maskOf (encT (maskAfter U (trS'.take j)) (.run sj))) evs
    rw [maskOf_encT]; exact hm

end Concurrency.CallSegOkG

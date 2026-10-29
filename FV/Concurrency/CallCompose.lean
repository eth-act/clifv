module

public import FV.Concurrency.RealizeCompiled

@[expose] public section

/-!
# Calls: composing per-function refinements along the call (T2h, #311, layer 4b)

`csem`'s `call` step has no events, but the callee's Arm code accesses memory, so its events must
appear in the thread's trace. The decision (`docs/plans/atomics.md` §3e, *Calls*): the thread's
Arm machine runs the callee's code (no hook), and the callee's Arm events are matched through the
**callee's own refinement**, composed with the caller's along the call, as the linking induction
does for single-threaded runs (`E2E.ExecBytes`, `Reach`: the callee's activation at depth `M`);
an **external** callee's events are given by an explicit, trusted event contract
(`ExtEvContract`).

* `XClosed tr`: every successful store exclusive (`relXW`) of an Arm trace follows a load
  exclusive (`acqXR`) of the same trace. A segment with this property starts no monitor pair
  with an earlier segment, so monitor pairs (`ArmAllocThread.MonPair`) of a concatenation are the
  segments' (`monPair_left`, `monPair_right`).
* **`Refines.app`**: refinements of consecutive Arm segments into consecutive CLIF traces compose
  (`appMap`: the second segment's positions shifted past the first), the atomic updates the
  monitor pairs of the whole trace.
* `Realized env p Priv ls k c c'`: the first `k` labels of the Arm run `ls` realize a CLIF thread
  run from `c` to `c'` (`ClifCStepTerm.CRun`): `Refines Maps Priv` with the monitor pairs atomic,
  exclusive-closed; `Realized.trans` (`Refines.app`, `CRun.append`).
* `FunReal`: **the function contract** of an activation entered in the Arm thread state `u` with
  the CLIF thread state `c` (its frame pushed): every precise run under the run condition `ok`
  realizes a prefix that is the whole run, ends where the end condition `E` holds (of the
  realized Arm prefix and the CLIF state), or ends where the activation has returned (`Ret`).
* **`link_compose`, the linking induction**: per-function *segment* obligations (from an
  activation's invariant `Inv`, a run realizes a prefix that ends, returns, or ends at a call:
  the callee entered with its entry relation `Ent`, the caller's invariant again after every
  return `Ret` of the callee) and the external callees' contracts give `FunReal` for every
  activation of every function (strong induction on the run's length; the call consumes at
  least the `bl`).
* **`ExtEvContract`**: the event contract of external callees (trusted: code outside the
  program): the outside code's Arm run from an entry realizes a CLIF-level run of the callee's
  specification (`Realized`: its events with `Maps` kinds, in order, its CLIF events outside the
  thread's private set, its other writes private, atomic updates the monitor pairs) up to its
  return, and its writes avoid the caller's private set `Fr`.
* `realizes_linked`: `RealizeCompiled.realizes_compiled` for threads given by their contracts
  (`FunReal` of the threads' entry activations, through `realizes_of_threads_priv`).
-/

namespace Concurrency.CallCompose

open Arm ArmThread Prog ClifThread ProgE2E ThreadRefine ArmAllocThread ClifCStepTerm PrepThread
  ThreadCompose RealizeCompiled

/-! ## Traces -/

section traces
variable {α : Type}

theorem evAt_shift (A B : List (List α)) (q : Nat × Nat) :
    evAt (A ++ B) (shift A.length q) = evAt B q := by
  rw [evAt_append_ge _ _ (by simp [shift])]
  simp [shift]

theorem conv_append (A B : List (List Ev)) : conv (A ++ B) = conv A ++ conv B := List.map_append

@[simp] theorem conv_length (A : List (List Ev)) : (conv A).length = A.length := List.length_map _

theorem lt_of_isSome {tr : List (List α)} {p : Nat × Nat} (h : (evAt tr p).isSome) :
    p.1 < tr.length := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
  exact evAt_lt hx

end traces

/-- **Exclusive-closed Arm traces**: every successful store exclusive (`relXW`) follows a load
exclusive (`acqXR`) of the trace. -/
def XClosed (tr : List (List Ev)) : Prop :=
  ∀ b y, evAt tr b = some y → y.k = .relXW → ∃ a x, evAt tr a = some x ∧ x.k = .acqXR ∧ Lt a b

theorem xClosed_nil : XClosed [] := fun b y hy => by rw [evAt_nil] at hy; cases hy

/-- A trace without store exclusive events is exclusive-closed. -/
theorem xClosed_of {tr : List (List Ev)} (h : ∀ b y, evAt tr b = some y → y.k ≠ .relXW) :
    XClosed tr := fun b y hy hk => absurd hk (h b y hy)

theorem XClosed.append {A B : List (List Ev)} (hA : XClosed A) (hB : XClosed B) :
    XClosed (A ++ B) := by
  intro b y hy hk
  by_cases hb : b.1 < A.length
  · rw [evAt_append_lt _ _ hb] at hy
    obtain ⟨a, x, hx, hxk, hab⟩ := hA b y hy hk
    have ha : a.1 < A.length := evAt_lt hx
    exact ⟨a, x, by rw [evAt_append_lt _ _ ha]; exact hx, hxk, hab⟩
  · rw [evAt_append_ge _ _ (by omega)] at hy
    obtain ⟨a, x, hx, hxk, hab⟩ := hB _ y hy hk
    refine ⟨shift A.length a, x, by rw [evAt_shift]; exact hx, hxk, ?_⟩
    obtain ⟨b1, b2⟩ := b
    simp only [Lt, shift] at hab ⊢
    omega

/-! ## Monitor pairs of a concatenation -/

/-- The monitor pairs of `A ++ B` ending in `A` are `A`'s. -/
theorem monPair_left {A B : List (List Ev)} {a b : Nat × Nat} (hb : b.1 < A.length) :
    MonPair (A ++ B) a b ↔ MonPair A a b := by
  have e : ∀ q : Nat × Nat, q.1 < A.length → evAt (A ++ B) q = evAt A q := fun q hq =>
    evAt_append_lt _ _ hq
  have hlt : ∀ q : Nat × Nat, Lt q b → q.1 < A.length := fun q h => by
    rcases h with h | ⟨h, -⟩ <;> omega
  constructor
  · rintro ⟨⟨x, hx, hxk⟩, ⟨y, hy, hyk⟩, hab, hbt⟩
    exact ⟨⟨x, by rw [← e a (hlt a hab)]; exact hx, hxk⟩, ⟨y, by rw [← e b hb]; exact hy, hyk⟩,
      hab, fun q z h1 h2 hz => hbt q z h1 h2 (by rw [e q (hlt q h2)]; exact hz)⟩
  · rintro ⟨⟨x, hx, hxk⟩, ⟨y, hy, hyk⟩, hab, hbt⟩
    exact ⟨⟨x, by rw [e a (hlt a hab)]; exact hx, hxk⟩, ⟨y, by rw [e b hb]; exact hy, hyk⟩, hab,
      fun q z h1 h2 hz => hbt q z h1 h2 (by rw [← e q (hlt q h2)]; exact hz)⟩

/-- The monitor pairs of `A ++ B` starting in `B` are `B`'s, shifted. -/
theorem monPair_right {A B : List (List Ev)} {a b : Nat × Nat} :
    MonPair (A ++ B) (shift A.length a) (shift A.length b) ↔ MonPair B a b := by
  constructor
  · rintro ⟨⟨x, hx, hxk⟩, ⟨y, hy, hyk⟩, hab, hbt⟩
    refine ⟨⟨x, by rw [← evAt_shift A]; exact hx, hxk⟩, ⟨y, by rw [← evAt_shift A]; exact hy, hyk⟩,
      lt_shift.1 hab, fun q z h1 h2 hz => hbt (shift A.length q) z (lt_shift.2 h1) (lt_shift.2 h2)
        (by rw [evAt_shift]; exact hz)⟩
  · rintro ⟨⟨x, hx, hxk⟩, ⟨y, hy, hyk⟩, hab, hbt⟩
    refine ⟨⟨x, by rw [evAt_shift]; exact hx, hxk⟩, ⟨y, by rw [evAt_shift]; exact hy, hyk⟩,
      lt_shift.2 hab, fun q z h1 h2 hz => ?_⟩
    have hq : A.length ≤ q.1 := by
      obtain ⟨a1, a2⟩ := a; obtain ⟨q1, q2⟩ := q
      simp only [Lt, shift] at h1; omega
    have e : q = shift A.length (q.1 - A.length, q.2) := by
      obtain ⟨q1, q2⟩ := q; simp only [shift] at hq ⊢; congr 1; omega
    rw [e] at h1 h2 hz
    rw [evAt_shift] at hz
    exact hbt _ z (lt_shift.1 h1) (lt_shift.1 h2) hz

/-! ## Refinements of consecutive segments -/

/-- The position map of two consecutive refinements: the first `n` source steps through `ψ1`, the
rest through `ψ2` shifted past the first target segment's `m` steps. -/
def appMap (n m : Nat) (ψ1 ψ2 : Nat × Nat → Nat × Nat) (p : Nat × Nat) : Nat × Nat :=
  if p.1 < n then ψ1 p else shift m (ψ2 (p.1 - n, p.2))

section app
variable {K : Type} {MK : K → AKind → Prop} {Priv : Nat → Prop}

theorem appMap_lt {n m : Nat} {ψ1 ψ2 : Nat × Nat → Nat × Nat} {p : Nat × Nat} (h : p.1 < n) :
    appMap n m ψ1 ψ2 p = ψ1 p := by simp [appMap, h]

theorem appMap_ge {n m : Nat} {ψ1 ψ2 : Nat × Nat → Nat × Nat} {p : Nat × Nat} (h : ¬ p.1 < n) :
    appMap n m ψ1 ψ2 p = shift m (ψ2 (p.1 - n, p.2)) := by simp [appMap, h]

theorem appMap_shift {n m : Nat} {ψ1 ψ2 : Nat × Nat → Nat × Nat} (q : Nat × Nat) :
    appMap n m ψ1 ψ2 (shift n q) = shift m (ψ2 q) := by
  obtain ⟨q1, q2⟩ := q
  have h : ¬ (shift n (q1, q2)).1 < n := by simp only [shift]; omega
  rw [appMap_ge h]
  simp [shift]

/-- **Refinements of consecutive Arm segments compose**, the second segment exclusive-closed or
the first one without load exclusive (so no monitor pair of the whole trace starts in the first
segment and ends in the second). -/
theorem Refines.app {A B : List (List (Ev K BVal))} {TA TB : List (List Ev)}
    {ψ1 ψ2 : Nat × Nat → Nat × Nat}
    (h1 : Refines MK Priv (MonPair TA) A (conv TA) ψ1)
    (h2 : Refines MK Priv (MonPair TB) B (conv TB) ψ2)
    (hx : XClosed TB ∨ ∀ a x, evAt TA a = some x → x.k ≠ .acqXR) :
    Refines MK Priv (MonPair (TA ++ TB)) (A ++ B) (conv (TA ++ TB))
      (appMap A.length TA.length ψ1 ψ2) := by
  have sA : ∀ p, (evAt A p).isSome → p.1 < A.length := fun p h => lt_of_isSome h
  have tA : ∀ p, (evAt A p).isSome → (ψ1 p).1 < TA.length := fun p h => by
    have := lt_of_isSome (h1.img h); simpa using this
  have eS : ∀ p : Nat × Nat, ¬ p.1 < A.length → evAt (A ++ B) p = evAt B (p.1 - A.length, p.2) :=
    fun p h => evAt_append_ge _ _ (by omega)
  have eS' : ∀ q : Nat × Nat, (q.1 + A.length - A.length, q.2) = q := fun q => by
    obtain ⟨q1, q2⟩ := q; simp
  rw [conv_append]
  exact {
    ev := fun p x hx => by
      by_cases hp : p.1 < A.length
      · rw [evAt_append_lt _ _ hp] at hx
        obtain ⟨y, hy, rest⟩ := h1.ev p x hx
        refine ⟨y, ?_, rest⟩
        rw [appMap_lt hp, evAt_append_lt _ _ (evAt_lt hy)]
        exact hy
      · rw [eS p hp] at hx
        obtain ⟨y, hy, rest⟩ := h2.ev _ x hx
        refine ⟨y, ?_, rest⟩
        rw [appMap_ge hp, ← conv_length TA, evAt_shift]
        exact hy
    mono := fun p q hp hq hl => by
      by_cases hpa : p.1 < A.length <;> by_cases hqa : q.1 < A.length
      · rw [evAt_append_lt _ _ hpa] at hp
        rw [evAt_append_lt _ _ hqa] at hq
        rw [appMap_lt hpa, appMap_lt hqa]
        exact h1.mono p q hp hq hl
      · rw [evAt_append_lt _ _ hpa] at hp
        rw [appMap_lt hpa, appMap_ge hqa]
        have := tA p hp
        left; simp only [shift]; omega
      · exfalso
        obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
        simp only [Lt] at hl hpa hqa; omega
      · rw [eS p hpa] at hp
        rw [eS q hqa] at hq
        rw [appMap_ge hpa, appMap_ge hqa]
        refine lt_shift.2 (h2.mono _ _ hp hq ?_)
        obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
        simp only [Lt] at hl hpa hqa ⊢; omega
    shared := fun p x hx hF hP => by
      by_cases hp : p.1 < A.length
      · rw [evAt_append_lt _ _ hp] at hx; exact h1.shared p x hx hF hP
      · rw [eS p hp] at hx; exact h2.shared _ x hx hF hP
    priv := fun p y hy hW hn => by
      by_cases hp : p.1 < (conv TA).length
      · rw [evAt_append_lt _ _ hp] at hy
        refine h1.priv p y hy hW fun q hq e => hn q ?_ ?_
        · rw [evAt_append_lt _ _ (sA q hq)]; exact hq
        · rw [appMap_lt (sA q hq)]; exact e
      · rw [evAt_append_ge _ _ (by omega)] at hy
        refine h2.priv _ y hy hW fun q hq e => hn (shift A.length q) ?_ ?_
        · rw [evAt_shift]; exact hq
        · rw [appMap_shift, e]
          obtain ⟨p1, p2⟩ := p
          simp only [conv_length] at hp
          have := conv_length TA
          simp only [shift]; congr 1; omega
    len := fun j hj => by
      by_cases hja : j < A.length
      · rw [List.getElem_append_left hja]; exact h1.len j hja
      · rw [List.getElem_append_right (by omega)]
        exact h2.len _ (by simp at hj; omega)
    pair := fun j hj h2l => by
      by_cases hja : j < A.length
      · rw [List.getElem_append_left hja] at h2l
        have hp := h1.pair j hja h2l
        rw [appMap_lt (p := (j, 0)) hja, appMap_lt (p := (j, 1)) hja]
        have hb : (ψ1 (j, 1)).1 < TA.length := tA _ (by
          simp only [evAt, List.getElem?_eq_getElem hja, Option.bind_some]
          rw [List.getElem?_eq_getElem (by omega)]; rfl)
        exact (monPair_left hb).2 hp
      · rw [List.getElem_append_right (by omega)] at h2l
        have hjb : j - A.length < B.length := by simp at hj; omega
        have hp := h2.pair _ hjb h2l
        rw [appMap_ge (p := (j, 0)) hja, appMap_ge (p := (j, 1)) hja]
        exact monPair_right.2 hp
    pair_inv := fun p q hp hq hpr => by
      by_cases hpa : p.1 < A.length <;> by_cases hqa : q.1 < A.length
      · rw [evAt_append_lt _ _ hpa] at hp
        rw [evAt_append_lt _ _ hqa] at hq
        rw [appMap_lt hpa, appMap_lt hqa] at hpr
        exact h1.pair_inv p q hp hq ((monPair_left (tA q hq)).1 hpr)
      · -- a monitor pair from the first segment into the second: excluded by `hx`
        exfalso
        rw [evAt_append_lt _ _ hpa] at hp
        rw [eS q hqa] at hq
        rw [appMap_lt hpa, appMap_ge hqa] at hpr
        obtain ⟨⟨x0, hx0, hx0k⟩, ⟨y, hy, hyk⟩, -, hbt⟩ := hpr
        have hpl := tA p hp
        rcases hx with hx | hx
        · rw [evAt_shift] at hy
          obtain ⟨a, x, hxa, hxk, hab⟩ := hx _ y hy hyk
          refine (hbt (shift TA.length a) x ?_ (lt_shift.2 hab)
            (by rw [evAt_shift]; exact hxa)).1 hxk
          left; simp only [shift]; omega
        · rw [evAt_append_lt _ _ hpl] at hx0
          exact hx _ x0 hx0 hx0k
      · exfalso
        rw [eS p hpa] at hp
        rw [evAt_append_lt _ _ hqa] at hq
        rw [appMap_ge hpa, appMap_lt hqa] at hpr
        obtain ⟨-, -, hab, -⟩ := hpr
        have := tA q hq
        simp only [Lt, shift] at hab; omega
      · rw [eS p hpa] at hp
        rw [eS q hqa] at hq
        rw [appMap_ge hpa, appMap_ge hqa] at hpr
        obtain ⟨j, e0, e1⟩ := h2.pair_inv _ _ hp hq (monPair_right.1 hpr)
        refine ⟨j + A.length, ?_, ?_⟩
        · obtain ⟨p1, p2⟩ := p
          simp only [Prod.mk.injEq] at e0 hpa ⊢; omega
        · obtain ⟨q1, q2⟩ := q
          simp only [Prod.mk.injEq] at e1 hqa ⊢; omega }

/-- The empty source refines any target without writes outside `Priv`. -/
theorem refines_nil : Refines MK Priv (MonPair []) ([] : List (List (Ev K BVal))) (conv []) id where
  ev p x hx := by rw [evAt_nil] at hx; cases hx
  mono p _ hp := by rw [evAt_nil] at hp; cases hp
  shared p x hx := by rw [evAt_nil] at hx; cases hx
  priv p y hy := by simp [conv, evAt_nil] at hy
  len j hj := absurd hj (Nat.not_lt_zero _)
  pair j hj := absurd hj (Nat.not_lt_zero _)
  pair_inv p _ hp := by rw [evAt_nil] at hp; cases hp

end app

/-! ## Realized prefixes -/

section realized
variable (env : Clif.Env) (p : Clif.Program) (Priv : Nat → Prop)

/-- **The first `k` labels of the Arm run `ls` realize a CLIF thread run** from `c` to `c'`:
`Refines Maps Priv`, the atomic updates the prefix's monitor pairs, the prefix exclusive-closed. -/
def Realized (ls : List Lab) (k : Nat) (c c' : TState) : Prop :=
  k ≤ ls.length ∧ ∃ (trS : List (List (Ev SKind BVal))) (ψ : Nat × Nat → Nat × Nat),
    CRun env p c trS c' ∧ XClosed (evTr (ls.take k)) ∧
    Refines Maps Priv (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ

variable {env p Priv}

theorem Realized.zero (ls : List Lab) (c : TState) : Realized env p Priv ls 0 c c :=
  ⟨Nat.zero_le _, [], id, .nil, by simpa [evTr] using xClosed_nil, by simpa [evTr] using refines_nil⟩

theorem Realized.le {ls : List Lab} {k : Nat} {c c' : TState} (h : Realized env p Priv ls k c c') :
    k ≤ ls.length := h.1

/-- **Realized prefixes compose**: `k1` labels from `c` to `c1`, then `k2` labels of the rest
from `c1` to `c2`. -/
theorem Realized.trans {ls : List Lab} {k1 k2 : Nat} {c c1 c2 : TState}
    (h1 : Realized env p Priv ls k1 c c1) (h2 : Realized env p Priv (ls.drop k1) k2 c1 c2) :
    Realized env p Priv ls (k1 + k2) c c2 := by
  obtain ⟨hk1, A, ψ1, r1, x1, f1⟩ := h1
  obtain ⟨hk2, B, ψ2, r2, x2, f2⟩ := h2
  have e : evTr (ls.take (k1 + k2)) = evTr (ls.take k1) ++ evTr ((ls.drop k1).take k2) := by
    rw [List.take_add, evTr_append]
  refine ⟨by simp at hk2; omega, A ++ B, appMap A.length (evTr (ls.take k1)).length ψ1 ψ2,
    r1.append r2, ?_, ?_⟩
  · rw [e]; exact x1.append x2
  · rw [e]; exact Refines.app f1 f2 (.inl x2)

end realized

/-! ## The function contract and the linking induction -/

section link
variable (env : Clif.Env) (p : Clif.Program) (Priv : Nat → Prop) (M : ArmState → ArmState)
  (ok : ArmState → Lab → Prop)

/-- An Arm thread state with its exclusive monitor. -/
abbrev AT := ArmState × Mon

/-- **The function contract** of an activation entered in `u` with the CLIF thread state `c` (its
frame pushed): every precise run under `ok` realizes a prefix that is the whole run, or ends where
the end condition `E` holds of the realized Arm prefix and the CLIF state (e.g. the CLIF thread
stops, or the prefix drives an activation's allocated code to its end), or ends where the
activation has returned (`Ret u c v c'`: the Arm state `v` and the CLIF state `c'` after its
return). -/
def FunReal (Ret : AT → TState → AT → TState → Prop) (E : List Lab → TState → Prop) (u : AT)
    (c : TState) : Prop :=
  ∀ ls t', PRun Policy.arm M ok u ls t' → ∃ k c', Realized env p Priv ls k c c' ∧
    (k = ls.length ∨ E (ls.take k) c' ∨ ∃ v, PRun Policy.arm M ok u (ls.take k) v ∧ Ret u c v c')

/-- **The segment obligation of a function's activation** with invariant `Inv` (entered at `u`,
`c`; now at `x`, `d`): every precise run realizes a prefix that is the whole run, ends in `E`,
ends where the activation has returned, or ends after at least one step at the entry of a callee
`h` (`Ent h`), from whose every return (`Ret h`) the activation's invariant holds again. -/
def SegOk {G : Type} (Ent : G → AT → TState → Prop) (Ret : G → AT → TState → AT → TState → Prop)
    (E : List Lab → TState → Prop) (Inv : AT → TState → AT → TState → Prop) (g : G) : Prop :=
  ∀ u c x d, Inv u c x d → ∀ ls t', PRun Policy.arm M ok x ls t' →
    ∃ k d', Realized env p Priv ls k d d' ∧
      (k = ls.length ∨ E (ls.take k) d' ∨
        (∃ v, PRun Policy.arm M ok x (ls.take k) v ∧ Ret g u c v d') ∨
        (0 < k ∧ ∃ v h, PRun Policy.arm M ok x (ls.take k) v ∧ Ent h v d' ∧
          ∀ z d'', Ret h v d' z d'' → Inv u c z d''))

/-- **The event contract of external callees** (trusted: code outside the program, not compiled
by us). For every external callee `h` (`Ext h`) entered in the Arm thread state `u` with the CLIF
state `c` (`Ent h u c`: `c` runs the callee's CLIF-level specification), every precise run of
the thread's machine under `ok` realizes a CLIF-level run of the specification
(`Realized`: its Arm events are the CLIF events, with `Maps` kinds, in order, the CLIF events
outside the thread's private set `Priv`, its other writes private, its atomic updates monitor
pairs) on a prefix that is the whole run, ends in `E`, or ends at the callee's return (`Ret h`),
and **the writes of that prefix avoid the caller's private set** `Fr u` (the outside code
touches the thread's stack only below the caller's frame). -/
structure ExtEvContract {G : Type} (Ext : G → Prop) (Ent : G → AT → TState → Prop)
    (Ret : G → AT → TState → AT → TState → Prop) (E : List Lab → TState → Prop)
    (Fr : AT → Nat → Prop) : Prop where
  real : ∀ h u c, Ext h → Ent h u c → ∀ ls t', PRun Policy.arm M ok u ls t' →
    ∃ k c', Realized env p Priv ls k c c' ∧
      (∀ q y, evAt (evTr (ls.take k)) q = some y → y.k.dir = .W → ¬ Fr u y.addr.toNat) ∧
      (k = ls.length ∨ E (ls.take k) c' ∨ ∃ v, PRun Policy.arm M ok u (ls.take k) v ∧ Ret h u c v c')

variable {env p Priv M ok}

/-- The contract gives the external callees' function contracts. -/
theorem ExtEvContract.funReal {G : Type} {Ext : G → Prop} {Ent : G → AT → TState → Prop}
    {Ret : G → AT → TState → AT → TState → Prop} {E : List Lab → TState → Prop}
    {Fr : AT → Nat → Prop} (hX : ExtEvContract env p Priv M ok Ext Ent Ret E Fr) {h : G} {u : AT} {c : TState}
    (he : Ext h) (hen : Ent h u c) : FunReal env p Priv M ok (Ret h) E u c := fun ls t' hr => by
  obtain ⟨k, c', hR, -, hend⟩ := hX.real h u c he hen ls t' hr
  exact ⟨k, c', hR, hend⟩

theorem take_prun {u t' : AT} {ls : List Lab} (hr : PRun Policy.arm M ok u ls t') (k : Nat) :
    ∃ v, PRun Policy.arm M ok u (ls.take k) v ∧ PRun Policy.arm M ok v (ls.drop k) t' := by
  have := hr
  rw [← List.take_append_drop k ls] at this
  exact PRun.split _ _ this

/-- **The linking induction** (module doc): from the segment obligations of the program's
functions and the external callees' contracts, every activation entered by `Ent` satisfies the
function contract (the end condition `E` closed under prefixing the Arm run with the caller's
part, `hE`). -/
theorem link_compose {G : Type} {Ext : G → Prop} {Ent : G → AT → TState → Prop}
    {Ret : G → AT → TState → AT → TState → Prop} {E : List Lab → TState → Prop}
    {Inv : G → AT → TState → AT → TState → Prop} (hE : ∀ A B d, E B d → E (A ++ B) d)
    (hinit : ∀ g u c, ¬ Ext g → Ent g u c → Inv g u c u c)
    (hseg : ∀ g, ¬ Ext g → SegOk env p Priv M ok Ent Ret E (Inv g) g)
    (hext : ∀ h u c, Ext h → Ent h u c → FunReal env p Priv M ok (Ret h) E u c) :
    ∀ g u c, Ent g u c → FunReal env p Priv M ok (Ret g) E u c := by
  -- the invariant's statement, by strong induction on the run's length
  have key : ∀ n g u c x d ls t', ls.length ≤ n → ¬ Ext g → Inv g u c x d →
      PRun Policy.arm M ok x ls t' → ∃ k d', Realized env p Priv ls k d d' ∧
        (k = ls.length ∨ E (ls.take k) d' ∨ ∃ v, PRun Policy.arm M ok x (ls.take k) v ∧
          Ret g u c v d') := by
    intro n
    induction n with
    | zero =>
      intro g u c x d ls t' hl hg hI hr
      obtain rfl : ls = [] := List.eq_nil_of_length_eq_zero (by omega)
      exact ⟨0, d, Realized.zero _ _, .inl rfl⟩
    | succ n ih =>
      intro g u c x d ls t' hl hg hI hr
      obtain ⟨k, d', hR, hend⟩ := hseg g hg u c x d hI ls t' hr
      rcases hend with h | h | h | ⟨hk, v, h, hv, hent, hres⟩
      · exact ⟨k, d', hR, .inl h⟩
      · exact ⟨k, d', hR, .inr (.inl h)⟩
      · exact ⟨k, d', hR, .inr (.inr h)⟩
      · -- the call: the callee's contract on the rest of the run
        have hkl := hR.le
        obtain ⟨v', hv', hrest⟩ := take_prun hr k
        obtain rfl := PRun.det hv' hv
        have hlen1 : (ls.drop k).length ≤ n := by simp; omega
        have hcal : ∃ k2 d2, Realized env p Priv (ls.drop k) k2 d' d2 ∧
            (k2 = (ls.drop k).length ∨ E ((ls.drop k).take k2) d2 ∨
              ∃ z, PRun Policy.arm M ok v' ((ls.drop k).take k2) z ∧ Ret h v' d' z d2) := by
          by_cases hx : Ext h
          · exact hext h v' d' hx hent _ _ hrest
          · exact ih h v' d' v' d' (ls.drop k) t' hlen1 hx (hinit h v' d' hx hent) hrest
        obtain ⟨k2, d2, hR2, hend2⟩ := hcal
        have hR12 := hR.trans hR2
        rcases hend2 with h2 | h2 | ⟨z, hz, hret⟩
        · refine ⟨k + k2, d2, hR12, .inl ?_⟩
          simp at h2; omega
        · refine ⟨k + k2, d2, hR12, .inr (.inl ?_)⟩
          rw [List.take_add]
          exact hE _ _ _ h2
        · -- the callee returned: the caller resumes on the rest
          have hk2 := hR2.le
          obtain ⟨z', hz', hrest2⟩ := take_prun hrest k2
          obtain rfl := PRun.det hz' hz
          have hlen2 : (ls.drop k |>.drop k2).length ≤ n := by simp; omega
          obtain ⟨k3, d3, hR3, hend3⟩ :=
            ih g u c z' d2 _ t' hlen2 hg (hres z' d2 hret) hrest2
          rw [List.drop_drop] at hR3 hend3
          have hR123 := hR12.trans hR3
          refine ⟨k + k2 + k3, d3, hR123, ?_⟩
          rcases hend3 with h3 | h3 | ⟨w, hw, hret3⟩
          · left; simp at h3 hk2 ⊢; omega
          · have e : ls.take (k + k2 + k3) = ls.take k ++ (ls.drop k).take k2 ++
                (ls.drop (k + k2)).take k3 := by
              rw [List.take_add, List.take_add]
            refine .inr (.inl ?_)
            rw [e]
            exact hE _ _ _ h3
          · refine .inr (.inr ⟨w, ?_, hret3⟩)
            have e : ls.take (k + k2 + k3) = ls.take k ++ (ls.drop k).take k2 ++
                (ls.drop (k + k2)).take k3 := by
              rw [List.take_add, List.take_add]
            rw [e]
            exact (hv'.append hz').append hw
  intro g u c hen ls t' hr
  by_cases hx : Ext g
  · exact hext g u c hx hen ls t' hr
  · exact key ls.length g u c u c ls t' (Nat.le_refl _) hx (hinit g u c hx hen) hr

/-- **The linking induction with external callees under their event contract.** -/
theorem link_compose_ext {G : Type} {Ext : G → Prop} {Ent : G → AT → TState → Prop}
    {Ret : G → AT → TState → AT → TState → Prop} {E : List Lab → TState → Prop}
    {Fr : AT → Nat → Prop} {Inv : G → AT → TState → AT → TState → Prop}
    (hE : ∀ A B d, E B d → E (A ++ B) d) (hinit : ∀ g u c, ¬ Ext g → Ent g u c → Inv g u c u c)
    (hseg : ∀ g, ¬ Ext g → SegOk env p Priv M ok Ent Ret E (Inv g) g)
    (hX : ExtEvContract env p Priv M ok Ext Ent Ret E Fr) :
    ∀ g u c, Ent g u c → FunReal env p Priv M ok (Ret g) E u c :=
  link_compose hE hinit hseg fun _ _ _ he hen => hX.funReal he hen

end link

/-! ## The program -/

/-- **The contract for `n` threads given by their function contracts** (`realizes_compiled` for
threads whose Arm runs realize prefixes, e.g. by `link_compose`): each thread `i` runs a precise
Arm run `ls i` of its machine `M i` under `ok i` from `sA i`, whose prefixes are realized from the
CLIF state `cs i` with the thread's private set `Priv i`. Every execution of the realized prefixes
(well formed, its `rmw` the monitor pairs, its initial locations beyond the CLIF ones private to
some thread, the CLIF ones with the same initial bytes) in which no thread's events touch another
thread's private set is realized by CLIF threads from the `cs i` (`Realizes`, any outcome). -/
theorem realizes_linked {n : Nat} {env : Clif.Env} {p : Clif.Program} {Priv : Nat → Nat → Prop}
    {M : Nat → ArmState → ArmState} {ok : Nat → ArmState → Lab → Prop} {cs : Nat → TState}
    {sA : Nat → AT}
    (hc : ∀ i < n, ∀ ls t', PRun Policy.arm (M i) (ok i) (sA i) ls t' →
      ∃ k c', Realized env p (Priv i) ls k (cs i) c')
    {ls : Nat → List Lab} {t' : Nat → AT}
    (hr : ∀ i < n, PRun Policy.arm (M i) (ok i) (sA i) (ls i) (t' i)) :
    ∃ k : Nat → Nat, (∀ i < n, k i ≤ (ls i).length) ∧
      ∀ (PA : Traces ProgE2E.AState AKind BVal) (locsA locsC : List (Nat × Nat)) (MA0 MC0 : Bytes)
        (rfA coA rmwA : Rel PEv), PA.n = n →
        (∀ i < n, PA.tr i = conv (evTr ((ls i).take (k i)))) →
        (PA.exec locsA rfA coA rmwA).Wf →
        (∀ i < n, ∀ a b, rmwA (.thr i a.1 a.2) (.thr i b.1 b.2) ↔
          MonPair (evTr ((ls i).take (k i))) a b) →
        locsC <+: locsA →
        (∀ q (h : q < locsA.length), locsC.length ≤ q → ∃ j, j < n ∧ Priv j (locsA[q]).1) →
        (∀ q (h : q < locsC.length),
          bytesI.get MA0 (locsC[q]).1 (locsC[q]).2 = bytesI.get MC0 (locsC[q]).1 (locsC[q]).2) →
        (∀ i < n, ∀ j < n, j ≠ i → ∀ q x, evAt (PA.tr i) q = some x → x.dir ≠ .F →
          ¬ Priv j x.loc) →
        ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = n ∧
          (∀ i < n, PC.st i 0 = cs i) ∧ PC.Runs (CStep env p) ∧
          Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ (fun _ _ _ => True) := by
  classical
  have hth : ∀ i (hi : i < n), ∃ (k : Nat) (trS : List (List (Ev SKind BVal))) (st : Nat → TState)
      (ψ : Nat × Nat → Nat × Nat), k ≤ (ls i).length ∧
      st 0 = cs i ∧ (∀ j (h : j < trS.length), CStep env p (st j) trS[j] (st (j + 1))) ∧
      Refines Maps (Priv i) (MonPair (evTr ((ls i).take k))) trS
        (conv (evTr ((ls i).take k))) ψ := fun i hi => by
    obtain ⟨k, c', hk, trS, ψ, hrun, -, href⟩ := hc i hi _ _ (hr i hi)
    obtain ⟨st, h0, hst, -⟩ := crun_states hrun
    exact ⟨k, trS, st, ψ, hk, h0, hst, href⟩
  let k : Nat → Nat := fun i => if hi : i < n then Classical.choose (hth i hi) else 0
  have hk : ∀ i (hi : i < n), ∃ (trS : List (List (Ev SKind BVal))) (st : Nat → TState)
      (ψ : Nat × Nat → Nat × Nat), k i ≤ (ls i).length ∧
      st 0 = cs i ∧ (∀ j (h : j < trS.length), CStep env p (st j) trS[j] (st (j + 1))) ∧
      Refines Maps (Priv i) (MonPair (evTr ((ls i).take (k i)))) trS
        (conv (evTr ((ls i).take (k i)))) ψ := fun i hi => by
    simp only [k, hi, dite_true]
    exact Classical.choose_spec (hth i hi)
  refine ⟨k, fun i hi => by obtain ⟨_, _, _, h, -⟩ := hk i hi; exact h, ?_⟩
  intro PA locsA locsC MA0 MC0 rfA coA rmwA hn htr hwf hrmw hlocs hpriv0 hval0 hdisj
  obtain ⟨PC, φ, hPn, hs0, hruns, hreal⟩ := PrivCoh.realizes_of_threads_priv (T := CStep env p)
    (s0 := cs) (PrivT := fun i l => i < n ∧ Priv i l)
    (pairT := fun i => MonPair (evTr ((ls i).take (k i)))) (Obs := fun _ _ _ => True)
    hwf (fun i hi => hrmw i (hn ▸ hi)) hlocs
    (fun q h hq => by obtain ⟨j, hj, hP⟩ := hpriv0 q h hq; exact ⟨j, hj, hP⟩) hval0 (fun i hi => by
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

end Concurrency.CallCompose

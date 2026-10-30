import FV.Concurrency.ClifMM

/-!
# Programs: thread semantics, the interleaving machine, executions of traces (T2e, #303)

The program level of the memory-model layer, generic in the thread semantics:

* a **thread semantics** `TSem σ K V` steps a thread state with a list of memory events (`Ev`:
  kind, direction, location, size, value);
* the **interleaving machine** `MStep I T` of a program: thread states and one shared memory (an
  interface `MemI`: read and write `n` bytes at a location); a step of thread `i` is a step of `T`
  whose reads return the memory's values, and it writes its writes. This is the sequentially
  consistent multi-threaded semantics;
* an **execution of a program** (`Traces.exec`): per-thread traces of `T` (`Traces.Runs`), initial
  writes (`init q`, one per initial location, thread 0), and the relations `rf`, `co`, `rmw` over
  the events `PEv`, as an `Exec` of `FV/Concurrency/Exec.lean`;
* **replay** (`replay`): a finite sequentially consistent execution of a program, whose reads read
  the values of their writes and whose accesses do not partially overlap, is a run of the
  interleaving machine from the initial memory to the threads' final states. Each step of a thread
  has at most one event or is an atomic update (`StepShape`).

`drf_sc_init`: DRF-SC (`ClifMM.drf_sc`) with initial writes, which race with nothing: they have no
incoming `po`/`com` edge, so they are on no cycle.

Plan: `docs/plans/atomics.md` (T2e).
-/

namespace Concurrency.Prog

open Rel

/-! ## Events, memory, thread semantics, the interleaving machine -/

/-- A memory event: kind, direction, location (start address), size, value. -/
structure Ev (K V : Type) where
  k : K
  dir : Dir
  loc : Nat
  n : Nat
  val : V

/-- A memory: `get M l n` the value of the `n` bytes at `l`, `put` writes them (`ok n v`: `v` is
a value of `n` bytes). Accesses of disjoint ranges do not interfere. -/
structure MemI (Mem V : Type) where
  get : Mem → Nat → Nat → V
  put : Mem → Nat → Nat → V → Mem
  ok : Nat → V → Prop
  get_put_same : ∀ M l n v, ok n v → get (put M l n v) l n = v
  get_put_disj : ∀ M l n v l' n', (l + n ≤ l' ∨ l' + n' ≤ l) → get (put M l n v) l' n' = get M l' n'

variable {K V Mem σ : Type}

/-- The memory after an event (a write writes, others do not). -/
def write1 (I : MemI Mem V) (M : Mem) (e : Ev K V) : Mem :=
  if e.dir = .W then I.put M e.loc e.n e.val else M

/-- The events of a step read the values of the memory (after the step's earlier writes). -/
def Agrees (I : MemI Mem V) : Mem → List (Ev K V) → Prop
  | _, [] => True
  | M, e :: es => (e.dir = .R → e.val = I.get M e.loc e.n) ∧ Agrees I (write1 I M e) es

/-- The memory after a step's events. -/
def applyEvs (I : MemI Mem V) (M : Mem) (es : List (Ev K V)) : Mem := es.foldl (write1 I) M

/-- A thread semantics: a step of a thread with its events. -/
abbrev TSem (σ K V : Type) := σ → List (Ev K V) → σ → Prop

/-- `ts` with thread `i` set to `s`. -/
def upd (ts : Nat → σ) (i : Nat) (s : σ) : Nat → σ := fun j => if j = i then s else ts j

/-- **The interleaving machine**: a step of one thread against the shared memory. -/
inductive MStep (I : MemI Mem V) (T : TSem σ K V) : (Nat → σ) × Mem → (Nat → σ) × Mem → Prop
  | mk {ts : Nat → σ} {M : Mem} {i : Nat} {es : List (Ev K V)} {s' : σ} :
      T (ts i) es s' → Agrees I M es → MStep I T (ts, M) (upd ts i s', applyEvs I M es)

/-- Runs of the interleaving machine. -/
inductive MRun (I : MemI Mem V) (T : TSem σ K V) : (Nat → σ) × Mem → (Nat → σ) × Mem → Prop
  | refl {c} : MRun I T c c
  | tail {c c' c''} : MRun I T c c' → MStep I T c' c'' → MRun I T c c''

/-! ## Executions of a program -/

/-- The traces of a program's threads `0 … n-1`: thread `i`'s steps' events `tr i` and its
states `st i j` (before step `j`). -/
structure Traces (σ K V : Type) where
  n : Nat
  tr : Nat → List (List (Ev K V))
  st : Nat → Nat → σ

/-- The traces are runs of `T`. -/
def Traces.Runs (T : TSem σ K V) (P : Traces σ K V) : Prop :=
  ∀ i < P.n, ∀ j (h : j < (P.tr i).length), T (P.st i j) ((P.tr i)[j]) (P.st i (j + 1))

/-- Events of an execution: the initial write `init q` (of the `q`-th initial location) and the
`k`-th event of step `j` of thread `i`. -/
inductive PEv where
  | init (q : Nat)
  | thr (i j k : Nat)
  deriving DecidableEq

/-- The event of the traces at a position. -/
def Traces.evAt (P : Traces σ K V) : PEv → Option (Ev K V)
  | .init _ => none
  | .thr i j k => if i < P.n then ((P.tr i)[j]?).bind (·[k]?) else none

/-- Program order: initial writes in their order, then each thread's events in order. -/
def PEv.po : PEv → PEv → Prop
  | .init q, .init q' => q < q'
  | .thr i j k, .thr i' j' k' => i = i' ∧ (j < j' ∨ (j = j' ∧ k < k'))
  | _, _ => False

/-- The thread of an event (`0`: the initial writes). -/
def PEv.tid : PEv → Nat
  | .init _ => 0
  | .thr i _ _ => i + 1

/-- The execution graph of the traces with the initial locations `locs` (location, size) and the
relations `rf`, `co`, `rmw`. Positions without an event are fences of no thread order
significance (`dir = F`, no `rf`/`co`) and are not events (`ev`). -/
def Traces.exec (P : Traces σ K V) (locs : List (Nat × Nat)) (rf co rmw : Rel PEv) : Exec PEv where
  tid := PEv.tid
  dir e := match e with
    | .init q => if q < locs.length then .W else .F
    | e => match P.evAt e with
      | some x => x.dir
      | none => .F
  loc e := match e with
    | .init q => (locs[q]?.getD (0, 0)).1
    | e => match P.evAt e with
      | some x => x.loc
      | none => 0
  po := PEv.po
  rf := rf
  co := co
  rmw := rmw
  ev e := match e with
    | .init q => q < locs.length
    | e => (P.evAt e).isSome

/-- The size of an event. -/
def Traces.sz (P : Traces σ K V) (locs : List (Nat × Nat)) : PEv → Nat
  | .init q => (locs[q]?.getD (0, 0)).2
  | e => match P.evAt e with
    | some x => x.n
    | none => 0

/-- The value of an event (an initial write: the initial memory's). -/
def Traces.val (I : MemI Mem V) (M0 : Mem) (P : Traces σ K V) (locs : List (Nat × Nat))
    (v0 : V) : PEv → V
  | .init q => I.get M0 (locs[q]?.getD (0, 0)).1 (locs[q]?.getD (0, 0)).2
  | e => match P.evAt e with
    | some x => x.val
    | none => v0

/-- The shape of the steps: no event, one event, or an atomic update (a read and then a write,
`rmw`-paired); `rmw` pairs only those. -/
def Traces.StepShape (P : Traces σ K V) (rmw : Rel PEv) : Prop :=
  (∀ i < P.n, ∀ j (h : j < (P.tr i).length), ((P.tr i)[j]).length ≤ 1 ∨
    (((P.tr i)[j]).length = 2 ∧ rmw (.thr i j 0) (.thr i j 1))) ∧
  (∀ a b, rmw a b → ∃ i j, a = .thr i j 0 ∧ b = .thr i j 1)

/-- Distinct accesses (of the same or different locations) do not partially overlap: the same
location has the same size, different locations have disjoint ranges. -/
def NoOverlap (X : Exec PEv) (sz : PEv → Nat) : Prop :=
  ∀ a b, X.dir a ≠ .F → X.dir b ≠ .F →
    (X.loc a = X.loc b → sz a = sz b) ∧
    (X.loc a ≠ X.loc b → X.loc a + sz a ≤ X.loc b ∨ X.loc b + sz b ≤ X.loc a)

/-- No write is `co`-before an initial write. -/
def InitFirst (X : Exec PEv) : Prop := ∀ w q, ¬ X.co w (.init q)

/-! ## Sequential consistency from a rank on the events of the execution -/

/-- **An execution is SC if a rank on its events (`V`) increases along `po` and `com`** (the
certificate the witnesses use; `po` on other positions does not matter, `com` relates events). -/
theorem sc_of_rank_on {E : Type} {X : Exec E} (hX : X.Wf) (V : E → Prop) (rank : E → Nat)
    (hcomV : ∀ a b, X.com a b → V a ∧ V b)
    (hpo : ∀ a b, V a → V b → X.po a b → rank a < rank b)
    (hcom : ∀ a b, X.com a b → rank a < rank b) : X.SC := by
  intro a ha
  rcases cycle_split hX.po_trans ha with h | ⟨b, hb⟩
  · exact hX.po_irrefl _ h
  · -- every step of the rotated cycle starts and ends at an event of `V`
    have step : ∀ x y, V x → seq (opt X.po) X.com x y → V y ∧ rank x < rank y := by
      rintro x y hx ⟨z, hxz, hzy⟩
      have hz := (hcomV _ _ hzy).1
      refine ⟨(hcomV _ _ hzy).2, ?_⟩
      rcases hxz with rfl | hxz
      · exact hcom _ _ hzy
      · exact Nat.lt_trans (hpo _ _ hx hz hxz) (hcom _ _ hzy)
    have hbV : V b := by
      obtain ⟨c, ⟨z, -, hz⟩⟩ := plus_last hb
      exact (hcomV _ _ hz).2
    have key : ∀ y, Relation.TransGen (seq (opt X.po) X.com) b y → V y ∧ rank b < rank y := by
      intro y h
      induction h with
      | single h => exact step _ _ hbV h
      | tail _ h2 ih =>
        obtain ⟨hc, hlt⟩ := ih
        obtain ⟨hy, hlt'⟩ := step _ _ hc h2
        exact ⟨hy, Nat.lt_trans hlt hlt'⟩
    exact Nat.lt_irrefl _ (key b hb).2

/-! ## DRF-SC with initial writes -/

theorem plus_restr_of_step {E : Type} {r : Rel E} {P : E → Prop}
    (ht : ∀ a b, r a b → P a → P b) {a b : E} (ha : P a) (h : Relation.TransGen r a b) :
    Relation.TransGen (restr P r) a b := by
  induction h with
  | single h => exact .single ⟨ha, h, ht _ _ h ha⟩
  | @tail c d hac h2 ih =>
    have hc : P c := by
      cases ih with
      | single h => exact h.2.2
      | tail _ h => exact h.2.2
    exact .tail ih ⟨hc, h2, ht _ _ h2 hc⟩

theorem plus_back {E : Type} {r s : Rel E} {P : E → Prop} (hs : Trans s)
    (hb : ∀ a b, P b → r a b → P a ∧ s a b) {a b : E} (h : Relation.TransGen r a b) (hP : P b) :
    s a b := by
  induction h with
  | single h => exact (hb _ _ hP h).2
  | @tail c d _ h2 ih =>
    have := hb _ _ hP h2
    exact hs _ _ _ (ih this.1) this.2

/-- **DRF-SC with initial writes**: race-freedom is needed only between non-initial events when
the initial events' incoming `po`/`com` edges are `po` edges from initial events. -/
theorem drf_sc_init {E : Type} {X : Exec E} {k : E → SKind} (Init : E → Prop) (hX : X.Wf)
    (hc : ClifMM.Consistent X k)
    (hr : ∀ a b, ¬ Init a → ¬ Init b → ClifMM.Conflict X a b → ¬ (ClifMM.At k a ∧ ClifMM.At k b) →
      ClifMM.hb X k a b ∨ ClifMM.hb X k b a)
    (hin : ∀ a b, Init b → union X.po X.com a b → Init a ∧ X.po a b) : X.SC := by
  let C : Rel E := restr (ClifMM.At k) X.com
  have hstep : ∀ a b, restr (fun e => ¬ Init e) (union X.po X.com) a b →
      Relation.TransGen (union X.po C) a b := by
    rintro a b ⟨ha, h | h, hb⟩
    · exact .single (.inl h)
    · by_cases hat : ClifMM.At k a ∧ ClifMM.At k b
      · exact .single (.inr ⟨hat.1, h, hat.2⟩)
      · have hcf : ClifMM.Conflict X a b :=
          ⟨hX.com_ne h, hX.com_loc h, (hX.com_notF h).1, (hX.com_notF h).2, hX.com_write h⟩
        rcases hr a b ha hb hcf hat with h' | h'
        · refine plus_mono ?_ h'
          rintro x y (h | h)
          · exact .inl h
          · exact .inr ⟨(ClifMM.sw_at h).1, .inl h.2.1, (ClifMM.sw_at h).2⟩
        · exact absurd (hc.coherence b a h' (.inr (.single h))) id
  intro a ha
  by_cases hia : Init a
  · exact hX.po_irrefl a (plus_back hX.po_trans hin ha hia)
  have hcyc := plus_flat hstep (plus_restr_of_step (P := fun e => ¬ Init e)
    (fun x y h hx hy => hx (hin x y hy h).1) hia ha)
  have hpo : Trans X.po := hX.po_trans
  rcases cycle_split hpo hcyc with h | ⟨b, hb⟩
  · exact hX.po_irrefl _ h
  · have hend : ∀ x y, seq (opt X.po) C x y → ClifMM.At k y := by
      rintro x y ⟨z, -, hz⟩; exact hz.2.2
    have hlift : ∀ {x y}, ClifMM.At k x → Relation.TransGen (seq (opt X.po) C) x y →
        Relation.TransGen (restr (ClifMM.At k) (union X.po X.com)) x y := by
      intro x y hx hxy
      have one : ∀ u v, ClifMM.At k u → seq (opt X.po) C u v →
          Relation.TransGen (restr (ClifMM.At k) (union X.po X.com)) u v := by
        rintro u v hu ⟨z, hz | hz, hzc⟩
        · subst hz; exact .single ⟨hu, .inr hzc.2.1, hzc.2.2⟩
        · exact .tail (.single ⟨hu, .inl hz, hzc.1⟩) ⟨hzc.1, .inr hzc.2.1, hzc.2.2⟩
      induction hxy with
      | single h => exact one _ _ hx h
      | tail h1 h2 ih =>
        obtain ⟨c, hc⟩ := plus_last h1
        exact ih.trans (one _ _ (hend _ _ hc) h2)
    obtain ⟨c, hlast⟩ := plus_last hb
    exact hc.sc b (hlift (hend _ _ hlast) hb)

end Concurrency.Prog

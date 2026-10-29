module

public import FV.Concurrency.ArmAllocThread

@[expose] public section

/-!
# Precise Arm runs of straight-line segments (T2h, #311, layer 4b)

The per-item lemmas of layer 4b (`docs/plans/atomics.md` §3e) compare a precise Arm run
(`ArmAllocThread.PRun`, reads returning any bytes) with the single-core run of the machine
(`iterN f`), which the register-level proof knows. Two cases cover the straight-line items:

* `prun_own`: when every read of the run returns the thread's own bytes (no read at all, or
  reads of the private set under `ok`), the run **is** the single-core run and its labels are
  the single-core steps' events (`segEvs`);
* `prun_one_read`: a segment whose single-core run has one read at step `i0` and no other event
  (on every memory after it): a precise run stops before the read (no event, single-core so
  far), or its read returns some bytes `e` and the run is the single-core run **from the state
  patched with `e`** (`VCodeThread.patch`), its labels that run's events.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot ArmPrecise Backend.Proof VCodeThread

/-- The events of `n` single-core steps of `f` from `s`, step by step. -/
def segEvs (f : ArmState → ArmState) : Nat → ArmState → List (List Ev)
  | 0, _ => []
  | n + 1, s => stepEvs s :: segEvs f n (f s)

theorem segEvs_length (f : ArmState → ArmState) : ∀ n s, (segEvs f n s).length = n
  | 0, _ => rfl
  | n + 1, s => by simp [segEvs, segEvs_length f n]

theorem segEvs_get (f : ArmState → ArmState) : ∀ n s i (h : i < n),
    (segEvs f n s)[i]'(by rw [segEvs_length]; exact h) = stepEvs (iterN f i s)
  | n + 1, s, 0, _ => rfl
  | n + 1, s, i + 1, h => by
    simp only [segEvs, List.getElem_cons_succ, iterN]
    exact segEvs_get f n (f s) i (by omega)

/-! ## Precise labels and own reads -/

theorem reread_of_agrees : ∀ {m M : Memory} {E : List Ev}, Agrees (reread m E) M → Agrees E M →
    reread m E = E
  | _, _, [], _, _ => rfl
  | m, M, e :: E, h1, h2 => by
    have h1' : Agrees (reread m E) M := fun x hx => h1 x (List.mem_cons_of_mem _ (by
      simpa [reread] using hx))
    have h2' : Agrees E M := fun x hx => h2 x (List.mem_cons_of_mem _ hx)
    have ih := reread_of_agrees h1' h2'
    simp only [reread, List.map_cons] at ih ⊢
    rw [ih]
    congr 1
    obtain ⟨k, a, n, v⟩ := e
    unfold reread1
    split
    · rename_i hr
      simp only at hr ⊢
      have a1 := h1 ⟨k, a, n, readM n a m⟩ (by simp [reread, reread1, hr]) hr
      have a2 := h2 ⟨k, a, n, v⟩ List.mem_cons_self hr
      simp only at a1 a2
      rw [← a1, a2]
    · rfl

/-- Reading back no read leaves the events. -/
theorem reread_noR : ∀ {m : Memory} {E : List Ev}, (∀ e ∈ E, e.k.dir ≠ .R) → reread m E = E
  | _, [], _ => rfl
  | m, e :: E, h => by
    simp only [reread, List.map_cons, reread1, h e List.mem_cons_self, ite_false]
    congr 1
    exact reread_noR fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem agrees_noR {E : List Ev} (h : ∀ e ∈ E, e.k.dir ≠ .R) (M : Memory) : Agrees E M :=
  fun e he hr => absurd hr (h e he)

/-- The step is no store exclusive (so it cannot fail). -/
def NoStx (s : ArmState) : Prop := ∀ rel rs rn, cls s ≠ .stx rel rs rn

/-- **A precise step reading its own bytes** is the single-core step, its label the step's
events. -/
theorem tstep_own {P : Policy} {f : ArmState → ArmState} {s : ArmState} {mon : Mon} {l : Lab}
    {t1 : ArmState × Mon} (hs : TStep P f (s, mon) l t1) (hp : Precise s l)
    (hag : Agrees l.evs s.mem) (hx : l.xfail = false) :
    t1.1 = f s ∧ l.evs = stepEvs s ∧ Footprint f s l.evs := by
  cases hs with
  | @exec _ _ evs _ _ hfp _ =>
    refine ⟨by show f (setMem (applyR evs s.mem) s) = f s; rw [applyR_of_agrees hag]; rfl,
      ?_, hfp⟩
    rcases hp with h | ⟨m, hm⟩
    · cases h
    · simp only at hm hag ⊢
      rw [stepEvs_setMem] at hm
      rw [hm] at hag ⊢
      exact reread_of_agrees hag (agrees_stepEvs s)
  | xfail => cases hx

/-- A step without events commutes with replacing the memory. -/
theorem foot_nil_comm {f : ArmState → ArmState} {s : ArmState} (h : Footprint f s []) (M : Memory) :
    f (setMem M s) = setMem M (f s) := by
  have := h M (agrees_nil M)
  simpa [applyW, applyR, setMem_self] using this

theorem foot_nil_mem {f : ArmState → ArmState} {s : ArmState} (h : Footprint f s []) :
    (f s).mem = s.mem := by
  have := foot_nil_comm h s.mem
  rw [setMem_self] at this
  rw [this]; rfl

/-- A step from a state without events or store exclusive: no event, the single-core step. -/
theorem tstep_nil {P : Policy} {f : ArmState → ArmState} {s : ArmState} {mon : Mon} {l : Lab}
    {t1 : ArmState × Mon} (hs : TStep P f (s, mon) l t1) (hp : Precise s l)
    (he : stepEvs s = []) (hx : NoStx s) :
    t1.1 = f s ∧ l.evs = [] ∧ Footprint f s [] := by
  have hxf : l.xfail = false := by
    cases hs with
    | exec => rfl
    | xfail hc => exact absurd hc (hx _ _ _)
  have hl : l.evs = [] := by
    rcases hp with h | ⟨m, hm⟩
    · rw [hxf] at h; cases h
    · rw [hm, stepEvs_setMem, he]; rfl
  obtain ⟨h1, -, h3⟩ := tstep_own hs hp (by rw [hl]; exact agrees_nil _) hxf
  exact ⟨h1, hl, hl ▸ h3⟩

/-! ## Runs -/

section runs
variable {P : Policy} {f : ArmState → ArmState} {ok : ArmState → Lab → Prop}

/-- **A precise run whose reads return the thread's own bytes** (and that has no failing store
exclusive) is the single-core run; its labels are that run's events. -/
theorem prun_own : ∀ {L : List Lab} {s : ArmState} {mon : Mon} {t' : ArmState × Mon},
    PRun P f ok (s, mon) L t' →
    (∀ i (h : i < L.length), Agrees L[i].evs (iterN f i s).mem ∧ L[i].xfail = false) →
    t'.1 = iterN f L.length s ∧ evTr L = segEvs f L.length s
  | [], _, _, _, .nil, _ => ⟨rfl, rfl⟩
  | l :: L, s, mon, t', .cons (t1 := t1) hs hp _ hr, h => by
    obtain ⟨h1, h2, -⟩ := tstep_own hs hp (h 0 (by simp)).1 (h 0 (by simp)).2
    obtain ⟨s1, mon1⟩ := t1
    simp only at h1
    subst h1
    have ih := prun_own hr fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [iterN] using this
    refine ⟨by simpa [iterN] using ih.1, ?_⟩
    simp only [evTr, List.map_cons, List.length_cons, segEvs] at ih ⊢
    rw [h2, ← ih.2]

/-- A precise run without events in its single-core steps: no event, the single-core run, every
step event-free (`Footprint` with no event). -/
theorem prun_nil : ∀ {L : List Lab} {s : ArmState} {mon : Mon} {t' : ArmState × Mon},
    PRun P f ok (s, mon) L t' →
    (∀ i < L.length, stepEvs (iterN f i s) = [] ∧ NoStx (iterN f i s)) →
    t'.1 = iterN f L.length s ∧ (∀ l ∈ L, l.evs = []) ∧
      ∀ i < L.length, Footprint f (iterN f i s) []
  | [], _, _, _, .nil, _ => ⟨rfl, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h (by simp)⟩
  | l :: L, s, mon, t', .cons (t1 := t1) hs hp _ hr, h => by
    obtain ⟨h1, h2, h3⟩ := tstep_nil hs hp (h 0 (by simp)).1 (h 0 (by simp)).2
    obtain ⟨s1, mon1⟩ := t1
    simp only at h1
    subst h1
    have ih := prun_nil hr fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [iterN] using this
    refine ⟨by simpa [iterN] using ih.1, ?_, fun i hi => ?_⟩
    · intro l' hl'
      rcases List.mem_cons.mp hl' with rfl | hl'
      · exact h2
      · exact ih.2.1 l' hl'
    · cases i with
      | zero => exact h3
      | succ i => simpa [iterN] using ih.2.2 i (by simp at hi; omega)

/-- Event-free single-core steps commute with replacing the memory. -/
theorem iterN_comm : ∀ {n : Nat} {s : ArmState},
    (∀ i < n, Footprint f (iterN f i s) []) → ∀ M, iterN f n (setMem M s) = setMem M (iterN f n s)
  | 0, _, _, _ => rfl
  | n + 1, s, h, M => by
    simp only [iterN]
    rw [foot_nil_comm (show Footprint f s [] from h 0 (by omega)) M]
    exact iterN_comm (s := f s) (fun i hi => by simpa [iterN] using h (i + 1) (by omega)) M

/-- The memory of event-free single-core steps is unchanged. -/
theorem iterN_nil_mem {n : Nat} {s : ArmState} (h : ∀ i < n, Footprint f (iterN f i s) []) :
    (iterN f n s).mem = s.mem := by
  have := iterN_comm h s.mem
  rw [setMem_self] at this
  rw [this]; rfl

theorem iterN_succ' (n : Nat) (s : ArmState) : iterN f (n + 1) s = f (iterN f n s) := by
  rw [iterN_add]; rfl

theorem iterN_one (s : ArmState) : iterN f 1 s = f s := rfl

theorem segEvs_one (s : ArmState) : segEvs f 1 s = [stepEvs s] := rfl

theorem segEvs_add : ∀ (a b : Nat) (s : ArmState),
    segEvs f (a + b) s = segEvs f a s ++ segEvs f b (iterN f a s)
  | 0, b, s => by simp [segEvs, iterN]
  | a + 1, b, s => by
    rw [Nat.add_right_comm]
    simp only [segEvs, iterN, List.cons_append]
    rw [segEvs_add a b (f s)]

theorem mem_segEvs : ∀ {n : Nat} {s : ArmState} {x : List Ev}, x ∈ segEvs f n s →
    ∃ i < n, x = stepEvs (iterN f i s)
  | 0, _, _, h => absurd h List.not_mem_nil
  | n + 1, s, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨0, by omega, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := mem_segEvs h
      exact ⟨i + 1, by omega, rfl⟩

theorem eq_of_nil {α : Type} {L L' : List (List α)} (hl : L.length = L'.length)
    (h : ∀ x ∈ L, x = []) (h' : ∀ x ∈ L', x = []) : L = L' :=
  List.ext_getElem hl fun i h1 h2 => by rw [h _ (List.getElem_mem h1), h' _ (List.getElem_mem h2)]

/-- `e` has the kind, address and size of `e0`. -/
def SameAcc (e e0 : Ev) : Prop := e.k = e0.k ∧ e.addr = e0.addr ∧ e.n = e0.n

/-- The read `e0` with the bytes of `M`. -/
theorem reread_one {e0 : Ev} (hR : e0.k.dir = .R) (M : Memory) :
    reread M [e0] = [⟨e0.k, e0.addr, e0.n, readM e0.n e0.addr M⟩] := by
  simp [reread, reread1, hR]

/-- A read patched into the memory is read back. -/
theorem stepEvs_patch_read {x : ArmState} {e0 : Ev} (hR : e0.k.dir = .R) (hn : e0.n ≤ 2 ^ 64)
    (hx : stepEvs x = [e0]) (m : Memory) (M : Memory) :
    stepEvs (setMem (applyR [⟨e0.k, e0.addr, e0.n, readM e0.n e0.addr m⟩] M) x) =
      [⟨e0.k, e0.addr, e0.n, readM e0.n e0.addr m⟩] := by
  rw [stepEvs_setMem, hx, reread_one hR]
  simp only [applyR, hR, ite_true, readM_writeM _ _ _ _ hn]

/-- **A precise run of a segment with one read** (module doc): the single-core run from `s` has
no event before step `i0`, the read `e0` at `i0`, and from any memory no event after it up to
`N`. A precise run of at most `N` steps stops before the read (no event, the single-core run), or
its read returns some bytes, `e`, and it is the single-core run from `s` patched with `e`. -/
theorem prun_one_read {N i0 : Nat} {s : ArmState} {e0 : Ev} (hR : e0.k.dir = .R)
    (hn : e0.n ≤ 2 ^ 64) (hi0 : i0 < N)
    (hpre : ∀ i < i0, stepEvs (iterN f i s) = [] ∧ NoStx (iterN f i s))
    (hat : stepEvs (iterN f i0 s) = [e0]) (hx0 : NoStx (iterN f i0 s))
    (hpost : ∀ e, SameAcc e e0 → ∀ i, i0 < i → i < N →
      stepEvs (iterN f i (patch [e] s)) = [] ∧ NoStx (iterN f i (patch [e] s)))
    {L : List Lab} {mon : Mon} {t' : ArmState × Mon} (hr : PRun P f ok (s, mon) L t')
    (hL : L.length ≤ N) :
    (L.length ≤ i0 ∧ t'.1 = iterN f L.length s ∧ ∀ l ∈ L, l.evs = []) ∨
    ∃ e, SameAcc e e0 ∧ t'.1 = iterN f L.length (patch [e] s) ∧
      evTr L = segEvs f L.length (patch [e] s) ∧
      ∀ i < N, stepEvs (iterN f i (patch [e] s)) = if i = i0 then [e] else [] := by
  by_cases hle : L.length ≤ i0
  · obtain ⟨h1, h2, -⟩ := prun_nil hr fun i hi => hpre i (by omega)
    exact .inl ⟨hle, h1, h2⟩
  right
  obtain ⟨A, l, B, rfl, hA⟩ : ∃ A l B, L = A ++ l :: B ∧ A.length = i0 := by
    refine ⟨L.take i0, L[i0]'(by omega), L.drop (i0 + 1), ?_, by simp; omega⟩
    simp
  obtain ⟨⟨x, mon1⟩, rA, rB⟩ := PRun.split A (l :: B) hr
  obtain ⟨hxA, hevA, hfA⟩ := prun_nil rA fun i hi => hpre i (by omega)
  rw [hA] at hxA hfA
  simp only at hxA
  subst hxA
  have hmem : (iterN f i0 s).mem = s.mem := iterN_nil_mem hfA
  cases rB with
  | @cons _ t2 _ _ _ hs hp _ rB =>
  have hxf : l.xfail = false := by
    cases hs with
    | exec => rfl
    | xfail hc => exact absurd hc (hx0 _ _ _)
  obtain ⟨m, hm⟩ : ∃ m, l.evs = stepEvs (setMem m (iterN f i0 s)) := by
    rcases hp with h | h
    · rw [hxf] at h; cases h
    · exact h
  rw [stepEvs_setMem, hat, reread_one hR] at hm
  let e : Ev := ⟨e0.k, e0.addr, e0.n, readM e0.n e0.addr m⟩
  have hcomm := iterN_comm hfA
  have hpe : iterN f i0 (patch [e] s) = patch [e] (iterN f i0 s) := by
    simp only [patch, hmem]; exact hcomm _
  have ht2 : t2.1 = iterN f (i0 + 1) (patch [e] s) := by
    cases hs with
    | exec =>
      simp only at hm
      subst hm
      rw [iterN_succ', hpe]; rfl
    | xfail => cases hxf
  have hate : stepEvs (iterN f i0 (patch [e] s)) = [e] := by
    rw [hpe]; exact stepEvs_patch_read hR hn hat m _
  have hpost' : ∀ i < B.length, stepEvs (iterN f i t2.1) = [] ∧ NoStx (iterN f i t2.1) := by
    intro i hi
    rw [ht2, ← iterN_add]
    exact hpost e ⟨rfl, rfl, rfl⟩ _ (by omega) (by simp at hL; omega)
  obtain ⟨s2, mon2⟩ := t2
  obtain ⟨hB, hevB, -⟩ := prun_nil rB hpost'
  simp only at ht2 hB
  subst ht2
  have hevs : ∀ i < N, stepEvs (iterN f i (patch [e] s)) = if i = i0 then [e] else [] := by
    intro i hi
    by_cases h1 : i = i0
    · rw [ite_eq_left h1, h1, hate]
    · rw [ite_eq_right h1]
      rcases Nat.lt_or_gt_of_ne h1 with h2 | h2
      · simp only [patch]
        have hfi : ∀ k < i, Footprint f (iterN f k s) [] := fun k hk => hfA k (by omega)
        rw [iterN_comm hfi, stepEvs_setMem, (hpre i h2).1]; rfl
      · exact (hpost e ⟨rfl, rfl, rfl⟩ i h2 hi).1
  refine ⟨e, ⟨rfl, rfl, rfl⟩, ?_, ?_, hevs⟩
  · rw [hB, ← iterN_add]; congr 1; simp; omega
  · have hlen : (A ++ l :: B).length = i0 + (B.length + 1) := by simp [hA]
    have hnil : ∀ i < N, i ≠ i0 → stepEvs (iterN f i (patch [e] s)) = [] := fun i hi hne => by
      rw [hevs i hi, ite_eq_right hne]
    have hN : i0 + (B.length + 1) ≤ N := by simp at hL; omega
    rw [hlen, segEvs_add, Nat.add_comm B.length 1, segEvs_add, segEvs_one, iterN_one]
    simp only [evTr, List.map_append, List.map_cons, List.singleton_append]
    congr 1
    · refine eq_of_nil (by simp [segEvs_length, hA]) (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hx
        exact hevA l' hl'
      · obtain ⟨i, hi, rfl⟩ := mem_segEvs hx
        exact hnil i (by omega) (by omega)
    · congr 1
      · rw [hm, hate]
      · refine eq_of_nil (by simp [segEvs_length]) (fun x hx => ?_) (fun x hx => ?_)
        · obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hx
          exact hevB l' hl'
        · obtain ⟨i, hi, rfl⟩ := mem_segEvs hx
          rw [← iterN_succ' (f := f), ← iterN_add]
          exact hnil _ (by omega) (by omega)

end runs

end Concurrency.ArmAllocThread

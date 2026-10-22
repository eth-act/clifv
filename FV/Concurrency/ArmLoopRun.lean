import FV.Concurrency.ArmAllocSeg

/-!
# Precise Arm runs of LL/SC retry loops (T2, #311, layer 4b)

Cranelift's LL/SC loops (`atomicRmwLoop`, `atomicCasLoop`) retry when their `stlxr` fails
(`cbnz w24, loop`). Under the Arm policy a store exclusive may fail at any time
(`ArmThread.TStep.xfail`), and between two iterations other threads may write the location, so a
precise run of the thread may go round the loop any number of times, each iteration's `ldaxr`
reading other bytes. This file is the run level of such loops, generic in the machine `f` and in
an invariant `Hd` of the loop heads:

* `RetryLoop`: **the shape of a retry loop** on the machine: at a head the `ldaxr` reads `rd y`;
  after it (from the head patched with any read `e` of that access) `p - 1` steps without event
  or store exclusive lead to a state `z` that has left the loop (`Ex`, the `atomic_cas` loop's
  `b.ne`) or is at a store exclusive (`StoreAt`): its success writes one event and is followed by
  an event-free `cbnz`, its failure by an event-free `cbnz` back to a head;
* **`retry_run`: the measure on the Arm run**: by induction on the run's length (each failed
  iteration takes `p + 2 > 0` steps), every precise run from a head has no write event at all
  (`NoW`: it ends before a successful store exclusive), or it consists of failed iterations
  (writing nothing) and a final iteration (`Final`) from a head `y1` whose `ldaxr` reads `e`,
  ending at the exit (`Ex`) or at a successful store exclusive (and its `cbnz`);
* `img_pair`, `img_one`: the final iteration's `ldaxr` read and successful `stlxr` write are an
  image (`Img`) of a source step `[e, wv]` (an atomic update: **a monitor pair**, `MonPair`, as
  only event-free steps lie between them), or its read alone of a source step `[e]`; the failed
  iterations before it read only (their reads may return other bytes: **interference between
  retries**), so they write nothing private or shared.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot ArmPrecise Backend.Proof VCodeThread ThreadRefine

/-! ## Traces without writes -/

/-- A trace without write events. -/
def NoW (tr : List (List Ev)) : Prop := ∀ p y, evAt tr p = some y → y.k.dir ≠ .W

theorem noW_nil : NoW [] := fun p y h => by rw [evAt_nil] at h; cases h

theorem noW_append {A B : List (List Ev)} (hA : NoW A) (hB : NoW B) : NoW (A ++ B) := by
  intro p y hy
  rcases Nat.lt_or_ge p.1 A.length with h | h
  · rw [evAt_append_lt _ _ h] at hy; exact hA _ _ hy
  · rw [evAt_append_ge _ _ h] at hy; exact hB _ _ hy

theorem noW_left {A B : List (List Ev)} (h : NoW (A ++ B)) : NoW A := by
  intro p y hy
  exact h p y (by rw [evAt_append_lt _ _ (evAt_lt hy)]; exact hy)

theorem noW_of {tr : List (List Ev)} (h : ∀ x ∈ tr, ∀ e ∈ x, e.k.dir ≠ .W) : NoW tr := by
  intro p y hy
  simp only [evAt] at hy
  cases hx : tr[p.1]? with
  | none => rw [hx] at hy; cases hy
  | some x =>
    rw [hx] at hy
    exact h x (List.mem_of_getElem? hx) y (List.mem_of_getElem? hy)

theorem privW_of_noW {Priv : Nat → Prop} {tr : List (List Ev)} (h : NoW tr) : PrivW Priv tr :=
  fun p y hy hW => absurd hW (h p y hy)

/-- The trace of the steps from an `ldaxr` read `e` to `p - 1` event-free steps after it. -/
def segR (e : Ev) (p : Nat) : List (List Ev) := [e] :: List.replicate (p - 1) []

theorem segR_length (e : Ev) {p : Nat} (hp : 0 < p) : (segR e p).length = p := by
  simp [segR]; omega

theorem noW_segR {e : Ev} (he : e.k.dir = .R) (p : Nat) : NoW (segR e p) := by
  refine noW_of fun x hx y hy => ?_
  simp only [segR, List.mem_cons, List.mem_replicate] at hx
  rcases hx with rfl | ⟨-, rfl⟩
  · simp only [List.mem_singleton] at hy; subst hy; rw [he]; decide
  · cases hy

theorem noW_nils {T : List (List Ev)} (h : ∀ x ∈ T, x = []) : NoW T :=
  noW_of fun x hx y hy => by rw [h x hx] at hy; cases hy

/-! ## Retry loops -/

/-- **A store exclusive `z` of a retry loop** (status register `rs`): its success writes one event
and is followed by an event-free step without store exclusive (the `cbnz`); so is its failure, and
that step leads back to a head. -/
structure StoreAt (f : ArmState → ArmState) (Hd : ArmState → Prop) (rs : BitVec 5) (z : ArmState) :
    Prop where
  stx : ∃ rel rn, cls z = .stx rel rs rn
  wr : ∃ wv : Ev, wv.k.dir = .W ∧ stepEvs z = [wv]
  next : stepEvs (f z) = [] ∧ NoStx (f z)
  fnext : stepEvs (failState rs z) = [] ∧ NoStx (failState rs z)
  back : Hd (f (failState rs z))

/-- **The shape of a retry loop on the machine `f`** (module doc): from a head `y` (`Hd`), the
`ldaxr` reads `rd y`; after it, from the head patched with any read `e` of that access, `p - 1`
event-free steps without store exclusive lead to the exit (`Ex`) or to a store exclusive. -/
structure RetryLoop (f : ArmState → ArmState) (Hd : ArmState → Prop) (rd : ArmState → Ev) (p : Nat)
    (rs : BitVec 5) (Ex : ArmState → Prop) : Prop where
  pos : 0 < p
  read : ∀ y, Hd y → (rd y).k.dir = .R ∧ (rd y).n ≤ 2 ^ 64 ∧ stepEvs y = [rd y] ∧ NoStx y
  mid : ∀ y, Hd y → ∀ e, SameAcc e (rd y) → ∀ i, 0 < i → i < p →
    stepEvs (iterN f i (patch [e] y)) = [] ∧ NoStx (iterN f i (patch [e] y))
  last : ∀ y, Hd y → ∀ e, SameAcc e (rd y) →
    Ex (iterN f p (patch [e] y)) ∨ StoreAt f Hd rs (iterN f p (patch [e] y))

/-- **The final iteration of a run `ls` from `t`** after `q` steps of failed iterations (writing
nothing): from the head `y1`, the `ldaxr` reads `e` and `p - 1` event-free steps follow. -/
structure Final (P : Policy) (f : ArmState → ArmState) (ok : ArmState → Lab → Prop)
    (Hd : ArmState → Prop) (rd : ArmState → Ev) (p : Nat) (t : ArmState × Mon) (ls : List Lab)
    (q : Nat) (y1 : ArmState) (e : Ev) : Prop where
  hd : Hd y1
  acc : SameAcc e (rd y1)
  le : q + p ≤ ls.length
  pre : NoW (evTr (ls.take q))
  seg : evTr (ls.take (q + p)) = evTr (ls.take q) ++ segR e p
  run : ∃ mon1, PRun P f ok t (ls.take (q + p)) (iterN f p (patch [e] y1), mon1)

/-- The outcome of a precise run of a retry loop (module doc): no write at all, or a final
iteration at the exit or at a successful store exclusive (with its `cbnz` when the run goes on). -/
def RetryOut (P : Policy) (f : ArmState → ArmState) (ok : ArmState → Lab → Prop)
    (Hd : ArmState → Prop) (rd : ArmState → Ev) (p : Nat) (rs : BitVec 5) (Ex : ArmState → Prop)
    (t : ArmState × Mon) (ls : List Lab) : Prop :=
  NoW (evTr ls) ∨ ∃ q y1 e, Final P f ok Hd rd p t ls q y1 e ∧
    (Ex (iterN f p (patch [e] y1)) ∨
      (StoreAt f Hd rs (iterN f p (patch [e] y1)) ∧ q + p + 1 ≤ ls.length ∧
        ∃ wv : Ev, wv.k.dir = .W ∧ stepEvs (iterN f p (patch [e] y1)) = [wv] ∧
          evTr (ls.take (q + p + 1)) = evTr (ls.take q) ++ segR e p ++ [[wv]] ∧
          (q + p + 2 ≤ ls.length →
            evTr (ls.take (q + p + 2)) = evTr (ls.take q) ++ segR e p ++ [[wv], []] ∧
            ∃ mon2, PRun P f ok t (ls.take (q + p + 2))
              (f (f (iterN f p (patch [e] y1))), mon2))))

section retry
variable {P : Policy} {f : ArmState → ArmState} {ok : ArmState → Lab → Prop}
  {Hd : ArmState → Prop} {rd : ArmState → Ev} {p : Nat} {rs : BitVec 5} {Ex : ArmState → Prop}

theorem segEvs_segR {s : ArmState} {e : Ev} (hp : 0 < p)
    (h : ∀ i < p, stepEvs (iterN f i s) = if i = 0 then [e] else []) : segEvs f p s = segR e p := by
  refine List.ext_getElem (by rw [segEvs_length, segR_length e hp]) fun i h1 h2 => ?_
  rw [segEvs_get f p s i (by rwa [segEvs_length] at h1), h i (by rwa [segEvs_length] at h1)]
  rcases i with _ | i
  · simp [segR]
  · simp [segR]

theorem take_app {α : Type} (A B : List α) (k : Nat) : (A ++ B).take (A.length + k) = A ++ B.take k := by
  induction A with
  | nil => simp
  | cons a A ih =>
    rw [List.length_cons, Nat.add_right_comm, List.cons_append, List.take_succ_cons, ih]; rfl

/-- A precise step from a store exclusive with one write event, not failing: the write's label,
the machine's step. -/
theorem tstep_store {s : ArmState} {mon : Mon} {l : Lab} {t1 : ArmState × Mon} {wv : Ev}
    (hs : TStep P f (s, mon) l t1) (hp : Precise s l) (hx : l.xfail = false) (hW : wv.k.dir = .W)
    (hev : stepEvs s = [wv]) : l.evs = [wv] ∧ t1.1 = f s := by
  have hl : l.evs = [wv] := by
    rcases hp with h | ⟨M, hM⟩
    · rw [hx] at h; cases h
    · rw [hM, stepEvs_setMem, hev]
      obtain ⟨k, a, n, v⟩ := wv
      exact reread_W hW M a n v
  refine ⟨hl, ?_⟩
  cases hs with
  | exec =>
    simp only at hl ⊢
    rw [hl]
    simp only [applyR, hW, show (Dir.W = Dir.R) = False from by simp, ite_false]
    rfl
  | xfail => cases hx

/-- Failed iterations before a run of a retry loop: the outcome survives prefixing a run without
writes. -/
theorem retryOut_shift {B0 rest : List Lab} {t t0 : ArmState × Mon} (hB : PRun P f ok t B0 t0)
    (hnw : NoW (evTr B0)) (h : RetryOut P f ok Hd rd p rs Ex t0 rest) :
    RetryOut P f ok Hd rd p rs Ex t (B0 ++ rest) := by
  rcases h with h | ⟨q, y1, e, hF, hX⟩
  · left; rw [evTr_append]; exact noW_append hnw h
  right
  have hT : ∀ k, (B0 ++ rest).take (B0.length + k) = B0 ++ rest.take k := take_app B0 rest
  have e1 : B0.length + q + p = B0.length + (q + p) := by omega
  have e2 : B0.length + q + p + 1 = B0.length + (q + p + 1) := by omega
  have e3 : B0.length + q + p + 2 = B0.length + (q + p + 2) := by omega
  refine ⟨B0.length + q, y1, e, ⟨hF.hd, hF.acc, by simp; have := hF.le; omega, ?_, ?_, ?_⟩, ?_⟩
  · rw [hT, evTr_append]; exact noW_append hnw hF.pre
  · rw [e1, hT, hT, evTr_append, evTr_append, hF.seg, List.append_assoc]
  · obtain ⟨mon1, hr1⟩ := hF.run; exact ⟨mon1, by rw [e1, hT]; exact PRun.append hB hr1⟩
  rcases hX with hx | ⟨hst, hle, wv, hW, hwv, hs1, hs2⟩
  · exact .inl hx
  refine .inr ⟨hst, by simp; omega, wv, hW, hwv, ?_, fun h2 => ?_⟩
  · rw [e2, hT, hT, evTr_append, evTr_append, hs1]; simp [List.append_assoc]
  · obtain ⟨h3, mon2, hr2⟩ := hs2 (by simp at h2; omega)
    refine ⟨by rw [e3, hT, hT, evTr_append, evTr_append, h3]; simp [List.append_assoc], mon2, ?_⟩
    rw [e3, hT]; exact PRun.append hB hr2

/-- **The measure on the Arm run** (module doc): by induction on the length of the run, each
failed iteration taking `p + 2` steps. -/
theorem retry_run (hL : RetryLoop f Hd rd p rs Ex) :
    ∀ (N : Nat) (ls : List Lab) (y : ArmState) (mon : Mon) (t' : ArmState × Mon),
      ls.length ≤ N → Hd y → PRun P f ok (y, mon) ls t' → RetryOut P f ok Hd rd p rs Ex (y, mon) ls := by
  intro N
  induction N with
  | zero =>
    intro ls y mon t' hN _ _
    obtain rfl : ls = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact .inl noW_nil
  | succ N ih =>
  intro ls y mon t' hN hy hr
  obtain ⟨hR, hn, hat, hx0⟩ := hL.read y hy
  obtain ⟨tp, r1, r2⟩ := PRun.split (ls.take p) (ls.drop p) (by rw [List.take_append_drop]; exact hr)
  rcases prun_one_read (N := p) (i0 := 0) hR hn hL.pos (fun i hi => absurd hi (Nat.not_lt_zero _))
      hat hx0 (fun e he i h0 hi => hL.mid y hy e he i h0 hi) r1
      (List.length_take_le p ls) with ⟨hle, -, -⟩ | ⟨e, he, ht1, hevT, hstep⟩
  · have : ls = [] := by
      rcases ls with _ | ⟨l, ls⟩
      · rfl
      · simp at hle; have := hL.pos; omega
    subst this
    exact .inl noW_nil
  have heR : e.k.dir = .R := by rw [he.1]; exact hR
  by_cases hlt : ls.length < p
  · left
    have hL' : ls.take p = ls := List.take_of_length_le (by omega)
    rw [hL'] at hevT
    rw [hevT]
    refine noW_of fun x hx y' hy' => ?_
    obtain ⟨i, hi, rfl⟩ := mem_segEvs hx
    rw [hstep i (by omega)] at hy'
    split at hy'
    · simp only [List.mem_singleton] at hy'; subst hy'; rw [heR]; decide
    · cases hy'
  obtain ⟨A, B, rfl, hA⟩ : ∃ A B, ls = A ++ B ∧ A.length = p :=
    ⟨ls.take p, ls.drop p, (List.take_append_drop p ls).symm, by simp; omega⟩
  rw [List.take_left' hA] at r1 ht1 hevT
  rw [List.drop_left' hA] at r2
  rw [hA] at ht1 hevT
  have hsegp : evTr A = segR e p := hevT.trans (segEvs_segR hL.pos fun i hi => hstep i hi)
  obtain ⟨z0, mon1⟩ := tp
  simp only at ht1
  subst ht1
  have hT : ∀ k, (A ++ B).take (A.length + k) = A ++ B.take k := take_app A B
  have hfin : Final P f ok Hd rd p (y, mon) (A ++ B) 0 y e := by
    refine ⟨hy, he, by simp; omega, by simpa [evTr] using noW_nil, ?_, ⟨mon1, ?_⟩⟩
    · rw [Nat.zero_add, List.take_left' hA, List.take_zero]
      exact hsegp
    · rw [Nat.zero_add, List.take_left' hA]; exact r1
  rcases hL.last y hy e he with hex | hst
  · exact .inr ⟨0, y, e, hfin, .inl hex⟩
  cases B with
  | nil =>
    left
    rw [List.append_nil, hsegp]
    exact noW_segR heR p
  | cons l rest =>
  cases r2 with
  | @cons _ t1 _ _ _ hs hp hok r3 =>
  cases hxf : l.xfail with
  | false =>
    obtain ⟨wv, hW, hwv⟩ := hst.wr
    obtain ⟨hl, ht1⟩ := tstep_store hs hp hxf hW hwv
    refine .inr ⟨0, y, e, hfin, .inr ⟨hst, by simp; omega, wv, hW, hwv, ?_, fun h2 => ?_⟩⟩
    · rw [show 0 + p + 1 = A.length + 1 by omega, hT, List.take_zero, evTr_append, hsegp]
      simp [evTr, hl]
    · cases rest with
      | nil => simp at h2; omega
      | cons l2 rest2 =>
      cases r3 with
      | @cons _ t2 _ _ _ hs2 hp2 hok2 r4 =>
      obtain ⟨s1, mon1'⟩ := t1
      simp only at ht1
      subst ht1
      obtain ⟨h21, hl2, -⟩ := tstep_nil hs2 hp2 hst.next.1 hst.next.2
      obtain ⟨s2, mon2⟩ := t2
      simp only at h21
      subst h21
      refine ⟨?_, mon2, ?_⟩
      · rw [show 0 + p + 2 = A.length + 2 by omega, hT, List.take_zero, evTr_append, hsegp]
        simp [evTr, hl, hl2]
      · rw [show 0 + p + 2 = A.length + 2 by omega, hT]
        simp only [List.take_succ_cons, List.take_zero]
        exact PRun.append r1 (.cons hs hp hok (.cons hs2 hp2 hok2 .nil))
  | true =>
    have hl0 : l.evs = [] := by
      cases hs with
      | exec => cases hxf
      | xfail => rfl
    obtain ⟨rel0, rn0, hc0⟩ := hst.stx
    have ht1 : t1.1 = failState rs (iterN f p (patch [e] y)) := by
      cases hs with
      | exec => cases hxf
      | xfail hc =>
        rw [hc0] at hc
        cases hc
        rfl
    cases rest with
    | nil =>
      left
      rw [evTr_append]
      refine noW_append (hsegp ▸ noW_segR heR p) (noW_nils fun x hx => ?_)
      simp only [evTr, List.map_cons, List.map_nil, List.mem_singleton] at hx
      rw [hx, hl0]
    | cons l2 rest2 =>
    cases r3 with
    | @cons _ t2 _ _ _ hs2 hp2 hok2 r4 =>
    obtain ⟨s1, mon1'⟩ := t1
    simp only at ht1
    subst ht1
    obtain ⟨h21, hl2, -⟩ := tstep_nil hs2 hp2 hst.fnext.1 hst.fnext.2
    obtain ⟨s2, mon2⟩ := t2
    simp only at h21
    subst h21
    have hout := ih rest2 _ mon2 t' (by simp at hN; omega) hst.back r4
    have hB : PRun P f ok (y, mon) (A ++ [l, l2]) (f (failState rs (iterN f p (patch [e] y))), mon2) :=
      PRun.append r1 (.cons hs hp hok (.cons hs2 hp2 hok2 .nil))
    have hnw : NoW (evTr (A ++ [l, l2])) := by
      rw [evTr_append, hsegp]
      refine noW_append (noW_segR heR p) (noW_nils fun x hx => ?_)
      simp only [evTr, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hl0
      · exact hl2
    have := retryOut_shift hB hnw hout
    simpa using this

/-! ## The final iteration's image -/

theorem evAt_seg {A : List (List Ev)} {e : Ev} {p : Nat} (hp : 0 < p) {X : List (List Ev)}
    {q : Nat × Nat} {z : Ev} (h : evAt (A ++ (segR e p ++ X)) q = some z) :
    (q.1 < A.length ∧ evAt A q = some z) ∨ (q = (A.length, 0) ∧ z = e) ∨
      (A.length + p ≤ q.1 ∧ evAt X (q.1 - A.length - p, q.2) = some z) := by
  obtain ⟨q1, q2⟩ := q
  rcases Nat.lt_or_ge q1 A.length with h1 | h1
  · exact .inl ⟨h1, by rwa [evAt_append_lt _ _ h1] at h⟩
  right
  rw [evAt_append_ge _ _ h1] at h
  obtain ⟨d, rfl⟩ : ∃ d, q1 = A.length + d := ⟨q1 - A.length, by omega⟩
  simp only [Nat.add_sub_cancel_left] at h
  rcases Nat.lt_or_ge d p with hd | hd
  · rw [evAt_append_lt _ _ (by rw [segR_length e hp]; exact hd)] at h
    rcases d with _ | d
    · simp only [segR, evAt, List.getElem?_cons_zero, Option.bind_some] at h
      rcases q2 with _ | q2
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        exact .inl ⟨rfl, h.symm⟩
      · simp at h
    · simp [segR, evAt, List.getElem?_replicate] at h
      split at h <;> simp at h
  · right
    rw [evAt_append_ge _ _ (by rw [segR_length e hp]; exact hd), segR_length e hp] at h
    refine ⟨by omega, ?_⟩
    simpa [Nat.add_sub_cancel_left] using h

/-- **The final iteration's `ldaxr` read and successful `stlxr` write are the image of an atomic
update** `[e, wv]`: a monitor pair (only event-free steps between them), the other steps of the
segment (failed iterations, the `cbnz`) writing nothing. -/
theorem img_pair {Priv : Nat → Prop} {A : List (List Ev)} {e wv : Ev} {p : Nat} (hp : 0 < p)
    (hA : NoW A) (he : e.k = .acqXR) (hw : wv.k = .relXW)
    (hsh : ∀ x ∈ [e, wv], x.k.dir ≠ .F → ¬ Priv x.addr.toNat) {T : List (List Ev)}
    (hT : ∀ x ∈ T, x = []) :
    Img Priv [e, wv] (A ++ (segR e p ++ ([wv] :: T)))
      (fun k => if k = 0 then (A.length, 0) else (A.length + p, 0)) := by
  have hX : ∀ {q : Nat × Nat} {z : Ev}, evAt ([wv] :: T) q = some z → q = (0, 0) ∧ z = wv := by
    intro q z h
    obtain ⟨q1, q2⟩ := q
    rcases q1 with _ | q1
    · rcases q2 with _ | q2
      · simp [evAt] at h; exact ⟨rfl, h.symm⟩
      · simp [evAt] at h
    · simp only [evAt, List.getElem?_cons_succ] at h
      cases hq : T[q1]? with
      | none => rw [hq] at h; cases h
      | some x =>
        rw [hq, hT x (List.mem_of_getElem? hq)] at h
        simp at h
  have hpos : ∀ {q : Nat × Nat} {z : Ev}, evAt (A ++ (segR e p ++ ([wv] :: T))) q = some z →
      (q.1 < A.length ∧ evAt A q = some z) ∨ (q = (A.length, 0) ∧ z = e) ∨
        (q = (A.length + p, 0) ∧ z = wv) := by
    intro q z h
    obtain ⟨q1, q2⟩ := q
    rcases evAt_seg hp h with h1 | h1 | ⟨h1, h2⟩
    · exact .inl h1
    · exact .inr (.inl h1)
    · obtain ⟨e1, rfl⟩ := hX h2
      simp only [Prod.mk.injEq] at e1 h1
      exact .inr (.inr ⟨by simp only [Prod.mk.injEq]; omega, rfl⟩)
  have h0 : evAt (A ++ (segR e p ++ ([wv] :: T))) (A.length, 0) = some e := by
    rw [evAt_append_ge _ _ (Nat.le_refl _), Nat.sub_self,
      evAt_append_lt _ _ (by rw [segR_length e hp]; exact hp)]
    simp [segR, evAt]
  have h1 : evAt (A ++ (segR e p ++ ([wv] :: T))) (A.length + p, 0) = some wv := by
    rw [evAt_append_ge _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      evAt_append_ge _ _ (by simp [segR_length e hp]), segR_length e hp, Nat.sub_self]
    simp [evAt]
  refine ⟨fun k hk => ?_, fun k k' h12 h2 => ?_, fun q y hy hW hn => ?_, hsh, .inr ⟨e, wv, rfl, he, hw⟩,
    fun _ => ⟨⟨e, by simpa using h0, he⟩, ⟨wv, by simpa using h1, hw⟩, by simp [Lt]; omega,
      fun q z hq1 hq2 hz => ?_⟩⟩
  · match k, hk with
    | 0, _ => simpa using h0
    | 1, _ => simpa using h1
    | k + 2, hk => exact absurd hk (by simp)
  · obtain rfl : k = 0 := by simp at h2; omega
    obtain rfl : k' = 1 := by simp at h2; omega
    simp [Lt]; omega
  · rcases hpos hy with ⟨-, h⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact absurd hW (hA _ _ h)
    · exact absurd rfl (hn 0 (by simp))
    · exact absurd rfl (hn 1 (by simp))
  · simp only [Lt, ite_true, show (1 : Nat) ≠ 0 from by decide, ite_false] at hq1 hq2
    rcases hpos hz with ⟨h, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · omega
    · simp at hq1
    · simp at hq2

/-- **The final iteration's `ldaxr` read alone is the image of a one-event source step** (the
`atomic_cas` loop's exit when the values differ). -/
theorem img_one {Priv : Nat → Prop} {A : List (List Ev)} {e : Ev} {p : Nat} (hp : 0 < p)
    (hA : NoW A) (heR : e.k.dir = .R) (hne : e.k ≠ .relXW)
    (hsh : ∀ x ∈ [e], x.k.dir ≠ .F → ¬ Priv x.addr.toNat) :
    Img Priv [e] (A ++ segR e p) (fun _ => (A.length, 0)) := by
  have hpos : ∀ {q : Nat × Nat} {z : Ev}, evAt (A ++ segR e p) q = some z →
      (q.1 < A.length ∧ evAt A q = some z) ∨ (q = (A.length, 0) ∧ z = e) := by
    intro q z h
    rw [← List.append_nil (segR e p)] at h
    rcases evAt_seg hp h with h1 | h1 | ⟨-, h2⟩
    · exact .inl h1
    · exact .inr h1
    · rw [evAt_nil] at h2; cases h2
  have h0 : evAt (A ++ segR e p) (A.length, 0) = some e := by
    rw [evAt_append_ge _ _ (Nat.le_refl _), Nat.sub_self]
    simp [segR, evAt]
  refine ⟨fun k hk => ?_, fun k k' h12 h2 => by simp at h2; omega, fun q y hy hW hn => ?_, hsh,
    .inl ⟨by simp, fun x hx => by simp at hx; subst hx; exact hne⟩, fun h => by simp at h⟩
  · obtain rfl : k = 0 := by simpa using hk
    simpa using h0
  · rcases hpos hy with ⟨-, h⟩ | ⟨rfl, rfl⟩
    · exact absurd hW (hA _ _ h)
    · rw [heR] at hW; cases hW

end retry

end Concurrency.ArmAllocThread

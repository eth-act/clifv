module

public import FV.Opt.Proof.DomFacts
public import FV.Opt.Proof.CompleteLicm

@[expose] public section

/-!
# `Cfg.dominators` computes the dominator tree (M1)

`Opt.build_domFacts`: the `idom` array of `Cfg.build f` has the facts `Opt.DomFacts` — entries are
blocks, the entry is the root, RPO numbers decrease towards the root, the edge certificate, and
every dominator of a reachable block is a tree ancestor of it. No hypothesis on `f`.

The proof (namespace `Opt.DomAlgo`) first rewrites `Cfg.dominators` into plain recursive functions
(`dominators_eq`: the finger walk `walk`, the predecessor fold `newOf`, one round `round`, the
rounds `rounds`), then proves an invariant `Inv` over abstract `preds`/`succs`/`rpo`/`num` that
satisfy `Hyp`. The forest of a state `s` is read with the root cut (`Anc (s.set! 0 none)`).
- `Inv.pi` (soundness, Cooper–Harvey–Kennedy): a path from the entry to the parent of `x`
  avoiding `d ≠ x` extends to `x`. Hence every dominator of a defined block is a forest ancestor
  (`Inv.sound`).
- `Inv.q` (completeness, Kam–Ullman): after `k` rounds, a path of at most `m < k` edges to `x`
  avoiding `a` gives one to the parent of `x`. Paths of `|rpo|` edges suffice (`Hyp.bound`,
  pigeonhole on the blocks reached), so after the `n + 2` rounds every parent dominates its child.
  A round without change is a fixpoint, which keeps every level.
- `Inv.walk`: the finger walk with fuel `2n + 2` returns the nearest common ancestor (RPO numbers
  strictly decrease along parents, `Inv.rk`).
`Hyp.parent` (every reachable block but the entry has a predecessor earlier in the reverse
postorder) is the depth-first-search fact `postorder_parent`; it makes every reachable block
defined after the first round and gives `Inv.rk`.
-/

namespace Opt

open Clif

namespace DomAlgo

/-- One step of the finger walk of `Cfg.dominators`. -/
def G (s : Array (Option Nat)) (num : Nat → Nat) (st : Nat × Nat) : Nat × Nat :=
  if num st.1 > num st.2 then (s[st.1]!.getD 0, st.2) else (st.1, s[st.2]!.getD 0)

/-- The finger walk with fuel. -/
def walk (s : Array (Option Nat)) (num : Nat → Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, st => st
  | k + 1, st => if st.1 = st.2 then st else walk s num k (G s num st)

def pstep (s : Array (Option Nat)) (num : Nat → Nat) (F : Nat) (o : Option Nat) (p : Nat) :
    Option Nat :=
  if s[p]!.isNone = true then o else
    match o with
    | none => some p
    | some q => some (walk s num F (p, q)).1

def newOf (preds : Array (List Nat)) (s : Array (Option Nat)) (num : Nat → Nat) (F b : Nat) :
    Option Nat :=
  (preds[b]!).foldl (pstep s num F) none

def rstep (preds : Array (List Nat)) (num : Nat → Nat) (F : Nat) (st : Array (Option Nat) × Bool)
    (b : Nat) : Array (Option Nat) × Bool :=
  if b = 0 then st else
    if (newOf preds st.1 num F b != st.1[b]!) = true then (st.1.set! b (newOf preds st.1 num F b), true)
    else st

def round (preds : Array (List Nat)) (rpo : List Nat) (num : Nat → Nat) (F : Nat)
    (s : Array (Option Nat)) : Array (Option Nat) × Bool :=
  rpo.foldl (rstep preds num F) (s, false)

def rounds (preds : Array (List Nat)) (rpo : List Nat) (num : Nat → Nat) (F : Nat) :
    Nat → Array (Option Nat) → Array (Option Nat)
  | 0, s => s
  | k + 1, s => if (round preds rpo num F s).2 = false then (round preds rpo num F s).1
    else rounds preds rpo num F k (round preds rpo num F s).1

theorem forIn_yield_foldl {α σ : Type} (l : List α) (init : σ) (f : α → σ → Id (ForInStep σ))
    (g : σ → α → σ) (h : ∀ a s, f a s = pure (.yield (g s a))) :
    forIn l init f = pure (l.foldl g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => rw [List.forIn_cons, h]; exact ih _

theorem forIn_walk (s : Array (Option Nat)) (num : Nat → Nat) (l : List Nat) (st : Nat × Nat)
    (f : Nat → Nat × Nat → Id (ForInStep (Nat × Nat)))
    (h : ∀ a st, f a st = if st.1 = st.2 then pure (.done st) else pure (.yield (G s num st))) :
    forIn l st f = pure (walk s num l.length st) := by
  induction l generalizing st with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, h]
    by_cases hs : st.1 = st.2
    · simp [hs, walk]
    · simp only [hs, ite_false, List.length_cons, walk]; exact ih _

theorem forIn_rounds (preds : Array (List Nat)) (rpo : List Nat) (num : Nat → Nat) (F : Nat)
    (l : List Nat) (s : Array (Option Nat)) (f : Nat → Array (Option Nat) → Id (ForInStep (Array (Option Nat))))
    (h : ∀ a s, f a s = if (round preds rpo num F s).2 = false then pure (.done (round preds rpo num F s).1)
      else pure (.yield (round preds rpo num F s).1)) :
    forIn l s f = pure (rounds preds rpo num F l.length s) := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, h]
    by_cases hs : (round preds rpo num F s).2 = false
    · simp [hs, rounds]
    · simp only [hs, List.length_cons, rounds]; exact ih _

theorem dominators_eq (preds : Array (List Nat)) (rpo : Array Nat) (rpoNum : Array (Option Nat))
    (h : preds.size ≠ 0) :
    Cfg.dominators preds rpo rpoNum =
      (rounds preds rpo.toList (fun b => (rpoNum[b]?.join).getD preds.size) (2 * preds.size + 2)
        (preds.size + 2) ((Array.replicate preds.size none).set! 0 (some 0))).set! 0 none := by
  unfold Cfg.dominators
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', beq_iff_eq, h, ite_false]
  rw [forIn_rounds preds rpo.toList (fun b => (rpoNum[b]?.join).getD preds.size) (2 * preds.size + 2) _ _ _ ?_]
  · simp; rfl
  intro a s
  rw [← Array.forIn_toList, forIn_yield_foldl _ _ _
    (rstep preds (fun b => (rpoNum[b]?.join).getD preds.size) (2 * preds.size + 2)) ?_]
  · simp only [round, pure_bind]
    by_cases h2 : (List.foldl (rstep preds (fun b => (rpoNum[b]?.join).getD preds.size)
      (2 * preds.size + 2)) (s, false) rpo.toList).snd = false <;> simp
  intro b st
  unfold rstep newOf
  by_cases hb : b = 0
  · simp [hb]
  · simp only [hb, ite_false]
    rw [forIn_yield_foldl _ _ _ (pstep st.1 (fun b => (rpoNum[b]?.join).getD preds.size)
      (2 * preds.size + 2)) ?_]
    · simp only [pure_bind]
      split <;> rfl
    intro p o
    unfold pstep
    split
    · rfl
    · cases o with
      | none => rfl
      | some q =>
        simp only
        rw [forIn_walk st.1 (fun b => (rpoNum[b]?.join).getD preds.size) _ _ _ ?_]
        · simp
        intro x st'
        unfold G
        split
        · rfl
        · split <;> rfl


/-! ## Paths of bounded length -/

/-- Paths from the entry block with at most `m` edges avoiding block `a`. -/
inductive PathL (succs : Array (List Nat)) (a : Nat) : Nat → Nat → Prop
  | entry (m : Nat) : a ≠ 0 → PathL succs a m 0
  | step {m u x : Nat} : PathL succs a m u → x ∈ succs[u]! → x ≠ a → PathL succs a (m + 1) x

theorem PathL.mono {succs : Array (List Nat)} {a m x : Nat} (h : PathL succs a m x) :
    ∀ {m'}, m ≤ m' → PathL succs a m' x := by
  induction h with
  | entry m ha => intro m' _; exact .entry m' ha
  | step _ hx hxa ih =>
    intro m' hm
    obtain ⟨k, rfl⟩ : ∃ k, m' = k + 1 := ⟨m' - 1, by omega⟩
    exact .step (ih (by omega)) hx hxa

theorem PathL.ne {succs : Array (List Nat)} {a m x : Nat} (h : PathL succs a m x) : x ≠ a := by
  cases h with
  | entry _ ha => exact fun h => ha h.symm
  | step _ _ hxa => exact hxa

theorem PathL.toRA {succs : Array (List Nat)} {a m x : Nat} (h : PathL succs a m x) :
    ReachAvoid succs a x := by
  induction h with
  | entry _ ha => exact .entry ha
  | step _ hx hxa ih => exact .step ih hx hxa

theorem ReachAvoid.toPathL {succs : Array (List Nat)} {a x : Nat} (h : ReachAvoid succs a x) :
    ∃ m, PathL succs a m x := by
  induction h with
  | entry ha => exact ⟨0, .entry 0 ha⟩
  | step _ hx hxa ih => obtain ⟨m, hm⟩ := ih; exact ⟨m + 1, .step hm hx hxa⟩

theorem not_ra_zero {succs : Array (List Nat)} {x : Nat} : ¬ ReachAvoid succs 0 x := by
  intro h
  induction h with
  | entry ha => exact ha rfl
  | step _ _ _ ih => exact ih

/-! ## The hypotheses on the graph -/

/-- What the analysis needs of `preds`, `succs`, the reverse postorder and its numbering. -/
structure Hyp (succs preds : Array (List Nat)) (rpo : List Nat) (num : Nat → Nat) : Prop where
  lt : ∀ x ∈ rpo, x < preds.size
  nodup : rpo.Nodup
  idx : ∀ i (h : i < rpo.length), num rpo[i] = i
  zero : 0 ∈ rpo
  pred_succ : ∀ b ∈ rpo, ∀ p ∈ preds[b]!, b ∈ succs[p]!
  succ_pred : ∀ b ∈ rpo, ∀ p ∈ rpo, b ∈ succs[p]! → p ∈ preds[b]!
  closed : ∀ p ∈ rpo, ∀ x ∈ succs[p]!, x ∈ rpo
  parent : ∀ b ∈ rpo, b ≠ 0 → ∃ p ∈ rpo, b ∈ succs[p]! ∧ num p < num b
  len : rpo.length ≤ preds.size

section Core
variable {succs preds : Array (List Nat)} {rpo : List Nat} {num : Nat → Nat}

theorem Hyp.num_lt (H : Hyp succs preds rpo num) {x : Nat} (hx : x ∈ rpo) : num x < rpo.length := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  rw [H.idx i hi]; exact hi

theorem Hyp.num_inj (H : Hyp succs preds rpo num) {x y : Nat} (hx : x ∈ rpo) (hy : y ∈ rpo)
    (h : num x = num y) : x = y := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
  rw [H.idx i hi, H.idx j hj] at h
  subst h; rfl

theorem Hyp.mem_pre (H : Hyp succs preds rpo num) {pre rest : List Nat} {b p : Nat}
    (hr : rpo = pre ++ b :: rest) (hp : p ∈ rpo) (hlt : num p < num b) : p ∈ pre := by
  have hb : num b = pre.length := by
    have h1 : pre.length < rpo.length := by rw [hr]; simp
    have h2 : rpo[pre.length] = b := by simp [hr]
    rw [← h2, H.idx _ h1]
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
  rw [H.idx i hi] at hlt
  have : rpo[i] = pre[i] := by simp [hr, List.getElem_append_left (by omega : i < pre.length)]
  rw [this]; exact List.getElem_mem _

theorem Hyp.ra_mem (H : Hyp succs preds rpo num) {a x : Nat} (h : ReachAvoid succs a x) : x ∈ rpo := by
  induction h with
  | entry _ => exact H.zero
  | step _ hx _ ih => exact H.closed _ ih _ hx

theorem Hyp.path_mem (H : Hyp succs preds rpo num) {a m x : Nat} (h : PathL succs a m x) : x ∈ rpo :=
  H.ra_mem h.toRA

/-! ## Array facts -/

theorem get_set (s : Array (Option Nat)) {b : Nat} (x : Nat) (v : Option Nat) (hb : b < s.size) :
    (s.set! b v)[x]! = if x = b then v else s[x]! := by
  rw [getElem!_opt, getElem!_opt]
  by_cases h : x = b
  · subst h; simp [Array.set!_eq_setIfInBounds, hb]
  · simp [Array.set!_eq_setIfInBounds, h, Ne.symm h]

theorem tget (s : Array (Option Nat)) (x : Nat) :
    (s.set! 0 none)[x]?.join = if x = 0 then none else s[x]! := by
  rw [getElem!_opt]
  by_cases h : x = 0
  · subst h; by_cases h0 : 0 < s.size <;> simp [Array.set!_eq_setIfInBounds, h0]
  · simp [Array.set!_eq_setIfInBounds, h, Ne.symm h]

theorem tget_some {s : Array (Option Nat)} {x c : Nat} (h : (s.set! 0 none)[x]?.join = some c) :
    x ≠ 0 ∧ s[x]! = some c := by
  rw [tget] at h
  by_cases hx : x = 0
  · simp [hx] at h
  · simp only [hx, ite_false] at h; exact ⟨hx, h⟩

theorem set_self (s : Array (Option Nat)) {b : Nat} {v : Option Nat} (hb : b < s.size) (h : s[b]! = v) :
    s.set! b v = s := by
  apply Array.ext_getElem?
  intro i
  by_cases hi : i = b
  · subst hi
    simp [Array.set!_eq_setIfInBounds, hb, ← h]
  · simp [Array.set!_eq_setIfInBounds, Ne.symm hi]


/-! ## The invariant of the rounds -/

/-- `x` has a value in the current approximation `s` (`s[0]! = some 0` during the loop). -/
abbrev D (s : Array (Option Nat)) (x : Nat) : Prop := ∃ y, s[x]! = some y

/-- The invariant during round `k + 1` (`P`: the blocks processed in it). The forest of `s` is
read with the root cut (`Anc (s.set! 0 none)`). `pi`: a path to the parent avoiding `d` extends
to the child (soundness); `q`: a short path to a child avoiding `a` gives one to the parent
(completeness, Kam–Ullman). -/
structure Inv (succs preds : Array (List Nat)) (rpo : List Nat) (num : Nat → Nat) (k : Nat)
    (P : Nat → Prop) (s : Array (Option Nat)) : Prop where
  size : s.size = preds.size
  s0 : s[0]! = some 0
  dr : ∀ x y, s[x]! = some y → x ∈ rpo
  dd : ∀ x y, x ≠ 0 → s[x]! = some y → D s y
  rk : ∀ x y, x ≠ 0 → s[x]! = some y → num y < num x
  pi : ∀ x y, x ≠ 0 → s[x]! = some y → ∀ d, d ≠ x → ReachAvoid succs d y → ReachAvoid succs d x
  q : ∀ x y, x ≠ 0 → s[x]! = some y → ∀ m, (m < k ∨ (P x ∧ m ≤ k)) → ∀ a,
    PathL succs a m x → PathL succs a m y
  df : ∀ x ∈ rpo, (0 < k ∨ P x) → D s x

variable {k : Nat} {P : Nat → Prop} {s : Array (Option Nat)}

theorem Inv.anc (I : Inv succs preds rpo num k P s) {z x : Nat} (h : Anc (s.set! 0 none) z x)
    (hx : D s x) : num z ≤ num x ∧ D s z := by
  induction h with
  | refl => exact ⟨Nat.le_refl _, hx⟩
  | up hc _ ih =>
    obtain ⟨h0, hs⟩ := tget_some hc
    have := I.rk _ _ h0 hs
    have := ih (I.dd _ _ h0 hs)
    exact ⟨by omega, this.2⟩

theorem Inv.sound (I : Inv succs preds rpo num k P s) {d : Nat} :
    ∀ N x, num x < N → D s x → ¬ ReachAvoid succs d x → Anc (s.set! 0 none) d x := by
  intro N
  induction N with
  | zero => intro x h; omega
  | succ N ih =>
    intro x hN hx hd
    by_cases hdx : d = x
    · subst hdx; exact .refl _
    by_cases hx0 : x = 0
    · subst hx0
      exact absurd (ReachAvoid.entry (succs := succs) (fun h => hdx h)) hd
    obtain ⟨y, hy⟩ := hx
    have hyx := I.rk _ _ hx0 hy
    refine .up (by rw [tget]; simp [hx0, hy]) (ih y (by omega) (I.dd _ _ hx0 hy) ?_)
    exact fun h => hd (I.pi _ _ hx0 hy d hdx h)

theorem Inv.sound' (I : Inv succs preds rpo num k P s) {d x : Nat} (hx : D s x)
    (hd : ¬ ReachAvoid succs d x) : Anc (s.set! 0 none) d x :=
  I.sound _ x (Nat.lt_succ_self _) hx hd

theorem Inv.num0 (I : Inv succs preds rpo num k P s) {x : Nat} (hx : D s x) : num 0 ≤ num x :=
  (I.anc (I.sound' hx not_ra_zero) hx).1

theorem Inv.mem (I : Inv succs preds rpo num k P s) {x : Nat} (hx : D s x) : x ∈ rpo := by
  obtain ⟨y, hy⟩ := hx; exact I.dr _ _ hy

/-- The finger walk finds the nearest common ancestor. -/
theorem Inv.walk (H : Hyp succs preds rpo num) (I : Inv succs preds rpo num k P s) :
    ∀ K a c, D s a → D s c → num a + num c < K →
      D s (walk s num K (a, c)).1 ∧ ∀ z, Anc (s.set! 0 none) z (walk s num K (a, c)).1 ↔
        Anc (s.set! 0 none) z a ∧ Anc (s.set! 0 none) z c := by
  intro K
  induction K with
  | zero => intro a c _ _ h; omega
  | succ K ih =>
    intro a c ha hc hK
    simp only [DomAlgo.walk]
    by_cases hac : a = c
    · subst hac; simp only [ite_true]; exact ⟨ha, fun z => ⟨fun h => ⟨h, h⟩, fun h => h.1⟩⟩
    simp only [hac, ite_false, G]
    by_cases hlt : num a > num c
    · simp only [hlt, ite_true]
      have ha0 : a ≠ 0 := by rintro rfl; have := I.num0 hc; omega
      obtain ⟨a', ha'⟩ := ha
      have hrk := I.rk _ _ ha0 ha'
      simp only [ha', Option.getD_some]
      obtain ⟨h1, h2⟩ := ih a' c (I.dd _ _ ha0 ha') hc (by omega)
      refine ⟨h1, fun z => (h2 z).trans ⟨fun ⟨h3, h4⟩ => ⟨.up (by rw [tget]; simp [ha0, ha']) h3, h4⟩,
        fun ⟨h3, h4⟩ => ⟨?_, h4⟩⟩⟩
      by_cases hza : z = a
      · subst hza; have := (I.anc h4 hc).1; omega
      · obtain ⟨c', hc', h5⟩ := h3.strict hza
        obtain ⟨_, hc''⟩ := tget_some hc'
        rw [ha'] at hc''; cases hc''; exact h5
    · simp only [hlt, ite_false]
      have hne : num a ≠ num c := fun h => hac (H.num_inj (I.mem ha) (I.mem hc) h)
      have hc0 : c ≠ 0 := by rintro rfl; have := I.num0 ha; omega
      obtain ⟨c', hc'⟩ := hc
      have hrk := I.rk _ _ hc0 hc'
      simp only [hc', Option.getD_some]
      obtain ⟨h1, h2⟩ := ih a c' ha (I.dd _ _ hc0 hc') (by omega)
      refine ⟨h1, fun z => (h2 z).trans ⟨fun ⟨h3, h4⟩ => ⟨h3, .up (by rw [tget]; simp [hc0, hc']) h4⟩,
        fun ⟨h3, h4⟩ => ⟨h3, ?_⟩⟩⟩
      by_cases hzc : z = c
      · subst hzc; have := (I.anc h3 ha).1; omega
      · obtain ⟨a', ha', h5⟩ := h4.strict hzc
        obtain ⟨_, ha''⟩ := tget_some ha'
        rw [hc'] at ha''; cases ha''; exact h5

/-- The specification of the predecessor fold after the predecessors `L`. -/
def Spec (s : Array (Option Nat)) (o : Option Nat) (L : List Nat) : Prop :=
  match o with
  | none => ∀ p ∈ L, s[p]! = none
  | some r => D s r ∧ ∀ z, Anc (s.set! 0 none) z r ↔ ∀ p ∈ L, D s p → Anc (s.set! 0 none) z p

theorem Inv.fold (H : Hyp succs preds rpo num) (I : Inv succs preds rpo num k P s) :
    ∀ (ps L : List Nat) (o : Option Nat), Spec s o L →
      Spec s (ps.foldl (pstep s num (2 * preds.size + 2)) o) (L ++ ps) := by
  intro ps
  induction ps with
  | nil => intro L o h; simpa using h
  | cons p ps ih =>
    intro L o h
    rw [List.foldl_cons, show L ++ p :: ps = (L ++ [p]) ++ ps by simp]
    apply ih
    unfold pstep
    by_cases hp : s[p]!.isNone = true
    · have hp' : s[p]! = none := by simpa using hp
      have hnd : ¬ D s p := by rintro ⟨y, hy⟩; rw [hp'] at hy; cases hy
      simp only [hp, ite_true]
      cases o with
      | none =>
        intro p' hp''
        simp only [List.mem_append, List.mem_singleton] at hp''
        rcases hp'' with h' | rfl
        · exact h p' h'
        · exact hp'
      | some r =>
        refine ⟨h.1, fun z => (h.2 z).trans ⟨fun h' p' hp'' hd => ?_, fun h' p' hp'' hd => h' p' (by simp [hp'']) hd⟩⟩
        simp only [List.mem_append, List.mem_singleton] at hp''
        rcases hp'' with h'' | rfl
        · exact h' p' h'' hd
        · exact absurd hd hnd
    · have hpd : D s p := by
        cases hs : s[p]! with
        | none => rw [hs] at hp; simp at hp
        | some y => exact ⟨y, hs⟩
      simp only [hp, Bool.false_eq_true, ite_false]
      cases o with
      | none =>
        refine ⟨hpd, fun z => ⟨fun h' p' hp'' hd => ?_, fun h' => h' p (by simp) hpd⟩⟩
        simp only [List.mem_append, List.mem_singleton] at hp''
        rcases hp'' with h'' | rfl
        · obtain ⟨y, hy⟩ := hd; rw [h p' h''] at hy; cases hy
        · exact h'
      | some q =>
        have hq := h.1
        have hpn := H.num_lt (I.mem hpd)
        have hqn := H.num_lt (I.mem hq)
        have hl := H.len
        obtain ⟨w1, w2⟩ := I.walk H (2 * preds.size + 2) p q hpd hq (by omega)
        refine ⟨w1, fun z => (w2 z).trans ⟨fun ⟨h3, h4⟩ p' hp'' hd => ?_, fun h' => ⟨h' p (by simp) hpd,
          (h.2 z).2 fun p' hp'' hd => h' p' (by simp [hp'']) hd⟩⟩⟩
        simp only [List.mem_append, List.mem_singleton] at hp''
        rcases hp'' with h'' | rfl
        · exact (h.2 z).1 h4 p' h'' hd
        · exact h3


theorem Inv.weaken (I : Inv succs preds rpo num k P s) {P' : Nat → Prop}
    (hq : ∀ x, x ≠ 0 → P' x → P x) (hd : ∀ x ∈ rpo, P' x → P x ∨ D s x) :
    Inv succs preds rpo num k P' s where
  size := I.size
  s0 := I.s0
  dr := I.dr
  dd := I.dd
  rk := I.rk
  pi := I.pi
  q x y hx hs m hm := I.q x y hx hs m (hm.imp_right fun h => ⟨hq x hx h.1, h.2⟩)
  df x hx h := by
    rcases h with h | h
    · exact I.df x hx (.inl h)
    · rcases hd x hx h with h' | h'
      · exact I.df x hx (.inr h')
      · exact h'

theorem Inv.chainQ (I : Inv succs preds rpo num k P s) {r u a m : Nat}
    (h : Anc (s.set! 0 none) r u) (hm : m < k) (hp : PathL succs a m u) : PathL succs a m r := by
  induction h with
  | refl => exact hp
  | up hc _ ih =>
    obtain ⟨h0, hs⟩ := tget_some hc
    exact ih (I.q _ _ h0 hs m (.inl hm) a hp)

theorem Inv.chainPI (I : Inv succs preds rpo num k P s) {r u d : Nat}
    (h : Anc (s.set! 0 none) r u) (hu : D s u) (hd : Anc (s.set! 0 none) d r)
    (hn : ¬ ReachAvoid succs d u) : ¬ ReachAvoid succs d r := by
  induction h with
  | refl => exact hn
  | up hc hrc ih =>
    rename_i u' c
    obtain ⟨h0, hs⟩ := tget_some hc
    have hcd := I.dd _ _ h0 hs
    refine ih hcd fun h => hn (I.pi _ _ h0 hs d ?_ h)
    rintro rfl
    have := (I.anc (hd.trans hrc) hcd).1
    have := I.rk _ _ h0 hs
    omega

/-- Processing block `b` of the reverse postorder keeps the invariant. -/
theorem Inv.rstep (H : Hyp succs preds rpo num) {pre rest : List Nat} {b : Nat}
    (hr : rpo = pre ++ b :: rest) {st : Array (Option Nat) × Bool}
    (I : Inv succs preds rpo num k (· ∈ pre) st.1) :
    Inv succs preds rpo num k (· ∈ pre ++ [b]) (rstep preds num (2 * preds.size + 2) st b).1 := by
  have hbr : b ∈ rpo := by rw [hr]; simp
  by_cases hb0 : b = 0
  · subst hb0
    simp only [DomAlgo.rstep, ite_true]
    refine I.weaken (fun x hx h => ?_) (fun x _ h => ?_)
    · simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact h
      · exact absurd h hx
    · simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact .inl h
      · exact .inr ⟨0, I.s0⟩
  obtain ⟨s, ch⟩ := st
  simp only at I
  have hbn : b < s.size := I.size ▸ H.lt b hbr
  obtain ⟨p0, hp0r, hp0s, hp0n⟩ := H.parent b hbr hb0
  have hp0d : D s p0 := I.df p0 hp0r (.inr (H.mem_pre hr hp0r hp0n))
  have hp0p : p0 ∈ preds[b]! := H.succ_pred b hbr p0 hp0r hp0s
  have hspec := I.fold H (preds[b]!) [] none (by simp [Spec])
  simp only [List.nil_append] at hspec
  have hP : ∀ x, x ≠ b → (x ∈ pre ++ [b] ↔ x ∈ pre) := by
    intro x hx; simp [hx]
  unfold DomAlgo.rstep
  simp only [hb0, ite_false]
  cases hnew : newOf preds s num (2 * preds.size + 2) b with
  | none =>
    unfold newOf at hnew
    rw [hnew] at hspec
    obtain ⟨y, hy⟩ := hp0d
    rw [hspec p0 hp0p] at hy; cases hy
  | some r =>
    unfold newOf at hnew
    rw [hnew] at hspec
    obtain ⟨hrd, hrA⟩ := hspec
    have hrp : ∀ p ∈ preds[b]!, D s p → Anc (s.set! 0 none) r p := (hrA r).1 (.refl r)
    have hr0 := hrp p0 hp0p hp0d
    have hrn : num r < num b := by have := (I.anc hr0 hp0d).1; omega
    have hrb : r ≠ b := by rintro rfl; omega
    have hg := get_set s (v := some r) (hb := hbn)
    have key : Inv succs preds rpo num k (· ∈ pre ++ [b]) (s.set! b (some r)) := {
      size := by simp [I.size]
      s0 := by rw [hg]; simp [Ne.symm hb0, I.s0]
      dr := by
        intro x y h
        rw [hg] at h
        by_cases hxb : x = b
        · subst hxb; exact hbr
        · simp only [hxb, ite_false] at h; exact I.dr _ _ h
      dd := by
        intro x y hx h
        rw [hg] at h
        by_cases hxb : x = b
        · subst hxb; simp only [ite_true] at h; cases h
          obtain ⟨z, hz⟩ := hrd; exact ⟨z, by rw [hg]; simp [hrb, hz]⟩
        · simp only [hxb, ite_false] at h
          obtain ⟨z, hz⟩ := I.dd _ _ hx h
          by_cases hyb : y = b
          · exact ⟨r, by rw [hg]; simp [hyb]⟩
          · exact ⟨z, by rw [hg]; simp [hyb, hz]⟩
      rk := by
        intro x y hx h
        rw [hg] at h
        by_cases hxb : x = b
        · subst hxb; simp only [ite_true] at h; cases h; exact hrn
        · simp only [hxb, ite_false] at h; exact I.rk _ _ hx h
      pi := by
        intro x y hx h d hdx hra
        rw [hg] at h
        by_cases hxb : x = b
        · subst hxb; simp only [ite_true] at h; cases h
          refine Classical.byContradiction fun hn => ?_
          have hall : ∀ p ∈ preds[x]!, D s p → Anc (s.set! 0 none) d p := by
            intro p hp hpd
            refine I.sound' hpd fun h' => hn (.step h' (H.pred_succ x hbr p hp) hdx.symm)
          have hdr : Anc (s.set! 0 none) d r := (hrA d).2 hall
          exact I.chainPI hr0 hp0d hdr
            (fun h' => hn (.step h' hp0s hdx.symm)) hra
        · simp only [hxb, ite_false] at h; exact I.pi _ _ hx h d hdx hra
      q := by
        intro x y hx h m hm a hpath
        rw [hg] at h
        by_cases hxb : x = b
        · subst hxb; simp only [ite_true] at h; cases h
          cases hpath with
          | entry _ _ => exact absurd rfl hx
          | step hu hxu hxa =>
            rename_i m' u
            have hm' : m' < k := by rcases hm with hm | ⟨_, hm⟩ <;> omega
            have hur := H.path_mem hu
            have hud : D s u := I.df u hur (.inl (by omega))
            have hup := H.succ_pred x hbr u hur hxu
            exact (I.chainQ (hrp u hup hud) hm' hu).mono (by omega)
        · simp only [hxb, ite_false] at h
          exact I.q _ _ hx h m (by rwa [hP x hxb] at hm) a hpath
      df := by
        intro x hx h
        by_cases hxb : x = b
        · subst hxb; exact ⟨r, by rw [hg]; simp⟩
        · rw [hP x hxb] at h
          obtain ⟨y, hy⟩ := I.df x hx h
          exact ⟨y, by rw [hg]; simp [hxb, hy]⟩ }
    split
    · exact key
    · rename_i hne
      have heq : s[b]! = some r := by simp at hne; exact hne.symm
      simpa only [set_self s hbn heq] using key


theorem Inv.round_fold (H : Hyp succs preds rpo num) :
    ∀ (rest pre : List Nat) (st : Array (Option Nat) × Bool), rpo = pre ++ rest →
      Inv succs preds rpo num k (· ∈ pre) st.1 →
      Inv succs preds rpo num k (· ∈ rpo) (rest.foldl (DomAlgo.rstep preds num (2 * preds.size + 2)) st).1 := by
  intro rest
  induction rest with
  | nil => intro pre st hr I; simp only [List.append_nil] at hr; subst hr; exact I
  | cons b rest ih =>
    intro pre st hr I
    exact ih (pre ++ [b]) _ (by simp [hr]) (I.rstep H hr)

/-- One round raises the level of the invariant. -/
theorem Inv.round (H : Hyp succs preds rpo num) (I : Inv succs preds rpo num k (fun _ => False) s) :
    Inv succs preds rpo num (k + 1) (fun _ => False) (round preds rpo num (2 * preds.size + 2) s).1 := by
  have I0 : Inv succs preds rpo num k (· ∈ ([] : List Nat)) (s, false).1 :=
    I.weaken (fun x _ h => by simp at h) (fun x _ h => by simp at h)
  have I1 := Inv.round_fold H rpo [] (s, false) (by simp) I0
  exact {
    size := I1.size
    s0 := I1.s0
    dr := I1.dr
    dd := I1.dd
    rk := I1.rk
    pi := I1.pi
    q := fun x y hx h m hm a hp => I1.q x y hx h m (by
      rcases hm with hm | ⟨hm, _⟩
      · by_cases hmk : m < k
        · exact .inl hmk
        · exact .inr ⟨I1.dr _ _ h, by omega⟩
      · exact hm.elim) a hp
    df := fun x hx _ => I1.df x hx (.inr hx) }

theorem rstep_fix {st : Array (Option Nat) × Bool} {b : Nat}
    (h : (DomAlgo.rstep preds num (2 * preds.size + 2) st b).2 = false) :
    st.2 = false ∧ (DomAlgo.rstep preds num (2 * preds.size + 2) st b).1 = st.1 := by
  unfold DomAlgo.rstep at h ⊢
  split
  · rename_i hb; rw [ite_eq_left hb] at h; exact ⟨h, rfl⟩
  · rename_i hb; rw [ite_eq_right hb] at h
    split
    · rename_i hc; rw [ite_eq_left hc] at h; cases h
    · rename_i hc; rw [ite_eq_right hc] at h; exact ⟨h, rfl⟩

theorem round_fix_fold :
    ∀ (l : List Nat) (st : Array (Option Nat) × Bool),
      (l.foldl (DomAlgo.rstep preds num (2 * preds.size + 2)) st).2 = false →
      st.2 = false ∧ (l.foldl (DomAlgo.rstep preds num (2 * preds.size + 2)) st).1 = st.1 := by
  intro l
  induction l with
  | nil => intro st h; exact ⟨h, rfl⟩
  | cons b l ih =>
    intro st h
    rw [List.foldl_cons] at h ⊢
    obtain ⟨h1, h2⟩ := ih _ h
    obtain ⟨h3, h4⟩ := rstep_fix h1
    exact ⟨h3, h2.trans h4⟩

theorem round_fix {s : Array (Option Nat)} (h : (round preds rpo num (2 * preds.size + 2) s).2 = false) :
    (round preds rpo num (2 * preds.size + 2) s).1 = s :=
  (round_fix_fold rpo (s, false) h).2

theorem Inv.rounds (H : Hyp succs preds rpo num) :
    ∀ K k s, Inv succs preds rpo num k (fun _ => False) s →
      Inv succs preds rpo num (k + K) (fun _ => False)
        (DomAlgo.rounds preds rpo num (2 * preds.size + 2) K s) := by
  intro K
  induction K with
  | zero => intro k s I; exact I
  | succ K ih =>
    intro k s I
    simp only [DomAlgo.rounds]
    split
    · rename_i hfix
      have hs := round_fix hfix
      rw [hs]
      have : ∀ j, Inv succs preds rpo num (k + j) (fun _ => False) s := by
        intro j
        induction j with
        | zero => exact I
        | succ j ihj => have := ihj.round H; rw [hs] at this; exact this
      exact this _
    · have := ih (k + 1) _ (I.round H)
      rw [show k + 1 + K = k + (K + 1) by omega] at this
      exact this

theorem Inv.init (H : Hyp succs preds rpo num) (hn : 0 < preds.size) :
    Inv succs preds rpo num 0 (fun _ => False) ((Array.replicate preds.size none).set! 0 (some 0)) := by
  have hg : ∀ x, ((Array.replicate preds.size (none : Option Nat)).set! 0 (some 0))[x]! =
      if x = 0 then some 0 else none := by
    intro x
    rw [get_set _ x _ (by simpa using hn)]
    by_cases hx : x = 0
    · simp [hx]
    · simp only [hx, ite_false]
      rw [getElem!_opt]
      by_cases hxn : x < preds.size <;> simp [hxn]
  refine ⟨by simp, by rw [hg]; simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y h; rw [hg] at h; split at h
    · subst_vars; exact H.zero
    · cases h
  all_goals first
    | (intro x y hx h; rw [hg] at h; simp [hx] at h)
    | (intro x _ h; simp at h)

/-! ## Short paths suffice -/

theorem filter_length_lt {α : Type} {l : List α} {p q : α → Bool}
    (hpq : ∀ k ∈ l, q k = true → p k = true) {x : α} (hx : x ∈ l) (hp : p x = true) (hq : q x = false) :
    (l.filter q).length < (l.filter p).length := by
  induction l with
  | nil => simp at hx
  | cons b l ih =>
    simp only [List.filter_cons]
    have hle := filter_length_le (l := l) fun k hk => hpq k (List.mem_cons_of_mem _ hk)
    rcases List.mem_cons.1 hx with rfl | hx'
    · simp [hp, hq]; omega
    · have := ih (fun k hk => hpq k (List.mem_cons_of_mem _ hk)) hx'
      by_cases hqb : q b = true
      · simp [hqb, hpq b (List.mem_cons_self ..)]; omega
      · simp only [hqb, Bool.false_eq_true, ite_false]
        split <;> simp <;> omega

theorem PathL.stable {a j : Nat} (hj : ∀ x, PathL succs a (j + 1) x → PathL succs a j x) :
    ∀ {m x}, PathL succs a m x → PathL succs a j x := by
  intro m x h
  induction h with
  | entry _ ha => exact .entry j ha
  | step _ hx hxa ih => exact hj _ (.step ih hx hxa)

open Classical in
/-- A block reachable avoiding `a` is reachable avoiding `a` in at most `|rpo|` steps. -/
theorem Hyp.bound (H : Hyp succs preds rpo num) {a x : Nat} (h : ReachAvoid succs a x) :
    PathL succs a rpo.length x := by
  let cnt : Nat → Nat := fun m => (rpo.filter fun x => decide (PathL succs a m x)).length
  have hgrow : ∀ m, (∀ j < m, ∃ y, PathL succs a (j + 1) y ∧ ¬ PathL succs a j y) → m ≤ cnt m := by
    intro m
    induction m with
    | zero => intro _; exact Nat.zero_le _
    | succ m ih =>
      intro hj
      have h1 := ih fun j hj' => hj j (by omega)
      obtain ⟨y, hy1, hy2⟩ := hj m (by omega)
      have : cnt m < cnt (m + 1) :=
        filter_length_lt (fun k _ hk => by simpa using (of_decide_eq_true hk).mono (Nat.le_succ m))
          (H.path_mem hy1) (by simpa using hy1) (by simpa using hy2)
      omega
  have hcnt : ∀ m, cnt m ≤ rpo.length := fun m => List.length_filter_le _ _
  have : ¬ ∀ j < rpo.length + 1, ∃ y, PathL succs a (j + 1) y ∧ ¬ PathL succs a j y := by
    intro hall; have := hgrow _ hall; have := hcnt (rpo.length + 1); omega
  obtain ⟨j, hj, hst⟩ : ∃ j < rpo.length + 1, ∀ y, PathL succs a (j + 1) y → PathL succs a j y := by
    refine Classical.byContradiction fun hn => this fun j hj => ?_
    refine Classical.byContradiction fun hn' => hn ⟨j, hj, fun y hy => ?_⟩
    exact Classical.byContradiction fun hy' => hn' ⟨y, hy, hy'⟩
  obtain ⟨m, hm⟩ := ReachAvoid.toPathL h
  exact (PathL.stable hst hm).mono (by omega)


/-- The final state of the rounds gives the facts of `DomFacts`. -/
theorem final (H : Hyp succs preds rpo num) (hn : 0 < preds.size) :
    let t := (DomAlgo.rounds preds rpo num (2 * preds.size + 2) (preds.size + 2)
      ((Array.replicate preds.size none).set! 0 (some 0))).set! 0 none
    (∀ b x, t[b]?.join = some x → b ∈ rpo ∧ x ∈ rpo ∧ num x < num b) ∧ t[0]?.join = none ∧
      (∀ u x, u ∈ rpo → x ∈ succs[u]! → ∀ y, t[x]?.join = some y → Anc t y u) ∧
      (∀ a b, b ∈ rpo → ¬ ReachAvoid succs a b → Anc t a b) := by
  intro t
  have I := Inv.rounds H (preds.size + 2) 0 _ (Inv.init H hn)
  simp only [Nat.zero_add] at I
  refine ⟨fun b x h => ?_, by show t[0]?.join = none; rw [tget]; simp, fun u x hu hx y h => ?_, fun a b hb h => ?_⟩
  · obtain ⟨h0, hs⟩ := tget_some h
    exact ⟨I.dr _ _ hs, I.mem (I.dd _ _ h0 hs), I.rk _ _ h0 hs⟩
  · obtain ⟨h0, hs⟩ := tget_some h
    have hyx : ¬ ReachAvoid succs y x := by
      intro hra
      have hp := I.q x y h0 hs rpo.length (.inl (by have := H.len; omega)) y (H.bound hra)
      exact hp.ne rfl
    have hne : x ≠ y := fun hxy => by subst hxy; have := I.rk _ _ h0 hs; omega
    exact I.sound' (I.df u hu (.inl (by omega))) fun h' => hyx (.step h' hx hne)
  · exact I.sound' (I.df b hb (.inl (by omega))) h

end Core

/-! ## The depth-first search: every block but the entry has a predecessor finished later -/

/-- The stack blocks, top first: each block but the bottom one (the entry) is a successor of the
block below it. -/
inductive SOk (succs : Array (List Nat)) : List Nat → Prop
  | nil : SOk succs []
  | root : SOk succs [0]
  | cons {x y : Nat} {l : List Nat} : SOk succs (x :: l) → y ∈ succs[x]! → y ≠ 0 → SOk succs (y :: x :: l)

theorem SOk.inv {succs : Array (List Nat)} {L : List Nat} (h : SOk succs L) :
    ∀ b R, L = b :: R → SOk succs R ∧ (b = 0 → R = []) ∧ (b ≠ 0 → ∃ x ∈ R, b ∈ succs[x]!) := by
  intro b R hL
  cases h with
  | nil => cases hL
  | root => cases hL; exact ⟨.nil, fun _ => rfl, fun h => absurd rfl h⟩
  | cons h1 h2 h3 => cases hL; exact ⟨h1, fun h => absurd h h3, fun _ => ⟨_, by simp, h2⟩⟩

/-- The extra invariant of the search. -/
structure DInv (succs : Array (List Nat)) (s : DfsSt) : Prop where
  v0 : s.1[0]! = true
  fr : ∀ fr ∈ s.2.1.toList, ∀ y ∈ fr.2, y ∈ succs[fr.1]!
  sok : SOk succs (s.2.1.toList.map (·.1)).reverse
  par : ∀ (i x : Nat), s.2.2.toList[i]? = some x → x ≠ 0 → ∃ p, x ∈ succs[p]! ∧
    (p ∈ s.2.1.toList.map (·.1) ∨ ∃ j : Nat, i < j ∧ s.2.2.toList[j]? = some p)
  fin : 0 ∈ s.2.2.toList → s.2.1.toList = []

theorem set_true_zero {vis : Array Bool} (h : vis[0]! = true) (x : Nat) : (vis.set! x true)[0]! = true := by
  by_cases hx : x < vis.size
  · rw [getElem!_set_true hx]; simp [h]
  · simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hx, dite_false]; exact h

/-- **Every block of the postorder but the entry has a predecessor later in the postorder** (its
parent in the search tree). -/
theorem postorder_parent (succs : Array (List Nat))
    (hS : ∀ i < succs.size, ∀ x ∈ succs[i]!, x < succs.size) (hn : succs.size ≠ 0) :
    ∀ (i x : Nat), (Cfg.postorder succs).toList[i]? = some x → x ≠ 0 →
      ∃ (j p : Nat), i < j ∧ (Cfg.postorder succs).toList[j]? = some p ∧ x ∈ succs[p]! := by
  have h0 := (postorder_closed succs hS hn).1
  revert h0
  unfold Cfg.postorder
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', beq_iff_eq, hn, ite_false]
  rw [bind_pure_comp]
  simp only [Functor.map]
  refine forIn_inv' _ _ _ (P := DInv succs)
    (Q := fun s : DfsSt => 0 ∈ s.2.2.toList → ∀ (i x : Nat), s.2.2.toList[i]? = some x → x ≠ 0 →
      ∃ (j p : Nat), i < j ∧ s.2.2.toList[j]? = some p ∧ x ∈ succs[p]!) ?_ ?_ ?_
  · have hlt : 0 < (Array.replicate succs.size false).size := by simp; omega
    refine ⟨by rw [getElem!_set_true hlt]; simp, fun fr hfr y hy => ?_, by simp; exact .root,
      fun i x h => by simp at h, fun h => by simp at h⟩
    simp at hfr; subst hfr; exact hy
  · rintro - ⟨vis, st, post⟩ ⟨hv0, hfr, hsok, hpar, hfin⟩
    simp only at hv0 hfr hsok hpar hfin
    cases hb : st.back? with
    | none => simpa [hb] using (⟨hv0, hfr, hsok, hpar, hfin⟩ : DInv succs (vis, st, post))
    | some fr =>
      obtain ⟨b, ss⟩ := fr
      have hst := back?_toList hb
      have hne : st.toList ≠ [] := by rw [hst]; simp
      have hfin' : 0 ∉ post.toList := fun h => hne (hfin h)
      rw [hst] at hfr hsok
      simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hsok
      have hfr' : ∀ fr ∈ st.pop.toList, ∀ y ∈ fr.2, y ∈ succs[fr.1]! :=
        fun fr h => hfr fr (List.mem_append_left _ h)
      have hbs : ∀ y ∈ ss, y ∈ succs[b]! := hfr (b, ss) (by simp)
      cases ss with
      | nil =>
        simp only [Id.run_pure, ForInStep.value]
        obtain ⟨hR, hR0, hRp⟩ := hsok.inv b _ rfl
        refine ⟨hv0, hfr', by simpa using hR, ?_, ?_⟩
        · intro i y hy hy0
          simp only [Array.toList_push] at hy ⊢
          by_cases hi : i < post.toList.length
          · rw [List.getElem?_append_left hi] at hy
            obtain ⟨p, hp, hp'⟩ := hpar i y hy hy0
            refine ⟨p, hp, ?_⟩
            rcases hp' with hp' | ⟨j, hij, hj⟩
            · rw [hst] at hp'
              simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
                List.mem_singleton] at hp'
              rcases hp' with hp' | rfl
              · exact .inl hp'
              · exact .inr ⟨post.toList.length, hi, by simp⟩
            · have hjl : j < post.toList.length := (List.getElem?_eq_some_iff.1 hj).1
              exact .inr ⟨j, hij, by rw [List.getElem?_append_left hjl]; exact hj⟩
          · have hil : i < post.toList.length + 1 := by
              have := (List.getElem?_eq_some_iff.1 hy).1; simpa using this
            have hi' : i = post.toList.length := by omega
            subst hi'
            simp at hy; subst hy
            obtain ⟨x, hx, hbx⟩ := hRp hy0
            exact ⟨x, hbx, .inl (by simpa using hx)⟩
        · intro h
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h
          rcases h with h | h
          · exact absurd h hfin'
          · have := hR0 h.symm
            rw [List.reverse_eq_nil_iff, List.map_eq_nil_iff] at this
            exact this
      | cons x rest =>
        have hxs : x ∈ succs[b]! := hbs x (List.mem_cons_self ..)
        simp only
        split
        · rename_i hvx
          have hvf : vis[x]! = false := by simp at hvx; exact hvx
          have hx0 : x ≠ 0 := by rintro rfl; rw [hv0] at hvf; cases hvf
          simp only [Id.run_pure, ForInStep.value]
          refine ⟨set_true_zero hv0 x, ?_, ?_, ?_, fun h => absurd h hfin'⟩
          · intro fr h y hy
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h
            rcases h with (h | rfl) | rfl
            · exact hfr' fr h y hy
            · exact hbs y (List.mem_cons_of_mem _ hy)
            · exact hy
          · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil,
              List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
              List.cons_append]
            exact .cons hsok hxs hx0
          · intro i y hy hy0
            obtain ⟨p, hp, hp'⟩ := hpar i y hy hy0
            refine ⟨p, hp, hp'.imp_left fun h => ?_⟩
            rw [hst] at h
            simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
              List.mem_singleton] at h
            simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil,
              List.mem_append, List.mem_singleton]
            rcases h with h | h
            · exact .inl (.inl h)
            · exact .inl (.inr h)
        · simp only [Id.run_pure, ForInStep.value]
          refine ⟨hv0, ?_, ?_, ?_, fun h => absurd h hfin'⟩
          · intro fr h y hy
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h
            rcases h with h | rfl
            · exact hfr' fr h y hy
            · exact hbs y (List.mem_cons_of_mem _ hy)
          · simpa using hsok
          · intro i y hy hy0
            obtain ⟨p, hp, hp'⟩ := hpar i y hy hy0
            refine ⟨p, hp, hp'.imp_left fun h => ?_⟩
            rw [hst] at h
            simpa using h
  · rintro ⟨vis, st, post⟩ ⟨_, _, _, hpar, hfin⟩ h0 i x hx hx0
    simp only at hpar hfin h0 hx ⊢
    have hst := hfin h0
    obtain ⟨p, hp, hp'⟩ := hpar i x hx hx0
    rcases hp' with hp' | ⟨j, hij, hj⟩
    · rw [hst] at hp'; simp at hp'
    · exact ⟨j, p, hij, hj, hp⟩




/-! ## `Cfg.build` -/

theorem nodup_length_le : ∀ (n : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < n) → l.length ≤ n := by
  intro n
  induction n with
  | zero => intro l _ h; cases l with
    | nil => exact Nat.le_refl _
    | cons x _ => exact absurd (h x (by simp)) (Nat.not_lt_zero _)
  | succ n ih =>
    intro l hl h
    by_cases hn : n ∈ l
    · have h1 := ih (l.erase n) (hl.erase n) fun x hx => by
        have := (hl.mem_erase_iff).1 hx
        have := h x this.2
        omega
      have h2 := List.length_erase_of_mem hn
      have : 0 < l.length := List.length_pos_of_mem hn
      omega
    · have := ih l hl fun x hx => by
        have := h x hx
        have : x ≠ n := fun h' => hn (h' ▸ hx)
        omega
      omega

theorem fold_set_other (l : List (Nat × Nat)) (r : Array (Option Nat)) (x : Nat)
    (hx : x ∉ l.map (·.1)) :
    (l.foldl (fun r (y : Nat × Nat) => r.set! y.1 (some y.2)) r)[x]? = r[x]? := by
  induction l generalizing r with
  | nil => rfl
  | cons y l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    rw [List.foldl_cons, ih _ hx.2]
    simp [Array.set!_eq_setIfInBounds, Ne.symm hx.1]

theorem fold_set_get (l : List Nat) (hl : l.Nodup) :
    ∀ (k : Nat) (r : Array (Option Nat)), (∀ x ∈ l, x < r.size) → ∀ i (h : i < l.length),
      ((l.zipIdx k).foldl (fun r (y : Nat × Nat) => r.set! y.1 (some y.2)) r)[l[i]]?.join =
        some (k + i) := by
  induction l with
  | nil => intro k r _ i h; simp at h
  | cons a l ih =>
    intro k r hr i hi
    rw [List.zipIdx_cons, List.foldl_cons]
    have ha : a < r.size := hr a (by simp)
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero]
      rw [fold_set_other _ _ _ (by rw [List.zipIdx_map_fst]; exact (List.nodup_cons.1 hl).1)]
      simp [Array.set!_eq_setIfInBounds, ha]
    | succ i =>
      simp only [List.getElem_cons_succ]
      rw [ih (List.nodup_cons.1 hl).2 (k + 1) _ (fun x hx => by simpa using hr x (by simp [hx])) i
        (by simpa using hi)]
      simp; omega

theorem build_rpoNum_get (f : Function) (i : Nat) (h : i < (Cfg.build f).rpo.toList.length) :
    (Cfg.build f).rpoNum[(Cfg.build f).rpo.toList[i]]?.join = some i := by
  rw [build_rpoNum, ← Array.foldl_toList, Array.toList_zipIdx]
  have := fold_set_get _ (build_rpo_nodup f) 0 (Array.replicate f.blocks.length none)
    (fun x hx => by simpa using build_rpo_lt f hx) i h
  simpa using this

theorem build_rpoNum_none (f : Function) {x : Nat} (hx : x ∉ (Cfg.build f).rpo.toList) :
    (Cfg.build f).rpoNum[x]?.join = none := by
  rw [build_rpoNum, ← Array.foldl_toList, Array.toList_zipIdx,
    fold_set_other _ _ _ (by rw [List.zipIdx_map_fst]; exact hx)]
  by_cases h : x < f.blocks.length <;> simp [h]

theorem build_reachable_mem (f : Function) {x : Nat} (h : (Cfg.build f).reachable x = true) :
    x ∈ (Cfg.build f).rpo.toList := by
  refine Classical.byContradiction fun hx => ?_
  unfold Cfg.reachable at h
  rw [build_rpoNum_none f hx] at h
  cases h

theorem build_mem_rpo (f : Function) {x : Nat} :
    x ∈ (Cfg.build f).rpo.toList ↔ x ∈ (Cfg.postorder (Cfg.build f).succs).toList := by
  rw [build_rpo, Array.toList_reverse, List.mem_reverse]

/-- The hypotheses of the analysis hold for `Cfg.build`. -/
theorem build_hyp (f : Function) (hL : f.blocks.length ≠ 0) :
    Hyp (Cfg.build f).succs (Cfg.build f).preds (Cfg.build f).rpo.toList
      (fun b => ((Cfg.build f).rpoNum[b]?.join).getD (Cfg.build f).preds.size) := by
  have hpsz := build_preds_size f
  have hS := build_succs_lt f
  have hn : (Cfg.build f).succs.size ≠ 0 := by rw [build_succs_size]; exact hL
  have hidx : ∀ i (h : i < (Cfg.build f).rpo.toList.length),
      ((Cfg.build f).rpoNum[(Cfg.build f).rpo.toList[i]]?.join).getD (Cfg.build f).preds.size = i := by
    intro i h; rw [build_rpoNum_get f i h]; rfl
  have hnum : ∀ i x, (Cfg.build f).rpo.toList[i]? = some x →
      ((Cfg.build f).rpoNum[x]?.join).getD (Cfg.build f).preds.size = i := by
    intro i x h
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 h
    exact hidx i hi
  refine ⟨fun x hx => hpsz ▸ build_rpo_lt f hx, build_rpo_nodup f, hidx,
    (build_mem_rpo f).2 (postorder_closed _ hS hn).1, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb p hp
    exact ((build_preds_mem f (build_rpo_lt f hb)).1 hp).2
  · intro b hb p hp h
    exact (build_preds_mem f (build_rpo_lt f hb)).2 ⟨build_rpo_lt f hp, h⟩
  · intro p hp x hx
    exact (build_mem_rpo f).2 (((postorder_closed _ hS hn).2 p ((build_mem_rpo f).1 hp)).2 x hx)
  · intro b hb hb0
    have hb' := (build_mem_rpo f).1 hb
    obtain ⟨i, hi, hbi⟩ := List.mem_iff_getElem.1 hb'
    obtain ⟨j, p, hij, hj, hp⟩ := postorder_parent _ hS hn i b (by rw [List.getElem?_eq_getElem hi, hbi]) hb0
    have hjl := (List.getElem?_eq_some_iff.1 hj).1
    have hrpo : (Cfg.build f).rpo.toList = (Cfg.postorder (Cfg.build f).succs).toList.reverse := by
      rw [build_rpo, Array.toList_reverse]
    have e1 : (Cfg.build f).rpo.toList[(Cfg.postorder (Cfg.build f).succs).toList.length - 1 - i]? =
        some b := by
      rw [hrpo, List.getElem?_reverse (by omega), show (Cfg.postorder (Cfg.build f).succs).toList.length -
        1 - ((Cfg.postorder (Cfg.build f).succs).toList.length - 1 - i) = i by omega]
      rw [List.getElem?_eq_getElem hi, hbi]
    have e2 : (Cfg.build f).rpo.toList[(Cfg.postorder (Cfg.build f).succs).toList.length - 1 - j]? =
        some p := by
      rw [hrpo, List.getElem?_reverse (by omega), show (Cfg.postorder (Cfg.build f).succs).toList.length -
        1 - ((Cfg.postorder (Cfg.build f).succs).toList.length - 1 - j) = j by omega]
      exact hj
    refine ⟨p, List.mem_of_getElem? e2, hp, ?_⟩
    rw [hnum _ _ e1, hnum _ _ e2]
    omega
  · exact hpsz ▸ nodup_length_le _ _ (build_rpo_nodup f) fun x hx => build_rpo_lt f hx

end DomAlgo

/-- **The dominator tree of `Cfg.build` has the facts of `DomFacts`** (`Cfg.dominators` reaches the
dominator tree within its `n + 2` rounds). -/
theorem build_domFacts (f : Function) : DomFacts (Cfg.build f) := by
  have hpsz := build_preds_size f
  have hsz : (Cfg.build f).size = f.blocks.length := by simp [Cfg.size, Cfg.build]
  by_cases hL : f.blocks.length = 0
  · have hid : (Cfg.build f).idom = #[] := by
      rw [build_idom_eq]; unfold Cfg.dominators; simp [hpsz, hL]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [hid, hsz, hL]
  have H := DomAlgo.build_hyp f hL
  have hn : 0 < (Cfg.build f).preds.size := by omega
  have hid := DomAlgo.dominators_eq (Cfg.build f).preds (Cfg.build f).rpo (Cfg.build f).rpoNum (by omega)
  rw [← build_idom_eq] at hid
  obtain ⟨h1, h2, h3, h4⟩ := DomAlgo.final H hn
  rw [← hid] at h1 h2 h3 h4
  have hget : ∀ x ∈ (Cfg.build f).rpo.toList, ∃ i, (Cfg.build f).rpoNum[x]?.join = some i := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    exact ⟨i, DomAlgo.build_rpoNum_get f i hi⟩
  refine ⟨fun b x h => ?_, h2, fun b x h => ?_, fun u x hu hx y h => h3 u x (DomAlgo.build_reachable_mem f hu) hx y h,
    fun a b hb _ h => h4 a b (DomAlgo.build_reachable_mem f hb) h⟩
  · have := H.lt x (h1 b x h).2.1; omega
  · obtain ⟨hb, hx, hlt⟩ := h1 b x h
    obtain ⟨i, hi⟩ := hget x hx
    obtain ⟨j, hj⟩ := hget b hb
    simp only [hi, hj, Option.getD_some] at hlt ⊢
    exact hlt


/-! ## Witness -/

namespace DomCompleteWitness

/-- An irreducible loop `block1 ⇄ block2` entered from `block0` at both blocks, followed by a loop
`block3 … block6` (latch `block6`) around the nested loop `block4, block5` (latch `block5`). -/
def fn : Function where
  name := "dom"
  sig := {}
  blocks := [
    { id := 0, term := .brif 0 { block := 1 } { block := 2 } },
    { id := 1, term := .jump { block := 2 } },
    { id := 2, term := .brif 0 { block := 1 } { block := 3 } },
    { id := 3, term := .jump { block := 4 } },
    { id := 4, term := .jump { block := 5 } },
    { id := 5, term := .brif 0 { block := 4 } { block := 6 } },
    { id := 6, term := .brif 0 { block := 3 } { block := 7 } },
    { id := 7, term := .ret [] }]

/-- The dominator tree: both blocks of the irreducible loop hang off the entry. -/
theorem idom_eq :
    (Cfg.build fn).idom = #[none, some 0, some 0, some 2, some 3, some 4, some 5, some 6] := by
  native_decide

/-- Non-vacuity of `build_domFacts`: its edge fact on the outer latch `block6 → block3` makes the
exit `block2` of the irreducible loop a tree ancestor of the latch (four tree steps up). -/
theorem witness : Anc (Cfg.build fn).idom 2 6 :=
  (build_domFacts fn).edge 6 3 (by native_decide) (by native_decide) 2 (by rw [idom_eq]; rfl)

end DomCompleteWitness

end Opt


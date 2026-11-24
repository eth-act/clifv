import Std.Data.HashSet.Lemmas

/-!
# The availability fixpoint over arrays, dense and sparse

`inFix` (`DriverCheck.lean`) computes the greatest solution of the availability constraints with
a worklist over (block, value) pairs on a blocks × values byte table (`fixLoop`), so its time and
memory grow with blocks × values (#1090: 9,034 × 18,554 = 167.6M pairs on num-bigint's
`check_sub`, of which 136.7M are removed one by one). This file states the constraints over the
arrays `inFix` builds (`ASol`), shows that `fixLoop`'s table is their greatest solution
(`Fix.dense_sol`, `Fix.dense_great`), and defines the sparse computation the compiler runs
instead (`fixSparse`, `inFixSparse` in `DriverCheck.lean`): per block the sorted array of its
available values, recomputed from the arrays of its predecessors, pass after pass (the first in
reverse postorder) until a pass changes nothing. Every pass keeps every solution
(`Fix.pass_inv`) and a pass that changes nothing ends at a solution (`Fix.pass_same`), so the
sparse result is the greatest solution too (`Fix.fixSparse_eq`). Its work grows with the number
of (block, available value) pairs, the size of `inFix`'s result.
-/

namespace Backend.Proof.Driver

/-- `x` is (still) available at the entry of block `tl` in `inB` (`nv` values per block). -/
def fixHas (nv : Nat) (inB : ByteArray) (tl x : Nat) : Bool := x < nv && inB.get! (tl * nv + x) != 0

/-- The worklist loop of `inFix`: pop a pair `(tl, x)`; if `x` is still available at `tl`'s entry,
remove it, and if it is neither a parameter nor a result of `tl` (so it also leaves the end of
`tl`), push the pairs it may now violate: `x` at the entries of `tl`'s successors, and the users
of `x` (the values whose definition reads it) at `tl`'s entry. Every pushed pair violates a
constraint when pushed, so each iteration removes a pair or pops one; `fixFuel` bounds the
iterations (`inFix_spec`). -/
def fixLoop (nv : Nat) (pars defs : Array (Std.HashSet Nat)) (succs users : Array (List Nat)) :
    Nat → ByteArray → List (Nat × Nat) → ByteArray
  | 0, inB, _ => inB
  | _ + 1, inB, [] => inB
  | fuel + 1, inB, (tl, x) :: rest =>
    if fixHas nv inB tl x then
      let inB := inB.set! (tl * nv + x) 0
      if !pars[tl]!.contains x && !defs[tl]!.contains x then
        let rest := succs[tl]!.foldl (fun w s => if fixHas nv inB s x then (s, x) :: w else w) rest
        let rest := users[x]!.foldl (fun w z => if fixHas nv inB tl z then (tl, z) :: w else w) rest
        fixLoop nv pars defs succs users fuel inB rest
      else fixLoop nv pars defs succs users fuel inB rest
    else fixLoop nv pars defs succs users fuel inB rest

/-- Enough iterations for `fixLoop` from `work` (`nb * nv` pairs, each removed at most once,
each removal pushing at most `maxPush` pairs). -/
def fixFuel (nb nv : Nat) (succs users : Array (List Nat)) (work : List (Nat × Nat)) : Nat :=
  let maxPush := succs.foldl (fun m s => max m s.length) 0 + users.foldl (fun m u => max m u.length) 0
  work.length + nb * nv * (maxPush + 1) + 1

namespace Fix

/-! ## Generic facts -/

/-- `a[i]!` through `a[i]?`. -/
theorem bang {α : Type} [Inhabited α] (a : Array α) (i : Nat) : a[i]! = a[i]?.getD default := by
  simp only [getElem!_def]; split <;> simp_all

/-- Membership in a left fold whose step adds the elements `P a`. -/
theorem mem_foldl {α β : Type} {H : List β → α → List β} {P : α → β → Prop}
    (hH : ∀ w a q, q ∈ H w a ↔ q ∈ w ∨ P a q) :
    ∀ (l : List α) (w : List β) (q : β), q ∈ l.foldl H w ↔ q ∈ w ∨ ∃ a ∈ l, P a q
  | [], w, q => by simp
  | a :: l, w, q => by
    rw [List.foldl_cons, mem_foldl hH l, hH]
    simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

/-- The length of a left fold whose step adds at most one element. -/
theorem length_foldl {α β : Type} {H : List β → α → List β}
    (hH : ∀ w a, (H w a).length ≤ w.length + 1) :
    ∀ (l : List α) (w : List β), (l.foldl H w).length ≤ w.length + l.length
  | [], w => by simp
  | a :: l, w => by
    have h1 := length_foldl hH l (H w a)
    have h2 := hH w a
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- A conditional push. -/
theorem mem_push {β : Type} (c : Bool) (b : β) (w : List β) (q : β) :
    q ∈ (if c = true then b :: w else w) ↔ q ∈ w ∨ (c = true ∧ q = b) := by
  cases c <;> simp [or_comm]

/-- A conditional push adds at most one element. -/
theorem length_push {β : Type} (c : Bool) (b : β) (w : List β) :
    (if c = true then b :: w else w).length ≤ w.length + 1 := by
  cases c <;> simp

/-- A doubly conditional push (`inFix`'s initial worklist). -/
theorem mem_push2 {β : Type} (c1 c2 : Bool) (b : β) (w : List β) (q : β) :
    q ∈ (if c1 = true then (if (!c2) = true then b :: w else w) else w) ↔
      q ∈ w ∨ ((c1 = true ∧ c2 = false) ∧ q = b) := by
  cases c1 <;> cases c2 <;> simp [or_comm]

/-- Prepending `v` at the indices of `l`. -/
theorem modify_fold (v : Nat) : ∀ (l : List Nat) (ps : Array (List Nat)),
    (l.foldl (fun ps s => ps.modify s (v :: ·)) ps).size = ps.size ∧
    ∀ t p, p ∈ (l.foldl (fun ps s => ps.modify s (v :: ·)) ps)[t]?.getD [] ↔
      p ∈ ps[t]?.getD [] ∨ (p = v ∧ t ∈ l ∧ t < ps.size)
  | [], ps => by simp
  | s :: l, ps => by
    obtain ⟨h1, h2⟩ := modify_fold v l (ps.modify s (v :: ·))
    simp only [List.foldl_cons, Array.size_modify] at h1 h2 ⊢
    refine ⟨h1, fun t p => ?_⟩
    rw [h2, Array.getElem?_modify]
    by_cases e : s = t
    · subst e
      rcases Nat.lt_or_ge s ps.size with hs | hs
      · simp only [Array.getElem?_eq_getElem hs, ite_true, Option.map_some, Option.getD_some,
          List.mem_cons, true_or, and_true, hs]
        constructor
        · rintro ((h | h) | ⟨h, -⟩) <;> simp_all
        · rintro (h | h) <;> simp_all
      · simp [Nat.not_lt.2 hs]
    · simp only [e, ite_false, List.mem_cons]
      constructor
      · rintro (h | ⟨h1, h2, h3⟩) <;> simp_all
      · rintro (h | ⟨h1, (h2 | h2), h3⟩)
        · exact .inl h
        · exact absurd h2.symm e
        · exact .inr ⟨h1, h2, h3⟩


/-- An element of an array is at most the fold of the maximum length. -/
theorem len_le_max (a : Array (List Nat)) (i : Nat) :
    (a[i]!).length ≤ a.foldl (fun m s => max m s.length) 0 := by
  rw [bang]
  rcases Nat.lt_or_ge i a.size with hi | hi
  · rw [Array.getElem?_eq_getElem hi, Option.getD_some]
    have := Array.foldl_induction (as := a)
      (fun n m => ∀ j (hj : j < n) (hj' : j < a.size), a[j].length ≤ m) (init := 0)
      (f := fun m s => max m s.length) (by intro j hj; omega) (by
        intro k m ih j hj hj'
        rcases Nat.lt_or_ge j k with h | h
        · exact Nat.le_trans (ih j h hj') (Nat.le_max_left _ _)
        · have : j = k.1 := by omega
          subst this
          exact Nat.le_max_right _ _)
    exact this i hi hi
  · rw [Array.getElem?_eq_none hi]
    exact Nat.zero_le _

/-! ## Bytes -/

/-- `fixHas` through the bytes. -/
theorem has_iff {nv : Nat} {inB : ByteArray} {tl x : Nat} :
    fixHas nv inB tl x = true ↔ x < nv ∧ inB.data[tl * nv + x]?.getD 0 ≠ 0 := by
  have : inB.get! (tl * nv + x) = inB.data[tl * nv + x]?.getD 0 := by
    show inB.data[_]! = _
    rw [bang]; rfl
  simp [fixHas, this]

/-- Distinct pairs have distinct byte indices. -/
theorem idx_inj {nv a b c d : Nat} (hb : b < nv) (hd : d < nv) (h : a * nv + b = c * nv + d) :
    a = c ∧ b = d := by
  have hn : 0 < nv := by omega
  have h1 := congrArg (· / nv) h
  have h2 := congrArg (· % nv) h
  simp only [Nat.mul_comm a nv, Nat.mul_comm c nv, Nat.mul_add_div hn, Nat.mul_add_mod,
    Nat.div_eq_of_lt hb, Nat.div_eq_of_lt hd, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hd,
    Nat.add_zero] at h1 h2
  exact ⟨h1, h2⟩

/-- The byte index of a pair of a block. -/
theorem idx_lt {nb nv tl x : Nat} (ht : tl < nb) (hx : x < nv) : tl * nv + x < nb * nv := by
  have := Nat.mul_le_mul_right nv (Nat.succ_le_of_lt ht)
  rw [Nat.succ_mul] at this
  omega

/-- Removing the pair `(tl, x)`. -/
theorem has_set {nv : Nat} {inB : ByteArray} {tl x : Nat} (hx : x < nv) (a b : Nat) :
    fixHas nv (inB.set! (tl * nv + x) 0) a b = true ↔
      fixHas nv inB a b = true ∧ ¬(a = tl ∧ b = x) := by
  rw [has_iff, has_iff]
  show (b < nv ∧ (inB.data.setIfInBounds (tl * nv + x) 0)[a * nv + b]?.getD 0 ≠ 0) ↔ _
  rw [Array.getElem?_setIfInBounds]
  by_cases hb : b < nv
  · by_cases e : a = tl ∧ b = x
    · obtain ⟨rfl, rfl⟩ := e
      simp only [ite_true]
      split <;> simp
    · have : tl * nv + x ≠ a * nv + b := fun h => e (idx_inj hb hx h.symm)
      simp [this, e, hb]
  · simp [hb]

/-- The number of present pairs. -/
def cnt (inB : ByteArray) : Nat := inB.data.toList.countP (· != 0)

/-- Removing a present pair decreases the count. -/
theorem cnt_set {nv : Nat} {inB : ByteArray} {tl x : Nat} (h : fixHas nv inB tl x = true) :
    cnt (inB.set! (tl * nv + x) 0) + 1 = cnt inB := by
  obtain ⟨-, hne⟩ := has_iff.1 h
  have hi : tl * nv + x < inB.data.size := by
    refine Nat.lt_of_not_ge fun hc => hne ?_
    rw [Array.getElem?_eq_none hc]; rfl
  rw [Array.getElem?_eq_getElem hi, Option.getD_some] at hne
  show (inB.data.setIfInBounds (tl * nv + x) 0).toList.countP _ + 1 = inB.data.toList.countP _
  have hl : tl * nv + x < inB.data.toList.length := by simpa using hi
  have hpos : 0 < inB.data.toList.countP (· != 0) :=
    List.countP_pos_iff.2 ⟨inB.data.toList[tl * nv + x], List.getElem_mem hl, by simpa using hne⟩
  rw [Array.toList_setIfInBounds, List.countP_set hl]
  have : (inB.data.toList[tl * nv + x] != 0) = true := by simpa using hne
  simp only [this, ite_true]
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, Nat.add_zero]
  omega

/-- The pairs present in `inB`. -/
def Has (nv : Nat) (inB : ByteArray) (tl x : Nat) : Prop := fixHas nv inB tl x = true

/-! ## The constraints over the arrays -/

/-- The out-constraint at `(tl, x)` for `S`: every predecessor has `x` at its end (as a parameter,
a result, or at its entry). -/
def AOut (preds : Array (List Nat)) (pars defs : Array (Std.HashSet Nat)) (S : Nat → Nat → Prop)
    (tl x : Nat) : Prop :=
  ∀ q ∈ preds[tl]!, pars[q]!.contains x = true ∨ defs[q]!.contains x = true ∨ S q x

/-- The closure constraint at `(tl, x)` for `S`: the operands of `x`'s definition are available
at `tl`'s entry and not results of `tl`. -/
def AClo (pars defs : Array (Std.HashSet Nat)) (args : Nat → List Nat) (S : Nat → Nat → Prop)
    (tl x : Nat) : Prop :=
  ∀ y ∈ args x, (pars[tl]!.contains y = true ∨ S tl y) ∧ defs[tl]!.contains y = false

/-- `S` solves the constraints below the candidates `C`. -/
def ASol (C : Nat → Nat → Prop) (preds : Array (List Nat)) (pars defs : Array (Std.HashSet Nat))
    (args : Nat → List Nat) (S : Nat → Nat → Prop) : Prop :=
  ∀ tl x, S tl x → C tl x ∧ AOut preds pars defs S tl x ∧ AClo pars defs args S tl x

theorem aOut_mono {preds : Array (List Nat)} {pars defs : Array (Std.HashSet Nat)}
    {S S' : Nat → Nat → Prop} (hS : ∀ a b, S a b → S' a b) {tl x : Nat}
    (h : AOut preds pars defs S tl x) : AOut preds pars defs S' tl x := fun q hq =>
  (h q hq).imp_right (Or.imp_right (hS q x))

theorem aClo_mono {pars defs : Array (Std.HashSet Nat)} {args : Nat → List Nat}
    {S S' : Nat → Nat → Prop} (hS : ∀ a b, S a b → S' a b) {tl x : Nat}
    (h : AClo pars defs args S tl x) : AClo pars defs args S' tl x := fun y hy =>
  ⟨(h y hy).1.imp_right (hS tl y), (h y hy).2⟩

/-- Solutions over equivalent candidates and operands (on the candidates) are the same. -/
theorem aSol_congr {C C' : Nat → Nat → Prop} {preds : Array (List Nat)}
    {pars defs : Array (Std.HashSet Nat)} {args args' : Nat → List Nat} {S : Nat → Nat → Prop}
    (hC : ∀ tl x, C tl x ↔ C' tl x) (hA : ∀ tl x, C tl x → args x = args' x) :
    ASol C preds pars defs args S ↔ ASol C' preds pars defs args' S := by
  refine ⟨fun h tl x hx => ?_, fun h tl x hx => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := h tl x hx
    refine ⟨(hC tl x).1 h1, h2, ?_⟩
    unfold AClo at h3 ⊢
    rw [← hA tl x h1]; exact h3
  · obtain ⟨h1, h2, h3⟩ := h tl x hx
    refine ⟨(hC tl x).2 h1, h2, ?_⟩
    unfold AClo at h3 ⊢
    rw [hA tl x ((hC tl x).2 h1)]; exact h3

/-! ## The dense table: `fixLoop` -/

/-- `inFix`'s initial worklist: the candidate pairs that violate a constraint. -/
def work0 (nb nv : Nat) (pars defs : Array (Std.HashSet Nat)) (preds : Array (List Nat))
    (args : Nat → List Nat) (inB0 : ByteArray) : List (Nat × Nat) :=
  (List.range' 1 (nb - 1)).foldl (fun work tl =>
    (List.range nv).foldl (fun work x =>
      if fixHas nv inB0 tl x then
        let outOk := preds[tl]!.all fun p =>
          pars[p]!.contains x || defs[p]!.contains x || fixHas nv inB0 p x
        let a0Ok := (args x).all fun y =>
          (pars[tl]!.contains y || fixHas nv inB0 tl y) && !defs[tl]!.contains y
        if !(outOk && a0Ok) then (tl, x) :: work else work
      else work) work) []

/-- The invariant of `fixLoop` over the arrays: present pairs are initial candidates, queued
present pairs violate a constraint, every present violating pair is queued, every solution is
present. -/
structure AInv (nv : Nat) (pars defs : Array (Std.HashSet Nat)) (preds : Array (List Nat))
    (args : Nat → List Nat) (inB0 inB : ByteArray) (work : List (Nat × Nat)) : Prop where
  cand : ∀ tl x, Has nv inB tl x → Has nv inB0 tl x
  queued : ∀ q ∈ work, Has nv inB q.1 q.2 →
    ¬(AOut preds pars defs (Has nv inB) q.1 q.2 ∧ AClo pars defs args (Has nv inB) q.1 q.2)
  viol : ∀ tl x, Has nv inB tl x →
    ¬(AOut preds pars defs (Has nv inB) tl x ∧ AClo pars defs args (Has nv inB) tl x) →
    (tl, x) ∈ work
  great : ∀ S, ASol (Has nv inB0) preds pars defs args S → ∀ tl x, S tl x → Has nv inB tl x

section Dense

variable {nb nv : Nat} {pars defs : Array (Std.HashSet Nat)} {succs preds users : Array (List Nat)}
  {args : Nat → List Nat} {inB0 : ByteArray}

/-- Removing the popped present pair `(tl, x)`: what changes. -/
theorem aremove {inB : ByteArray} {tl x : Nat} {rest : List (Nat × Nat)}
    (hi : AInv nv pars defs preds args inB0 inB ((tl, x) :: rest)) (hp : Has nv inB tl x) :
    (∀ a b, Has nv (inB.set! (tl * nv + x) 0) a b ↔ Has nv inB a b ∧ ¬(a = tl ∧ b = x)) ∧
    (∀ S, ASol (Has nv inB0) preds pars defs args S → ∀ a b, S a b →
      Has nv (inB.set! (tl * nv + x) 0) a b) ∧
    (∀ a b, Has nv (inB.set! (tl * nv + x) 0) a b →
      ¬(AOut preds pars defs (Has nv (inB.set! (tl * nv + x) 0)) a b ∧
        AClo pars defs args (Has nv (inB.set! (tl * nv + x) 0)) a b) →
      (a, b) ∈ rest ∨
        (b = x ∧ tl ∈ preds[a]! ∧ pars[tl]!.contains x = false ∧ defs[tl]!.contains x = false) ∨
        (a = tl ∧ x ∈ args b ∧ pars[tl]!.contains x = false ∧ defs[tl]!.contains x = false)) ∧
    (∀ q ∈ rest, Has nv (inB.set! (tl * nv + x) 0) q.1 q.2 →
      ¬(AOut preds pars defs (Has nv (inB.set! (tl * nv + x) 0)) q.1 q.2 ∧
        AClo pars defs args (Has nv (inB.set! (tl * nv + x) 0)) q.1 q.2)) := by
  have hx : x < nv := (has_iff.1 hp).1
  have hs : ∀ a b, Has nv (inB.set! (tl * nv + x) 0) a b ↔ Has nv inB a b ∧ ¬(a = tl ∧ b = x) :=
    fun a b => has_set hx a b
  have hsub : ∀ a b, Has nv (inB.set! (tl * nv + x) 0) a b → Has nv inB a b :=
    fun a b h => ((hs a b).1 h).1
  refine ⟨hs, fun S hS a b hab => ?_, fun a b hab hv => ?_, fun q hq hpq hv => ?_⟩
  · refine (hs a b).2 ⟨hi.great S hS a b hab, ?_⟩
    rintro ⟨rfl, rfl⟩
    have hok : AOut preds pars defs (Has nv inB) a b ∧ AClo pars defs args (Has nv inB) a b :=
      ⟨aOut_mono (hi.great S hS) (hS a b hab).2.1, aClo_mono (hi.great S hS) (hS a b hab).2.2⟩
    exact hi.queued (a, b) List.mem_cons_self hp hok
  · by_cases hr : (a, b) ∈ rest
    · exact .inl hr
    by_cases h2 : b = x ∧ tl ∈ preds[a]! ∧ pars[tl]!.contains x = false ∧
        defs[tl]!.contains x = false
    · exact .inr (.inl h2)
    by_cases h3 : a = tl ∧ x ∈ args b ∧ pars[tl]!.contains x = false ∧
        defs[tl]!.contains x = false
    · exact .inr (.inr h3)
    exfalso
    obtain ⟨hab', hne⟩ := (hs a b).1 hab
    have hold : AOut preds pars defs (Has nv inB) a b ∧ AClo pars defs args (Has nv inB) a b := by
      refine Classical.byContradiction fun hn => hr ?_
      rcases List.mem_cons.1 (hi.viol a b hab' hn) with e | e
      · simp only [Prod.mk.injEq] at e; exact absurd e hne
      · exact e
    apply hv
    refine ⟨fun p hpp => ?_, fun y hyy => ?_⟩
    · rcases hold.1 p hpp with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · by_cases e : p = tl ∧ b = x
        · obtain ⟨rfl, rfl⟩ := e
          cases hp' : pars[p]!.contains b
          · cases hd' : defs[p]!.contains b
            · exact absurd ⟨rfl, hpp, hp', hd'⟩ h2
            · exact .inr (.inl rfl)
          · exact .inl rfl
        · exact .inr (.inr ((hs p b).2 ⟨h, e⟩))
    · obtain ⟨h1, h1'⟩ := hold.2 y hyy
      refine ⟨?_, h1'⟩
      rcases h1 with h | h
      · exact .inl h
      · by_cases e : a = tl ∧ y = x
        · obtain ⟨rfl, rfl⟩ := e
          cases hp' : pars[a]!.contains y
          · exact absurd ⟨rfl, hyy, hp', h1'⟩ h3
          · exact .inl rfl
        · exact .inr ((hs a y).2 ⟨h, e⟩)
  · exact hi.queued q (List.mem_cons_of_mem _ hq) (hsub _ _ hpq)
      ⟨aOut_mono hsub hv.1, aClo_mono hsub hv.2⟩

/-- `fixLoop` with enough fuel ends with an empty worklist, keeping the invariant. -/
theorem aloop (hc0 : ∀ tl x, Has nv inB0 tl x → 1 ≤ tl ∧ tl < nb)
    (hsp : ∀ p s : Nat, p ∈ preds[s]! → s ∈ succs[p]!)
    (hps : ∀ p s : Nat, s ∈ succs[p]! → s < nb → p ∈ preds[s]!)
    (hus : ∀ y z : Nat, y < nv → (z ∈ users[y]! ↔ z < nv ∧ y ∈ args z))
    (M : Nat) (hM : ∀ tl x : Nat, succs[tl]!.length + users[x]!.length ≤ M) :
    ∀ fuel inB work, AInv nv pars defs preds args inB0 inB work →
      work.length + cnt inB * (M + 1) < fuel →
      AInv nv pars defs preds args inB0 (fixLoop nv pars defs succs users fuel inB work) []
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, inB, [], hi, _ => by simpa only [fixLoop] using hi
  | fuel + 1, inB, (tl, x) :: rest, hi, hf => by
    simp only [fixLoop]
    by_cases hp : fixHas nv inB tl x = true
    · rw [ite_eq_left hp]
      obtain ⟨hs, hg, hv, hw⟩ := aremove hi hp
      have hc : ∀ a b, Has nv (inB.set! (tl * nv + x) 0) a b → Has nv inB0 a b :=
        fun a b h => hi.cand a b ((hs a b).1 h).1
      have hcnt := cnt_set hp
      have hx : x < nv := (has_iff.1 hp).1
      simp only [List.length_cons] at hf
      have hK : cnt inB * (M + 1) = cnt (inB.set! (tl * nv + x) 0) * (M + 1) + (M + 1) := by
        rw [← hcnt, Nat.add_mul, Nat.one_mul]
      by_cases hn : (!pars[tl]!.contains x && !defs[tl]!.contains x) = true
      · rw [ite_eq_left hn]
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hn
        have hmem := mem_foldl (fun w s q => mem_push
          (fixHas nv (inB.set! (tl * nv + x) 0) s x) (s, x) w q)
        have hmem2 := mem_foldl (fun w z q => mem_push
          (fixHas nv (inB.set! (tl * nv + x) 0) tl z) (tl, z) w q)
        have hl1 := length_foldl (fun w s => length_push
          (fixHas nv (inB.set! (tl * nv + x) 0) s x) (s, x) w) succs[tl]! rest
        have hl2 := length_foldl (fun w z => length_push
          (fixHas nv (inB.set! (tl * nv + x) 0) tl z) (tl, z) w) users[x]!
          (succs[tl]!.foldl (fun w s =>
            if fixHas nv (inB.set! (tl * nv + x) 0) s x = true then (s, x) :: w else w) rest)
        have hMx := hM tl x
        apply aloop hc0 hsp hps hus M hM fuel
        · refine ⟨hc, fun q hq hpq => ?_, fun a b hab hab' => ?_, hg⟩
          · rw [hmem2, hmem] at hq
            rcases hq with (hq | ⟨s, hs', hsx, rfl⟩) | ⟨z, hz, hzx, rfl⟩
            · exact hw q hq hpq
            · have hsn : s < nb := (hc0 s x (hc s x hsx)).2
              rintro ⟨ho, -⟩
              rcases ho tl (hps tl s hs' hsn) with h | h | h
              · simp [hn.1] at h
              · simp [hn.2] at h
              · exact ((hs tl x).1 h).2 ⟨rfl, rfl⟩
            · have hz' := ((hus x z hx).1 hz).2
              rintro ⟨-, hcl⟩
              rcases (hcl x hz').1 with h | h
              · simp [hn.1] at h
              · exact ((hs tl x).1 h).2 ⟨rfl, rfl⟩
          · rw [hmem2, hmem]
            rcases hv a b hab hab' with h | ⟨rfl, h, -⟩ | ⟨rfl, h, -⟩
            · exact .inl (.inl h)
            · exact .inl (.inr ⟨a, hsp tl a h, hab, rfl⟩)
            · exact .inr ⟨b, (hus x b hx).2 ⟨(has_iff.1 hab).1, h⟩, hab, rfl⟩
        · omega
      · rw [ite_eq_right hn]
        have hxp : pars[tl]!.contains x = true ∨ defs[tl]!.contains x = true := by
          cases h1 : pars[tl]!.contains x
          · cases h2 : defs[tl]!.contains x
            · simp [h1, h2] at hn
            · exact .inr rfl
          · exact .inl rfl
        apply aloop hc0 hsp hps hus M hM fuel _ _ ⟨hc, hw, fun a b hab hab' => ?_, hg⟩ (by omega)
        rcases hv a b hab hab' with h | ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩
        · exact h
        · rcases hxp with h | h <;> simp_all
        · rcases hxp with h | h <;> simp_all
    · rw [ite_eq_right hp]
      simp only [List.length_cons] at hf
      refine aloop hc0 hsp hps hus M hM fuel _ _ ⟨hi.cand, fun q hq => hi.queued q
        (List.mem_cons_of_mem _ hq), fun a b hab hab' => ?_, hi.great⟩ (by omega)
      rcases List.mem_cons.1 (hi.viol a b hab hab') with e | e
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        exact absurd hab hp
      · exact e

/-- The invariant holds for the initial table and worklist. -/
theorem ainit (hc0 : ∀ tl x, Has nv inB0 tl x → 1 ≤ tl ∧ tl < nb) :
    AInv nv pars defs preds args inB0 inB0 (work0 nb nv pars defs preds args inB0) := by
  have hout : ∀ (inB : ByteArray) tl x, (preds[tl]!.all fun p =>
      pars[p]!.contains x || defs[p]!.contains x || fixHas nv inB p x) = true ↔
      AOut preds pars defs (Has nv inB) tl x := by
    intro inB tl x
    simp only [List.all_eq_true, Bool.or_eq_true, AOut, Has, or_assoc]
  have hclo : ∀ (inB : ByteArray) tl x, ((args x).all fun y =>
      (pars[tl]!.contains y || fixHas nv inB tl y) && !defs[tl]!.contains y) = true ↔
      AClo pars defs args (Has nv inB) tl x := by
    intro inB tl x
    simp only [List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', AClo, Has]
  have hmem : ∀ q, q ∈ work0 nb nv pars defs preds args inB0 ↔ q ∈ ([] : List (Nat × Nat)) ∨
      ∃ tl ∈ List.range' 1 (nb - 1), ∃ x ∈ List.range nv,
        (fixHas nv inB0 tl x = true ∧
          ((preds[tl]!.all fun p => pars[p]!.contains x || defs[p]!.contains x ||
              fixHas nv inB0 p x) &&
            ((args x).all fun y => (pars[tl]!.contains y || fixHas nv inB0 tl y) &&
              !defs[tl]!.contains y)) = false) ∧ q = (tl, x) := by
    intro q
    unfold work0
    apply mem_foldl
    intro w tl q
    apply mem_foldl
    intro w x q
    exact mem_push2 _ _ _ w q
  refine ⟨fun tl x h => h, fun q hq hpq => ?_, fun tl x h hv => ?_, fun S hS tl x h => (hS tl x h).1⟩
  · simp only [hmem, List.not_mem_nil, false_or] at hq
    obtain ⟨tl, -, x, -, ⟨-, hc⟩, rfl⟩ := hq
    intro ⟨ho, hcl⟩
    rw [← hout, ← hclo] at *
    simp_all
  · have hc := hc0 tl x h
    simp only [hmem, List.not_mem_nil, false_or]
    refine ⟨tl, List.mem_range'_1.2 ⟨hc.1, by omega⟩, x, List.mem_range.2 (has_iff.1 h).1,
      ⟨h, ?_⟩, rfl⟩
    cases e : ((preds[tl]!.all fun p => pars[p]!.contains x || defs[p]!.contains x ||
        fixHas nv inB0 p x) &&
      ((args x).all fun y => (pars[tl]!.contains y || fixHas nv inB0 tl y) &&
        !defs[tl]!.contains y))
    · rfl
    · simp only [Bool.and_eq_true] at e
      exact absurd ⟨(hout _ tl x).1 e.1, (hclo _ tl x).1 e.2⟩ hv

/-- `fixLoop`'s final table, from the initial table `inB0`. -/
def denseFinal (nb nv : Nat) (pars defs : Array (Std.HashSet Nat))
    (succs preds users : Array (List Nat)) (args : Nat → List Nat) (inB0 : ByteArray) : ByteArray :=
  fixLoop nv pars defs succs users (fixFuel nb nv succs users (work0 nb nv pars defs preds args inB0))
    inB0 (work0 nb nv pars defs preds args inB0)

/-- The loop ends with an empty worklist. -/
theorem dense_inv (hsz : inB0.size = nb * nv) (hc0 : ∀ tl x, Has nv inB0 tl x → 1 ≤ tl ∧ tl < nb)
    (hsp : ∀ p s : Nat, p ∈ preds[s]! → s ∈ succs[p]!)
    (hps : ∀ p s : Nat, s ∈ succs[p]! → s < nb → p ∈ preds[s]!)
    (hus : ∀ y z : Nat, y < nv → (z ∈ users[y]! ↔ z < nv ∧ y ∈ args z)) :
    AInv nv pars defs preds args inB0 (denseFinal nb nv pars defs succs preds users args inB0) [] := by
  apply aloop hc0 hsp hps hus (succs.foldl (fun m s => max m s.length) 0 +
    users.foldl (fun m u => max m u.length) 0)
  · intro tl x; exact Nat.add_le_add (len_le_max _ _) (len_le_max _ _)
  · exact ainit hc0
  · have h1 : cnt inB0 ≤ nb * nv := by
      have := List.countP_le_length (p := (· != 0)) (l := inB0.data.toList)
      simp only [cnt]
      have hs : inB0.data.toList.length = nb * nv := by simpa using hsz
      omega
    have h2 := Nat.mul_le_mul_right (succs.foldl (fun m s => max m s.length) 0 +
      users.foldl (fun m u => max m u.length) 0 + 1) h1
    dsimp only [fixFuel]
    omega

/-- The final table solves the constraints. -/
theorem dense_sol (hsz : inB0.size = nb * nv) (hc0 : ∀ tl x, Has nv inB0 tl x → 1 ≤ tl ∧ tl < nb)
    (hsp : ∀ p s : Nat, p ∈ preds[s]! → s ∈ succs[p]!)
    (hps : ∀ p s : Nat, s ∈ succs[p]! → s < nb → p ∈ preds[s]!)
    (hus : ∀ y z : Nat, y < nv → (z ∈ users[y]! ↔ z < nv ∧ y ∈ args z)) :
    ASol (Has nv inB0) preds pars defs args
      (Has nv (denseFinal nb nv pars defs succs preds users args inB0)) := by
  have hI := dense_inv (pars := pars) (defs := defs) hsz hc0 hsp hps hus
  intro tl x h
  refine ⟨hI.cand tl x h, ?_⟩
  exact Classical.byContradiction fun hn => by simpa using hI.viol tl x h hn

/-- The final table contains every solution. -/
theorem dense_great (hsz : inB0.size = nb * nv) (hc0 : ∀ tl x, Has nv inB0 tl x → 1 ≤ tl ∧ tl < nb)
    (hsp : ∀ p s : Nat, p ∈ preds[s]! → s ∈ succs[p]!)
    (hps : ∀ p s : Nat, s ∈ succs[p]! → s < nb → p ∈ preds[s]!)
    (hus : ∀ y z : Nat, y < nv → (z ∈ users[y]! ↔ z < nv ∧ y ∈ args z))
    {S : Nat → Nat → Prop} (hS : ASol (Has nv inB0) preds pars defs args S) {tl x : Nat}
    (h : S tl x) : Has nv (denseFinal nb nv pars defs succs preds users args inB0) tl x :=
  (dense_inv (pars := pars) (defs := defs) hsz hc0 hsp hps hus).great S hS tl x h

end Dense

/-! ## Sorted lists and arrays -/

/-- Two strictly increasing lists with the same elements are equal. -/
theorem eq_of_sorted_mem : ∀ {l1 l2 : List Nat}, l1.Pairwise (· < ·) → l2.Pairwise (· < ·) →
    (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 List.mem_cons_self) List.not_mem_nil
  | a :: _, [], _, _, h => absurd ((h a).1 List.mem_cons_self) List.not_mem_nil
  | a :: l1, b :: l2, h1, h2, h => by
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 List.mem_cons_self) with e | e
      · exact e
      rcases List.mem_cons.1 ((h b).2 List.mem_cons_self) with e' | e'
      · exact e'.symm
      have := h2.1 a e
      have := h1.1 b e'
      omega
    subst hab
    rw [eq_of_sorted_mem h1.2 h2.2 fun x => ?_]
    constructor
    · intro hx
      rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with e | e
      · subst e; exact absurd (h1.1 x hx) (Nat.lt_irrefl _)
      · exact e
    · intro hx
      rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with e | e
      · subst e; exact absurd (h2.1 x hx) (Nat.lt_irrefl _)
      · exact e

/-- A strictly increasing list of the elements below `n` with `p` is the filter of the range. -/
theorem eq_filter_range {l : List Nat} (hs : l.Pairwise (· < ·)) {n : Nat} {p : Nat → Bool}
    (hm : ∀ x, x ∈ l ↔ x < n ∧ p x = true) : l = (List.range n).filter p :=
  eq_of_sorted_mem hs ((List.pairwise_lt_range (n := n)).filter p) fun x => by
    rw [hm, List.mem_filter, List.mem_range]

/-- An element of a strictly increasing array is below the later ones. -/
theorem sorted_get {a : Array Nat} (hs : a.toList.Pairwise (· < ·)) {i j : Nat} (hij : i < j)
    (hj : j < a.size) : a[i]! < a[j]! := by
  have hi : i < a.size := Nat.lt_trans hij hj
  rw [bang, bang, Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hj]
  have := List.pairwise_iff_getElem.1 hs i j (by simpa using hi) (by simpa using hj) hij
  simpa using this

/-- Binary search for `x` in `a[lo:hi]`. -/
def bsGo (a : Array Nat) (x : Nat) (lo hi : Nat) : Bool :=
  if h : lo < hi then
    let mid := (lo + hi) / 2
    if a[mid]! < x then bsGo a x (mid + 1) hi
    else if x < a[mid]! then bsGo a x lo mid
    else true
  else false
termination_by hi - lo
decreasing_by all_goals omega

/-- `x` is an element of the sorted array `a` (binary search). -/
def bsMem (a : Array Nat) (x : Nat) : Bool := bsGo a x 0 a.size

theorem bsGo_iff {a : Array Nat} (hs : a.toList.Pairwise (· < ·)) (x : Nat) :
    ∀ n lo hi, hi - lo = n → hi ≤ a.size →
      (bsGo a x lo hi = true ↔ ∃ i, lo ≤ i ∧ i < hi ∧ a[i]! = x) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro lo hi hn hle
  rw [bsGo]
  by_cases h : lo < hi
  · rw [dite_eq_left h]
    dsimp only
    have hm1 : lo ≤ (lo + hi) / 2 := by omega
    have hm2 : (lo + hi) / 2 < hi := by omega
    by_cases h1 : a[(lo + hi) / 2]! < x
    · rw [ite_eq_left h1, ih (hi - ((lo + hi) / 2 + 1)) (by omega) _ _ rfl hle]
      constructor
      · rintro ⟨i, h2, h3, h4⟩; exact ⟨i, by omega, h3, h4⟩
      · rintro ⟨i, h2, h3, h4⟩
        refine ⟨i, Nat.lt_of_not_le fun hc => ?_, h3, h4⟩
        rcases Nat.lt_or_eq_of_le hc with hc | hc
        · have := sorted_get hs hc (by omega); omega
        · subst hc; omega
    · rw [ite_eq_right h1]
      by_cases h2 : x < a[(lo + hi) / 2]!
      · rw [ite_eq_left h2, ih ((lo + hi) / 2 - lo) (by omega) _ _ rfl (by omega)]
        constructor
        · rintro ⟨i, h3, h4, h5⟩; exact ⟨i, h3, by omega, h5⟩
        · rintro ⟨i, h3, h4, h5⟩
          refine ⟨i, h3, Nat.lt_of_not_le fun hc => ?_, h5⟩
          rcases Nat.lt_or_eq_of_le hc with hc | hc
          · have := sorted_get hs hc (by omega); omega
          · subst hc; omega
      · rw [ite_eq_right h2]
        exact ⟨fun _ => ⟨(lo + hi) / 2, hm1, hm2, by omega⟩, fun _ => rfl⟩
  · rw [dite_eq_right h]
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro i h1 h2; omega

/-- Binary search finds exactly the elements. -/
theorem bsMem_iff {a : Array Nat} (hs : a.toList.Pairwise (· < ·)) (x : Nat) :
    bsMem a x = true ↔ x ∈ a.toList := by
  rw [bsMem, bsGo_iff hs x _ 0 a.size rfl (Nat.le_refl _)]
  constructor
  · rintro ⟨i, -, hi, rfl⟩
    rw [bang, Array.getElem?_eq_getElem hi, Option.getD_some]
    exact Array.getElem_mem_toList hi
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
    refine ⟨i, Nat.zero_le _, by simpa using hi, ?_⟩
    have hi' : i < a.size := by simpa using hi
    rw [bang, Array.getElem?_eq_getElem hi', Option.getD_some, Array.getElem_toList]

/-- Push `z` on the reversed sorted prefix `acc` unless it is its head. -/
def pushU (z : Nat) : List Nat → List Nat
  | a :: acc => if a < z then z :: a :: acc else a :: acc
  | [] => [z]

/-- The sorted union of two sorted lists without repetitions (tail-recursive; `acc` holds the
merged prefix reversed). -/
def mergeUA : List Nat → List Nat → List Nat → List Nat
  | [], [], acc => acc.reverse
  | x :: xs, [], acc => mergeUA xs [] (pushU x acc)
  | [], y :: ys, acc => mergeUA [] ys (pushU y acc)
  | x :: xs, y :: ys, acc =>
    if x ≤ y then mergeUA xs (y :: ys) (pushU x acc) else mergeUA (x :: xs) ys (pushU y acc)
termination_by xs ys => xs.length + ys.length

/-- The sorted union of two sorted lists, without repetitions. -/
def mergeU (xs ys : List Nat) : List Nat := mergeUA xs ys []

/-- The invariant of `mergeUA`'s accumulator. -/
def AccOk (acc rest : List Nat) : Prop :=
  acc.Pairwise (· > ·) ∧ ∀ a ∈ acc, ∀ b ∈ rest, a ≤ b

theorem pushU_ok {z : Nat} {acc rest : List Nat} (h : AccOk acc (z :: rest))
    (hr : ∀ b ∈ rest, z ≤ b) :
    AccOk (pushU z acc) rest ∧ ∀ y, y ∈ pushU z acc ↔ y = z ∨ y ∈ acc := by
  obtain ⟨h1, h2⟩ := h
  cases acc with
  | nil =>
    simp only [pushU]
    exact ⟨⟨List.pairwise_singleton _ _, by simpa using hr⟩, by simp⟩
  | cons a acc =>
    have haz : a ≤ z := h2 a List.mem_cons_self z List.mem_cons_self
    by_cases e : a < z
    · rw [show pushU z (a :: acc) = z :: a :: acc by simp [pushU, e]]
      refine ⟨⟨List.pairwise_cons.2 ⟨fun y hy => ?_, h1⟩, fun y hy b hb => ?_⟩, fun y => by simp⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact e
        · exact Nat.lt_trans (List.pairwise_cons.1 h1 |>.1 y hy) e
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact hr b hb
        · exact h2 y hy b (List.mem_cons_of_mem _ hb)
    · rw [show pushU z (a :: acc) = a :: acc by simp [pushU, e]]
      have : a = z := by omega
      subst this
      exact ⟨⟨h1, fun y hy b hb => h2 y hy b (List.mem_cons_of_mem _ hb)⟩, fun y => by simp⟩

theorem mergeUA_spec : ∀ (xs ys acc : List Nat), xs.Pairwise (· ≤ ·) → ys.Pairwise (· ≤ ·) →
    AccOk acc (xs ++ ys) →
    (mergeUA xs ys acc).Pairwise (· < ·) ∧
      ∀ y, y ∈ mergeUA xs ys acc ↔ y ∈ acc ∨ y ∈ xs ∨ y ∈ ys
  | [], [], acc, _, _, h => by
    rw [mergeUA]
    refine ⟨List.pairwise_reverse.2 ?_, fun y => by simp⟩
    exact h.1.imp fun h => h
  | x :: xs, [], acc, hx, _, h => by
    rw [mergeUA]
    have hx' := List.pairwise_cons.1 hx
    obtain ⟨hp, hm⟩ := pushU_ok (rest := xs ++ []) (by simpa using h) (by simpa using hx'.1)
    obtain ⟨r1, r2⟩ := mergeUA_spec xs [] (pushU x acc) hx'.2 List.Pairwise.nil hp
    refine ⟨r1, fun y => ?_⟩
    rw [r2, hm]; simp [or_assoc, or_left_comm]
  | [], y :: ys, acc, _, hy, h => by
    rw [mergeUA]
    have hy' := List.pairwise_cons.1 hy
    obtain ⟨hp, hm⟩ := pushU_ok (rest := [] ++ ys) (by simpa using h) (by simpa using hy'.1)
    obtain ⟨r1, r2⟩ := mergeUA_spec [] ys (pushU y acc) List.Pairwise.nil hy'.2 hp
    refine ⟨r1, fun z => ?_⟩
    rw [r2, hm]; simp [or_assoc, or_left_comm]
  | x :: xs, y :: ys, acc, hx, hy, h => by
    rw [mergeUA]
    have hx' := List.pairwise_cons.1 hx
    have hy' := List.pairwise_cons.1 hy
    by_cases e : x ≤ y
    · rw [ite_eq_left e]
      obtain ⟨hp, hm⟩ := pushU_ok (z := x) (rest := xs ++ y :: ys) (by simpa using h) (by
        intro b hb
        rcases List.mem_append.1 hb with hb | hb
        · exact hx'.1 b hb
        · rcases List.mem_cons.1 hb with rfl | hb
          · exact e
          · exact Nat.le_trans e (hy'.1 b hb))
      obtain ⟨r1, r2⟩ := mergeUA_spec xs (y :: ys) (pushU x acc) hx'.2 hy hp
      refine ⟨r1, fun z => ?_⟩
      rw [r2, hm]; simp [or_assoc, or_left_comm]
    · rw [ite_eq_right e]
      have hp0 : AccOk acc (y :: (x :: xs ++ ys)) := by
        refine ⟨h.1, fun a ha b hb => h.2 a ha b ?_⟩
        simp only [List.mem_cons, List.mem_append] at hb ⊢
        rcases hb with hb | (hb | hb) | hb <;> simp_all
      obtain ⟨hp, hm⟩ := pushU_ok (z := y) (rest := x :: xs ++ ys) hp0 (by
        intro b hb
        simp only [List.cons_append, List.mem_cons, List.mem_append] at hb
        rcases hb with rfl | hb | hb
        · omega
        · exact Nat.le_trans (by omega) (hx'.1 b hb)
        · exact hy'.1 b hb)
      obtain ⟨r1, r2⟩ := mergeUA_spec (x :: xs) ys (pushU y acc) hx hy'.2 (by
        refine ⟨hp.1, fun a ha b hb => hp.2 a ha b ?_⟩
        simpa using hb)
      refine ⟨r1, fun z => ?_⟩
      rw [r2, hm]; simp [or_assoc, or_left_comm]
termination_by xs ys => xs.length + ys.length

/-- `mergeU` is strictly increasing with the elements of both lists. -/
theorem mergeU_spec {xs ys : List Nat} (hx : xs.Pairwise (· ≤ ·)) (hy : ys.Pairwise (· ≤ ·)) :
    (mergeU xs ys).Pairwise (· < ·) ∧ ∀ y, y ∈ mergeU xs ys ↔ y ∈ xs ∨ y ∈ ys := by
  obtain ⟨h1, h2⟩ := mergeUA_spec xs ys [] hx hy ⟨List.Pairwise.nil, by simp⟩
  exact ⟨h1, fun y => by rw [mergeU, h2]; simp⟩

end Fix

open Fix

/-! ## The sparse computation -/

/-- `x` is available at `tl`'s entry in the state `D`: in `tl`'s sorted array once computed,
else when it is a candidate. -/
def fixSpHas (cand : Nat → Nat → Bool) (D : Array (Option (Array Nat))) (tl x : Nat) : Bool :=
  match D.getD tl none with
  | some a => bsMem a x
  | none => cand tl x

/-- The first predecessor of `tl` already computed, with its array. -/
def fixSpBp (preds : Array (List Nat)) (D : Array (Option (Array Nat))) (tl : Nat) :
    Option (Nat × Array Nat) :=
  preds[tl]!.findSome? fun p => (D.getD p none).map fun a => (p, a)

/-- The values available at the end of that predecessor (its parameters and results `passS`,
sorted, and its entry array), or all values when no predecessor is computed. -/
def fixSpBase (nv : Nat) (passS : Array (List Nat)) : Option (Nat × Array Nat) → List Nat
  | some (p, a) => mergeU passS[p]! a.toList
  | none => List.range nv

/-- The candidates of `tl` available at the end of every predecessor, in increasing order. -/
def fixSpB (nv : Nat) (cand : Nat → Nat → Bool) (preds : Array (List Nat))
    (pars defs : Array (Std.HashSet Nat)) (passS : Array (List Nat))
    (D : Array (Option (Array Nat))) (tl : Nat) : List Nat :=
  let ps := preds[tl]!
  let bp := fixSpBp preds D tl
  let ct := cand tl
  (fixSpBase nv passS bp).filter fun x => ct x && ps.all fun q =>
    (match bp with
      | some (p, _) => q == p
      | none => false) ||
    pars[q]!.contains x || defs[q]!.contains x || fixSpHas cand D q x

/-- Those whose operands are available at `tl`'s entry (in `ref`: `tl`'s array, or the
candidates `B` before `tl` is computed) and not results of `tl`. -/
def fixSpN (pars defs : Array (Std.HashSet Nat)) (args : Nat → List Nat)
    (old : Option (Array Nat)) (B : List Nat) (tl : Nat) : Array Nat :=
  let pt := pars[tl]!
  let dt := defs[tl]!
  let ref := match old with
    | some a => a
    | none => B.toArray
  (B.filter fun x => (args x).all fun y => (pt.contains y || bsMem ref y) && !dt.contains y).toArray

/-- One block: its array recomputed from the state, and whether it changed. -/
def fixSpStep (nv : Nat) (cand : Nat → Nat → Bool) (preds : Array (List Nat))
    (pars defs : Array (Std.HashSet Nat)) (passS : Array (List Nat)) (args : Nat → List Nat)
    (st : Array (Option (Array Nat)) × Bool) (tl : Nat) : Array (Option (Array Nat)) × Bool :=
  match st with
  | (D, ch) =>
    let old := D.getD tl none
    let N := fixSpN pars defs args old (fixSpB nv cand preds pars defs passS D tl) tl
    let ch := ch || match old with
      | some a => a != N
      | none => true
    -- `D` is not shared here (the state is matched, not projected): `set!` updates in place
    (D.set! tl (some N), ch)

/-- A pass over the blocks `L`. -/
def fixSpPass (nv : Nat) (cand : Nat → Nat → Bool) (preds : Array (List Nat))
    (pars defs : Array (Std.HashSet Nat)) (passS : Array (List Nat)) (args : Nat → List Nat)
    (L : List Nat) (D : Array (Option (Array Nat))) : Array (Option (Array Nat)) × Bool :=
  L.foldl (fixSpStep nv cand preds pars defs passS args) (D, false)

/-- Passes over all blocks until one changes nothing (at most `fuel + 1` passes). -/
def fixSpIter (nb nv : Nat) (cand : Nat → Nat → Bool) (preds : Array (List Nat))
    (pars defs : Array (Std.HashSet Nat)) (passS : Array (List Nat)) (args : Nat → List Nat) :
    Nat → Array (Option (Array Nat)) → Option (Array (Option (Array Nat)))
  | fuel, D =>
    let r := fixSpPass nv cand preds pars defs passS args (List.range nb) D
    if r.2 then
      match fuel with
      | 0 => none
      | fuel + 1 => fixSpIter nb nv cand preds pars defs passS args fuel r.1
    else some r.1

/-- **The sparse computation**: a first pass over the blocks in the order `order` (reverse
postorder: `rpo`), then passes over all blocks until one changes nothing; `none` when `fuel + 1`
passes do not suffice. -/
def fixSparse (nb nv : Nat) (cand : Nat → Nat → Bool) (preds : Array (List Nat))
    (pars defs : Array (Std.HashSet Nat)) (passS : Array (List Nat)) (args : Nat → List Nat)
    (order : List Nat) (fuel : Nat) : Option (Array (Option (Array Nat))) :=
  fixSpIter nb nv cand preds pars defs passS args fuel
    (fixSpPass nv cand preds pars defs passS args order (Array.replicate nb none)).1

/-- The depth-first walk of `rpo`: `stack` holds the blocks being visited with their successors
still to visit; a block is prepended to `post` when its successors are done. -/
def rpoGo (nb : Nat) (succs : Array (List Nat)) :
    Nat → Array Bool → List (Nat × List Nat) → List Nat → List Nat
  | 0, _, _, post => post
  | _ + 1, _, [], post => post
  | fuel + 1, seen, (b, []) :: rest, post => rpoGo nb succs fuel seen rest (b :: post)
  | fuel + 1, seen, (b, s :: ss) :: rest, post =>
    if s < nb && !seen[s]! then
      rpoGo nb succs fuel (seen.set! s true) ((s, succs[s]!) :: (b, ss) :: rest) post
    else rpoGo nb succs fuel seen ((b, ss) :: rest) post

/-- The blocks reachable from the entry in reverse postorder (each block after its predecessors,
back edges aside): the order of `fixSparse`'s first pass. Only an order: any list gives the same
result. -/
def rpo (nb : Nat) (succs : Array (List Nat)) : List Nat :=
  if nb = 0 then [] else
    rpoGo nb succs (2 * succs.foldl (fun n l => n + l.length) 0 + 2 * nb + 2)
      ((Array.replicate nb false).set! 0 true) [(0, succs[0]!)] []

namespace Fix

/-! ## The sparse computation is the greatest solution -/

section Sparse

variable {nb nv : Nat} {cand : Nat → Nat → Bool} {preds : Array (List Nat)}
  {pars defs : Array (Std.HashSet Nat)} {passS : Array (List Nat)} {args : Nat → List Nat}

/-- The state has `nb` blocks and its arrays are strictly increasing. -/
def SpOk (nb : Nat) (D : Array (Option (Array Nat))) : Prop :=
  D.size = nb ∧ ∀ tl a, D.getD tl none = some a → a.toList.Pairwise (· < ·)

/-- Every solution is below the state. -/
def SpInv (cand : Nat → Nat → Bool) (preds : Array (List Nat)) (pars defs : Array (Std.HashSet Nat))
    (args : Nat → List Nat) (D : Array (Option (Array Nat))) : Prop :=
  ∀ S, ASol (fun tl x => cand tl x = true) preds pars defs args S → ∀ tl x, S tl x →
    fixSpHas cand D tl x = true

/-- The facts about the arrays the sparse computation reads. -/
structure SpHyp (nb nv : Nat) (cand : Nat → Nat → Bool) (pars defs : Array (Std.HashSet Nat))
    (passS : Array (List Nat)) : Prop where
  cand : ∀ tl x, cand tl x = true → tl < nb ∧ x < nv
  passS : ∀ p : Nat, (passS[p]!).Pairwise (· ≤ ·) ∧
    ∀ x, x ∈ passS[p]! ↔ pars[p]!.contains x = true ∨ defs[p]!.contains x = true

theorem fixSpHas_some {D : Array (Option (Array Nat))} {tl : Nat} {a : Array Nat}
    (h : D.getD tl none = some a) (x : Nat) : fixSpHas cand D tl x = bsMem a x := by
  simp [fixSpHas, h]

theorem bp_spec {D : Array (Option (Array Nat))} {tl p : Nat} {a : Array Nat}
    (h : fixSpBp preds D tl = some (p, a)) : p ∈ preds[tl]! ∧ D.getD p none = some a := by
  obtain ⟨q, hq, hq'⟩ := List.exists_of_findSome?_eq_some h
  cases e : D.getD q none with
  | none => simp [e] at hq'
  | some b =>
    simp only [e, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hq'
    obtain ⟨rfl, rfl⟩ := hq'
    exact ⟨hq, e⟩

theorem base_sorted (hH : SpHyp nb nv cand pars defs passS) {D : Array (Option (Array Nat))}
    (hD : SpOk nb D) (bp : Option (Nat × Array Nat))
    (hbp : ∀ p a, bp = some (p, a) → D.getD p none = some a) :
    (fixSpBase nv passS bp).Pairwise (· < ·) := by
  cases bp with
  | none => exact List.pairwise_lt_range
  | some pa =>
    obtain ⟨p, a⟩ := pa
    exact (mergeU_spec (hH.passS p).1
      ((hD.2 p a (hbp p a rfl)).imp Nat.le_of_lt)).1

theorem B_sorted (hH : SpHyp nb nv cand pars defs passS) {D : Array (Option (Array Nat))}
    (hD : SpOk nb D) (tl : Nat) :
    (fixSpB nv cand preds pars defs passS D tl).Pairwise (· < ·) :=
  (base_sorted hH hD _ fun _ _ h => (bp_spec h).2).filter _

/-- An element of `B` is a candidate available at the end of every predecessor (in the state). -/
theorem mem_B (hH : SpHyp nb nv cand pars defs passS) {D : Array (Option (Array Nat))}
    (hD : SpOk nb D) {tl x : Nat} (h : x ∈ fixSpB nv cand preds pars defs passS D tl) :
    cand tl x = true ∧ ∀ q ∈ preds[tl]!, pars[q]!.contains x = true ∨
      defs[q]!.contains x = true ∨ fixSpHas cand D q x = true := by
  unfold fixSpB at h
  rw [List.mem_filter] at h
  obtain ⟨hb, hx⟩ := h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hx
  refine ⟨hx.1, fun q hq => ?_⟩
  rcases hx.2 q hq with ((h | h) | h) | h
  · cases e : fixSpBp preds D tl with
    | none => simp [e] at h
    | some pa =>
      obtain ⟨p, a⟩ := pa
      simp only [e, beq_iff_eq] at h
      subst h
      obtain ⟨-, ha⟩ := bp_spec e
      rw [e, fixSpBase] at hb
      rcases ((mergeU_spec (hH.passS q).1 ((hD.2 q a ha).imp Nat.le_of_lt)).2 x).1 hb with h | h
      · rcases ((hH.passS q).2 x).1 h with h | h
        · exact .inl h
        · exact .inr (.inl h)
      · exact .inr (.inr (by rw [fixSpHas_some ha, bsMem_iff (hD.2 q a ha)]; exact h))
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr h)

/-- Every solution below the state is in `B`. -/
theorem sol_mem_B (hH : SpHyp nb nv cand pars defs passS) {D : Array (Option (Array Nat))}
    (hD : SpOk nb D) {S : Nat → Nat → Prop}
    (hS : ASol (fun tl x => cand tl x = true) preds pars defs args S)
    (hSD : ∀ tl x, S tl x → fixSpHas cand D tl x = true) {tl x : Nat} (h : S tl x) :
    x ∈ fixSpB nv cand preds pars defs passS D tl := by
  obtain ⟨hc, ho, -⟩ := hS tl x h
  unfold fixSpB
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · cases e : fixSpBp preds D tl with
    | none => exact List.mem_range.2 (hH.cand tl x hc).2
    | some pa =>
      obtain ⟨p, a⟩ := pa
      obtain ⟨hp, ha⟩ := bp_spec e
      rw [fixSpBase]
      refine ((mergeU_spec (hH.passS p).1 ((hD.2 p a ha).imp Nat.le_of_lt)).2 x).2 ?_
      rcases ho p hp with h' | h' | h'
      · exact .inl (((hH.passS p).2 x).2 (.inl h'))
      · exact .inl (((hH.passS p).2 x).2 (.inr h'))
      · have := hSD p x h'
        rw [fixSpHas_some ha, bsMem_iff (hD.2 p a ha)] at this
        exact .inr this
  · simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true]
    refine ⟨hc, fun q hq => ?_⟩
    rcases ho q hq with h' | h' | h'
    · exact .inl (.inl (.inr h'))
    · exact .inl (.inr h')
    · exact .inr (hSD q x h')

theorem mem_N {old : Option (Array Nat)} {B : List Nat} {tl x : Nat} :
    x ∈ (fixSpN pars defs args old B tl).toList ↔ x ∈ B ∧ ∀ y ∈ args x,
      (pars[tl]!.contains y = true ∨ bsMem (match old with
        | some a => a
        | none => B.toArray) y = true) ∧ defs[tl]!.contains y = false := by
  unfold fixSpN
  simp only [List.mem_filter, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true']

theorem N_sorted {old : Option (Array Nat)} {B : List Nat} (hB : B.Pairwise (· < ·)) (tl : Nat) :
    (fixSpN pars defs args old B tl).toList.Pairwise (· < ·) := by
  unfold fixSpN
  exact hB.filter _

theorem getD_set {D : Array (Option (Array Nat))} {tl t : Nat} {v : Option (Array Nat)} :
    (D.set! tl v).getD t none = if tl = t ∧ t < D.size then v else D.getD t none := by
  simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  by_cases e : tl = t
  · subst e
    by_cases h : tl < D.size
    · simp [h]
    · simp [h]
  · simp [e]

/-- A step keeps the state well formed. -/
theorem step_ok (hH : SpHyp nb nv cand pars defs passS) {D : Array (Option (Array Nat))}
    (hD : SpOk nb D) (b : Bool) (tl : Nat) :
    SpOk nb (fixSpStep nv cand preds pars defs passS args (D, b) tl).1 := by
  refine ⟨by simp [fixSpStep, hD.1], fun t a h => ?_⟩
  simp only [fixSpStep, getD_set] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact N_sorted (B_sorted hH hD tl) tl
  · exact hD.2 t a h

/-- A step keeps every solution below the state. -/
theorem step_inv (hH : SpHyp nb nv cand pars defs passS) {D : Array (Option (Array Nat))}
    (hD : SpOk nb D) (hI : SpInv cand preds pars defs args D) (b : Bool) (tl : Nat) :
    SpInv cand preds pars defs args (fixSpStep nv cand preds pars defs passS args (D, b) tl).1 := by
  intro S hS t x hx
  have hSD := hI S hS
  have hok := step_ok (preds := preds) (args := args) hH hD b tl
  by_cases e : tl = t ∧ t < D.size
  · obtain ⟨rfl, ht⟩ := e
    have hg : (fixSpStep nv cand preds pars defs passS args (D, b) tl).1.getD tl none =
        some (fixSpN pars defs args (D.getD tl none) (fixSpB nv cand preds pars defs passS D tl) tl) := by
      simp [fixSpStep, ht]
    rw [fixSpHas_some hg, bsMem_iff (hok.2 _ _ hg), mem_N]
    refine ⟨sol_mem_B hH hD hS hSD hx, fun y hy => ?_⟩
    obtain ⟨h1, h2⟩ := (hS tl x hx).2.2 y hy
    refine ⟨?_, h2⟩
    rcases h1 with h1 | h1
    · exact .inl h1
    · refine .inr ?_
      cases e : D.getD tl none with
      | some a =>
        have := hSD tl y h1
        rwa [fixSpHas_some e] at this
      | none =>
        simp only
        rw [bsMem_iff (by simpa using B_sorted hH hD tl)]
        simpa using sol_mem_B hH hD hS hSD h1
  · have hg : (fixSpStep nv cand preds pars defs passS args (D, b) tl).1.getD t none =
        D.getD t none := by
      unfold fixSpStep
      dsimp only
      rw [getD_set, ite_eq_right e]
    have := hSD t x hx
    unfold fixSpHas at this ⊢
    rw [hg]; exact this

/-- A pass keeps the state well formed and every solution below it. -/
theorem pass_inv (hH : SpHyp nb nv cand pars defs passS) :
    ∀ (L : List Nat) (D : Array (Option (Array Nat))) (b : Bool), SpOk nb D →
      SpInv cand preds pars defs args D →
      SpOk nb (L.foldl (fixSpStep nv cand preds pars defs passS args) (D, b)).1 ∧
      SpInv cand preds pars defs args (L.foldl (fixSpStep nv cand preds pars defs passS args) (D, b)).1
  | [], D, b, hD, hI => ⟨hD, hI⟩
  | tl :: L, D, b, hD, hI => by
    rw [List.foldl_cons]
    have e : fixSpStep nv cand preds pars defs passS args (D, b) tl =
        ((fixSpStep nv cand preds pars defs passS args (D, b) tl).1,
          (fixSpStep nv cand preds pars defs passS args (D, b) tl).2) := rfl
    rw [e]
    exact pass_inv hH L _ _ (step_ok hH hD b tl) (step_inv hH hD hI b tl)

theorem set_self {D : Array (Option (Array Nat))} {tl : Nat} {v : Option (Array Nat)}
    (h : D.getD tl none = v) : D.set! tl v = D := by
  apply Array.ext_getElem?
  intro i
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases e : tl = i
  · subst e
    by_cases ht : tl < D.size
    · simp [ht, ← h, Array.getD_eq_getD_getElem?]
    · simp [ht]
  · simp [e]

/-- A pass whose flag stays down changes nothing, and each of its blocks had its array equal to
its recomputation. -/
theorem pass_same : ∀ (L : List Nat) (D : Array (Option (Array Nat))) (b : Bool),
    (L.foldl (fixSpStep nv cand preds pars defs passS args) (D, b)).2 = false →
      b = false ∧ (L.foldl (fixSpStep nv cand preds pars defs passS args) (D, b)).1 = D ∧
      ∀ tl ∈ L, ∃ a, D.getD tl none = some a ∧
        fixSpN pars defs args (some a) (fixSpB nv cand preds pars defs passS D tl) tl = a
  | [], D, b, h => ⟨h, rfl, by simp⟩
  | tl :: L, D, b, h => by
    rw [List.foldl_cons] at h ⊢
    have e : fixSpStep nv cand preds pars defs passS args (D, b) tl =
        ((fixSpStep nv cand preds pars defs passS args (D, b) tl).1,
          (fixSpStep nv cand preds pars defs passS args (D, b) tl).2) := rfl
    rw [e] at h ⊢
    obtain ⟨h1, h2, h3⟩ := pass_same L _ _ h
    simp only [fixSpStep, Bool.or_eq_false_iff] at h1
    obtain ⟨hb, hc⟩ := h1
    cases eo : D.getD tl none with
    | none => simp [eo] at hc
    | some a =>
      simp only [eo, bne_eq_false_iff_eq] at hc
      have hD : (fixSpStep nv cand preds pars defs passS args (D, b) tl).1 = D := by
        simp only [fixSpStep, eo, ← hc]
        exact set_self eo
      rw [hD] at h2 h3 ⊢
      refine ⟨hb, h2, fun t ht => ?_⟩
      rcases List.mem_cons.1 ht with rfl | ht
      · exact ⟨a, eo, hc.symm⟩
      · exact h3 t ht

/-- After a pass over all blocks that changes nothing, the state is a solution. -/
theorem same_sol (hH : SpHyp nb nv cand pars defs passS) {D : Array (Option (Array Nat))}
    (hD : SpOk nb D)
    (h : ∀ tl ∈ List.range nb, ∃ a, D.getD tl none = some a ∧
      fixSpN pars defs args (some a) (fixSpB nv cand preds pars defs passS D tl) tl = a) :
    ASol (fun tl x => cand tl x = true) preds pars defs args
      (fun tl x => fixSpHas cand D tl x = true) := by
  intro tl x hx
  by_cases ht : tl < nb
  · obtain ⟨a, ha, hN⟩ := h tl (List.mem_range.2 ht)
    have hx' := hx
    rw [fixSpHas_some ha, bsMem_iff (hD.2 tl a ha), ← hN, mem_N] at hx'
    obtain ⟨hB, hcl⟩ := hx'
    obtain ⟨hc, ho⟩ := mem_B hH hD hB
    refine ⟨hc, ho, fun y hy => ?_⟩
    obtain ⟨h1, h2⟩ := hcl y hy
    refine ⟨?_, h2⟩
    rcases h1 with h1 | h1
    · exact .inl h1
    · exact .inr (by show fixSpHas cand D tl y = true; rw [fixSpHas_some ha]; exact h1)
  · have hsz : D.size ≤ tl := by rw [hD.1]; omega
    have hn : D.getD tl none = none := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hsz]
    unfold fixSpHas at hx
    rw [hn] at hx
    exact absurd (hH.cand tl x hx).1 ht

/-- The passes until one changes nothing: the result is well formed, has every solution below
it, is a solution, and every block is computed. -/
theorem iter_spec (hH : SpHyp nb nv cand pars defs passS) :
    ∀ (fuel : Nat) (D D' : Array (Option (Array Nat))), SpOk nb D →
      SpInv cand preds pars defs args D →
      fixSpIter nb nv cand preds pars defs passS args fuel D = some D' →
      SpOk nb D' ∧ SpInv cand preds pars defs args D' ∧
      ASol (fun tl x => cand tl x = true) preds pars defs args
        (fun tl x => fixSpHas cand D' tl x = true) ∧
      ∀ tl < nb, ∃ a, D'.getD tl none = some a
  | fuel, D, D', hD, hI, h => by
    unfold fixSpIter at h
    dsimp only at h
    have hP := pass_inv (args := args) (preds := preds) hH (List.range nb) D false hD hI
    split at h
    · rename_i hc
      cases fuel with
      | zero => simp at h
      | succ fuel =>
        exact iter_spec hH fuel _ D' hP.1 hP.2 h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      have hc' : (fixSpPass nv cand preds pars defs passS args (List.range nb) D).2 = false := by
        simpa using hc
      obtain ⟨-, h2, h3⟩ := pass_same (List.range nb) D false hc'
      unfold fixSpPass
      rw [h2]
      refine ⟨hD, hI, same_sol hH hD h3, fun tl ht => ?_⟩
      obtain ⟨a, ha, -⟩ := h3 tl (List.mem_range.2 ht)
      exact ⟨a, ha⟩

/-- **The sparse computation**: when it ends, its arrays hold exactly the values of every
solution's union, i.e. of the greatest solution: every solution is below it and it is one. -/
theorem fixSparse_spec (hH : SpHyp nb nv cand pars defs passS) {order : List Nat} {fuel : Nat}
    {D : Array (Option (Array Nat))}
    (h : fixSparse nb nv cand preds pars defs passS args order fuel = some D) :
    SpOk nb D ∧ SpInv cand preds pars defs args D ∧
      ASol (fun tl x => cand tl x = true) preds pars defs args
        (fun tl x => fixSpHas cand D tl x = true) ∧
      ∀ tl < nb, ∃ a, D.getD tl none = some a := by
  have h0 : SpOk nb (Array.replicate nb none) :=
    ⟨by simp, fun tl a h => by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at h
      split at h <;> simp at h⟩
  have i0 : SpInv cand preds pars defs args (Array.replicate nb none) := by
    intro S hS tl x hx
    have : (Array.replicate nb (none : Option (Array Nat))).getD tl none = none := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    unfold fixSpHas
    rw [this]
    exact (hS tl x hx).1
  have hP := pass_inv (args := args) (preds := preds) hH order _ false h0 i0
  exact iter_spec hH fuel _ D hP.1 hP.2 h

end Sparse

/-! ## The arrays `inFix` builds -/

/-- `inFix`'s predecessor lists, from its successor lists. -/
def predsOf (nb : Nat) (succs : Array (List Nat)) : Array (List Nat) :=
  succs.zipIdx.foldl (fun ps (ss, bi) => ss.foldl (fun ps s => ps.modify s (bi :: ·)) ps)
    (Array.replicate nb [])

/-- `inFix`'s users after the values below `n`: the values whose definition reads `y`. -/
def usersUpTo (nv : Nat) (args : Nat → List Nat) (n : Nat) : Array (List Nat) :=
  (List.range n).foldl (fun us z => (args z).foldl (fun us y => us.modify y (z :: ·)) us)
    (Array.replicate nv [])

/-- `inFix`'s initial table from the candidate test `g`. -/
def inB0Of (nb nv : Nat) (g : Nat → Nat → Bool) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := nb * nv) fun i =>
    let tl := i.1 / nv
    let x := i.1 % nv
    if g tl x then 1 else 0)

theorem predsOf_spec (nb : Nat) (succs : Array (List Nat)) :
    (predsOf nb succs).size = nb ∧ ∀ t q, q ∈ (predsOf nb succs)[t]?.getD [] ↔
      q < succs.size ∧ t ∈ succs[q]! ∧ t < nb := by
  have h : (predsOf nb succs).size = nb ∧ ∀ t q, q ∈ (predsOf nb succs)[t]?.getD [] ↔
      q < succs.zipIdx.size ∧ t ∈ succs[q]! ∧ t < nb := by
    unfold predsOf
    apply Array.foldl_induction (fun n (ps : Array (List Nat)) => ps.size = nb ∧
      ∀ t q, q ∈ ps[t]?.getD [] ↔ q < n ∧ t ∈ succs[q]! ∧ t < nb)
    · refine ⟨by simp, fun t q => ?_⟩
      simp only [Array.getElem?_replicate]
      split <;> simp
    · intro i ps ⟨hs, ih⟩
      simp only [Fin.getElem_fin, Array.getElem_zipIdx, Nat.zero_add]
      obtain ⟨h1, h2⟩ := modify_fold i.1 succs[i.1] ps
      refine ⟨by rw [h1, hs], fun t q => ?_⟩
      have hi : i.1 < succs.size := by simpa using i.2
      have e : succs[i.1] = succs[i.1]! := by
        rw [bang, Array.getElem?_eq_getElem hi, Option.getD_some]
      rw [h2, ih, hs, e]
      constructor
      · rintro (⟨h3, h4, h5⟩ | ⟨rfl, h4, h5⟩)
        · exact ⟨by omega, h4, h5⟩
        · exact ⟨by omega, h4, h5⟩
      · rintro ⟨h3, h4, h5⟩
        rcases Nat.lt_or_ge q i.1 with h6 | h6
        · exact .inl ⟨h6, h4, h5⟩
        · have : q = i.1 := by omega
          subst this
          exact .inr ⟨rfl, h4, h5⟩
  exact ⟨h.1, fun t q => by rw [h.2]; simp⟩

theorem usersUpTo_spec (nv : Nat) (args : Nat → List Nat) : ∀ n, (usersUpTo nv args n).size = nv ∧
    ∀ y < nv, ∀ z, z ∈ (usersUpTo nv args n)[y]?.getD [] ↔ z < n ∧ y ∈ args z
  | 0 => ⟨by simp [usersUpTo], fun y hy z => by simp [usersUpTo, hy]⟩
  | n + 1 => by
    obtain ⟨hs, ih⟩ := usersUpTo_spec nv args n
    have e : usersUpTo nv args (n + 1) =
        (args n).foldl (fun us y => us.modify y (n :: ·)) (usersUpTo nv args n) := by
      simp only [usersUpTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨h1, h2⟩ := modify_fold n (args n) (usersUpTo nv args n)
    rw [e]
    refine ⟨by rw [h1, hs], fun y hy z => ?_⟩
    rw [h2, ih y hy, hs]
    constructor
    · rintro (⟨h3, h4⟩ | ⟨rfl, h4, -⟩)
      · exact ⟨by omega, h4⟩
      · exact ⟨by omega, h4⟩
    · rintro ⟨h3, h4⟩
      rcases Nat.lt_or_ge z n with h5 | h5
      · exact .inl ⟨h5, h4⟩
      · have : z = n := by omega
        subst this
        exact .inr ⟨rfl, h4, hy⟩

/-- The initial table holds the pairs of the blocks and values with `g`. -/
theorem has_inB0Of {nb nv : Nat} (g : Nat → Nat → Bool) (tl x : Nat) :
    Has nv (inB0Of nb nv g) tl x ↔ tl < nb ∧ x < nv ∧ g tl x = true := by
  unfold Has
  rw [has_iff]
  by_cases hx : x < nv
  · by_cases ht : tl < nb
    · have hi : tl * nv + x < nb * nv := idx_lt ht hx
      have hn : 0 < nv := by omega
      have h1 : (tl * nv + x) / nv = tl := by
        rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hx, Nat.add_zero]
      have h2 : (tl * nv + x) % nv = x := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]
      simp only [inB0Of, Array.getElem?_ofFn, hi, dite_true, Option.getD_some, h1, h2]
      cases g tl x <;> simp [hx, ht]
    · have hi : ¬ tl * nv + x < nb * nv := by
        have := Nat.mul_le_mul_right nv (Nat.le_of_not_lt ht)
        omega
      simp [inB0Of, hi, ht]
  · simp [hx]

/-- **The sparse computation is `inFix`'s result**: when `fixSparse` ends, its arrays, read as
lists, are those of the dense table `fixLoop` computes from the candidates `g` (whose test the
sparse computation runs as `cand`). -/
theorem fixSparse_eq {nb nv : Nat} {g cand : Nat → Nat → Bool}
    {pars defs : Array (Std.HashSet Nat)} {succs passS : Array (List Nat)}
    {args args' : Nat → List Nat} {order : List Nat} {fuel : Nat}
    {D : Array (Option (Array Nat))}
    (hg1 : ∀ tl x, g tl x = true → 1 ≤ tl)
    (hcand : ∀ tl x, cand tl x = true ↔ tl < nb ∧ x < nv ∧ g tl x = true)
    (hpS : ∀ p : Nat, (passS[p]!).Pairwise (· ≤ ·) ∧
      ∀ x, x ∈ passS[p]! ↔ pars[p]!.contains x = true ∨ defs[p]!.contains x = true)
    (hargs : ∀ x, x < nv → args' x = args x)
    (h : fixSparse nb nv cand (predsOf nb succs) pars defs passS args' order fuel = some D) :
    D.map (fun o => (o.getD #[]).toList) =
      (Array.range nb).map fun tl => (List.range nv).filter (fixHas nv
        (denseFinal nb nv pars defs succs (predsOf nb succs) (usersUpTo nv args nv) args
          (inB0Of nb nv g)) tl) := by
  have hc : ∀ tl x, Has nv (inB0Of nb nv g) tl x ↔ cand tl x = true := fun tl x => by
    rw [has_inB0Of, hcand]
  have hc0 : ∀ tl x, Has nv (inB0Of nb nv g) tl x → 1 ≤ tl ∧ tl < nb := fun tl x h => by
    rw [has_inB0Of] at h
    exact ⟨hg1 tl x h.2.2, h.1⟩
  have hsz : (inB0Of nb nv g).size = nb * nv := by simp [inB0Of, ByteArray.size]
  obtain ⟨hps1, hps2⟩ := predsOf_spec nb succs
  have hsp : ∀ p s : Nat, p ∈ (predsOf nb succs)[s]! → s ∈ succs[p]! := fun p s h => by
    rw [bang] at h
    exact ((hps2 s p).1 h).2.1
  have hps : ∀ p s : Nat, s ∈ succs[p]! → s < nb → p ∈ (predsOf nb succs)[s]! := fun p s h hs => by
    rw [bang]
    refine (hps2 s p).2 ⟨?_, h, hs⟩
    refine Nat.lt_of_not_le fun hp => ?_
    rw [bang, Array.getElem?_eq_none hp] at h
    exact List.not_mem_nil h
  have hus : ∀ y z : Nat, y < nv → (z ∈ (usersUpTo nv args nv)[y]! ↔ z < nv ∧ y ∈ args z) :=
    fun y z hy => by rw [bang]; exact (usersUpTo_spec nv args nv).2 y hy z
  have hH : SpHyp nb nv cand pars defs passS :=
    ⟨fun tl x h => by have := (hcand tl x).1 h; exact ⟨this.1, this.2.1⟩, hpS⟩
  obtain ⟨hok, hinv, hsol, hall⟩ := fixSparse_spec hH h
  have hconv : ∀ S, ASol (Has nv (inB0Of nb nv g)) (predsOf nb succs) pars defs args S ↔
      ASol (fun tl x => cand tl x = true) (predsOf nb succs) pars defs args' S :=
    fun S => aSol_congr hc fun tl x h => (hargs x ((has_inB0Of g tl x).1 h).2.1).symm
  have hmem : ∀ tl x, fixSpHas cand D tl x = true ↔ Has nv (denseFinal nb nv pars defs succs
      (predsOf nb succs) (usersUpTo nv args nv) args (inB0Of nb nv g)) tl x := fun tl x =>
    ⟨fun hx => dense_great hsz hc0 hsp hps hus ((hconv _).2 hsol) hx,
      fun hx => hinv _ ((hconv _).1 (dense_sol hsz hc0 hsp hps hus)) tl x hx⟩
  apply Array.ext
  · simp [hok.1]
  · intro i h1 h2
    have hi : i < nb := by simpa using h2
    obtain ⟨a, ha⟩ := hall i hi
    have hDi : D[i]'(by simpa using h1) = some a := by
      have := ha
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using h1),
        Option.getD_some] at this
      exact this
    simp only [Array.getElem_map, Array.getElem_range, hDi, Option.getD_some]
    apply eq_filter_range (hok.2 i a ha)
    intro x
    rw [← bsMem_iff (hok.2 i a ha), ← fixSpHas_some ha, hmem]
    exact ⟨fun h => ⟨(has_iff.1 h).1, h⟩, fun h => h.2⟩


end Fix

end Backend.Proof.Driver

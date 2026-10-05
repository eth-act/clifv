import FV.Backend.Proof.LowerSpec

/-!
# Completeness of `lowerCheck`: the availability fixpoint `inFix`

`inFix f ctx gn` is the greatest solution of the must-availability constraints `FixOk f ctx gn`:
it satisfies them (`inFix_fixOk`) and contains every solution (`inFix_greatest`), for any CFG.
The worklist `fixLoop` runs to the end within `fixFuel` iterations.

The proof names the pieces `inFix` builds (`Fix.fSuccs`, `Fix.fPreds`, ..., `Fix.inFix_eq`),
relates each to its mathematical meaning (`succIdx`, `parsOf`, `defsOf`, `defArgs`,
`valueDefs`), and runs `fixLoop` under an invariant (`Fix.LInv`: present pairs are candidates,
queued present pairs violate a constraint, every present violating pair is queued, every
solution is present) with the potential `work.length + present * (maxPush + 1)`.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

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

/-- Setting the indices `g p` of `l`. -/
theorem set_fold {γ : Type} (g : γ → Nat) : ∀ (l : List γ) (a : Array Bool),
    (l.foldl (fun a p => a.setIfInBounds (g p) true) a).size = a.size ∧
    ∀ x < a.size, ((l.foldl (fun a p => a.setIfInBounds (g p) true) a)[x]?.getD false = true ↔
      a[x]?.getD false = true ∨ x ∈ l.map g)
  | [], a => by simp
  | p :: l, a => by
    obtain ⟨h1, h2⟩ := set_fold g l (a.setIfInBounds (g p) true)
    simp only [List.foldl_cons, Array.size_setIfInBounds] at h1 h2 ⊢
    refine ⟨h1, fun x hx => ?_⟩
    rw [h2 x hx, Array.getElem?_setIfInBounds, Array.getElem?_eq_getElem hx]
    by_cases e : g p = x
    · simp [e, hx]
    · simp [e, Ne.symm e]

/-- Setting the statement results of a body. -/
theorem body_fold : ∀ (body : List Clif.Stmt) (a : Array Bool),
    (body.foldl (fun a s => s.results.foldl (fun a r => a.setIfInBounds r true) a) a).size =
      a.size ∧
    ∀ x < a.size,
      ((body.foldl (fun a s => s.results.foldl (fun a r => a.setIfInBounds r true) a) a)[x]?.getD
        false = true ↔ a[x]?.getD false = true ∨ x ∈ body.flatMap (·.results))
  | [], a => by simp
  | s :: body, a => by
    obtain ⟨h1, h2⟩ := set_fold (fun r : Nat => r) s.results a
    obtain ⟨h3, h4⟩ := body_fold body (s.results.foldl (fun a r => a.setIfInBounds r true) a)
    simp only [List.foldl_cons]
    refine ⟨by rw [h3, h1], fun x hx => ?_⟩
    rw [h4 x (by rw [h1]; exact hx), h2 x hx]
    simp [or_assoc]

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

/-! ## The pieces of `inFix` -/

/-- `inFix`'s block-index map. -/
def fBim (f : Clif.Function) : Std.HashMap Clif.BlockId Nat :=
  f.blocks.toArray.zipIdx.foldl (fun m (B, i) => m.insertIfNew B.id i) {}

/-- `inFix`'s successor indices. -/
def fSuccs (f : Clif.Function) : Array (List Nat) :=
  f.blocks.toArray.map fun B => (succIds B.term).filterMap ((fBim f)[·]?)

/-- `inFix`'s predecessor indices. -/
def fPreds (f : Clif.Function) : Array (List Nat) :=
  (fSuccs f).zipIdx.foldl
    (fun ps (ss, bi) => ss.foldl (fun ps s => ps.modify s (bi :: ·)) ps)
    (Array.replicate f.blocks.toArray.size [])

/-- `inFix`'s parameter sets. -/
def fPars (f : Clif.Function) : Array (Std.HashSet Nat) :=
  f.blocks.toArray.map fun B => Std.HashSet.ofList (B.params.map (·.1))

/-- `inFix`'s result sets. -/
def fDefs (f : Clif.Function) : Array (Std.HashSet Nat) :=
  f.blocks.toArray.map fun B => Std.HashSet.ofList (B.body.flatMap (·.results))

/-- `inFix`'s value marks. -/
def fIsVal (f : Clif.Function) (nv : Nat) : Array Bool :=
  f.blocks.toArray.foldl (fun a B =>
    let a := B.params.foldl (fun a p => a.setIfInBounds p.1 true) a
    B.body.foldl (fun a s => s.results.foldl (fun a r => a.setIfInBounds r true) a) a)
    (Array.replicate nv false)

/-- `inFix`'s users, after the values below `n`. -/
def usersN (ctx : Ctx) (n : Nat) : Array (List Nat) :=
  (List.range n).foldl (fun us z =>
    (defArgs ctx z).foldl (fun us y => us.modify y (z :: ·)) us) (Array.replicate ctx.valDef.size [])

/-- `inFix`'s users. -/
def fUsers (ctx : Ctx) : Array (List Nat) := usersN ctx ctx.valDef.size

/-- `inFix`'s initial bytes. -/
def fInB0 (f : Clif.Function) (ctx : Ctx) (gn : Nat → Nat) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := f.blocks.toArray.size * ctx.valDef.size) fun i =>
    let tl := i.1 / ctx.valDef.size
    let x := i.1 % ctx.valDef.size
    if 1 ≤ tl && (fIsVal f ctx.valDef.size)[x]! && !(fPars f)[tl]!.contains x &&
      !(fPars f)[tl]!.contains (gn x) then 1 else 0)

/-- `inFix`'s initial worklist. -/
def fWork0 (f : Clif.Function) (ctx : Ctx) (gn : Nat → Nat) : List (Nat × Nat) :=
  (List.range' 1 (f.blocks.toArray.size - 1)).foldl (fun work tl =>
    (List.range ctx.valDef.size).foldl (fun work x =>
      if fixHas ctx.valDef.size (fInB0 f ctx gn) tl x then
        let outOk := (fPreds f)[tl]!.all fun p =>
          (fPars f)[p]!.contains x || (fDefs f)[p]!.contains x ||
            fixHas ctx.valDef.size (fInB0 f ctx gn) p x
        let a0Ok := (defArgs ctx x).all fun y =>
          ((fPars f)[tl]!.contains y || fixHas ctx.valDef.size (fInB0 f ctx gn) tl y) &&
            !(fDefs f)[tl]!.contains y
        if !(outOk && a0Ok) then (tl, x) :: work else work
      else work) work) []

/-- `inFix`, by its pieces. -/
theorem inFix_eq (f : Clif.Function) (ctx : Ctx) (gn : Nat → Nat) :
    inFix f ctx gn = (Array.range f.blocks.toArray.size).map fun tl =>
      (List.range ctx.valDef.size).filter (fixHas ctx.valDef.size
        (fixLoop ctx.valDef.size (fPars f) (fDefs f) (fSuccs f) (fUsers ctx)
          (fixFuel f.blocks.toArray.size ctx.valDef.size (fSuccs f) (fUsers ctx) (fWork0 f ctx gn))
          (fInB0 f ctx gn) (fWork0 f ctx gn)) tl) := rfl

variable {f : Clif.Function} {ctx : Ctx} {gn : Nat → Nat}

/-! ## The pieces, mathematically -/

/-- The block-index map is `blockIdx?`. -/
theorem bim_get (b : Nat) : (fBim f)[b]? = blockIdx? f b := by
  have h : ∀ b, (fBim f)[b]? = (f.blocks.take f.blocks.toArray.zipIdx.size).findIdx? (·.id == b) := by
    unfold fBim
    apply Array.foldl_induction
      (fun n (m : Std.HashMap Clif.BlockId Nat) => ∀ b, m[b]? = (f.blocks.take n).findIdx? (·.id == b))
    · intro b; simp
    · intro i m ih b
      have hi : i.1 < f.blocks.length := by simpa using i.2
      simp only []
      rw [Std.HashMap.getElem?_insertIfNew, List.take_add_one, List.findIdx?_append, ← ih b,
        List.getElem?_eq_getElem hi]
      simp only [Option.toList_some, List.findIdx?_singleton, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hi)]
      by_cases e : f.blocks[i.1].id = b
      · subst e
        cases hm : m[f.blocks[i.1].id]? <;> simp [Std.HashMap.mem_iff_isSome_getElem?, hm]
      · simp [e]
  rw [h b]
  simp [blockIdx?]

/-- The successors are `succIdx`. -/
theorem succs_get (p : Nat) : (fSuccs f)[p]! = succIdx f p := by
  rw [bang]; unfold fSuccs succIdx
  rw [Array.getElem?_map, List.getElem?_toArray]
  cases f.blocks[p]? <;> simp [bim_get] <;> rfl

/-- Successor indices are blocks. -/
theorem succIdx_lt {p s : Nat} (h : s ∈ succIdx f p) : s < f.blocks.length := by
  unfold succIdx at h
  split at h
  · obtain ⟨b, -, hb⟩ := List.mem_filterMap.1 h
    exact (List.findIdx?_eq_some_iff_getElem.1 hb).1
  · simp at h

/-- Only blocks have successors. -/
theorem succIdx_src {p s : Nat} (h : s ∈ succIdx f p) : p < f.blocks.length := by
  unfold succIdx at h
  split at h
  · rename_i B hB
    exact (List.getElem?_eq_some_iff.1 hB).1
  · simp at h

/-- The predecessors: `p` precedes `tl` iff `tl` is a successor of `p`. -/
theorem mem_preds (tl p : Nat) : p ∈ (fPreds f)[tl]! ↔ tl ∈ succIdx f p := by
  have h : (fPreds f).size = f.blocks.length ∧ ∀ t q, q ∈ (fPreds f)[t]?.getD [] ↔
      q < (fSuccs f).zipIdx.size ∧ t ∈ (fSuccs f)[q]! ∧ t < f.blocks.length := by
    unfold fPreds
    apply Array.foldl_induction (fun n (ps : Array (List Nat)) => ps.size = f.blocks.length ∧
      ∀ t q, q ∈ ps[t]?.getD [] ↔ q < n ∧ t ∈ (fSuccs f)[q]! ∧ t < f.blocks.length)
    · refine ⟨by simp, fun t q => ?_⟩
      simp only [Array.getElem?_replicate]
      split <;> simp
    · intro i ps ⟨hs, ih⟩
      simp only [Fin.getElem_fin, Array.getElem_zipIdx, Nat.zero_add]
      obtain ⟨h1, h2⟩ := modify_fold i.1 (fSuccs f)[i.1] ps
      refine ⟨by rw [h1, hs], fun t q => ?_⟩
      have hi : i.1 < (fSuccs f).size := by simpa using i.2
      have e : (fSuccs f)[i.1] = (fSuccs f)[i.1]! := by
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
  rw [bang]
  show p ∈ (fPreds f)[tl]?.getD [] ↔ _
  rw [h.2, succs_get]
  have hsz : (fSuccs f).size = f.blocks.length := by simp [fSuccs]
  constructor
  · exact fun h => h.2.1
  · intro h'
    have := succIdx_src h'
    exact ⟨by simpa [hsz] using this, h', succIdx_lt h'⟩

/-- The empty set contains nothing. -/
theorem dflt_contains (y : Nat) : (default : Std.HashSet Nat).contains y = false :=
  Std.HashSet.contains_empty

/-- The parameter sets are `parsOf`. -/
theorem pars_contains (tl y : Nat) : (fPars f)[tl]!.contains y = true ↔ y ∈ parsOf f tl := by
  rw [bang]; unfold fPars parsOf
  rw [Array.getElem?_map, List.getElem?_toArray]
  cases f.blocks[tl]? <;> simp [Std.HashSet.contains_ofList, dflt_contains]

/-- The result sets are `defsOf`. -/
theorem defs_contains (tl y : Nat) : (fDefs f)[tl]!.contains y = true ↔ y ∈ defsOf f tl := by
  rw [bang]; unfold fDefs defsOf
  rw [Array.getElem?_map, List.getElem?_toArray]
  cases f.blocks[tl]? <;> simp [Std.HashSet.contains_ofList, dflt_contains]

/-- The value marks are `valueDefs`. -/
theorem isVal_get {nv x : Nat} (hx : x < nv) : (fIsVal f nv)[x]! = true ↔ x ∈ valueDefs f := by
  have h : (fIsVal f nv).size = nv ∧ ∀ x < nv, ((fIsVal f nv)[x]?.getD false = true ↔
      x ∈ (f.blocks.take f.blocks.toArray.size).flatMap
        fun B => B.params.map (·.1) ++ B.body.flatMap (·.results)) := by
    unfold fIsVal
    apply Array.foldl_induction (fun n (a : Array Bool) => a.size = nv ∧ ∀ x < nv,
      (a[x]?.getD false = true ↔
        x ∈ (f.blocks.take n).flatMap fun B => B.params.map (·.1) ++ B.body.flatMap (·.results)))
    · exact ⟨by simp, fun x hx => by simp [hx]⟩
    · intro i a ⟨hs, ih⟩
      have hi : i.1 < f.blocks.length := by simpa using i.2
      obtain ⟨h1, h2⟩ := set_fold (fun p : Clif.ValueId × Clif.Ty => p.1)
        (f.blocks.toArray[i]).params a
      obtain ⟨h3, h4⟩ := body_fold (f.blocks.toArray[i]).body
        ((f.blocks.toArray[i]).params.foldl (fun a p => a.setIfInBounds p.1 true) a)
      refine ⟨by rw [h3, h1, hs], fun x hx => ?_⟩
      rw [h4 x (by rw [h1, hs]; exact hx), h2 x (by rw [hs]; exact hx), ih x hx,
        List.take_add_one, List.getElem?_eq_getElem hi]
      simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.mem_append, List.getElem_toArray, Fin.getElem_fin, or_assoc]
  rw [bang]
  show (fIsVal f nv)[x]?.getD false = true ↔ _
  rw [h.2 x hx]
  simp [valueDefs]

/-- The users of `y`, after the values below `n`. -/
theorem usersN_spec : ∀ n, (usersN ctx n).size = ctx.valDef.size ∧
    ∀ y < ctx.valDef.size, ∀ z, z ∈ (usersN ctx n)[y]?.getD [] ↔ z < n ∧ y ∈ defArgs ctx z
  | 0 => ⟨by simp [usersN], fun y hy z => by simp [usersN, hy]⟩
  | n + 1 => by
    obtain ⟨hs, ih⟩ := usersN_spec n
    have e : usersN ctx (n + 1) =
        (defArgs ctx n).foldl (fun us y => us.modify y (n :: ·)) (usersN ctx n) := by
      simp only [usersN, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨h1, h2⟩ := modify_fold n (defArgs ctx n) (usersN ctx n)
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

/-- The users of `y`: the values whose definition reads `y`. -/
theorem mem_users {y : Nat} (hy : y < ctx.valDef.size) (z : Nat) :
    z ∈ (fUsers ctx)[y]! ↔ z < ctx.valDef.size ∧ y ∈ defArgs ctx z := by
  rw [bang]
  exact (usersN_spec ctx.valDef.size).2 y hy z

/-- The candidates: what `FixOk.cand` allows. -/
def Cand (f : Clif.Function) (ctx : Ctx) (gn : Nat → Nat) (tl x : Nat) : Prop :=
  1 ≤ tl ∧ tl < f.blocks.length ∧ x < ctx.valDef.size ∧ x ∈ valueDefs f ∧
    x ∉ parsOf f tl ∧ gn x ∉ parsOf f tl

/-- The initial bytes are the candidates. -/
theorem has0 (tl x : Nat) : fixHas ctx.valDef.size (fInB0 f ctx gn) tl x = true ↔ Cand f ctx gn tl x := by
  rw [has_iff]
  unfold Cand
  by_cases hx : x < ctx.valDef.size
  · by_cases ht : tl < f.blocks.length
    · have hi : tl * ctx.valDef.size + x < f.blocks.toArray.size * ctx.valDef.size := by
        simpa using idx_lt ht hx
      have hn : 0 < ctx.valDef.size := by omega
      have h1 : (tl * ctx.valDef.size + x) / ctx.valDef.size = tl := by
        rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hx, Nat.add_zero]
      have h2 : (tl * ctx.valDef.size + x) % ctx.valDef.size = x := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]
      simp only [fInB0, Array.getElem?_ofFn, dite_eq_left hi, Option.getD_some, h1, h2]
      split
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', isVal_get hx] at hc
        simp only [ne_eq]
        refine ⟨fun _ => ⟨hc.1.1.1, ht, hx, hc.1.1.2, fun h => ?_, fun h => ?_⟩,
          fun _ => ⟨hx, by decide⟩⟩
        · have := (pars_contains (f := f) tl x).2 h; simp_all
        · have := (pars_contains (f := f) tl (gn x)).2 h; simp_all
      · rename_i hc
        simp only [ne_eq, not_true_eq_false, and_false, false_iff]
        rintro ⟨h3, -, -, h4, h5, h6⟩
        apply hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', isVal_get hx]
        refine ⟨⟨⟨h3, h4⟩, ?_⟩, ?_⟩
        · cases e : (fPars f)[tl]!.contains x
          · rfl
          · exact absurd ((pars_contains tl x).1 e) h5
        · cases e : (fPars f)[tl]!.contains (gn x)
          · rfl
          · exact absurd ((pars_contains tl (gn x)).1 e) h6
    · have hi : ¬ tl * ctx.valDef.size + x < f.blocks.toArray.size * ctx.valDef.size := by
        have := Nat.mul_le_mul_right ctx.valDef.size (Nat.le_of_not_lt ht)
        simp only [List.size_toArray]
        omega
      simp only [fInB0, Array.getElem?_ofFn, dite_eq_right hi]
      simp [ht]
  · simp [hx]

/-! ## The loop -/

/-- The pairs present in `inB`. -/
def Has (nv : Nat) (inB : ByteArray) (tl x : Nat) : Prop := fixHas nv inB tl x = true

/-- The out-constraint of `FixOk` at `(tl, x)` for the solution `S`. -/
def OutOk (f : Clif.Function) (S : Nat → Nat → Prop) (tl x : Nat) : Prop :=
  ∀ p, tl ∈ succIdx f p → x ∈ parsOf f p ∨ x ∈ defsOf f p ∨ S p x

/-- The closure constraint of `FixOk` at `(tl, x)` for the solution `S`. -/
def CloOk (f : Clif.Function) (ctx : Ctx) (S : Nat → Nat → Prop) (tl x : Nat) : Prop :=
  ∀ y ∈ defArgs ctx x, (y ∈ parsOf f tl ∨ S tl y) ∧ y ∉ defsOf f tl

theorem outOk_mono {S S' : Nat → Nat → Prop} (hS : ∀ a b, S a b → S' a b) {tl x : Nat}
    (h : OutOk f S tl x) : OutOk f S' tl x := fun p hp =>
  (h p hp).imp_right (Or.imp_right (hS p x))

theorem cloOk_mono {S S' : Nat → Nat → Prop} (hS : ∀ a b, S a b → S' a b) {tl x : Nat}
    (h : CloOk f ctx S tl x) : CloOk f ctx S' tl x := fun y hy =>
  ⟨(h y hy).1.imp_right (hS tl y), (h y hy).2⟩

/-- The invariant of `fixLoop`. -/
structure LInv (f : Clif.Function) (ctx : Ctx) (gn : Nat → Nat) (inB : ByteArray)
    (work : List (Nat × Nat)) : Prop where
  cand : ∀ tl x, Has ctx.valDef.size inB tl x → Cand f ctx gn tl x
  queued : ∀ q ∈ work, Has ctx.valDef.size inB q.1 q.2 →
    ¬(OutOk f (Has ctx.valDef.size inB) q.1 q.2 ∧ CloOk f ctx (Has ctx.valDef.size inB) q.1 q.2)
  viol : ∀ tl x, Has ctx.valDef.size inB tl x →
    ¬(OutOk f (Has ctx.valDef.size inB) tl x ∧ CloOk f ctx (Has ctx.valDef.size inB) tl x) →
    (tl, x) ∈ work
  great : ∀ D, FixOk f ctx gn D → ∀ tl x, D tl x → Has ctx.valDef.size inB tl x

/-- Removing the popped present pair `(tl, x)`: what changes. -/
theorem remove {inB : ByteArray} {tl x : Nat} {rest : List (Nat × Nat)}
    (hi : LInv f ctx gn inB ((tl, x) :: rest)) (hp : Has ctx.valDef.size inB tl x) :
    (∀ a b, Has ctx.valDef.size (inB.set! (tl * ctx.valDef.size + x) 0) a b ↔
      Has ctx.valDef.size inB a b ∧ ¬(a = tl ∧ b = x)) ∧
    (∀ D, FixOk f ctx gn D → ∀ a b, D a b →
      Has ctx.valDef.size (inB.set! (tl * ctx.valDef.size + x) 0) a b) ∧
    (∀ a b, Has ctx.valDef.size (inB.set! (tl * ctx.valDef.size + x) 0) a b →
      ¬(OutOk f (Has ctx.valDef.size (inB.set! (tl * ctx.valDef.size + x) 0)) a b ∧
        CloOk f ctx (Has ctx.valDef.size (inB.set! (tl * ctx.valDef.size + x) 0)) a b) →
      (a, b) ∈ rest ∨ (b = x ∧ a ∈ succIdx f tl ∧ x ∉ parsOf f tl ∧ x ∉ defsOf f tl) ∨
        (a = tl ∧ x ∈ defArgs ctx b ∧ x ∉ parsOf f tl ∧ x ∉ defsOf f tl)) ∧
    (∀ q ∈ rest, Has ctx.valDef.size (inB.set! (tl * ctx.valDef.size + x) 0) q.1 q.2 →
      ¬(OutOk f (Has ctx.valDef.size (inB.set! (tl * ctx.valDef.size + x) 0)) q.1 q.2 ∧
        CloOk f ctx (Has ctx.valDef.size (inB.set! (tl * ctx.valDef.size + x) 0)) q.1 q.2)) := by
  have hx : x < ctx.valDef.size := (has_iff.1 hp).1
  have hs : ∀ a b, Has ctx.valDef.size (inB.set! (tl * ctx.valDef.size + x) 0) a b ↔
      Has ctx.valDef.size inB a b ∧ ¬(a = tl ∧ b = x) := fun a b => has_set hx a b
  have hsub : ∀ a b, Has ctx.valDef.size (inB.set! (tl * ctx.valDef.size + x) 0) a b →
      Has ctx.valDef.size inB a b := fun a b h => ((hs a b).1 h).1
  refine ⟨hs, fun D hD a b hab => ?_, fun a b hab hv => ?_, fun q hq hpq hv => ?_⟩
  · refine (hs a b).2 ⟨hi.great D hD a b hab, ?_⟩
    rintro ⟨rfl, rfl⟩
    have hok : OutOk f (Has ctx.valDef.size inB) a b ∧ CloOk f ctx (Has ctx.valDef.size inB) a b :=
      ⟨outOk_mono (hi.great D hD) (hD.out a b hab), cloOk_mono (hi.great D hD) (hD.clo a b hab)⟩
    exact hi.queued (a, b) (List.mem_cons_self) hp hok
  · by_cases hr : (a, b) ∈ rest
    · exact .inl hr
    by_cases h2 : b = x ∧ a ∈ succIdx f tl ∧ x ∉ parsOf f tl ∧ x ∉ defsOf f tl
    · exact .inr (.inl h2)
    by_cases h3 : a = tl ∧ x ∈ defArgs ctx b ∧ x ∉ parsOf f tl ∧ x ∉ defsOf f tl
    · exact .inr (.inr h3)
    exfalso
    obtain ⟨hab', hne⟩ := (hs a b).1 hab
    have hold : OutOk f (Has ctx.valDef.size inB) a b ∧ CloOk f ctx (Has ctx.valDef.size inB) a b := by
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
          by_cases hp' : b ∈ parsOf f p
          · exact .inl hp'
          by_cases hd' : b ∈ defsOf f p
          · exact .inr (.inl hd')
          exact absurd ⟨rfl, hpp, hp', hd'⟩ h2
        · exact .inr (.inr ((hs p b).2 ⟨h, e⟩))
    · obtain ⟨h1, h1'⟩ := hold.2 y hyy
      refine ⟨?_, h1'⟩
      rcases h1 with h | h
      · exact .inl h
      · by_cases e : a = tl ∧ y = x
        · obtain ⟨rfl, rfl⟩ := e
          by_cases hp' : y ∈ parsOf f a
          · exact .inl hp'
          exact absurd ⟨rfl, hyy, hp', h1'⟩ h3
        · exact .inr ((hs a y).2 ⟨h, e⟩)
  · exact hi.queued q (List.mem_cons_of_mem _ hq) (hsub _ _ hpq)
      ⟨outOk_mono hsub hv.1, cloOk_mono hsub hv.2⟩

/-- `fixLoop` with enough fuel ends with an empty worklist, keeping the invariant. -/
theorem loop (M : Nat) (hM : ∀ tl x : Nat, (fSuccs f)[tl]!.length + (fUsers ctx)[x]!.length ≤ M) :
    ∀ fuel inB work, LInv f ctx gn inB work → work.length + cnt inB * (M + 1) < fuel →
      LInv f ctx gn (fixLoop ctx.valDef.size (fPars f) (fDefs f) (fSuccs f) (fUsers ctx) fuel inB work) []
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, inB, [], hi, _ => by simpa only [fixLoop] using hi
  | fuel + 1, inB, (tl, x) :: rest, hi, hf => by
    simp only [fixLoop]
    by_cases hp : fixHas ctx.valDef.size inB tl x = true
    · rw [ite_eq_left hp]
      obtain ⟨hs, hg, hv, hw⟩ := remove hi hp
      have hc : ∀ a b, Has ctx.valDef.size (inB.set! (tl * ctx.valDef.size + x) 0) a b →
          Cand f ctx gn a b := fun a b h => hi.cand a b ((hs a b).1 h).1
      have hcnt := cnt_set hp
      have hx : x < ctx.valDef.size := (has_iff.1 hp).1
      simp only [List.length_cons] at hf
      have hK : cnt inB * (M + 1) = cnt (inB.set! (tl * ctx.valDef.size + x) 0) * (M + 1) + (M + 1) := by
        rw [← hcnt, Nat.add_mul, Nat.one_mul]
      by_cases hn : (!(fPars f)[tl]!.contains x && !(fDefs f)[tl]!.contains x) = true
      · rw [ite_eq_left hn]
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hn
        have hx1 : x ∉ parsOf f tl := fun h => by simp [(pars_contains tl x).2 h] at hn
        have hx2 : x ∉ defsOf f tl := fun h => by simp [(defs_contains tl x).2 h] at hn
        have hmem := mem_foldl (fun w s q => mem_push
          (fixHas ctx.valDef.size (inB.set! (tl * ctx.valDef.size + x) 0) s x) (s, x) w q)
        have hmem2 := mem_foldl (fun w z q => mem_push
          (fixHas ctx.valDef.size (inB.set! (tl * ctx.valDef.size + x) 0) tl z) (tl, z) w q)
        have hl1 := length_foldl (fun w s => length_push
          (fixHas ctx.valDef.size (inB.set! (tl * ctx.valDef.size + x) 0) s x) (s, x) w)
          (fSuccs f)[tl]! rest
        have hl2 := length_foldl (fun w z => length_push
          (fixHas ctx.valDef.size (inB.set! (tl * ctx.valDef.size + x) 0) tl z) (tl, z) w)
          (fUsers ctx)[x]! ((fSuccs f)[tl]!.foldl (fun w s =>
            if fixHas ctx.valDef.size (inB.set! (tl * ctx.valDef.size + x) 0) s x = true
            then (s, x) :: w else w) rest)
        have hMx := hM tl x
        apply loop M hM fuel
        · refine ⟨hc, fun q hq hpq => ?_, fun a b hab hab' => ?_, hg⟩
          · rw [hmem2, hmem] at hq
            rcases hq with (hq | ⟨s, hs', hsx, rfl⟩) | ⟨z, hz, hzx, rfl⟩
            · exact hw q hq hpq
            · rw [succs_get] at hs'
              rintro ⟨ho, -⟩
              rcases ho tl hs' with h | h | h
              · exact hx1 h
              · exact hx2 h
              · exact ((hs tl x).1 h).2 ⟨rfl, rfl⟩
            · have hz' := ((mem_users hx z).1 hz).2
              rintro ⟨-, hcl⟩
              rcases (hcl x hz').1 with h | h
              · exact hx1 h
              · exact ((hs tl x).1 h).2 ⟨rfl, rfl⟩
          · rw [hmem2, hmem]
            rcases hv a b hab hab' with h | ⟨rfl, h, -⟩ | ⟨rfl, h, -⟩
            · exact .inl (.inl h)
            · exact .inl (.inr ⟨a, (by rw [succs_get]; exact h), hab, rfl⟩)
            · exact .inr ⟨b, (mem_users hx b).2 ⟨(has_iff.1 hab).1, h⟩, hab, rfl⟩
        · omega
      · rw [ite_eq_right hn]
        have hxp : x ∈ parsOf f tl ∨ x ∈ defsOf f tl := by
          by_cases h1 : x ∈ parsOf f tl
          · exact .inl h1
          · refine .inr ((defs_contains tl x).1 ?_)
            have := mt (pars_contains tl x).1 h1
            simp only [Bool.not_eq_true] at this
            simpa [this] using hn
        apply loop M hM fuel _ _ ⟨hc, hw, fun a b hab hab' => ?_, hg⟩ (by omega)
        rcases hv a b hab hab' with h | ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩
        · exact h
        · exact absurd hxp (by simp [h1, h2])
        · exact absurd hxp (by simp [h1, h2])
    · rw [ite_eq_right hp]
      simp only [List.length_cons] at hf
      refine loop M hM fuel _ _ ⟨hi.cand, fun q hq => hi.queued q (List.mem_cons_of_mem _ hq),
        fun a b hab hab' => ?_, hi.great⟩ (by omega)
      rcases List.mem_cons.1 (hi.viol a b hab hab') with e | e
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        exact absurd hab hp
      · exact e

/-- The initial worklist test: the out-constraint. -/
theorem outB_iff (inB : ByteArray) (tl x : Nat) :
    ((fPreds f)[tl]!.all fun p => (fPars f)[p]!.contains x || (fDefs f)[p]!.contains x ||
      fixHas ctx.valDef.size inB p x) = true ↔ OutOk f (Has ctx.valDef.size inB) tl x := by
  simp only [List.all_eq_true, Bool.or_eq_true, pars_contains, defs_contains, mem_preds, OutOk,
    Has, or_assoc]

/-- The initial worklist test: the closure constraint. -/
theorem cloB_iff (inB : ByteArray) (tl x : Nat) :
    ((defArgs ctx x).all fun y => ((fPars f)[tl]!.contains y || fixHas ctx.valDef.size inB tl y) &&
      !(fDefs f)[tl]!.contains y) = true ↔ CloOk f ctx (Has ctx.valDef.size inB) tl x := by
  simp only [List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    pars_contains, CloOk, Has]
  refine forall_congr' fun y => imp_congr_right fun _ => and_congr_right fun _ => ?_
  rw [← defs_contains tl y]
  simp

/-- The inner loop of `inFix`'s initial worklist. -/
theorem work_inner (tl : Nat) (w : List (Nat × Nat)) (q : Nat × Nat) :
    q ∈ (List.range ctx.valDef.size).foldl (fun work x =>
      if fixHas ctx.valDef.size (fInB0 f ctx gn) tl x then
        let outOk := (fPreds f)[tl]!.all fun p =>
          (fPars f)[p]!.contains x || (fDefs f)[p]!.contains x ||
            fixHas ctx.valDef.size (fInB0 f ctx gn) p x
        let a0Ok := (defArgs ctx x).all fun y =>
          ((fPars f)[tl]!.contains y || fixHas ctx.valDef.size (fInB0 f ctx gn) tl y) &&
            !(fDefs f)[tl]!.contains y
        if !(outOk && a0Ok) then (tl, x) :: work else work
      else work) w ↔ q ∈ w ∨
        ∃ x ∈ List.range ctx.valDef.size,
          (fixHas ctx.valDef.size (fInB0 f ctx gn) tl x = true ∧
            (((fPreds f)[tl]!.all fun p => (fPars f)[p]!.contains x || (fDefs f)[p]!.contains x ||
              fixHas ctx.valDef.size (fInB0 f ctx gn) p x) &&
            ((defArgs ctx x).all fun y =>
              ((fPars f)[tl]!.contains y || fixHas ctx.valDef.size (fInB0 f ctx gn) tl y) &&
                !(fDefs f)[tl]!.contains y)) = false) ∧ q = (tl, x) :=
  by
    apply mem_foldl
    intro w x q
    exact mem_push2 _ _ _ w q

/-- The invariant holds initially. -/
theorem init : LInv f ctx gn (fInB0 f ctx gn) (fWork0 f ctx gn) := by
  have hmem : ∀ q, q ∈ fWork0 f ctx gn ↔ q ∈ ([] : List (Nat × Nat)) ∨
      ∃ tl ∈ List.range' 1 (f.blocks.toArray.size - 1),
        ∃ x ∈ List.range ctx.valDef.size,
          (fixHas ctx.valDef.size (fInB0 f ctx gn) tl x = true ∧
            (((fPreds f)[tl]!.all fun p => (fPars f)[p]!.contains x || (fDefs f)[p]!.contains x ||
              fixHas ctx.valDef.size (fInB0 f ctx gn) p x) &&
            ((defArgs ctx x).all fun y =>
              ((fPars f)[tl]!.contains y || fixHas ctx.valDef.size (fInB0 f ctx gn) tl y) &&
                !(fDefs f)[tl]!.contains y)) = false) ∧ q = (tl, x) := by
    intro q
    unfold fWork0
    apply mem_foldl
    intro w tl q
    exact work_inner tl w q
  refine ⟨fun tl x h => (has0 tl x).1 h, fun q hq hpq => ?_, fun tl x h hv => ?_,
    fun D hD tl x h => (has0 tl x).2 (hD.cand tl x h)⟩
  · simp only [hmem, List.not_mem_nil, false_or] at hq
    obtain ⟨tl, -, x, -, ⟨-, hc⟩, rfl⟩ := hq
    intro ⟨ho, hcl⟩
    rw [← outB_iff, ← cloB_iff] at *
    simp_all
  · have hc := (has0 tl x).1 h
    simp only [hmem, List.not_mem_nil, false_or]
    refine ⟨tl, List.mem_range'_1.2 ⟨hc.1, by have := hc.2.1; simp; omega⟩, x, List.mem_range.2 hc.2.2.1,
      ⟨h, ?_⟩, rfl⟩
    cases e : (((fPreds f)[tl]!.all fun p => (fPars f)[p]!.contains x || (fDefs f)[p]!.contains x ||
        fixHas ctx.valDef.size (fInB0 f ctx gn) p x) &&
      ((defArgs ctx x).all fun y =>
        ((fPars f)[tl]!.contains y || fixHas ctx.valDef.size (fInB0 f ctx gn) tl y) &&
          !(fDefs f)[tl]!.contains y))
    · rfl
    · simp only [Bool.and_eq_true] at e
      exact absurd ⟨(outB_iff _ tl x).1 e.1, (cloB_iff _ tl x).1 e.2⟩ hv

/-- The bytes `inFix` reads off. -/
def final (f : Clif.Function) (ctx : Ctx) (gn : Nat → Nat) : ByteArray :=
  fixLoop ctx.valDef.size (fPars f) (fDefs f) (fSuccs f) (fUsers ctx)
    (fixFuel f.blocks.toArray.size ctx.valDef.size (fSuccs f) (fUsers ctx) (fWork0 f ctx gn))
    (fInB0 f ctx gn) (fWork0 f ctx gn)

/-- The loop ends with an empty worklist. -/
theorem final_inv : LInv f ctx gn (final f ctx gn) [] := by
  apply loop ((fSuccs f).foldl (fun m s => max m s.length) 0 +
    (fUsers ctx).foldl (fun m u => max m u.length) 0)
  · intro tl x; exact Nat.add_le_add (len_le_max _ _) (len_le_max _ _)
  · exact init
  · have h1 : cnt (fInB0 f ctx gn) ≤ f.blocks.toArray.size * ctx.valDef.size := by
      have := List.countP_le_length (p := (· != 0)) (l := (fInB0 f ctx gn).data.toList)
      simpa [cnt, fInB0] using this
    have h2 := Nat.mul_le_mul_right ((fSuccs f).foldl (fun m s => max m s.length) 0 +
      (fUsers ctx).foldl (fun m u => max m u.length) 0 + 1) h1
    dsimp only [fixFuel]
    omega

/-- Membership in `inFix`: presence in the final bytes. -/
theorem mem_inFix (tl x : Nat) :
    x ∈ (inFix f ctx gn).getD tl [] ↔ Has ctx.valDef.size (final f ctx gn) tl x := by
  rw [inFix_eq, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  by_cases ht : tl < f.blocks.toArray.size
  · simp only [ht, ite_true, Option.map_some, Option.getD_some, List.mem_filter, List.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨(has_iff.1 h).1, h⟩⟩
  · simp only [ht, ite_false, Option.map_none, Option.getD_none, List.not_mem_nil, false_iff]
    intro h
    exact ht (by simpa using (final_inv.cand tl x h).2.1)

/-- Present pairs of the final bytes satisfy the constraints. -/
theorem final_ok {tl x : Nat} (h : Has ctx.valDef.size (final f ctx gn) tl x) :
    OutOk f (Has ctx.valDef.size (final f ctx gn)) tl x ∧
      CloOk f ctx (Has ctx.valDef.size (final f ctx gn)) tl x :=
  Classical.byContradiction fun hn => by simpa using final_inv.viol tl x h hn

end Fix

variable {f : Clif.Function} {ctx : Ctx} {gn : Nat → Nat}

/-- `inFix` has one entry per block. -/
theorem inFix_size : (inFix f ctx gn).size = f.blocks.length := by
  rw [Fix.inFix_eq]; simp

/-- `inFix` satisfies the constraints. -/
theorem inFix_fixOk : FixOk f ctx gn (fun tl x => x ∈ (inFix f ctx gn).getD tl []) := by
  refine ⟨fun tl x h => Fix.final_inv.cand tl x ((Fix.mem_inFix tl x).1 h),
    fun tl x h p hp => ?_, fun tl x h y hy => ?_⟩
  · rcases (Fix.final_ok ((Fix.mem_inFix tl x).1 h)).1 p hp with h' | h' | h'
    · exact .inl h'
    · exact .inr (.inl h')
    · exact .inr (.inr ((Fix.mem_inFix p x).2 h'))
  · obtain ⟨h1, h2⟩ := (Fix.final_ok ((Fix.mem_inFix tl x).1 h)).2 y hy
    exact ⟨h1.imp_right (Fix.mem_inFix tl y).2, h2⟩

/-- `inFix` contains every solution of the constraints. -/
theorem inFix_greatest {D : Nat → Nat → Prop} (hD : FixOk f ctx gn D) {tl x : Nat} (h : D tl x) :
    x ∈ (inFix f ctx gn).getD tl [] :=
  (Fix.mem_inFix tl x).2 (Fix.final_inv.great D hD tl x h)

end Backend.Proof.Driver

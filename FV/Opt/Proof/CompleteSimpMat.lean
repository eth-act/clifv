import FV.Opt.Proof.SimpMat
import FV.Opt.Proof.CompleteLicm

/-!
# Completeness of simplify: output views, placeable values, `materialize`

The syntactic side of the simplify pass (`FV/Opt/Simplify.lean`), for its completeness proof
(`FV/Opt/Proof/CompleteSimp.lean`):

* an *output view* `V : Nat → Option Block` is the part of the output built so far (the blocks
  already processed, and the current block up to the current statement); `DefAt V x d t` is a
  definition site of `x` in it (`defSites` numbering) and `AvailAt` the availability of
  `Opt.wfCert` in it;
* `Placed st B x`: `x` is placeable — not *bad* (`B`: a later leaf, a removed value, the statement
  being processed), known, and the operands of its nodes and of the nodes of its e-class are
  placeable. Such values are what `materialize` may meet;
* `MInv`: the state facts `materialize` needs (fresh numbering, typed nodes, `avail` agrees
  with the view on good values);
* `mat_spec`: `materialize` of a good value appends well-typed pure nodes over available good
  values (each defined once) and returns a good value available at the end of the block.
-/

namespace Opt

open Clif

/-! ## Output views -/

/-- `x` is defined in the view `V` at site `(d, t)` (`defSites` numbering). -/
def DefAt (V : Nat → Option Block) (x : ValueId) (d t : Nat) : Prop :=
  ∃ b, V d = some b ∧ ((t = 0 ∧ ∃ p ∈ b.params, p.1 = x) ∨
    ∃ j s, t = j + 1 ∧ b.body[j]? = some s ∧ x ∈ s.results)

/-- `x` is available before statement `k` of block `i` of the view. -/
def AvailAt (idom : Array (Option Nat)) (V : Nat → Option Block) (i k : Nat) (x : ValueId) :
    Prop :=
  ∃ d t, DefAt V x d t ∧ ((d = i ∧ t ≤ k) ∨ (d ≠ i ∧ Anc idom d i))

/-- `x` is available at the end of what the view has of block `i`. -/
def AvailHere (idom : Array (Option Nat)) (V : Nat → Option Block) (i : Nat) (x : ValueId) :
    Prop :=
  ∃ d t, DefAt V x d t ∧ (d = i ∨ Anc idom d i)

/-- Append statements to block `bi` of the view. -/
def emitV (V : Nat → Option Block) (bi : Nat) (new : List Stmt) : Nat → Option Block :=
  fun d => if d = bi then (V d).map fun b => { b with body := b.body ++ new } else V d

theorem emitV_nil (V : Nat → Option Block) (bi : Nat) : emitV V bi [] = V := by
  funext d; unfold emitV; split
  · subst d; cases V bi <;> simp
  · rfl

theorem emitV_append (V : Nat → Option Block) (bi : Nat) (a c : List Stmt) :
    emitV (emitV V bi a) bi c = emitV V bi (a ++ c) := by
  funext d; by_cases hd : d = bi
  · subst hd; simp only [emitV]; cases V d <;> simp
  · simp [emitV, hd]

theorem DefAt.emit {V : Nat → Option Block} {x : ValueId} {d t : Nat} (h : DefAt V x d t)
    (bi : Nat) (new : List Stmt) : DefAt (emitV V bi new) x d t := by
  obtain ⟨b, hb, h⟩ := h
  unfold emitV
  by_cases hd : d = bi
  · subst hd
    refine ⟨{ b with body := b.body ++ new }, by simp [hb], ?_⟩
    rcases h with h | ⟨j, s, rfl, hs, hx⟩
    · exact .inl h
    · exact .inr ⟨j, s, rfl, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hs).1]; exact hs, hx⟩
  · exact ⟨b, by simp [hd, hb], h⟩

theorem AvailAt.emit {idom : Array (Option Nat)} {V : Nat → Option Block} {i k : Nat}
    {x : ValueId} (h : AvailAt idom V i k x) (bi : Nat) (new : List Stmt) :
    AvailAt idom (emitV V bi new) i k x := by
  obtain ⟨d, t, hd, h⟩ := h
  exact ⟨d, t, hd.emit bi new, h⟩

theorem AvailHere.emit {idom : Array (Option Nat)} {V : Nat → Option Block} {i : Nat}
    {x : ValueId} (h : AvailHere idom V i x) (bi : Nat) (new : List Stmt) :
    AvailHere idom (emitV V bi new) i x := by
  obtain ⟨d, t, hd, h⟩ := h
  exact ⟨d, t, hd.emit bi new, h⟩

/-- A definition in the extended view is old, or one of the appended statements. -/
theorem DefAt.of_emit {V : Nat → Option Block} {bi : Nat} {new : List Stmt} {x : ValueId}
    {d t : Nat} (h : DefAt (emitV V bi new) x d t) :
    DefAt V x d t ∨ ∃ b, V bi = some b ∧ d = bi ∧
      ∃ j s, t = b.body.length + j + 1 ∧ new[j]? = some s ∧ x ∈ s.results := by
  obtain ⟨b', hb', h⟩ := h
  by_cases hd : d = bi
  · subst hd
    obtain ⟨b, hb, rfl⟩ : ∃ b, V d = some b ∧ b' = { b with body := b.body ++ new } := by
      unfold emitV at hb'; cases hV : V d <;> simp_all
    rcases h with h | ⟨j, s, rfl, hs, hx⟩
    · exact .inl ⟨b, hb, .inl h⟩
    · rcases Nat.lt_or_ge j b.body.length with hj | hj
      · rw [List.getElem?_append_left hj] at hs
        exact .inl ⟨b, hb, .inr ⟨j, s, rfl, hs, hx⟩⟩
      · rw [List.getElem?_append_right hj] at hs
        exact .inr ⟨b, hb, rfl, j - b.body.length, s, by omega, hs, hx⟩
  · simp only [emitV, hd, ite_false] at hb'
    exact .inl ⟨b', hb', h⟩

/-- A value available at the end of block `i` is available before its next statement. -/
theorem AvailHere.at_end {idom : Array (Option Nat)} {V : Nat → Option Block} {i : Nat}
    {x : ValueId} {b : Block} (hb : V i = some b) (h : AvailHere idom V i x) :
    AvailAt idom V i b.body.length x := by
  obtain ⟨d, t, hd, h⟩ := h
  by_cases hdi : d = i
  · subst hdi
    refine ⟨d, t, hd, .inl ⟨rfl, ?_⟩⟩
    obtain ⟨b', hb', h'⟩ := hd
    rw [hb] at hb'; cases hb'
    rcases h' with ⟨rfl, -⟩ | ⟨j, s, rfl, hs, -⟩
    · exact Nat.zero_le _
    · exact (List.getElem?_eq_some_iff.1 hs).1
  · exact ⟨d, t, hd, .inr ⟨hdi, h.resolve_left hdi⟩⟩

theorem AvailAt.here {idom : Array (Option Nat)} {V : Nat → Option Block} {i k : Nat}
    {x : ValueId} (h : AvailAt idom V i k x) : AvailHere idom V i x := by
  obtain ⟨d, t, hd, h | h⟩ := h
  · exact ⟨d, t, hd, .inl h.1⟩
  · exact ⟨d, t, hd, .inr h.2⟩

/-! ## Placeable values -/

/-- `z` is reachable from `x` through the operands of the nodes (`defs`) of `x` and of its e-class
(`alts`). -/
inductive GReach (defs : Std.HashMap ValueId Inst) (alts : Std.HashMap ValueId (List ValueId)) :
    ValueId → ValueId → Prop
  | refl (x : ValueId) : GReach defs alts x x
  | node {x y z : ValueId} {n : Inst} : defs.get? x = some n → y ∈ operands n →
      GReach defs alts y z → GReach defs alts x z
  | alt {x y z m : ValueId} {ms : List ValueId} {n : Inst} : alts.get? x = some ms → m ∈ ms →
      defs.get? m = some n → y ∈ operands n → GReach defs alts y z → GReach defs alts x z

/-- `x` is placeable (module doc): everything reachable from it is known and not bad. -/
def Placed (st : SState) (B : ValueId → Prop) (x : ValueId) : Prop :=
  ∀ z, GReach st.defs st.alts x z → ¬ B z ∧ st.known z = true

theorem Placed.not_bad {st : SState} {B : ValueId → Prop} {x : ValueId} (h : Placed st B x) : ¬ B x :=
  (h x (.refl x)).1

theorem Placed.known {st : SState} {B : ValueId → Prop} {x : ValueId} (h : Placed st B x) :
    st.known x = true :=
  (h x (.refl x)).2

theorem Placed.defs {st : SState} {B : ValueId → Prop} {x : ValueId} (h : Placed st B x) :
    ∀ n, st.defs.get? x = some n → ∀ y ∈ operands n, Placed st B y :=
  fun _ hn _ hy z hz => h z (.node hn hy hz)

theorem Placed.alts {st : SState} {B : ValueId → Prop} {x : ValueId} (h : Placed st B x) :
    ∀ ms, st.alts.get? x = some ms → ∀ m ∈ ms, ∀ n, st.defs.get? m = some n →
      ∀ y ∈ operands n, Placed st B y :=
  fun _ hms _ hm _ hn _ hy z hz => h z (.alt hms hm hn hy hz)

theorem Placed.mk {st : SState} {B : ValueId → Prop} {x : ValueId} (hb : ¬ B x)
    (hk : st.known x = true) (hd : ∀ n, st.defs.get? x = some n → ∀ y ∈ operands n, Placed st B y)
    (ha : ∀ ms, st.alts.get? x = some ms → ∀ m ∈ ms, ∀ n, st.defs.get? m = some n →
      ∀ y ∈ operands n, Placed st B y) : Placed st B x := by
  intro z hz
  cases hz with
  | refl => exact ⟨hb, hk⟩
  | node hn hy hz => exact hd _ hn _ hy z hz
  | alt hms hm hn hy hz => exact ha _ hms _ hm _ hn _ hy z hz

/-- Placeability is kept when the state grows: known values stay known, placeable values do not
become bad, and changed nodes or classes are over values placeable before. -/
theorem Placed.mono {st st' : SState} {B B' : ValueId → Prop}
    (hk : ∀ x, st.known x = true → st'.known x = true)
    (hB : ∀ x, Placed st B x → ¬ B' x)
    (hd : ∀ x n', st'.defs.get? x = some n' →
      st.defs.get? x = some n' ∨ ∀ y ∈ operands n', Placed st B y)
    (ha : ∀ x ms', st'.alts.get? x = some ms' → st.alts.get? x = some ms' ∨
      ∀ m ∈ ms', ∀ n, st'.defs.get? m = some n → ∀ y ∈ operands n, Placed st B y) :
    ∀ x, Placed st B x → Placed st' B' x := by
  have key : ∀ x z, GReach st'.defs st'.alts x z → Placed st B x → Placed st B z := by
    intro x z h
    induction h with
    | refl => exact id
    | node hn hy _ ih =>
      intro hx
      rcases hd _ _ hn with h | h
      · exact ih (hx.defs _ h _ hy)
      · exact ih (h _ hy)
    | alt hms hm hn hy _ ih =>
      intro hx
      rcases ha _ _ hms with h | h
      · rcases hd _ _ hn with h2 | h2
        · exact ih (hx.alts _ h _ hm _ h2 _ hy)
        · exact ih (h2 _ hy)
      · exact ih (h _ hm _ hn _ hy)
  intro x hx z hz
  have := key x z hz hx
  exact ⟨hB z this, hk z this.known⟩

/-! ## Renaming lemmas -/

theorem nodeTy_mapOperands (τ : ValueId → ValueId) (n : Inst) :
    SState.nodeTy (mapOperands τ n) = SState.nodeTy n := by
  simp only [SState.nodeTy, resultTypes_mapOperands]

theorem renameOps_eq (n : Inst) (ops : List ValueId) :
    renameOps n ops = mapOperands (fun y => ((operands n).zip ops).lookup y |>.getD y) n := rfl

/-- Every operand of `renameOps n ops` is the renaming of an operand of `n` at the same position
(`ops` as long as the operands). -/
theorem renameOps_ops {n : Inst} {ops : List ValueId} (hl : (operands n).length = ops.length) :
    ∀ y' ∈ operands (renameOps n ops), ∃ (j : Nat) (y : ValueId), (operands n)[j]? = some y ∧ ops[j]? = some y' := by
  intro y' hy'
  rw [renameOps_eq, operands_mapOperands, List.mem_map] at hy'
  obtain ⟨y, hy, rfl⟩ := hy'
  obtain ⟨j, hj, hl'⟩ := lookup_zip _ _ hl hy
  obtain ⟨z, hz⟩ : ∃ z, ops[j]? = some z := by
    have : j < ops.length := by
      have := (List.getElem?_eq_some_iff.1 hj).1; omega
    exact ⟨_, List.getElem?_eq_getElem this⟩
  rw [hz] at hl'
  exact ⟨j, y, hj, by rw [hz, hl']; rfl⟩

theorem pureTyped_grow {ty ty' : ValueId → Option Ty} {f : Function} {n : Inst}
    (hp : isPure n = true) (h : pureTyped ty f n = true)
    (hg : ∀ y t, ty y = some t → ty' y = some t) : pureTyped ty' f n = true := by
  rw [← h]; symm
  refine pureTyped_congr (fun y hy => ?_) rfl rfl
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (pureTyped_ops hp h y hy)
  rw [ht, hg y t ht]

theorem known_iff {st : SState} {x : ValueId} :
    st.known x = true ↔ (st.defs.get? x).isSome ∨ st.avail.contains x = true := by
  simp only [SState.known, Bool.or_eq_true, hm_contains_iff]

/-! ## The state facts of `materialize` -/

/-- The state facts `materialize` needs and keeps (module doc), for the output view `V` and the
bad values `B`. -/
structure MInv (f : Function) (V : Nat → Option Block) (B : ValueId → Prop) (st : SState) :
    Prop where
  fn : st.fn = f
  maxLt : maxValue f < st.next
  knownLt : ∀ x, st.known x = true → x < st.next
  typesFresh : ∀ x, st.next ≤ x → st.types.get? x = none
  defsTy : ∀ x n, st.defs.get? x = some n → isPure n = true ∧
    pureTyped (fun y => st.types.get? y) f n = true ∧ st.types.get? x = SState.nodeTy n
  altsKnown : ∀ x ms, st.alts.get? x = some ms → st.known x = true
  availDef : ∀ x d, st.avail.get? x = some d → ¬ B x → ∃ t, DefAt V x d t
  defAvail : ∀ x d t, DefAt V x d t → st.avail.get? x = some d
  newBig : ∀ x n, st.defs.get? x = some n → st.avail.contains x = false → ¬ B x → maxValue f < x
  badLe : ∀ x, B x → x ≤ maxValue f
  uniq : ∀ x d t d' t', DefAt V x d t → DefAt V x d' t' → d = d' ∧ t = t'

/-- An emitted statement at index `k` of block `bi`: `r = n'`, the renaming of an allowed node,
recorded in the graph, with available placeable operands. -/
def NewOk (idom : Array (Option Nat)) (V : Nat → Option Block) (bi k : Nat)
    (allowed : Inst → Bool) (B : ValueId → Prop) (st : SState) (s : Stmt) : Prop :=
  ∃ r n', s = { results := [r], inst := n' } ∧ st.defs.get? r = some n' ∧
    st.avail.get? r = some bi ∧ ¬ B r ∧ (∃ n τ, allowed n = true ∧ n' = mapOperands τ n) ∧
    ∀ y ∈ operands n', AvailAt idom V bi k y ∧ Placed st B y

/-- How the state moves while materialising (only the graph and output fields change). -/
structure MStep (bi : Nat) (st st' : SState) (new : List Stmt) : Prop where
  shape : ∃ d a t c nx, st' = { st with defs := d, avail := a, types := t, cost := c, next := nx }
  next : st.next ≤ st'.next
  types : ∀ y t, st.types.get? y = some t → st'.types.get? y = some t
  typesKnown : ∀ y, st.known y = true → st'.types.get? y = st.types.get? y
  avail : ∀ y d, st.avail.get? y = some d → st'.avail.get? y = some d
  availNew : ∀ y d, st'.avail.get? y = some d →
    st.avail.get? y = some d ∨ (d = bi ∧ ∃ s ∈ new, y ∈ s.results)
  defsKeep : ∀ y n, st.defs.get? y = some n → st.avail.contains y = true →
    st'.defs.get? y = some n
  defsOld : ∀ y, (st.defs.get? y).isSome → (st'.defs.get? y).isSome
  fresh : ∀ y n, st'.defs.get? y = some n → st.defs.get? y = some n ∨ maxValue st.fn < y

theorem MStep.known {bi : Nat} {st st' : SState} {new : List Stmt} (h : MStep bi st st' new) :
    ∀ x, st.known x = true → st'.known x = true := by
  intro x hx
  rcases known_iff.1 hx with hx | hx
  · exact known_iff.2 (.inl (h.defsOld x hx))
  · obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 hx)
    exact known_iff.2 (.inr ((hm_contains_iff _ _).2 (by rw [h.avail x d hd]; rfl)))

theorem MStep.refl (bi : Nat) (st : SState) : MStep bi st st [] :=
  ⟨⟨_, _, _, _, _, rfl⟩, Nat.le_refl _, fun _ _ h => h, fun _ _ => rfl, fun _ _ h => h,
   fun _ _ h => .inl h, fun _ _ h _ => h, fun _ h => h, fun _ _ h => .inl h⟩

theorem MStep.trans {bi : Nat} {st st1 st2 : SState} {n1 n2 : List Stmt} (h1 : MStep bi st st1 n1)
    (h2 : MStep bi st1 st2 n2) : MStep bi st st2 (n1 ++ n2) := by
  refine ⟨?_, Nat.le_trans h1.next h2.next, fun y t h => h2.types y t (h1.types y t h),
    fun y hy => (h2.typesKnown y (h1.known y hy)).trans (h1.typesKnown y hy),
    fun y d h => h2.avail y d (h1.avail y d h), fun y d h => ?_, fun y n h ha => ?_,
    fun y h => h2.defsOld y (h1.defsOld y h), fun y n h => ?_⟩
  · obtain ⟨d1, a1, t1, c1, x1, rfl⟩ := h1.shape
    obtain ⟨d2, a2, t2, c2, x2, rfl⟩ := h2.shape
    exact ⟨d2, a2, t2, c2, x2, rfl⟩
  · rcases h2.availNew y d h with h | ⟨rfl, s, hs, hy⟩
    · rcases h1.availNew y d h with h | ⟨rfl, s, hs, hy⟩
      · exact .inl h
      · exact .inr ⟨rfl, s, List.mem_append_left _ hs, hy⟩
    · exact .inr ⟨rfl, s, List.mem_append_right _ hs, hy⟩
  · refine h2.defsKeep y n (h1.defsKeep y n h ha) ?_
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 ha)
    exact (hm_contains_iff _ _).2 (by rw [h1.avail y d hd]; rfl)
  · have hfn : st1.fn = st.fn := by obtain ⟨_, _, _, _, _, e⟩ := h1.shape; rw [e]
    rcases h2.fresh y n h with h | h
    · exact h1.fresh y n h
    · exact .inr (by rw [← hfn]; exact h)

theorem NewOk.mono {idom : Array (Option Nat)} {V : Nat → Option Block} {bi k : Nat}
    {allowed : Inst → Bool} {B : ValueId → Prop} {st st' : SState} {s : Stmt} {more : List Stmt}
    (h : NewOk idom V bi k allowed B st s) (hs : MStep bi st st' more)
    (hg : ∀ y, Placed st B y → Placed st' B y) :
    NewOk idom (emitV V bi more) bi k allowed B st' s := by
  obtain ⟨r, n', rfl, hd, ha, hrb, hal, hops⟩ := h
  refine ⟨r, n', rfl, hs.defsKeep r n' hd ((hm_contains_iff _ _).2 (by rw [ha]; rfl)),
    hs.avail r bi ha, hrb, hal, fun y hy => ⟨(hops y hy).1.emit bi more, hg y (hops y hy).2⟩⟩

theorem NewOk.weakenB {idom : Array (Option Nat)} {V : Nat → Option Block} {bi k : Nat}
    {allowed : Inst → Bool} {B B' : ValueId → Prop} {st : SState} {s : Stmt}
    (h : NewOk idom V bi k allowed B st s) (hB : ∀ y, B' y → B y) :
    NewOk idom V bi k allowed B' st s := by
  obtain ⟨r, n', rfl, hd, ha, hrb, hal, hops⟩ := h
  have hg : ∀ y, Placed st B y → Placed st B' y :=
    Placed.mono (fun _ h => h) (fun y hy hb => hy.not_bad (hB y hb)) (fun _ _ h => .inl h)
      (fun _ _ h => .inl h)
  exact ⟨r, n', rfl, hd, ha, fun h => hrb (hB r h), hal, fun y hy => ⟨(hops y hy).1, hg y (hops y hy).2⟩⟩

theorem NewOk.mono' {idom : Array (Option Nat)} {V : Nat → Option Block} {bi k : Nat}
    {allowed : Inst → Bool} {B : ValueId → Prop} {st st' : SState} {s : Stmt} {more : List Stmt}
    (h : NewOk idom V bi k allowed B st s)
    (hd : ∀ y n, st.defs.get? y = some n → st.avail.contains y = true → st'.defs.get? y = some n)
    (ha : ∀ y d, st.avail.get? y = some d → st'.avail.get? y = some d)
    (hg : ∀ y, Placed st B y → Placed st' B y) :
    NewOk idom (emitV V bi more) bi k allowed B st' s := by
  obtain ⟨r, n', rfl, hd', ha', hrb, hal, hops⟩ := h
  refine ⟨r, n', rfl, hd r n' hd' ((hm_contains_iff _ _).2 (by rw [ha']; rfl)),
    ha r bi ha', hrb, hal, fun y hy => ⟨(hops y hy).1.emit bi more, hg y (hops y hy).2⟩⟩

/-- A run of `materialize` steps (module doc): the state facts, placeability, the state change and
the emitted statements. -/
structure MRun (f : Function) (idom : Array (Option Nat)) (allowed : Inst → Bool) (bi : Nat)
    (B : ValueId → Prop) (V : Nat → Option Block) (st st' : SState) (new : List Stmt) : Prop where
  inv : MInv f (emitV V bi new) B st'
  good : ∀ y, Placed st B y → Placed st' B y
  step : MStep bi st st' new
  nodes : ∀ y n', st'.defs.get? y = some n' →
    st.defs.get? y = some n' ∨ ∀ z ∈ operands n', Placed st' B z
  stmts : ∀ b, V bi = some b → ∀ j s, new[j]? = some s →
    NewOk idom (emitV V bi new) bi (b.body.length + j) allowed B st' s

theorem MRun.refl {f : Function} {idom : Array (Option Nat)} {allowed : Inst → Bool} {bi : Nat}
    {B : ValueId → Prop} {V : Nat → Option Block} {st : SState} (h : MInv f V B st) :
    MRun f idom allowed bi B V st st [] :=
  ⟨by rw [emitV_nil]; exact h, fun _ h => h, MStep.refl bi st, fun _ _ h => .inl h,
   fun _ _ j s hs => by simp at hs⟩

theorem MRun.trans {f : Function} {idom : Array (Option Nat)} {allowed : Inst → Bool} {bi : Nat}
    {B : ValueId → Prop} {V : Nat → Option Block} {st st1 st2 : SState} {n1 n2 : List Stmt}
    (h1 : MRun f idom allowed bi B V st st1 n1) (h2 : MRun f idom allowed bi B (emitV V bi n1) st1 st2 n2) :
    MRun f idom allowed bi B V st st2 (n1 ++ n2) := by
  refine ⟨by rw [← emitV_append]; exact h2.inv, fun y h => h2.good y (h1.good y h),
    h1.step.trans h2.step, fun y n' hy => ?_, fun b hb j s hs => ?_⟩
  · rcases h2.nodes y n' hy with h | h
    · rcases h1.nodes y n' h with h' | h'
      · exact .inl h'
      · exact .inr fun z hz => h2.good z (h' z hz)
    · exact .inr h
  rw [← emitV_append]
  rcases Nat.lt_or_ge j n1.length with hj | hj
  · rw [List.getElem?_append_left hj] at hs
    exact (h1.stmts b hb j s hs).mono h2.step h2.good
  · rw [List.getElem?_append_right hj] at hs
    have hb1 : emitV V bi n1 bi = some { b with body := b.body ++ n1 } := by simp [emitV, hb]
    have := h2.stmts _ hb1 (j - n1.length) s hs
    simp only [List.length_append] at this
    rwa [show b.body.length + n1.length + (j - n1.length) = b.body.length + j by omega] at this

/-! ## One emission -/

section Emit

variable {f : Function} {idom : Array (Option Nat)} {allowed : Inst → Bool} {bi : Nat}
  {B : ValueId → Prop} {V : Nat → Option Block}

theorem hm_get?_insert' {β : Type} (m : Std.HashMap ValueId β) (k a : ValueId) (v : β) :
    (m.insert k v).get? a = if k = a then some v else m.get? a := hm_get?_insert m k a v

/-- Bumping the fresh-value counter keeps the state facts. -/
theorem MInv.bump {st : SState} (h : MInv f V B st) :
    MInv f V B ({ st with next := st.next + 1 } : SState) where
  fn := h.fn
  maxLt := Nat.lt_succ_of_lt h.maxLt
  knownLt x hx := Nat.lt_succ_of_lt (h.knownLt x hx)
  typesFresh x hx := h.typesFresh x (Nat.le_of_succ_le hx)
  defsTy := h.defsTy
  altsKnown := h.altsKnown
  availDef := h.availDef
  defAvail := h.defAvail
  newBig := h.newBig
  badLe := h.badLe
  uniq := h.uniq

/-- Emitting `r = n'` (a copy of `x`) at the end of block `bi`. -/
theorem emit_run {st : SState} {x r : ValueId} {n n' : Inst} {τ : ValueId → ValueId} {b : Block}
    (hI : MInv f V B st) (hb : V bi = some b)
    (hrn : r < st.next) (hrmax : maxValue f < r) (hra : st.avail.contains r = false)
    (hrd : ∀ d t, ¬ DefAt V r d t)
    (hrb : ¬ B r) (hrt : st.types.get? r = none ∨ st.types.get? r = st.types.get? x)
    (hrk : st.known r = true → st.types.get? r = st.types.get? x)
    (hp : isPure n' = true) (hty : pureTyped (fun y => st.types.get? y) f n' = true)
    (htx : st.types.get? x = SState.nodeTy n') (hsome : (SState.nodeTy n').isSome)
    (hal : allowed n = true) (hn' : n' = mapOperands τ n)
    (hops : ∀ y ∈ operands n', AvailHere idom V bi y ∧ Placed st B y)
    (hralts : ∀ ms, st.alts.get? r = some ms → ∀ m ∈ ms, ∀ n, st.defs.get? m = some n →
      ∀ y ∈ operands n, Placed st B y) :
    MRun f idom allowed bi B V st (st.emit bi x r n') [{ results := [r], inst := n' }] ∧
      Placed (st.emit bi x r n') B r ∧
      AvailHere idom (emitV V bi [{ results := [r], inst := n' }]) bi r ∧
      (st.emit bi x r n').types.get? r = st.types.get? x := by
  obtain ⟨ed, ea, et, en, eal, emm, efn, -, -, -, -⟩ := emit_fields st bi x r n'
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hsome
  rw [ht] at htx
  have et' : (st.emit bi x r n').types = st.types.insert r t := by rw [et, htx]
  generalize hst' : st.emit bi x r n' = st' at ed ea et' en eal emm efn ⊢
  have hdefs : ∀ y, st'.defs.get? y = if r = y then some n' else st.defs.get? y := by
    intro y; rw [ed, hm_get?_insert']
  have havail : ∀ y, st'.avail.get? y = if r = y then some bi else st.avail.get? y := by
    intro y; rw [ea, hm_get?_insert']
  have htypes : ∀ y, st'.types.get? y = if r = y then some t else st.types.get? y := by
    intro y; rw [et', hm_get?_insert']
  have hrav : st.avail.get? r = none := by
    rw [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.getElem?_eq_none_of_contains_eq_false hra
  have tgrow : ∀ y u, st.types.get? y = some u → st'.types.get? y = some u := by
    intro y u hy
    rw [htypes]; split
    · rename_i hry; subst hry
      rcases hrt with h | h
      · rw [h] at hy; cases hy
      · rw [h, htx] at hy; exact hy
    · exact hy
  have agrow : ∀ y d, st.avail.get? y = some d → st'.avail.get? y = some d := by
    intro y d hy
    rw [havail]; split
    · rename_i hry; subst hry; rw [hrav] at hy; cases hy
    · exact hy
  have kgrow : ∀ y, st.known y = true → st'.known y = true := by
    intro y hy
    rcases known_iff.1 hy with h | h
    · refine known_iff.2 (.inl ?_)
      rw [hdefs]; split <;> simp_all
    · refine known_iff.2 (.inr ?_)
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 h)
      exact (hm_contains_iff _ _).2 (by rw [agrow y d hd]; rfl)
  have hgood : ∀ y, Placed st B y → Placed st' B y := by
    refine Placed.mono kgrow (fun y hy => hy.not_bad) (fun y m hm => ?_) (fun y ms hms => ?_)
    · rw [hdefs] at hm; split at hm
      · cases hm; exact .inr fun z hz => (hops z hz).2
      · exact .inl hm
    · rw [eal] at hms; exact .inl hms
  have hdefV : ∀ y d t', DefAt (emitV V bi [({ results := [r], inst := n' } : Stmt)]) y d t' → DefAt V y d t' ∨ (y = r ∧ d = bi ∧ t' = b.body.length + 1) := by
    intro y d t' h
    rcases h.of_emit with h | ⟨b0, hb0, rfl, j, s0, rfl, hs0, hy⟩
    · exact .inl h
    · rw [hb] at hb0; cases hb0
      have hj : j = 0 := by
        rcases j with _ | j
        · rfl
        · simp at hs0
      subst hj
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs0
      subst hs0
      simp only [List.mem_singleton] at hy
      exact .inr ⟨hy, rfl, rfl⟩
  have hdefR : DefAt (emitV V bi [({ results := [r], inst := n' } : Stmt)]) r bi (b.body.length + 1) := by
    refine ⟨{ b with body := b.body ++ [({ results := [r], inst := n' } : Stmt)] }, by simp [emitV, hb], .inr ⟨b.body.length, ({ results := [r], inst := n' } : Stmt), rfl, ?_, ?_⟩⟩
    · simp
    · simp
  have hinv : MInv f (emitV V bi [({ results := [r], inst := n' } : Stmt)]) B st' := by
    refine ⟨by rw [efn]; exact hI.fn, by rw [en]; exact hI.maxLt, fun y hy => ?_, fun y hy => ?_,
      fun y m hm => ?_, fun y ms hms => ?_, fun y d hy hby => ?_, fun y d t' hy => ?_,
      fun y m hm ha hby => ?_, hI.badLe, fun y d t1 d' t2 h1 h2 => ?_⟩
    · rw [en]
      rcases known_iff.1 hy with h | h
      · rw [hdefs] at h; split at h
        · rename_i hry; subst hry; exact hrn
        · exact hI.knownLt y (known_iff.2 (.inl h))
      · rw [ea, hm_contains_insert'] at h
        rcases h with rfl | h
        · exact hrn
        · exact hI.knownLt y (known_iff.2 (.inr h))
    · rw [en] at hy; rw [htypes]; split
      · rename_i hry; rw [← hry] at hy; exact absurd hy (Nat.not_le.2 hrn)
      · exact hI.typesFresh y hy
    · rw [hdefs] at hm; split at hm
      · rename_i hry; subst hry; cases hm
        refine ⟨hp, pureTyped_grow hp hty tgrow, by rw [htypes, ite_eq_left rfl]; exact ht.symm⟩
      · rename_i hry
        obtain ⟨h1, h2, h3⟩ := hI.defsTy y m hm
        exact ⟨h1, pureTyped_grow h1 h2 tgrow, by rw [htypes, ite_eq_right hry]; exact h3⟩
    · rw [eal] at hms; exact kgrow y (hI.altsKnown y ms hms)
    · rw [havail] at hy; split at hy
      · rename_i hry; subst hry; cases hy; exact ⟨_, hdefR⟩
      · obtain ⟨t', h⟩ := hI.availDef y d hy hby; exact ⟨t', h.emit bi [({ results := [r], inst := n' } : Stmt)]⟩
    · rcases hdefV y d t' hy with h | ⟨rfl, rfl, rfl⟩
      · exact agrow y d (hI.defAvail y d t' h)
      · rw [havail, ite_eq_left rfl]
    · rw [hdefs] at hm; split at hm
      · rename_i hry; subst hry
        rw [ea, Std.HashMap.contains_insert] at ha; simp at ha
      · have ha' : st.avail.contains y = false := by
          cases hc : st.avail.contains y with
          | false => rfl
          | true =>
            obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 hc)
            have := agrow y d hd
            rw [← Bool.not_eq_true, hm_contains_iff, this] at ha; simp at ha
        exact hI.newBig y m hm ha' hby
    · rcases hdefV y d t1 h1 with h1 | ⟨hy1, hd1, ht1⟩
      · rcases hdefV y d' t2 h2 with h2 | ⟨hy2, hd2, ht2⟩
        · exact hI.uniq _ _ _ _ _ h1 h2
        · rw [hy2] at h1; exact absurd h1 (hrd _ _)
      · rcases hdefV y d' t2 h2 with h2 | ⟨hy2, hd2, ht2⟩
        · rw [hy1] at h2; exact absurd h2 (hrd _ _)
        · exact ⟨hd1.trans hd2.symm, ht1.trans ht2.symm⟩
  have hstep : MStep bi st st' [({ results := [r], inst := n' } : Stmt)] := by
    refine ⟨⟨st.defs.insert r n', st.avail.insert r bi, st'.types, st'.cost, st.next, ?_⟩,
      by rw [en]; exact Nat.le_refl _, tgrow, fun y hy => ?_, agrow, fun y d hy => ?_,
      fun y m hm ha => ?_, fun y hy => ?_, fun y m hm => ?_⟩
    · rw [← hst']; rfl
    · rw [htypes]; split
      · rename_i hry; subst hry; rw [hrk hy, htx]
      · rfl
    · rw [havail] at hy; split at hy
      · rename_i hry; subst hry; cases hy; exact .inr ⟨rfl, ({ results := [r], inst := n' } : Stmt), by simp, by simp⟩
      · exact .inl hy
    · rw [hdefs]; split
      · rename_i hry; subst hry; rw [ha] at hra; cases hra
      · exact hm
    · rw [hdefs]; split <;> simp_all
    · rw [hdefs] at hm; split at hm
      · rename_i hry; subst hry; exact .inr (by rw [hI.fn]; exact hrmax)
      · exact .inl hm
  have hgr : Placed st' B r := by
    refine Placed.mk hrb (known_iff.2 (.inr (by rw [ea, hm_contains_insert']; exact .inl rfl)))
      (fun m hm y hy => ?_) (fun ms hms m hm n0 hn0 y hy => ?_)
    · rw [hdefs, ite_eq_left rfl] at hm; cases hm; exact hgood y (hops y hy).2
    · rw [eal] at hms
      rw [hdefs] at hn0; split at hn0
      · cases hn0; exact hgood y (hops y hy).2
      · exact hgood y (hralts ms hms m hm n0 hn0 y hy)
  refine ⟨⟨hinv, hgood, hstep, fun y m hm => ?_, fun b0 hb0 j s0 hs0 => ?_⟩, hgr, ⟨bi, _, hdefR, .inl rfl⟩,
    by rw [htypes, ite_eq_left rfl, htx]⟩
  · rw [hdefs] at hm; split at hm
    · cases hm; exact .inr fun z hz => hgood z (hops z hz).2
    · exact .inl hm
  rw [hb] at hb0; cases hb0
  have hj : j = 0 := by
    rcases j with _ | j
    · rfl
    · simp at hs0
  subst hj
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hs0
  subst hs0
  refine ⟨r, n', rfl, by rw [hdefs, ite_eq_left rfl], by rw [havail, ite_eq_left rfl], hrb, ⟨n, τ, hal, hn'⟩,
    fun y hy => ⟨?_, hgood y (hops y hy).2⟩⟩
  simpa using ((hops y hy).1.at_end hb).emit bi [({ results := [r], inst := n' } : Stmt)]

end Emit

/-! ## `materialize` -/

theorem foldlM_option_mem {α β : Type} (g : β → α → Option β) (I : List α → β → Prop)
    (l : List α) (hstep : ∀ pre a rest c c', pre ++ a :: rest = l → I pre c → g c a = some c' →
      I (pre ++ [a]) c') :
    ∀ (l' pre : List α) (b b' : β), pre ++ l' = l → I pre b → l'.foldlM g b = some b' → I l b' := by
  intro l'
  induction l' with
  | nil =>
    intro pre b b' hl hb h
    simp only [List.foldlM, pure, Option.some.injEq] at h
    subst h; simpa [← hl] using hb
  | cons a as ih =>
    intro pre b b' hl hb h
    simp only [List.foldlM] at h
    cases hg : g b a with
    | none => rw [hg] at h; cases h
    | some c =>
      rw [hg] at h
      exact ih (pre ++ [a]) c b' (by simpa using hl) (hstep pre a as b c hl hb hg) h

theorem Placed.congr {st st' : SState} {B : ValueId → Prop} (hd : st'.defs = st.defs)
    (ha : st'.alts = st.alts) (hv : st'.avail = st.avail) {x : ValueId} (h : Placed st B x) :
    Placed st' B x :=
  Placed.mono (fun y hy => by simpa [SState.known, hd, hv] using hy) (fun _ h => h.not_bad)
    (fun y n hn => .inl (by rw [← hd]; exact hn)) (fun y ms hms => .inl (by rw [← ha]; exact hms))
    x h

theorem Placed.bump {st : SState} {B : ValueId → Prop} {k : Nat} {x : ValueId} (h : Placed st B x) :
    Placed ({ st with next := k } : SState) B x :=
  Placed.congr (st := st) (st' := ({ st with next := k } : SState)) rfl rfl rfl h

theorem MRun.bump {f : Function} {idom : Array (Option Nat)} {allowed : Inst → Bool} {bi : Nat}
    {B : ValueId → Prop} {V : Nat → Option Block} {st : SState} (h : MInv f V B st) :
    MRun f idom allowed bi B V st ({ st with next := st.next + 1 } : SState) [] :=
  ⟨by rw [emitV_nil]; exact h.bump, fun _ h => h.bump,
   ⟨⟨_, _, _, _, _, rfl⟩, Nat.le_succ _, fun _ _ h => h, fun _ _ => rfl, fun _ _ h => h,
    fun _ _ h => .inl h, fun _ _ h _ => h, fun _ h => h, fun _ _ h => .inl h⟩, fun _ _ h => .inl h,
   fun _ _ j s hs => by simp at hs⟩

section Mat

variable {f : Function} {cfg : Cfg} {allowed : Inst → Bool} {bi : Nat} {B : ValueId → Prop}

/-- What `materialize` of a placeable value does (module doc). -/
def MatOk (f : Function) (cfg : Cfg) (allowed : Inst → Bool) (bi : Nat) (B : ValueId → Prop)
    (V : Nat → Option Block) (st : SState) (out : Array Stmt) (x x' : ValueId) (st' : SState)
    (out' : Array Stmt) : Prop :=
  ∃ new, out'.toList = out.toList ++ new ∧ MRun f cfg.idom allowed bi B V st st' new ∧
    Placed st' B x' ∧ AvailHere cfg.idom (emitV V bi new) bi x' ∧ st'.types.get? x' = st.types.get? x

theorem clone_ok {fuel : Nat}
    (ih : ∀ st out x x' st' out' V b, MInv f V B st → V bi = some b → Placed st B x →
      materialize cfg allowed bi fuel (st, out) x = some (x', st', out') →
      MatOk f cfg allowed bi B V st out x x' st' out')
    {st : SState} {out : Array Stmt} {x x' : ValueId} {st' : SState} {out' : Array Stmt}
    {V : Nat → Option Block} {b : Block} (hI : MInv f V B st) (hb : V bi = some b)
    (hx : Placed st B x)
    (hc : materialize.clone cfg allowed bi fuel st out x = some (x', st', out')) :
    MatOk f cfg allowed bi B V st out x x' st' out' := by
  rw [materialize.clone] at hc
  split at hc
  · cases hc
  rename_i n hxn
  split at hc
  · cases hc
  rename_i hchk
  simp only [Bool.or_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none, not_or] at hchk
  obtain ⟨⟨hal, hty⟩, htx⟩ := hchk
  have hal' : allowed n = true := by simpa using hal
  have hty' : st.typedNode n = true := by simpa using hty
  simp only [SState.typedNode, Bool.and_eq_true] at hty'
  obtain ⟨hpure, hptyped⟩ := hty'
  rw [hI.fn] at hptyped
  have hopty : ∀ y ∈ operands n, (st.types.get? y).isSome := pureTyped_ops hpure hptyped
  -- the operands
  let I : List ValueId → SState × Array Stmt × Array ValueId → Prop := fun pre acc =>
    ∃ new1, acc.2.1.toList = out.toList ++ new1 ∧
      MRun f cfg.idom allowed bi B V st acc.1 new1 ∧ acc.2.2.toList.length = pre.length ∧
      ∀ (j : Nat) (y : ValueId), pre[j]? = some y → ∃ y', acc.2.2.toList[j]? = some y' ∧
        Placed acc.1 B y' ∧ AvailHere cfg.idom (emitV V bi new1) bi y' ∧
          acc.1.types.get? y' = st.types.get? y
  have hfold := foldlM_option_mem (I := I) (l := operands n)
    (g := fun (acc : SState × Array Stmt × Array ValueId) y =>
      match materialize cfg allowed bi fuel (acc.1, acc.2.1) y with
      | none => none
      | some (y', st, out) => some (st, out, acc.2.2.push y'))
    (by
      intro pre a rest c c' hl hI' hg
      obtain ⟨new1, hout1, hrun1, hlen1, hops1⟩ := hI'
      split at hg
      · cases hg
      rename_i y' st2 out2 hm
      cases hg
      have ha : a ∈ operands n := by rw [← hl]; simp
      have hga : Placed c.1 B a := hrun1.good a (hx.defs n hxn a ha)
      obtain ⟨new2, hout2, hrun2, hg2, hh2, ht2⟩ := ih _ _ _ _ _ _ _
        { b with body := b.body ++ new1 } hrun1.inv (by simp [emitV, hb]) hga hm
      refine ⟨new1 ++ new2, by rw [hout2, hout1]; simp, hrun1.trans hrun2, by simp [hlen1],
        fun j y hj => ?_⟩
      simp only [Array.toList_push]
      by_cases hjl : j < pre.length
      · rw [List.getElem?_append_left hjl] at hj
        obtain ⟨u', h1, h2, h3, h4⟩ := hops1 j y hj
        refine ⟨u', by rw [List.getElem?_append_left (by rw [hlen1]; exact hjl)]; exact h1,
          hrun2.good u' h2, by rw [← emitV_append]; exact h3.emit bi new2, ?_⟩
        have hy : y ∈ operands n := by
          rw [← hl]; exact List.mem_append_left _ (List.mem_of_getElem? hj)
        obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (hopty y hy)
        rw [ht] at h4 ⊢; exact hrun2.step.types u' t h4
      · have hjl' : j = pre.length := by
          have := (List.getElem?_eq_some_iff.1 hj).1
          simp at this; omega
        subst hjl'
        simp at hj; subst hj
        refine ⟨y', by simp [← hlen1], hg2, by rw [← emitV_append]; exact hh2, ?_⟩
        obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (hopty _ ha)
        rw [ht] at ⊢; rw [ht2]; exact hrun1.step.types _ t ht)
    (operands n) [] (st, out, #[]) 
  split at hc
  · cases hc
  rename_i st1 out1 ops hf
  obtain ⟨new1, hout1, hrun1, hlen, hops⟩ := hfold _ rfl ⟨[], by simp, MRun.refl hI, rfl,
    fun j u hj => by simp at hj⟩ hf
  dsimp only at hc hout1 hrun1 hlen hops
  split at hc
  · cases hc
  rename_i hcyc
  -- the renaming of the operands
  let τ := fun y => (((operands n).zip ops.toList).lookup y).getD y
  have hren : renameOps n ops.toList = mapOperands τ n := rfl
  have hτ : ∀ y ∈ operands n, Placed st1 B (τ y) ∧ AvailHere cfg.idom (emitV V bi new1) bi (τ y) ∧
      st1.types.get? (τ y) = st.types.get? y := by
    intro y hy
    obtain ⟨j, hj, hl⟩ := lookup_zip (operands n) ops.toList hlen.symm hy
    obtain ⟨y', h1', h2', h3', h4'⟩ := hops j y hj
    have : τ y = y' := by simp only [τ, hl, h1']; rfl
    rw [this]; exact ⟨h2', h3', h4'⟩
  have hb1 : emitV V bi new1 bi = some { b with body := b.body ++ new1 } := by simp [emitV, hb]
  have hp' : isPure (renameOps n ops.toList) = true := by rw [hren, isPure_mapOperands]; exact hpure
  have hnty : SState.nodeTy (renameOps n ops.toList) = SState.nodeTy n := by
    rw [hren, nodeTy_mapOperands]
  have hxty : st.types.get? x = SState.nodeTy n := (hI.defsTy x n hxn).2.2
  obtain ⟨tx, htx'⟩ := Option.isSome_iff_exists.1 (Option.isSome_iff_ne_none.2 htx)
  have hty1 : ∀ st2 : SState, (∀ y t, st1.types.get? y = some t → st2.types.get? y = some t) →
      pureTyped (fun y => st2.types.get? y) f (renameOps n ops.toList) = true := by
    intro st2 hg2
    rw [hren, pureTyped_mapOperands]
    rw [← hptyped]
    refine pureTyped_congr (fun y hy => ?_) rfl rfl
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (hopty y hy)
    simp only [Function.comp]
    rw [ht, hg2 _ t (by rw [(hτ y hy).2.2, ht])]
  have hops' : ∀ y ∈ operands (renameOps n ops.toList),
      AvailHere cfg.idom (emitV V bi new1) bi y ∧ Placed st1 B y := by
    intro y hy
    rw [hren, operands_mapOperands, List.mem_map] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    exact ⟨(hτ u hu).2.1, (hτ u hu).1⟩
  have hx1 : st1.types.get? x = some tx := hrun1.step.types x tx htx'
  split at hc
  · -- a fresh copy of the available `x`
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    have hI1 := hrun1.inv.bump
    have hnext : st1.avail.contains st1.next = false := by
      cases hc : st1.avail.contains st1.next with
      | false => rfl
      | true =>
        exact absurd (hrun1.inv.knownLt _ (known_iff.2 (.inr hc))) (Nat.lt_irrefl _)
    obtain ⟨hrun2, hg2, hh2, ht2⟩ := emit_run (V := emitV V bi new1) (idom := cfg.idom)
      (allowed := allowed) (x := x) (n := n) (τ := τ) hI1 hb1 (Nat.lt_succ_self _)
      hrun1.inv.maxLt hnext
      (fun d t hd => by
        have h2 := (hm_contains_iff _ _).2 (by rw [hrun1.inv.defAvail _ d t hd]; rfl)
        rw [hnext] at h2; cases h2)
      (fun hB => absurd (Nat.lt_of_lt_of_le hrun1.inv.maxLt (hrun1.inv.badLe _ hB)) (Nat.lt_irrefl _))
      (.inl (hrun1.inv.typesFresh _ (Nat.le_refl _)))
      (fun hk => absurd (hrun1.inv.knownLt _ hk) (Nat.lt_irrefl _)) hp' (hty1 _ (fun _ _ h => h))
      (by simp only; rw [hx1, hnty, ← hxty, htx']) (by rw [hnty, ← hxty, htx']; rfl) hal' hren
      (fun y hy => ⟨(hops' y hy).1, (hops' y hy).2.bump⟩)
      (fun ms hms => by
        have := hrun1.inv.altsKnown _ ms hms
        have := hrun1.inv.knownLt _ this; simp at this)
    rw [← emitV_nil (emitV V bi new1) bi] at hrun2
    have hall := hrun1.trans ((MRun.bump hrun1.inv).trans hrun2)
    simp only [List.nil_append] at hall
    refine ⟨new1 ++ [_], by simp [hout1], hall, hg2, by rw [← emitV_append]; exact hh2, ?_⟩
    rw [ht2]; simp only; rw [hx1, htx']
  · -- the virtual `x`
    rename_i hwas
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    have hxa1 : st1.avail.contains x = false := by
      simp only [Bool.not_eq_true] at hwas
      simp only [hwas, Bool.not_false, Bool.true_and, Bool.not_eq_true] at hcyc
      exact hcyc
    have hgx1 := hrun1.good x hx
    obtain ⟨hrun2, -, hh2, ht2⟩ := emit_run (V := emitV V bi new1) (idom := cfg.idom)
      (allowed := allowed) (x := x) (n := n) (τ := τ) hrun1.inv hb1
      (Nat.lt_of_lt_of_le (hI.knownLt x hx.known) hrun1.step.next)
      (by
        refine hI.newBig x n hxn ?_ hx.not_bad
        cases hc : st.avail.contains x with
        | false => rfl
        | true =>
          obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 hc)
          have h3 := (hm_contains_iff _ _).2 (by rw [hrun1.step.avail x d hd]; rfl)
          rw [hxa1] at h3; cases h3)
      hxa1
      (fun d t hd => by
        have h2 := (hm_contains_iff _ _).2 (by rw [hrun1.inv.defAvail _ d t hd]; rfl)
        rw [hxa1] at h2; cases h2)
      hx.not_bad (.inr rfl) (fun _ => rfl) hp' (hty1 _ (fun _ _ h => h)) (by rw [hx1, hnty, ← hxty, htx'])
      (by rw [hnty, ← hxty, htx']; rfl) hal' hren hops' (hgx1.alts)
    refine ⟨new1 ++ [_], by simp [hout1], hrun1.trans hrun2, hrun2.good x hgx1,
      by rw [← emitV_append]; exact hh2, ?_⟩
    rw [ht2, hx1, htx']

/-- **`materialize` of a placeable value** (module doc). -/
theorem mat_spec : ∀ fuel st out x x' st' out' V b, MInv f V B st → V bi = some b →
    Placed st B x → materialize cfg allowed bi fuel (st, out) x = some (x', st', out') →
    MatOk f cfg allowed bi B V st out x x' st' out' := by
  intro fuel
  induction fuel with
  | zero => intro st out x x' st' out' V b _ _ _ h; simp [materialize] at h
  | succ fuel ih =>
    intro st out x x' st' out' V b hI hb hx h
    rw [materialize] at h
    split at h
    · rename_i d hd
      split at h
      · rename_i hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp only [Bool.and_eq_true] at hcond
        obtain ⟨t, ht⟩ := hI.availDef x d hd hx.not_bad
        refine ⟨[], by simp, MRun.refl hI, hx, ⟨d, t, by rw [emitV_nil]; exact ht, ?_⟩, rfl⟩
        by_cases hdb : d = bi
        · exact .inl hdb
        · exact .inr (dominates_sound hcond.1)
      · exact clone_ok ih hI hb hx h
    · exact clone_ok ih hI hb hx h

/-- `materializeAll` of placeable values: every value is renamed to a placeable value of the same
type available at the end of the block. -/
theorem matAll_spec {st : SState} {xs : List ValueId} {m : List (ValueId × ValueId)}
    {st' : SState} {out : Array Stmt} {V : Nat → Option Block} {b : Block}
    (hI : MInv f V B st) (hb : V bi = some b) (hxs : ∀ y ∈ xs, Placed st B y)
    (hm : materializeAll cfg allowed bi st xs = some (m, st', out)) :
    MRun f cfg.idom allowed bi B V st st' out.toList ∧ m.map Prod.fst = xs ∧
      ∀ p ∈ m, Placed st' B p.2 ∧ AvailHere cfg.idom (emitV V bi out.toList) bi p.2 ∧
        st'.types.get? p.2 = st.types.get? p.1 := by
  unfold materializeAll at hm
  let I : List ValueId → List (ValueId × ValueId) × SState × Array Stmt → Prop := fun pre acc =>
    MRun f cfg.idom allowed bi B V st acc.2.1 acc.2.2.toList ∧ acc.1.map Prod.fst = pre ∧
      ∀ p ∈ acc.1, Placed acc.2.1 B p.2 ∧ AvailHere cfg.idom (emitV V bi acc.2.2.toList) bi p.2 ∧
        acc.2.1.types.get? p.2 = st.types.get? p.1
  have := foldlM_option_mem (I := I) (l := xs)
    (g := fun (acc : List (ValueId × ValueId) × SState × Array Stmt) x => do
      let (x', st, out) ← materialize cfg allowed bi (acc.2.1.defs.size + 1) (acc.2.1, acc.2.2) x
      pure (acc.1 ++ [(x, x')], st, out))
    (by
      intro pre a rest c c' hl hI' hg
      obtain ⟨m0, st0, out0⟩ := c
      obtain ⟨hrun0, hmap, hps⟩ := hI'
      simp only [bind, Option.bind] at hg
      split at hg
      · cases hg
      rename_i r hr
      obtain ⟨x', st1, out1⟩ := r
      simp only [pure, Option.some.injEq] at hg
      subst hg
      have ha : a ∈ xs := by rw [← hl]; simp
      dsimp only [I] at hrun0 hmap hps hr ⊢
      obtain ⟨new, hout, hrun1, hg1, hh1, ht1⟩ := mat_spec _ _ _ _ _ _ _ _
        { b with body := b.body ++ out0.toList } hrun0.inv (by simp [emitV, hb])
        (hrun0.good a (hxs a ha)) hr
      rw [hout]
      refine ⟨hrun0.trans hrun1, by simp [hmap],
        fun p hp => ?_⟩
      rw [← emitV_append]
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · obtain ⟨e1, e2, e3⟩ := hps p hp
        exact ⟨hrun1.good _ e1, e2.emit bi new, by rw [hrun1.step.typesKnown _ e1.known, e3]⟩
      · exact ⟨hg1, hh1, by rw [ht1, hrun0.step.typesKnown _ (hxs a ha).known]⟩)
    xs [] ([], st, #[]) _ (by simp) ⟨MRun.refl hI, rfl, fun p hp => by cases hp⟩ hm
  exact this

end Mat

end Opt

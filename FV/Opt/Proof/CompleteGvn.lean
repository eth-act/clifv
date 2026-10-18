import FV.Opt.Proof.CheckComplete
import FV.Opt.Gvn

/-!
# Completeness of the GVN stage (M1)

On a well-formed function (`check g = .ok info`), the output of `Opt.gvnFull` passes `check` and
the edit validator `editOk` with GVN's substitution (`gvn_complete`), so `Opt.optimizeReport` never
stops at a GVN stage.

The proof has two parts. *What GVN does* (`gvnFull_spec`): the dominator-tree walk processes
every block at most once (its children lists are distinct, `domChildren_spec`), and every renaming
`v ↦ w` it records is a pure `v = m` deleted in favour of a kept pure `w = n` with the same renamed
node, `w` defined earlier in the block or in a strict tree ancestor (the scoped table only holds
values of the block's tree ancestors); the output is the input with the renamed statements deleted
and every operand renamed. *Why the validators accept that* (`gvnOut_check`, `gvnOut_editOk`): as
for DCE, every kept use stays available (a renamed operand moves up the tree), types are kept
(the two nodes have the same result types), and a deleted statement is `delOk`.
-/

namespace Opt

open Clif

/-! ## Renamings -/

theorem resultTypes_mapOperands (σ : ValueId → ValueId) (i : Inst) (sg : FnRef → Option Signature)
    (sd : Nat → Option Signature) : (mapOperands σ i).resultTypes sg sd = i.resultTypes sg sd := by
  cases i <;> try rfl
  rename_i op _ _
  cases op <;> rfl

theorem pureTyped_mapOperands (ty : ValueId → Option Ty) (f : Function) (σ : ValueId → ValueId)
    (i : Inst) : pureTyped ty f (mapOperands σ i) = pureTyped (ty ∘ σ) f i := by
  cases i <;> rfl

/-- A substitution whose values are not keys. -/
def ChainFree (S : Subst) : Prop := ∀ k w : ValueId, S[k]? = some w → S[w]? = none

/-- `S ⊆ S'`. -/
def SubLe (S S' : Subst) : Prop := ∀ k w : ValueId, S[k]? = some w → S'[k]? = some w

theorem SubLe.refl (S : Subst) : SubLe S S := fun _ _ h => h

theorem SubLe.trans {S S' S'' : Subst} (h1 : SubLe S S') (h2 : SubLe S' S'') : SubLe S S'' :=
  fun k w h => h2 k w (h1 k w h)

theorem find_none {S : Subst} {x : ValueId} (h : S[x]? = none) : S.find x = x := by
  unfold Subst.find
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, List.range'_succ,
    List.forIn_cons, Std.HashMap.get?_eq_getElem?, h]
  rfl

/-- On a chain-free substitution `find` is one step. -/
theorem find_chainFree {S : Subst} (hc : ChainFree S) (x : ValueId) : S.find x = (S[x]?).getD x := by
  cases hx : S[x]? with
  | none => rw [find_none hx]; rfl
  | some w =>
    have hw := hc x w hx
    have hpos : 0 < S.size := by
      rcases Nat.eq_zero_or_pos S.size with h | h
      · exfalso
        have : S.isEmpty = true := by simp [Std.HashMap.isEmpty_eq_size_eq_zero, h]
        rw [Std.HashMap.isEmpty_iff_forall_not_mem] at this
        exact this x (Std.HashMap.mem_iff_isSome_getElem?.2 (by simp [hx]))
      · exact h
    unfold Subst.find
    simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
      Nat.add_sub_cancel, Nat.div_one]
    obtain ⟨n, hn⟩ : ∃ n, S.size = n + 1 := ⟨S.size - 1, by omega⟩
    rw [hn]
    simp only [List.range'_succ, List.forIn_cons, Std.HashMap.get?_eq_getElem?, hx, pure_bind, hw]
    rfl

theorem find_comp {S S' : Subst} (hle : SubLe S S') (hc' : ChainFree S') (hc : ChainFree S)
    (x : ValueId) : S'.find (S.find x) = S'.find x := by
  rw [find_chainFree hc]
  cases hx : S[x]? with
  | none => rfl
  | some w =>
    simp only [Option.getD_some]
    have h' := hle x w hx
    rw [find_chainFree hc', find_chainFree hc' x, h', hc' x w h']
    rfl

theorem ChainFree.empty : ChainFree (∅ : Subst) := by intro k w h; simp at h

/-- `Subst.apply` renames every body statement and terminator by `find`. -/
theorem apply_eq (S : Subst) (f : Function) :
    S.apply f = { f with blocks := f.blocks.map fun b =>
      { b with body := b.body.map (renStmt S.find), term := mapTerm S.find b.term } } := by
  unfold Subst.apply
  split
  · rename_i h
    have hid : S.find = id := by
      funext x
      apply find_none
      rw [Std.HashMap.isEmpty_iff_forall_not_mem] at h
      cases hx : S[x]? with
      | none => rfl
      | some w => exact absurd (Std.HashMap.mem_iff_isSome_getElem?.2 (by simp [hx])) (h x)
    rw [hid]
    have hr : renStmt id = id := funext renStmt_id
    have hb : ∀ b : Block, { b with body := b.body.map (renStmt id), term := mapTerm id b.term } = b := by
      intro b; cases b; simp [mapTerm_id, hr]
    simp only [hb, List.map_id']
  · rfl


abbrev Tbl := Std.HashMap Inst ValueId
/-- The state of GVN's body loop: substitution, removed count, scoped table, block-local table,
emitted body. -/
abbrev GSt := Subst × Nat × Tbl × Tbl × Array Stmt

/-- GVN on one statement. -/
def gvnStmt (local? : Inst → Bool) (s : GSt) (st : Stmt) : GSt :=
  match st.results, isPure (mapOperands s.1.find st.inst) with
  | [v], true =>
    match (if local? (mapOperands s.1.find st.inst) = true then s.2.2.2.1 else s.2.2.1).get?
        (mapOperands s.1.find st.inst) with
    | some w => (s.1.insert v w, s.2.1 + 1, s.2.2.1, s.2.2.2.1, s.2.2.2.2)
    | none =>
      if local? (mapOperands s.1.find st.inst) = true then
        (s.1, s.2.1, s.2.2.1, s.2.2.2.1.insert (mapOperands s.1.find st.inst) v,
          s.2.2.2.2.push { st with inst := mapOperands s.1.find st.inst })
      else
        (s.1, s.2.1, s.2.2.1.insert (mapOperands s.1.find st.inst) v, s.2.2.2.1,
          s.2.2.2.2.push { st with inst := mapOperands s.1.find st.inst })
  | _, _ => (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.push { st with inst := mapOperands s.1.find st.inst })

theorem forIn_yield_foldl {α σ : Type} (B : α → σ → Id (ForInStep σ)) (g : σ → α → σ)
    (hB : ∀ a s, B a s = pure (ForInStep.yield (g s a))) (l : List α) (init : σ) :
    forIn l init B = pure (l.foldl g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => rw [List.forIn_cons, hB]; simp only [pure_bind]; exact ih _

/-! ## The facts GVN maintains -/

/-- GVN keeps a statement unless it is a single-result statement whose result is renamed. -/
def keepG (S : Subst) (st : Stmt) : Bool :=
  match st.results with
  | [v] => !S.contains v
  | _ => true

/-- `x = n` is the pure statement `j` of block `d` (`x` its single result). -/
def PureAt (f : Function) (x : ValueId) (d j : Nat) (n : Inst) : Prop :=
  ∃ b st, f.blocks[d]? = some b ∧ b.body[j]? = some st ∧ st.results = [x] ∧ st.inst = n ∧
    isPure n = true

/-- A renaming `v ↦ w` of GVN (`Pr`: the processed statement positions). -/
def KeyOk (f : Function) (idom : Array (Option Nat)) (Pr : Nat → Nat → Prop) (S : Subst)
    (v w : ValueId) : Prop :=
  ∃ d j m d' j' n, PureAt f v d j m ∧ Pr d j ∧ PureAt f w d' j' n ∧ Pr d' j' ∧ S[w]? = none ∧
    mapOperands S.find n = mapOperands S.find m ∧ ((d' = d ∧ j' < j) ∨ (d' ≠ d ∧ Anc idom d' d))

def SubOk (f : Function) (idom : Array (Option Nat)) (Pr : Nat → Nat → Prop) (S : Subst) : Prop :=
  ∀ v w, S[v]? = some w → KeyOk f idom Pr S v w

/-- A table entry `n ↦ w` usable in block `c` before its statement `k` (`own`: entries of `c`'s
own earlier statements are allowed). -/
def EntryOk (f : Function) (idom : Array (Option Nat)) (Pr : Nat → Nat → Prop) (S : Subst)
    (c k : Nat) (own : Bool) (n : Inst) (w : ValueId) : Prop :=
  ∃ d' j' n', PureAt f w d' j' n' ∧ Pr d' j' ∧ S[w]? = none ∧
    mapOperands S.find n' = mapOperands S.find n ∧
    ((d' ≠ c ∧ Anc idom d' c) ∨ (own = true ∧ d' = c ∧ j' < k))

def TblOk (f : Function) (idom : Array (Option Nat)) (Pr : Nat → Nat → Prop) (S : Subst)
    (c k : Nat) (own : Bool) (tbl : Tbl) : Prop :=
  ∀ n w, tbl.get? n = some w → EntryOk f idom Pr S c k own n w

/-- `S'` grows `S` by keys outside the positions `Pr`. -/
structure Grows (f : Function) (S S' : Subst) (Pr : Nat → Nat → Prop) : Prop where
  le : SubLe S S'
  cf : ChainFree S
  cf' : ChainFree S'
  fresh : ∀ v w, S'[v]? = some w → S[v]? = none → ∀ d j m, PureAt f v d j m → ¬ Pr d j

section Spec

variable {f : Function} {idom : Array (Option Nat)}

theorem SubOk.chainFree {Pr : Nat → Nat → Prop} {S : Subst} (h : SubOk f idom Pr S) :
    ChainFree S := by
  intro v w hv
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hw, _⟩ := h v w hv
  exact hw

theorem SubOk.mono {Pr Pr' : Nat → Nat → Prop} {S : Subst} (h : SubOk f idom Pr S)
    (hPr : ∀ d j, Pr d j → Pr' d j) : SubOk f idom Pr' S := by
  intro v w hv
  obtain ⟨d, j, m, d', j', n, h1, h2, h3, h4, h5, h6, h7⟩ := h v w hv
  exact ⟨d, j, m, d', j', n, h1, hPr _ _ h2, h3, hPr _ _ h4, h5, h6, h7⟩

theorem mapOperands_grow {S S' : Subst} (hle : SubLe S S') (hc : ChainFree S) (hc' : ChainFree S')
    {n m : Inst} (h : mapOperands S.find n = mapOperands S.find m) :
    mapOperands S'.find n = mapOperands S'.find m := by
  have e1 := congrArg (mapOperands S'.find) h
  simp only [mapOperands_comp] at e1
  have hfc : S'.find ∘ S.find = S'.find := funext fun x => find_comp hle hc' hc x
  rwa [hfc] at e1

theorem Grows.none {S S' : Subst} {Pr : Nat → Nat → Prop} (hg : Grows f S S' Pr) {w : ValueId}
    {d j : Nat} {n : Inst} (hw : PureAt f w d j n) (hp : Pr d j) (hS : S[w]? = none) :
    S'[w]? = none := by
  cases h : S'[w]? with
  | none => rfl
  | some u => exact absurd hp (hg.fresh w u h hS d j n hw)

theorem EntryOk.grow {Pr Pr' : Nat → Nat → Prop} {S S' : Subst} {c k k' : Nat} {own : Bool}
    {n : Inst} {w : ValueId} (h : EntryOk f idom Pr S c k own n w) (hg : Grows f S S' Pr)
    (hPr : ∀ d j, Pr d j → Pr' d j) (hk : k ≤ k') : EntryOk f idom Pr' S' c k' own n w := by
  obtain ⟨d', j', n', h1, h2, h3, h4, h5⟩ := h
  refine ⟨d', j', n', h1, hPr _ _ h2, hg.none h1 h2 h3, mapOperands_grow hg.le hg.cf hg.cf' h4, ?_⟩
  rcases h5 with h5 | ⟨h5, h6, h7⟩
  · exact .inl h5
  · exact .inr ⟨h5, h6, by omega⟩

theorem TblOk.grow {Pr Pr' : Nat → Nat → Prop} {S S' : Subst} {c k k' : Nat} {own : Bool}
    {tbl : Tbl} (h : TblOk f idom Pr S c k own tbl) (hg : Grows f S S' Pr)
    (hPr : ∀ d j, Pr d j → Pr' d j) (hk : k ≤ k') : TblOk f idom Pr' S' c k' own tbl :=
  fun n w hw => (h n w hw).grow hg hPr hk

theorem KeyOk.grow {Pr Pr' : Nat → Nat → Prop} {S S' : Subst} {v w : ValueId}
    (h : KeyOk f idom Pr S v w) (hg : Grows f S S' Pr) (hPr : ∀ d j, Pr d j → Pr' d j) :
    KeyOk f idom Pr' S' v w := by
  obtain ⟨d, j, m, d', j', n, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨d, j, m, d', j', n, h1, hPr _ _ h2, h3, hPr _ _ h4, hg.none h3 h4 h5,
    mapOperands_grow hg.le hg.cf hg.cf' h6, h7⟩

theorem Grows.refl {S : Subst} {Pr : Nat → Nat → Prop} (hc : ChainFree S) : Grows f S S Pr :=
  ⟨SubLe.refl S, hc, hc, fun v w h h' => by rw [h] at h'; cases h'⟩

theorem Grows.trans {S S' S'' : Subst} {Pr : Nat → Nat → Prop} (h1 : Grows f S S' Pr)
    (h2 : Grows f S' S'' Pr) : Grows f S S'' Pr := by
  refine ⟨h1.le.trans h2.le, h1.cf, h2.cf', fun v w hv hS d j m hp hpr => ?_⟩
  cases h' : S'[v]? with
  | none => exact h2.fresh v w hv h' d j m hp hpr
  | some u => exact h1.fresh v u h' hS d j m hp hpr

theorem PureAt.site {x : ValueId} {d j : Nat} {n : Inst} (h : PureAt f x d j n) :
    (x, (d, j + 1)) ∈ defSites f := by
  obtain ⟨b, st, hb, hst, hr, -, -⟩ := h
  exact mem_defSites.2 ⟨d, b, hb, .inr ⟨j, st, hst, by simp [hr], rfl⟩⟩

/-- Values are defined once: the position of a pure statement is determined by its result. -/
theorem PureAt.unique (hu : UniqueDefs f) {x : ValueId} {d j d2 j2 : Nat} {n n2 : Inst}
    (h1 : PureAt f x d j n) (h2 : PureAt f x d2 j2 n2) : d = d2 ∧ j = j2 ∧ n = n2 := by
  have := site_unique hu h1.site h2.site
  simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at this
  obtain ⟨rfl, rfl⟩ := this
  obtain ⟨b, st, hb, hst, -, hn, -⟩ := h1
  obtain ⟨b2, st2, hb2, hst2, -, hn2, -⟩ := h2
  rw [hb] at hb2; cases hb2
  rw [hst] at hst2; cases hst2
  exact ⟨rfl, rfl, hn.symm.trans hn2⟩

/-- A renamed value is defined by a pure statement at a processed position. -/
theorem SubOk.key {Pr : Nat → Nat → Prop} {S : Subst} (h : SubOk f idom Pr S) {v : ValueId}
    (hv : S.contains v = true) : ∃ d j m, PureAt f v d j m ∧ Pr d j := by
  obtain ⟨w, hw⟩ : ∃ w, S[v]? = some w := by
    cases h' : S[v]? with
    | none => simp [Std.HashMap.contains_eq_isSome_getElem?, h'] at hv
    | some w => exact ⟨w, rfl⟩
  obtain ⟨d, j, m, _, _, _, h1, h2, _⟩ := h v w hw
  exact ⟨d, j, m, h1, h2⟩

/-- A result of a statement at an unprocessed position is not renamed. -/
theorem not_key_of_unprocessed (hu : UniqueDefs f) {Pr : Nat → Nat → Prop} {S : Subst}
    (h : SubOk f idom Pr S) {d j : Nat} {b : Block} {st : Stmt} (hb : f.blocks[d]? = some b)
    (hst : b.body[j]? = some st) (hn : ¬ Pr d j) {r : ValueId} (hr : r ∈ st.results) :
    S[r]? = none := by
  cases hc : S[r]? with
  | none => rfl
  | some w =>
    exfalso
    obtain ⟨d', j', m, hp, hpr⟩ := h.key (v := r) (by simp [Std.HashMap.contains_eq_isSome_getElem?, hc])
    have := site_unique hu hp.site (mem_defSites.2 ⟨d, b, hb, .inr ⟨j, st, hst, hr, rfl⟩⟩)
    simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at this
    obtain ⟨rfl, rfl⟩ := this
    exact hn hpr

theorem keepG_of_unprocessed (hu : UniqueDefs f) {Pr : Nat → Nat → Prop} {S : Subst}
    (h : SubOk f idom Pr S) {d j : Nat} {b : Block} {st : Stmt} (hb : f.blocks[d]? = some b)
    (hst : b.body[j]? = some st) (hn : ¬ Pr d j) : keepG S st = true := by
  unfold keepG
  split
  · rename_i v hv
    have := not_key_of_unprocessed hu h hb hst hn (r := v) (by simp [hv])
    simp [Std.HashMap.contains_eq_isSome_getElem?, this]
  · rfl

end Spec

/-! ## One block -/

/-- Processed positions: the blocks `Done`. -/
def PrD (Done : List Nat) (d _j : Nat) : Prop := d ∈ Done

/-- Processed positions while block `bi` is processed up to its statement `k`. -/
def PrK (Done : List Nat) (bi k d j : Nat) : Prop := d ∈ Done ∨ (d = bi ∧ j < k)

/-- The invariant of GVN's body loop on block `bi` (= `b`), started from the substitution `S0`,
after `k` statements. -/
structure BInv (f : Function) (idom : Array (Option Nat)) (Done : List Nat) (bi : Nat) (b : Block)
    (S0 : Subst) (k : Nat) (s : GSt) : Prop where
  sub : SubOk f idom (PrK Done bi k) s.1
  grow : Grows f S0 s.1 (PrD Done)
  tbl : TblOk f idom (PrK Done bi k) s.1 bi k true s.2.2.1
  btbl : TblOk f idom (PrK Done bi k) s.1 bi k true s.2.2.2.1
  body : s.2.2.2.2.toList.map (renStmt s.1.find) =
    ((b.body.take k).filter (keepG s.1)).map (renStmt s.1.find)

section Block

variable {f : Function} {idom : Array (Option Nat)}

theorem Grows.weaken {S S' : Subst} {Pr Pr' : Nat → Nat → Prop} (h : Grows f S S' Pr)
    (hPr : ∀ d j, Pr' d j → Pr d j) : Grows f S S' Pr' :=
  ⟨h.le, h.cf, h.cf', fun v w h1 h2 d j m hp hpr => h.fresh v w h1 h2 d j m hp (hPr d j hpr)⟩

theorem find_idem {S : Subst} (hc : ChainFree S) (x : ValueId) : S.find (S.find x) = S.find x :=
  find_comp (SubLe.refl S) hc hc x

theorem mapOperands_find_idem {S : Subst} (hc : ChainFree S) (i : Inst) :
    mapOperands S.find (mapOperands S.find i) = mapOperands S.find i := by
  rw [mapOperands_comp]
  exact mapOperands_congr fun x _ => find_idem hc x

theorem renStmt_grow {S S' : Subst} (hle : SubLe S S') (hc : ChainFree S) (hc' : ChainFree S')
    (st : Stmt) : renStmt S'.find (renStmt S.find st) = renStmt S'.find st := by
  cases st
  simp only [renStmt, mapOperands_comp]
  congr 1
  exact mapOperands_congr fun x _ => find_comp hle hc' hc x

/-- Equal renamed bodies stay equal under a grown substitution. -/
theorem map_renStmt_grow {S S' : Subst} (hle : SubLe S S') (hc : ChainFree S) (hc' : ChainFree S')
    {l1 l2 : List Stmt} (h : l1.map (renStmt S.find) = l2.map (renStmt S.find)) :
    l1.map (renStmt S'.find) = l2.map (renStmt S'.find) := by
  have e := congrArg (List.map (renStmt S'.find)) h
  simp only [List.map_map] at e
  have hc2 : renStmt S'.find ∘ renStmt S.find = renStmt S'.find :=
    funext fun st => renStmt_grow hle hc hc' st
  rwa [hc2] at e

theorem TblOk.own {Pr : Nat → Nat → Prop} {S : Subst} {c k : Nat} {tbl : Tbl}
    (h : TblOk f idom Pr S c k false tbl) (k' : Nat) : TblOk f idom Pr S c k' true tbl := by
  intro n w hw
  obtain ⟨d', j', n', h1, h2, h3, h4, h5⟩ := h n w hw
  refine ⟨d', j', n', h1, h2, h3, h4, ?_⟩
  rcases h5 with h5 | ⟨h5, -⟩
  · exact .inl h5
  · cases h5

theorem TblOk.empty {Pr : Nat → Nat → Prop} {S : Subst} {c k : Nat} {own : Bool} :
    TblOk f idom Pr S c k own (∅ : Tbl) := by
  intro n w h; simp at h

theorem TblOk.insert {Pr : Nat → Nat → Prop} {S : Subst} {c k : Nat} {own : Bool} {tbl : Tbl}
    (h : TblOk f idom Pr S c k own tbl) {n : Inst} {w : ValueId} (hw : EntryOk f idom Pr S c k own n w) :
    TblOk f idom Pr S c k own (tbl.insert n w) := by
  intro n' w' h'
  rw [Std.HashMap.get?_insert] at h'
  split at h'
  · rename_i he
    simp only [beq_iff_eq] at he
    subst he; cases h'; exact hw
  · exact h n' w' h'

theorem take_succ_of_getElem? {α : Type} {l : List α} {k : Nat} {a : α} (h : l[k]? = some a) :
    l.take (k + 1) = l.take k ++ [a] := by
  rw [List.take_add_one, h]; rfl

/-- **GVN on one statement** keeps the block invariant. -/
theorem bInv_step (hu : UniqueDefs f) (local? : Inst → Bool) {Done : List Nat} {bi : Nat}
    {b : Block} (hb : f.blocks[bi]? = some b) (hbi : bi ∉ Done) {S0 : Subst} {k : Nat} {st : Stmt}
    (hst : b.body[k]? = some st) {s : GSt} (h : BInv f idom Done bi b S0 k s) :
    BInv f idom Done bi b S0 (k + 1) (gvnStmt local? s st) := by
  obtain ⟨S, rem, tbl, btbl, body⟩ := s
  obtain ⟨hsub, hgrow, htbl, hbtbl, hbody⟩ := h
  simp only at hsub hgrow htbl hbtbl hbody
  have hcf : ChainFree S := hsub.chainFree
  have hcur : ¬ PrK Done bi k bi k := by
    rintro (h | ⟨-, h⟩)
    · exact hbi h
    · omega
  have hmono : ∀ d j, PrK Done bi k d j → PrK Done bi (k + 1) d j := by
    rintro d j (h | ⟨h1, h2⟩)
    · exact .inl h
    · exact .inr ⟨h1, by omega⟩
  have hDK : ∀ d j, PrD Done d j → PrK Done bi k d j := fun d j h => .inl h
  -- the earlier statements of the block define values other than `st`'s
  have hprev : ∀ st0 ∈ b.body.take k, ∀ r ∈ st0.results, ∀ r' ∈ st.results, r ≠ r' := by
    intro st0 h0 r hr r' hr' hrr
    subst hrr
    obtain ⟨j0, hj0⟩ := List.mem_iff_getElem?.1 h0
    have hj0k : j0 < k := by
      have := (List.getElem?_eq_some_iff.1 hj0).1
      simp only [List.length_take] at this; omega
    rw [List.getElem?_take, ite_eq_left hj0k] at hj0
    have := site_unique hu (mem_defSites.2 ⟨bi, b, hb, .inr ⟨j0, st0, hj0, hr, rfl⟩⟩)
      (mem_defSites.2 ⟨bi, b, hb, .inr ⟨k, st, hst, hr', rfl⟩⟩)
    simp at this; omega
  have hkeep : keepG S st = true := keepG_of_unprocessed hu hsub hb hst hcur
  have htake := take_succ_of_getElem? hst
  -- kept: the body grows by the renamed statement
  have hkept : ∀ (inst : Inst), inst = mapOperands S.find st.inst →
      (body.push { st with inst := inst }).toList.map (renStmt S.find) =
        ((b.body.take (k + 1)).filter (keepG S)).map (renStmt S.find) := by
    intro inst hi
    rw [htake, List.filter_append, Array.toList_push, List.map_append, List.map_append, hbody]
    simp only [List.filter_cons, List.filter_nil, hkeep, ite_true, List.map_cons, List.map_nil]
    congr 2
    cases st
    simp only [renStmt, hi, mapOperands_find_idem hcf]
  unfold gvnStmt
  split
  · rename_i v hv hp
    simp only at hp
    have hpure : isPure st.inst = true := by rwa [isPure_mapOperands] at hp
    have hpv : PureAt f v bi k st.inst := ⟨b, st, hb, hst, hv, rfl, hpure⟩
    have hvS : S[v]? = none := not_key_of_unprocessed hu hsub hb hst hcur (by simp [hv])
    split
    · -- a hit: `v` is renamed to `w`
      rename_i w hw
      have hE : EntryOk f idom (PrK Done bi k) S bi k true (mapOperands S.find st.inst) w := by
        split at hw
        · exact hbtbl _ _ hw
        · exact htbl _ _ hw
      obtain ⟨d', j', n', hpw, hprw, hwS, hn', hpos⟩ := hE
      have hvw : v ≠ w := by
        intro he; subst he
        obtain ⟨rfl, rfl, -⟩ := PureAt.unique hu hpv hpw
        exact hcur hprw
      have hget : ∀ x, (S.insert v w)[x]? = if v = x then some w else S[x]? := by
        intro x; rw [Std.HashMap.getElem?_insert]; simp
      have hcf' : ChainFree (S.insert v w) := by
        intro k0 w0 h0
        rw [hget] at h0 ⊢
        split at h0
        · cases h0; rw [ite_eq_right hvw]; exact hwS
        · have hw0 : S[w0]? = none := hcf k0 w0 h0
          obtain ⟨_, _, _, d0, j0, n0, _, _, hp0, hpr0, _⟩ := hsub k0 w0 h0
          have : v ≠ w0 := by
            intro he; subst he
            obtain ⟨rfl, rfl, -⟩ := PureAt.unique hu hpv hp0
            exact hcur hpr0
          rw [ite_eq_right this]; exact hw0
      have hle : SubLe S (S.insert v w) := by
        intro k0 w0 h0
        rw [hget, ite_eq_right]; · exact h0
        rintro rfl; rw [hvS] at h0; cases h0
      have hG : Grows f S (S.insert v w) (PrK Done bi k) := by
        refine ⟨hle, hcf, hcf', fun x y hx hxS d j m hpx hpr => ?_⟩
        rw [hget] at hx
        split at hx
        · rename_i he; subst he
          obtain ⟨rfl, rfl, -⟩ := PureAt.unique hu hpv hpx
          exact hcur hpr
        · rw [hx] at hxS; cases hxS
      refine ⟨?_, hgrow.trans (hG.weaken hDK), htbl.grow hG hmono (by omega),
        hbtbl.grow hG hmono (by omega), ?_⟩
      · intro x y hx
        by_cases hxv : x = v
        · subst hxv
          rw [hget, ite_eq_left rfl] at hx; cases hx
          refine ⟨bi, k, st.inst, d', j', n', hpv, .inr ⟨rfl, by omega⟩, hpw, hmono _ _ hprw, ?_, ?_, ?_⟩
          · rw [hget, ite_eq_right hvw]; exact hwS
          · rw [mapOperands_grow hle hcf hcf' hn', mapOperands_comp]
            exact mapOperands_congr fun x _ => find_comp hle hcf' hcf x
          · rcases hpos with ⟨hne, ha⟩ | ⟨-, rfl, hj⟩
            · exact .inr ⟨hne, ha⟩
            · exact .inl ⟨rfl, hj⟩
        · rw [hget, ite_eq_right (Ne.symm hxv)] at hx
          exact (hsub x y hx).grow hG hmono
      · simp only
        rw [htake, List.filter_append]
        have hk' : keepG (S.insert v w) st = false := by
          simp [keepG, hv]
        have hf : (b.body.take k).filter (keepG (S.insert v w)) = (b.body.take k).filter (keepG S) := by
          apply List.filter_congr
          intro st0 h0
          unfold keepG
          split
          · rename_i r hr
            have : r ≠ v := hprev st0 h0 r (by simp [hr]) v (by simp [hv])
            simp [Std.HashMap.contains_insert, Ne.symm this]
          · rfl
        simp only [List.filter_cons, List.filter_nil, hk', Bool.false_eq_true, ite_false,
          List.append_nil, hf]
        exact map_renStmt_grow hle hcf hcf' hbody
    · -- a miss: kept, recorded in a table
      rename_i hw
      have hE : EntryOk f idom (PrK Done bi (k + 1)) S bi (k + 1) true (mapOperands S.find st.inst) v :=
        ⟨bi, k, st.inst, hpv, .inr ⟨rfl, by omega⟩, hvS, (mapOperands_find_idem hcf st.inst).symm,
          .inr ⟨rfl, rfl, by omega⟩⟩
      have hG := Grows.refl (f := f) (Pr := PrK Done bi k) hcf
      split
      · exact ⟨hsub.mono hmono, hgrow, htbl.grow hG hmono (by omega),
          (hbtbl.grow hG hmono (by omega)).insert hE, hkept _ rfl⟩
      · exact ⟨hsub.mono hmono, hgrow, (htbl.grow hG hmono (by omega)).insert hE,
          hbtbl.grow hG hmono (by omega), hkept _ rfl⟩
  · have hG := Grows.refl (f := f) (Pr := PrK Done bi k) hcf
    exact ⟨hsub.mono hmono, hgrow, htbl.grow hG hmono (by omega), hbtbl.grow hG hmono (by omega),
      hkept _ rfl⟩

/-- `keepG` is stable under growth on statements at positions where no key was added. -/
theorem keepG_grow (hu : UniqueDefs f) {Pr Pr' : Nat → Nat → Prop} {S S' : Subst}
    (hg : Grows f S S' Pr) (hsub' : SubOk f idom Pr' S') {d j : Nat} {b : Block} {st : Stmt}
    (hb : f.blocks[d]? = some b) (hst : b.body[j]? = some st) (hp : Pr d j) :
    keepG S' st = keepG S st := by
  unfold keepG
  split
  · rename_i r hr
    congr 1
    simp only [Std.HashMap.contains_eq_isSome_getElem?]
    cases h : S[r]? with
    | some w => rw [hg.le r w h]
    | none =>
      cases h' : S'[r]? with
      | none => rfl
      | some y =>
        exfalso
        obtain ⟨d0, j0, m0, hp0, _⟩ := hsub'.key (v := r) (by simp [Std.HashMap.contains_eq_isSome_getElem?, h'])
        have := site_unique hu hp0.site (mem_defSites.2 ⟨d, b, hb, .inr ⟨j, st, hst, by simp [hr], rfl⟩⟩)
        simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at this
        obtain ⟨rfl, rfl⟩ := this
        exact hg.fresh r y h' h _ _ _ hp0 hp
  · rfl

theorem bInv_fold (hu : UniqueDefs f) (local? : Inst → Bool) {Done : List Nat} {bi : Nat}
    {b : Block} (hb : f.blocks[bi]? = some b) (hbi : bi ∉ Done) {S0 : Subst} {init : GSt}
    (h0 : BInv f idom Done bi b S0 0 init) :
    BInv f idom Done bi b S0 b.body.length (b.body.foldl (gvnStmt local?) init) := by
  suffices ∀ k, k ≤ b.body.length → BInv f idom Done bi b S0 k ((b.body.take k).foldl (gvnStmt local?) init) by
    simpa using this b.body.length (Nat.le_refl _)
  intro k
  induction k with
  | zero => intro _; simpa using h0
  | succ k ih =>
    intro hk
    obtain ⟨st, hst⟩ : ∃ st, b.body[k]? = some st := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [take_succ_of_getElem? hst, List.foldl_append]
    exact bInv_step hu local? hb hbi hst (ih (by omega))

end Block

/-! ## The walk over the dominator tree -/

/-- GVN's outer loop state: substitution, output blocks, removed count, stack. -/
abbrev OSt := Subst × Array Block × Nat × Array (Nat × Tbl)

/-- The invariant of the walk (`Done`: the processed blocks). -/
def OInv (f : Function) (idom : Array (Option Nat)) (s : OSt) : Prop :=
  ∃ Done : List Nat,
    (Done ++ s.2.2.2.toList.map (·.1)).Nodup ∧
    (∀ x ∈ Done ++ s.2.2.2.toList.map (·.1), x < f.blocks.length ∧
      (x = 0 ∨ ∃ p ∈ Done, idom[x]?.join = some p)) ∧
    SubOk f idom (PrD Done) s.1 ∧
    (∀ e ∈ s.2.2.2.toList, TblOk f idom (PrD Done) s.1 e.1 0 false e.2) ∧
    s.2.1.size = f.blocks.length ∧
    ∀ i b, f.blocks[i]? = some b → (i ∉ Done → s.2.1[i]! = b) ∧
      (i ∈ Done → ∃ body, s.2.1[i]! = { b with body } ∧
        body.map (renStmt s.1.find) = (b.body.filter (keepG s.1)).map (renStmt s.1.find))

/-- A block of GVN's output. -/
def gB (S : Subst) (b : Block) : Block :=
  { b with body := (b.body.filter (keepG S)).map (renStmt S.find), term := mapTerm S.find b.term }

/-- GVN's output (`GvnOut`). -/
def gvnF (f : Function) (S : Subst) : Function := { f with blocks := f.blocks.map (gB S) }

/-- What GVN returns: renamings with their facts, and the input with the renamed statements
deleted and every operand renamed. -/
def GvnOut (f : Function) (idom : Array (Option Nat)) (g : Function) (S : Subst) : Prop :=
  SubOk f idom (fun _ _ => True) S ∧
    g = gvnF f S

theorem foldl_push_pair {β γ : Type} (l : List β) (t : γ) (acc : Array (β × γ)) :
    (l.foldl (fun s c => s.push (c, t)) acc).toList = acc.toList ++ l.map (·, t) := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => simp [ih]

theorem getElem!_set!_block (out : Array Block) (i j : Nat) (b : Block) (hi : i < out.size) :
    (out.set! i b)[j]! = if i = j then b else out[j]! := by
  by_cases h : i = j
  · subst h; simp [getElem!_def, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hi]
  · simp [getElem!_def, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, h]

/-- **What GVN does** (module doc). -/
theorem gvnFull_spec {f : Function} {info : Info} (hc : Checked f info) (local? : Inst → Bool) :
    GvnOut f info.cfg.idom (gvnFull f info local?).1 (gvnFull f info local?).2.2 := by
  have hcfg : info.cfg = Cfg.build f := by rw [hc.info_eq]; rfl
  have hu := hc.unique
  have hroot : info.cfg.idom[0]?.join = none := hc.wf.root
  have hrank := hc.wf.rank
  have hlen : 0 < f.blocks.length := by
    have := hc.core.1; simp [Cfg.size, Cfg.build] at this; simpa using this
  unfold gvnFull
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  rw [bind_pure_comp]
  simp only [Functor.map]
  refine forIn_inv' _ _ _ (P := OInv f info.cfg.idom)
    (Q := fun s : OSt => GvnOut f info.cfg.idom (s.1.apply { f with blocks := s.2.1.toList }) s.1) ?_ ?_ ?_
  · -- the initial state
    refine ⟨[], by simp, fun x hx => ?_, fun v w h => by simp at h, fun e he => ?_, by simp,
      fun i b hb => ⟨fun _ => ?_, fun h => by simp at h⟩⟩
    · simp at hx; subst hx; exact ⟨hlen, .inl rfl⟩
    · simp at he; subst he; exact TblOk.empty
    · simp [getElem!_def, hb]
  · -- one step
    rintro - ⟨S, out, rem, stk⟩ ⟨Done, hnd, hbl, hsub, htb, hsz, hout⟩
    simp only at hnd hbl hsub htb hsz hout ⊢
    split
    · exact ⟨Done, hnd, hbl, hsub, htb, hsz, hout⟩
    · rename_i bi tbl0 hback
      rw [forIn_yield_foldl _ (gvnStmt local?) (fun st s => by
        unfold gvnStmt
        rcases hr : st.results with _ | ⟨v, _ | ⟨_, _⟩⟩ <;>
          cases hp : isPure (mapOperands s.1.find st.inst) <;> simp only [hr, hp]
        cases hg : (if local? (mapOperands s.1.find st.inst) = true then s.2.2.2.1 else s.2.2.1).get?
          (mapOperands s.1.find st.inst) <;> simp only [hg]
        cases hl : local? (mapOperands s.1.find st.inst) <;> simp only [hl, Bool.false_eq_true,
          ite_false, ite_true] <;> rfl)]
      simp only [pure_bind]
      have hbB : bi ∈ Done ++ stk.toList.map (·.1) := by
        rw [back?_toList hback]; simp
      obtain ⟨hbil, -⟩ := hbl bi hbB
      obtain ⟨b, hb⟩ : ∃ b, f.blocks[bi]? = some b := ⟨_, List.getElem?_eq_getElem hbil⟩
      have hbA : f.blocks.toArray[bi]! = b := by simp [getElem!_def, hb]
      rw [hbA]
      have hbi : bi ∉ Done := by
        rw [back?_toList hback] at hnd
        simp only [List.map_append, List.map_cons, List.map_nil] at hnd
        intro h
        have := (List.nodup_append.1 hnd).2.2 bi h bi (by simp)
        exact this rfl
      have h0 : BInv f info.cfg.idom Done bi b S 0 (S, rem, tbl0, ∅, #[]) := by
        refine ⟨hsub.mono fun d j h => .inl h, Grows.refl hsub.chainFree, ?_, TblOk.empty, by simp⟩
        exact ((htb (bi, tbl0) (by rw [back?_toList hback]; simp)).own 0).grow
          (Grows.refl hsub.chainFree) (fun d j h => .inl h) (Nat.le_refl _)
      have hB := bInv_fold hu local? hb hbi h0
      generalize b.body.foldl (gvnStmt local?) (S, rem, tbl0, ∅, #[]) = r at hB
      obtain ⟨S', rem', tbl', btbl', body'⟩ := r
      rw [forIn_yield_foldl _ (fun (s : Array (Nat × Tbl)) c => s.push (c, tbl')) (fun c s => rfl)]
      simp only [pure_bind, Id.run_pure, ForInStep.value]
      obtain ⟨hsub', hgrow', htbl', -, hbody'⟩ := hB
      simp only [List.take_length] at hsub' hgrow' htbl' hbody'
      have hstk : stk.toList = stk.pop.toList ++ [(bi, tbl0)] := back?_toList hback
      have hrank' : ∀ x y, info.cfg.idom[x]?.join = some y →
          (wfData f info).rank y < (wfData f info).rank x := hrank
      have hch := domChildren_spec info.cfg (by rw [hcfg]; exact build_rpo_nodup f) bi
      have hchild : ∀ c ∈ info.cfg.domChildren[bi]!, c < f.blocks.length ∧
          info.cfg.idom[c]?.join = some bi := fun c hc =>
        ⟨build_rpo_lt f (by rw [← hcfg]; exact (hch.2 c hc).1), by rw [← getElem!_opt]; exact (hch.2 c hc).2⟩
      have hcDone : ∀ c ∈ info.cfg.domChildren[bi]!, c ∉ Done ++ stk.toList.map (·.1) := by
        intro c hc hin
        rcases (hbl c hin).2 with h | ⟨p, hp, hpc⟩
        · subst h; have := (hchild 0 hc).2; rw [hroot] at this; cases this
        · rw [(hchild c hc).2] at hpc; cases hpc; exact hbi hp
      have hcbi : ∀ c ∈ info.cfg.domChildren[bi]!, c ≠ bi := fun c hc h => by
        subst h; have := hrank' c c (hchild c hc).2; omega
      rw [hstk] at hnd hcDone
      simp only [List.map_append, List.map_cons, List.map_nil] at hnd hcDone
      have hnd' := List.nodup_append.1 hnd
      have hnd2 := List.nodup_append.1 hnd'.2.1
      refine ⟨bi :: Done, ?_, ?_, hsub'.mono fun d j h => ?_, ?_, by simp [hsz], ?_⟩
      · rw [foldl_push_pair]
        simp only [List.map_append, List.map_map, List.cons_append]
        have hR : (info.cfg.domChildren[bi]!.reverse.map ((·.1) ∘ fun c => (c, tbl'))) =
            info.cfg.domChildren[bi]!.reverse := by
          simp [Function.comp_def]
        rw [hR]
        refine List.nodup_cons.2 ⟨?_, ?_⟩
        · simp only [List.mem_append, List.mem_reverse, not_or]
          refine ⟨hbi, fun h => hnd2.2.2 bi h bi (by simp) rfl, fun h => hcbi bi h rfl⟩
        · refine List.nodup_append.2 ⟨hnd'.1, List.nodup_append.2 ⟨hnd2.1, ?_, ?_⟩, ?_⟩
          · exact (List.reverse_perm _).nodup_iff.2 hch.1
          · intro a ha c hc hac
            subst hac
            exact hcDone a (List.mem_reverse.1 hc) (List.mem_append_right _ (List.mem_append_left _ ha))
          · intro a ha c hc hac
            subst hac
            rcases List.mem_append.1 hc with hc | hc
            · exact hnd'.2.2 a ha a (List.mem_append_left _ hc) rfl
            · exact hcDone a (List.mem_reverse.1 hc) (List.mem_append_left _ ha)
      · rw [foldl_push_pair]
        intro x hx
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.map_append, List.map_map,
          List.mem_map, Function.comp_def, List.mem_reverse] at hx
        rcases hx with rfl | hx | hx | ⟨c, hc, rfl⟩
        · obtain ⟨h1, h2⟩ := hbl x hbB
          refine ⟨h1, ?_⟩
          rcases h2 with h2 | ⟨p, hp, h2⟩
          · exact .inl h2
          · exact .inr ⟨p, List.mem_cons_of_mem _ hp, h2⟩
        · obtain ⟨h1, h2⟩ := hbl x (List.mem_append_left _ hx)
          refine ⟨h1, ?_⟩
          rcases h2 with h2 | ⟨p, hp, h2⟩
          · exact .inl h2
          · exact .inr ⟨p, List.mem_cons_of_mem _ hp, h2⟩
        · obtain ⟨h1, h2⟩ := hbl x (by
            rw [hstk, List.map_append]
            exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map.2 hx)))
          refine ⟨h1, ?_⟩
          rcases h2 with h2 | ⟨p, hp, h2⟩
          · exact .inl h2
          · exact .inr ⟨p, List.mem_cons_of_mem _ hp, h2⟩
        · exact ⟨(hchild c hc).1, .inr ⟨bi, List.mem_cons_self .., (hchild c hc).2⟩⟩
      · rcases h with h | ⟨rfl, -⟩
        · exact List.mem_cons_of_mem _ h
        · exact List.mem_cons_self ..
      · rw [foldl_push_pair]
        intro e he
        rcases List.mem_append.1 he with he | he
        · exact (htb e (by rw [back?_toList hback]; exact List.mem_append_left _ he)).grow hgrow'
            (fun d j h => List.mem_cons_of_mem _ h) (Nat.le_refl _)
        · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
          have hc' := List.mem_reverse.1 hc
          intro n w hw
          obtain ⟨d', j', n', hp, hpr, hS, hn, hpos⟩ := htbl' n w hw
          have hcb := (hchild c hc').2
          refine ⟨d', j', n', hp, ?_, hS, hn, .inl ⟨?_, ?_⟩⟩
          · rcases hpr with h | ⟨rfl, -⟩
            · exact List.mem_cons_of_mem _ h
            · exact List.mem_cons_self ..
          · rintro rfl
            rcases hpos with ⟨-, ha⟩ | ⟨-, rfl, -⟩
            · have h1 := (ha.rank_le hrank').1
              have h2 := hrank' _ _ hcb
              omega
            · exact hcbi _ hc' rfl
          · rcases hpos with ⟨-, ha⟩ | ⟨-, rfl, -⟩
            · exact .up hcb ha
            · exact .up hcb (.refl _)
      · intro i b0 hb0
        rw [getElem!_set!_block _ _ _ _ (by rw [hsz]; exact hbil)]
        by_cases hib : bi = i
        · subst hib
          rw [hb] at hb0; cases hb0
          refine ⟨fun h => absurd (List.mem_cons_self ..) h, fun _ => ⟨body'.toList, by simp, ?_⟩⟩
          simp only [ite_true]
          exact hbody'
        · simp only [hib, ite_false, List.mem_cons, not_or]
          refine ⟨fun h => (hout i b0 hb0).1 h.2, fun h => ?_⟩
          rcases h with rfl | h
          · exact absurd rfl hib
          obtain ⟨body, he, hrel⟩ := (hout i b0 hb0).2 h
          refine ⟨body, he, ?_⟩
          rw [map_renStmt_grow hgrow'.le hgrow'.cf hgrow'.cf' hrel]
          congr 1
          apply List.filter_congr
          intro st hst
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hst
          exact (keepG_grow hu hgrow' hsub' hb0 hj h).symm
  · -- the end: the output
    rintro ⟨S, out, rem, stk⟩ ⟨Done, -, -, hsub, -, hsz, hout⟩
    simp only at hsub hsz hout ⊢
    refine ⟨hsub.mono fun _ _ _ => trivial, ?_⟩
    simp only [gvnF, gB]
    rw [apply_eq]
    congr 1
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_map, Array.getElem?_toList]
    cases hb : f.blocks[i]? with
    | none =>
      have : out.size ≤ i := by
        rw [hsz]; exact Nat.le_of_not_lt fun h => by rw [List.getElem?_eq_getElem h] at hb; cases hb
      simp [Array.getElem?_eq_none this]
    | some b =>
      have hi : i < out.size := hsz ▸ (List.getElem?_eq_some_iff.1 hb).1
      rw [Array.getElem?_eq_getElem hi]
      simp only [Option.map_some, Option.some.injEq]
      have e : out[i] = out[i]! := (getElem!_pos out i hi).symm
      rw [e]
      by_cases hd : i ∈ Done
      · obtain ⟨body, he, hbody⟩ := (hout i b hb).2 hd
        rw [he]; simp [gB, hbody]
      · rw [(hout i b hb).1 hd]
        have hall : b.body.filter (keepG S) = b.body := by
          apply List.filter_eq_self.2
          intro st hst
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hst
          exact keepG_of_unprocessed hu hsub hb hj hd
        simp [gB, hall]

/-! ## The output: definition sites, types, availability -/

theorem exists_fidx_map {p : Stmt → Bool} {F : Stmt → Stmt} {l : List Stmt} {k' : Nat} {t : Stmt}
    (h : ((l.filter p).map F)[k']? = some t) :
    ∃ k st, l[k]? = some st ∧ p st = true ∧ fidx p l k = k' ∧ t = F st := by
  rw [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨st, hst, rfl⟩ := h
  obtain ⟨k, hk, hp, rfl⟩ := exists_fidx p l k' st hst
  exact ⟨k, st, hk, hp, rfl, rfl⟩

theorem termCalls_mapTerm (σ : ValueId → ValueId) (t : Terminator) :
    termCalls (mapTerm σ t) = (termCalls t).map (mapBlockCall σ) := by
  cases t <;> simp [termCalls, mapTerm]

section Out

variable {f : Function} {S : Subst}

theorem gvnF_get (i : Nat) : (gvnF f S).blocks[i]? = (f.blocks[i]?).map (gB S) := by
  simp [gvnF]

theorem gvnF_build : Cfg.build (gvnF f S) = Cfg.build f := by
  apply build_congr
  simp only [cfgShape, gvnF, List.map_map]
  apply List.map_congr_left
  intro b _
  simp [gB, termSuccs_mapTerm]

theorem gvnF_stmtTys (st : Stmt) : stmtTys (gvnF f S) (renStmt S.find st) = stmtTys f st := by
  simp only [stmtTys, renStmt, gvnF, resultTypes_mapOperands]

theorem gvnF_stmtEvs (i : Nat) (st : Stmt) :
    stmtEvs (gvnF f S) i (renStmt S.find st) = stmtEvs f i st := by
  unfold stmtEvs; rw [gvnF_stmtTys]; rfl

theorem gvnF_arity (h : Arity f) : Arity (gvnF f S) := by
  intro b hb st hst
  simp only [gvnF, List.mem_map] at hb
  obtain ⟨b0, hb0, rfl⟩ := hb
  simp only [gB, List.mem_map, List.mem_filter] at hst
  obtain ⟨st0, ⟨hst0, -⟩, rfl⟩ := hst
  rw [gvnF_stmtTys]
  simpa [renStmt] using h b0 hb0 st0 hst0

theorem gvnF_defList_sublist : (defList (gvnF f S)).Sublist (defList f) := by
  unfold defList
  rw [show (gvnF f S).blocks = f.blocks.map (gB S) from rfl, List.zipIdx_map, List.flatMap_map]
  apply flatMap_sublist
  rintro ⟨b, i⟩ _
  simp only [Prod.map, id, blockEvs, gB, List.flatMap_map, gvnF_stmtEvs]
  exact (Sublist.flatMap' List.filter_sublist _).append_left _

theorem gvnF_mem_defSites {v : ValueId} {s : Nat × Nat} :
    (v, s) ∈ defSites (gvnF f S) ↔ ∃ i b, f.blocks[i]? = some b ∧
      ((∃ p ∈ b.params, p.1 = v ∧ s = (i, 0)) ∨
        ∃ j st, b.body[j]? = some st ∧ keepG S st = true ∧ v ∈ st.results ∧
          s = (i, fidx (keepG S) b.body j + 1)) := by
  rw [mem_defSites]
  simp only [gvnF_get, Option.map_eq_some_iff]
  constructor
  · rintro ⟨i, b', ⟨b, hb, rfl⟩, h | ⟨j', st, hst, hv, rfl⟩⟩
    · exact ⟨i, b, hb, .inl h⟩
    · obtain ⟨j, st0, hj, hk, rfl, rfl⟩ := exists_fidx_map hst
      exact ⟨i, b, hb, .inr ⟨j, st0, hj, hk, hv, rfl⟩⟩
  · rintro ⟨i, b, hb, h | ⟨j, st, hj, hk, hv, rfl⟩⟩
    · exact ⟨i, _, ⟨b, hb, rfl⟩, .inl h⟩
    · refine ⟨i, _, ⟨b, hb, rfl⟩, .inr ⟨_, renStmt S.find st, ?_, hv, rfl⟩⟩
      simp only [gB, List.getElem?_map, getElem?_filter_fidx _ b.body j st hj hk, Option.map_some]

end Out

/-- Alignment of a body with a filtered, renamed copy: kept statements match, the others are
deletable and match no kept statement. -/
theorem align_filter_map (c : EditCtx) (p : Stmt → Bool) :
    ∀ (l : List Stmt) (k0 : Nat),
      (∀ s ∈ l, p s = true → c.keepOk s (renStmt c.σ s) = true) →
      (∀ j s, l[j]? = some s → p s = false →
        c.delOk s (k0 + fidx p l j) = true ∧ ∀ t ∈ l, p t = true → c.keepOk s (renStmt c.σ t) = false) →
      c.align l ((l.filter p).map (renStmt c.σ)) k0 = true
  | [], k0, _, _ => by simp [EditCtx.align]
  | s :: l, k0, hk, hd => by
    have hk' := fun s' (hs' : s' ∈ l) => hk s' (List.mem_cons_of_mem _ hs')
    by_cases hp : p s = true
    · simp only [List.filter_cons, hp, ite_true, List.map_cons]
      rw [EditCtx.align]
      simp only [hk s (List.mem_cons_self ..) hp, ite_true]
      refine align_filter_map c p l (k0 + 1) hk' (fun j s' hj hp' => ?_)
      have := hd (j + 1) s' (by simpa using hj) hp'
      rw [fidx_succ] at this
      simp only [hp, ite_true] at this
      exact ⟨by rw [show k0 + 1 + fidx p l j = k0 + (1 + fidx p l j) by omega]; exact this.1,
        fun t ht => this.2 t (List.mem_cons_of_mem _ ht)⟩
    · have hpf : p s = false := by simpa using hp
      have h0 := hd 0 s rfl hpf
      simp only [fidx, List.take_zero, List.filter_nil, List.length_nil, Nat.add_zero] at h0
      have ih := align_filter_map c p l k0 hk' (fun j s' hj hp' => by
        have := hd (j + 1) s' (by simpa using hj) hp'
        rw [fidx_succ] at this
        simp only [hpf, Bool.false_eq_true, ite_false, Nat.zero_add] at this
        exact ⟨this.1, fun t ht => this.2 t (List.mem_cons_of_mem _ ht)⟩)
      simp only [List.filter_cons, hpf, Bool.false_eq_true, ite_false]
      cases hf : l.filter p with
      | nil =>
        rw [hf] at ih
        rw [List.map_nil, EditCtx.align, h0.1, Bool.true_and]
        simpa using ih
      | cons t ts =>
        have ht : t ∈ l ∧ p t = true := List.mem_filter.1 (hf ▸ List.mem_cons_self ..)
        rw [hf, List.map_cons] at ih
        rw [List.map_cons, EditCtx.align]
        have hne := h0.2 t (List.mem_cons_of_mem _ ht.1) ht.2
        simp only [hne, Bool.false_eq_true, ite_false, h0.1, ite_true]
        exact ih

section OutFacts

variable {f : Function} {info : Info} (hc : Checked f info) {S : Subst}
  (hS : SubOk f info.cfg.idom (fun _ _ => True) S)
include hc hS

theorem gvnF_nodup : ((defList (gvnF f S)).map (·.1)).Nodup :=
  (gvnF_defList_sublist.map (·.1)).nodup hc.nodup

theorem gvnF_unique : UniqueDefs (gvnF f S) := by
  unfold UniqueDefs
  rw [defSites_map_fst (gvnF_arity hc.arity)]
  exact gvnF_nodup hc hS

/-- A renamed result is the single result of a deleted statement. -/
theorem key_pureAt {d j : Nat} {b : Block} {st : Stmt} (hb : f.blocks[d]? = some b)
    (hst : b.body[j]? = some st) {r w : ValueId} (hr : r ∈ st.results) (hw : S[r]? = some w) :
    st.results = [r] ∧ keepG S st = false := by
  obtain ⟨d0, j0, m, d', j', n, hp, -, -, -, -, -, -⟩ := hS r w hw
  have := site_unique hc.unique hp.site (mem_defSites.2 ⟨d, b, hb, .inr ⟨j, st, hst, hr, rfl⟩⟩)
  simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at this
  obtain ⟨rfl, rfl⟩ := this
  obtain ⟨b', st', hb', hst', hr', -, -⟩ := hp
  rw [hb] at hb'; cases hb'
  rw [hst] at hst'; cases hst'
  refine ⟨hr', ?_⟩
  simp [keepG, hr', Std.HashMap.contains_eq_isSome_getElem?, hw]

theorem kept_not_key {d j : Nat} {b : Block} {st : Stmt} (hb : f.blocks[d]? = some b)
    (hst : b.body[j]? = some st) (hk : keepG S st = true) {r : ValueId} (hr : r ∈ st.results) :
    S[r]? = none := by
  cases hw : S[r]? with
  | none => rfl
  | some w => rw [(key_pureAt hc hS hb hst hr hw).2] at hk; cases hk

theorem param_not_key {d : Nat} {b : Block} (hb : f.blocks[d]? = some b) {p : ValueId × Ty}
    (hp : p ∈ b.params) : S[p.1]? = none := by
  cases hw : S[p.1]? with
  | none => rfl
  | some w =>
    obtain ⟨d0, j0, m, -, -, -, hpa, -, -, -, -, -, -⟩ := hS p.1 w hw
    have := site_unique hc.unique hpa.site (mem_defSites.2 ⟨d, b, hb, .inl ⟨p, hp, rfl, rfl⟩⟩)
    simp at this

omit hc hS in
theorem keepG_of_none {st : Stmt} {x : ValueId} (hx : x ∈ st.results) (hn : S[x]? = none) :
    ∀ r, st.results = [r] → keepG S st = true := by
  intro r hr
  rw [hr] at hx; simp at hx; subst hx
  simp [keepG, hr, Std.HashMap.contains_eq_isSome_getElem?, hn]

omit hc hS in
theorem keepG_of_none' {st : Stmt} {x : ValueId} (hx : x ∈ st.results) (hn : S[x]? = none) :
    keepG S st = true := by
  unfold keepG
  split
  · rename_i r hr; have := keepG_of_none (S := S) hx hn r hr; simpa [keepG, hr] using this
  · rfl

/-- The site of an unrenamed value in the output. -/
theorem gvn_site {x : ValueId} {d t : Nat} (hs : (x, (d, t)) ∈ defSites f) (hn : S[x]? = none) :
    ∃ b, f.blocks[d]? = some b ∧ (x, (d, fpos (keepG S) b t)) ∈ defSites (gvnF f S) ∧
      ∀ j0, t = j0 + 1 → ∃ st0, b.body[j0]? = some st0 ∧ keepG S st0 = true := by
  obtain ⟨i, b, hb, ⟨p, hp, rfl, he⟩ | ⟨j, st, hj, hv, he⟩⟩ := mem_defSites.1 hs
  · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact ⟨b, hb, gvnF_mem_defSites.2 ⟨d, b, hb, .inl ⟨p, hp, rfl, rfl⟩⟩, fun j0 h => by cases h⟩
  · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    have hk : keepG S st = true := keepG_of_none' hv hn
    refine ⟨b, hb, gvnF_mem_defSites.2 ⟨d, b, hb, .inr ⟨j, st, hj, hk, hv, rfl⟩⟩, fun j0 h => ?_⟩
    cases h; exact ⟨st, hj, hk⟩

omit hS in
theorem gvn_idom : (wfData (gvnF f S) (coreInfo (gvnF f S))).idom = (wfData f info).idom := by
  simp [wfData, coreInfo, gvnF_build, hc.info_eq]

omit hS in
theorem gvn_rank : (wfData (gvnF f S) (coreInfo (gvnF f S))).rank = (wfData f info).rank := by
  simp [wfData, coreInfo, gvnF_build, hc.info_eq]

omit hS in
theorem gvn_index : (wfData (gvnF f S) (coreInfo (gvnF f S))).index = (wfData f info).index := by
  simp [wfData, coreInfo, gvnF_build, hc.info_eq]

theorem gvn_dm {x : ValueId} {s : Nat × Nat} (h : (x, s) ∈ defSites (gvnF f S)) :
    (wfData (gvnF f S) (coreInfo (gvnF f S))).dm x = some s :=
  (defMap_get_iff (gvnF_unique hc hS) x s).2 h

/-- **Availability moves to the output** (renamed operand, filtered position). -/
theorem gvn_avail {i : Nat} {b : Block} (hb : f.blocks[i]? = some b) {j : Nat} {x : ValueId}
    (hA : Avail (wfData f info) i j x) :
    Avail (wfData (gvnF f S) (coreInfo (gvnF f S))) i (fidx (keepG S) b.body j) (S.find x) := by
  have hcf : ChainFree S := hS.chainFree
  have hrank := hc.wf.rank
  obtain ⟨d, t, hd, h⟩ := hA
  have hs := hc.wf.sitesRev x (d, t) hd
  cases hx : S[x]? with
  | none =>
    rw [find_none hx]
    obtain ⟨bd, hbd, hs', hk⟩ := gvn_site hc hS hs hx
    refine ⟨d, fpos (keepG S) bd t, gvn_dm hc hS hs', ?_⟩
    rcases h with ⟨rfl, ht⟩ | ⟨hne, ha⟩
    · left
      refine ⟨rfl, ?_⟩
      rw [hb] at hbd; cases hbd
      cases t with
      | zero => simp [fpos]
      | succ j0 =>
        obtain ⟨st0, h0, hk0⟩ := hk j0 rfl
        exact fidx_lt _ b.body (by omega) h0 hk0
    · exact .inr ⟨hne, by rw [gvn_idom hc]; exact ha⟩
  | some w =>
    rw [find_chainFree hcf, hx, Option.getD_some]
    obtain ⟨d0, j0, m, d', j1, n, hpx, -, hpw, -, hwS, -, hpos⟩ := hS x w hx
    have := site_unique hc.unique hs hpx.site
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    obtain ⟨bw, hbw, hsw, hkw⟩ := gvn_site hc hS hpw.site hwS
    obtain ⟨st1, h1, hk1⟩ := hkw j1 rfl
    refine ⟨d', fidx (keepG S) bw.body j1 + 1, gvn_dm hc hS hsw, ?_⟩
    rcases h with ⟨rfl, ht⟩ | ⟨hne, ha⟩
    · rcases hpos with ⟨rfl, hj⟩ | ⟨hne', ha'⟩
      · left
        refine ⟨rfl, ?_⟩
        rw [hb] at hbw; cases hbw
        exact fidx_lt _ b.body (by omega) h1 hk1
      · exact .inr ⟨hne', by rw [gvn_idom hc]; exact ha'⟩
    · rcases hpos with ⟨rfl, -⟩ | ⟨hne', ha'⟩
      · exact .inr ⟨hne, by rw [gvn_idom hc]; exact ha⟩
      · refine .inr ⟨fun he => ?_, by rw [gvn_idom hc]; exact ha'.trans ha⟩
        subst he
        exact hne (Anc.antisymm hrank ha ha')

/-- A defined value keeps its event in the output if it is not renamed. -/
theorem gvn_def_kept {e : DefEv} (he : e ∈ defList f) (hn : S[e.1]? = none) :
    e ∈ defList (gvnF f S) := by
  obtain ⟨i, b, hb, h⟩ := mem_defList.1 he
  rw [mem_defList]
  refine ⟨i, gB S b, by rw [gvnF_get, hb]; rfl, ?_⟩
  rcases h with h | ⟨st, hst, hes⟩
  · exact .inl h
  · refine .inr ⟨renStmt S.find st, ?_, by rw [gvnF_stmtEvs]; exact hes⟩
    simp only [gB, List.mem_map, List.mem_filter]
    exact ⟨st, ⟨hst, keepG_of_none' (stmtEvs_fst_mem hes) hn⟩, rfl⟩

/-- **Types are kept** under the renaming. -/
theorem gvn_tm {x : ValueId} (hx : x ∈ (defList f).map (·.1)) :
    (wfData (gvnF f S) (coreInfo (gvnF f S))).tm (S.find x) = (wfData f info).tm x := by
  have hcf : ChainFree S := hS.chainFree
  have hn' := gvnF_nodup hc hS
  have hkeep : ∀ y ∈ (defList f).map (·.1), S[y]? = none →
      (wfData (gvnF f S) (coreInfo (gvnF f S))).tm y = (wfData f info).tm y := by
    intro y hy hyn
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
    rw [tm_of_defList hn' (gvn_def_kept hc hS he hyn)]
    simp only [wfData, hc.info_eq, coreInfo, Std.HashMap.get?_eq_getElem?]
    exact ((defsState_get f hc.nodup).1 e he).1.symm
  cases hxs : S[x]? with
  | none => rw [find_none hxs]; exact hkeep x hx hxs
  | some w =>
    rw [find_chainFree hcf, hxs, Option.getD_some]
    obtain ⟨d0, j0, m, d', j1, n, hpx, -, hpw, -, hwS, hmap, -⟩ := hS x w hxs
    obtain ⟨bw, stw, hbw, hstw, hrw, rfl, -⟩ := hpw
    obtain ⟨bx, stx, hbx, hstx, hrx, rfl, -⟩ := hpx
    have hwd : w ∈ (defList f).map (·.1) := hc.defined (hc.wf.sites w _ (mem_defSites.2
      ⟨d', bw, hbw, .inr ⟨j1, stw, hstw, by simp [hrw], rfl⟩⟩))
    rw [hkeep w hwd hwS]
    obtain ⟨tsw, htw, hlw, hrtw⟩ := hc.wf.results d' bw hbw j1 stw hstw
    obtain ⟨tsx, htx, hlx, hrtx⟩ := hc.wf.results d0 bx hbx j0 stx hstx
    have heq : tsw = tsx := by
      have e1 := resultTypes_mapOperands S.find stw.inst (sigOf f) (fun _ => none)
      have e2 := resultTypes_mapOperands S.find stx.inst (sigOf f) (fun _ => none)
      rw [hmap] at e1
      rw [e1] at e2
      rw [htw, htx] at e2
      exact Option.some.inj e2
    rw [hrtw 0 w (by simp [hrw]), hrtx 0 x (by simp [hrx]), heq]


omit hc hS in
theorem gvnF_blocks : (gvnF f S).blocks = f.blocks.map (gB S) := rfl

/-- **The output of GVN satisfies the certificate facts.** -/
theorem gvn_wf : Wf (gvnF f S) (wfData (gvnF f S) (coreInfo (gvnF f S))) := by
  have hW := hc.wf
  have hn' := gvnF_nodup hc hS
  refine { ids := ?_, sites := ?_, sitesRev := ?_, root := ?_, rank := ?_, params := ?_,
           uses := ?_, results := ?_, pure := ?_, termUses := ?_, edges := ?_ }
  · intro i b' hb'
    rw [gvnF_get, Option.map_eq_some_iff] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    rw [gvn_index hc]; exact hW.ids i b hb
  · exact fun v s hs => (defMap_get_iff (gvnF_unique hc hS) v s).2 hs
  · exact fun v s hs => (defMap_get_iff (gvnF_unique hc hS) v s).1 hs
  · rw [gvn_idom hc]; exact hW.root
  · rw [gvn_idom hc, gvn_rank hc]; exact hW.rank
  · exact fun i b hb p hp => tm_param hn' hb hp
  · intro i b' hb' j' st' hst v hv
    rw [gvnF_get, Option.map_eq_some_iff] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    obtain ⟨j, st, hj, hk, rfl, rfl⟩ := exists_fidx_map hst
    simp only [renStmt, operands_mapOperands, List.mem_map] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    exact gvn_avail hc hS hb (hW.uses i b hb j st hj x hx)
  · intro i b' hb' j' st' hst
    have hb'' := hb'
    rw [gvnF_get, Option.map_eq_some_iff] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    obtain ⟨j, st, hj, hk, rfl, rfl⟩ := exists_fidx_map hst
    obtain ⟨ts, hts, hlen, -⟩ := hW.results i b hb j st hj
    have hts' : (renStmt S.find st).inst.resultTypes (sigOf (gvnF f S)) (fun _ => none) = some ts := by
      simp only [renStmt, resultTypes_mapOperands]; exact hts
    exact ⟨ts, hts', hlen, fun n r hr => tm_result hn' hb'' (List.mem_of_getElem? hst) hts' hlen hr⟩
  · intro i b' hb' j' st' hst hp
    rw [gvnF_get, Option.map_eq_some_iff] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    obtain ⟨j, st, hj, hk, rfl, rfl⟩ := exists_fidx_map hst
    simp only [renStmt, isPure_mapOperands] at hp ⊢
    rw [pureTyped_mapOperands, ← hW.pure i b hb j st hj hp]
    apply pureTyped_congr _ rfl rfl
    intro x hx
    exact gvn_tm hc hS (hc.op_defined hb (List.mem_of_getElem? hj) hx)
  · intro i b' hb' v hv
    rw [gvnF_get, Option.map_eq_some_iff] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    simp only [gB, termOperands_mapTerm, List.mem_map] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    have := gvn_avail hc hS hb (hW.termUses i b hb x hx)
    rw [fidx_length] at this
    simpa [gB] using this
  · intro i b' hb' id hid
    rw [gvnF_get, Option.map_eq_some_iff] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    simp only [gB, termSuccs_mapTerm] at hid
    obtain ⟨j, b0, hj, hb0, hid0, hanc⟩ := hW.edges i b hb id hid
    refine ⟨j, gB S b0, by rw [gvn_index hc]; exact hj, by rw [gvnF_get, hb0]; rfl, hid0, ?_⟩
    rw [gvn_idom hc]; exact hanc

theorem gvn_types {x : ValueId} (hx : x ∈ (defList f).map (·.1)) :
    (defsState (gvnF f S)).1[S.find x]? = (defsState f).1[x]? := by
  have := gvn_tm hc hS hx
  simpa [wfData, coreInfo, hc.info_eq, Std.HashMap.get?_eq_getElem?] using this

/-- **`checkCore` accepts GVN's output.** -/
theorem gvn_coreOk : CoreOk (gvnF f S) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc.core
  have hn' := gvnF_nodup hc hS
  refine coreOk_of_wf (by rw [gvnF_build]; exact h1) (by rw [gvnF_build]; exact h2)
    (by rw [gvnF_build]; exact h3) ?_ ?_ (gvn_wf hc hS) ?_ ?_
  · rw [defsOk_iff]
    exact ⟨gvnF_arity hc.arity, (allAlong_evC_iff _ _).2 ⟨fun e _ => by simp, hn'⟩⟩
  · rw [gvnF_blocks, getElem!_map_params f.blocks (gB S) (fun _ => rfl)]; exact h5
  · intro i b' hb' bc hbc
    rw [gvnF_get, Option.map_eq_some_iff] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    simp only [gB, termCalls_mapTerm, List.mem_map] at hbc
    obtain ⟨bc0, hbc0, rfl⟩ := hbc
    obtain ⟨-, -, hcalls, -⟩ := h6 (b, i) (List.mem_zipIdx_iff_getElem?.2 hb)
    obtain ⟨j, hj, hok⟩ := hcalls bc0 hbc0
    refine ⟨j, by rw [gvnF_build]; exact hj, ?_⟩
    rw [gvnF_blocks, getElem!_map_params f.blocks (gB S) (fun _ => rfl)]
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, mapBlockCall, List.length_map,
      List.zip_map_right, List.mem_map] at hok ⊢
    refine ⟨hok.1, ?_⟩
    rintro _ ⟨⟨p, a⟩, hpa, rfl⟩
    have ha : a ∈ bc0.args := (List.of_mem_zip hpa).2
    have hta := termCalls_args hbc0 ha
    simp only [Prod.map, id, Std.HashMap.get?_eq_getElem?]
    rw [gvn_types hc hS (hc.term_defined hb hta)]
    simpa [Std.HashMap.get?_eq_getElem?] using hok.2 (p, a) hpa
  · intro b' hb'
    simp only [gvnF_blocks, List.mem_map] at hb'
    obtain ⟨b, hbm, rfl⟩ := hb'
    obtain ⟨i, hb⟩ := List.mem_iff_getElem?.1 hbm
    obtain ⟨-, -, -, hbr⟩ := h6 (b, i) (List.mem_zipIdx_iff_getElem?.2 hb)
    simp only [gB]
    revert hbr
    cases ht : b.term <;> simp only [brTableOk, mapTerm, imp_self]
    intro h
    rw [Std.HashMap.get?_eq_getElem?] at h ⊢
    rename_i x _ _
    have hx : x ∈ termOperands b.term := brTable_operand ht
    rw [gvn_types hc hS (hc.term_defined hb hx)]; exact h

/-- **`check` accepts GVN's output.** -/
theorem gvn_check : check (gvnF f S) = .ok (coreInfo (gvnF f S)) := by
  have hw : wfCert (gvnF f S) (coreInfo (gvnF f S)).cfg (coreInfo (gvnF f S)).types = true :=
    wfCert_complete (gvn_wf hc hS)
  exact (check_ok_iff (gvnF f S) (coreInfo (gvnF f S))).2 ⟨gvn_coreOk hc hS, rfl, hw⟩



/-- **The edit validator accepts GVN's output** (renaming `S.find`). -/
theorem gvn_editOk : editOk S.find f (gvnF f S) info (coreInfo (gvnF f S)) = true := by
  have hcf := hS.chainFree
  have hu := hc.unique
  have hW' := gvn_wf hc hS
  have hidom : (coreInfo (gvnF f S)).cfg.idom = info.cfg.idom := gvn_idom hc
  simp only [editOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨by simp [sameHeader, gvnF], hidom⟩, by simp [gvnF]⟩, ?_⟩, ?_⟩
  · rintro ⟨⟨b, b'⟩, i⟩ hx
    have hx' := List.mem_zipIdx_iff_getElem?.1 hx
    simp only [List.getElem?_zip_eq_some] at hx'
    obtain ⟨hb, hb'⟩ := hx'
    rw [gvnF_get, hb] at hb'
    simp only [Option.map_some, Option.some.injEq] at hb'
    subst hb'
    simp only [gB, true_and, and_true]
    refine ⟨fun p hp => find_none (param_not_key hc hS hb hp), ?_⟩
    apply align_filter_map _ (keepG S) b.body 0
    · intro st hst hk
      simp only [EditCtx.keepOk, beq_self_eq_true, Bool.true_and, List.all_eq_true, beq_iff_eq]
      intro r hr
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hst
      exact find_none (kept_not_key hc hS hb hj hk hr)
    · intro j s hj hk
      obtain ⟨v, hv, hvS⟩ : ∃ v, s.results = [v] ∧ S.contains v = true := by
        unfold keepG at hk
        split at hk
        · rename_i v hv; exact ⟨v, hv, by simpa using hk⟩
        · cases hk
      obtain ⟨w, hw⟩ : ∃ w, S[v]? = some w := by
        cases h : S[v]? with
        | none => simp [Std.HashMap.contains_eq_isSome_getElem?, h] at hvS
        | some w => exact ⟨w, rfl⟩
      obtain ⟨d0, j0, m, d', j1, n, hpv, -, hpw, -, hwS, hmap, hpos⟩ := hS v w hw
      have := site_unique hu hpv.site (mem_defSites.2 ⟨i, b, hb, .inr ⟨j, s, hj, by simp [hv], rfl⟩⟩)
      simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at this
      obtain ⟨rfl, rfl⟩ := this
      obtain ⟨b1, s1, hb1, hs1, -, hm, hpm⟩ := hpv
      rw [hb] at hb1; cases hb1
      rw [hj] at hs1; cases hs1
      subst hm
      have hfw : S.find v = w := by rw [find_chainFree hcf, hw]; rfl
      obtain ⟨bw, hbw, hsw, hkw⟩ := gvn_site hc hS hpw.site hwS
      obtain ⟨stw, hstw, hkstw⟩ := hkw j1 rfl
      refine ⟨?_, fun t ht hkt => ?_⟩
      · simp only [EditCtx.delOk, Bool.or_eq_true, Bool.and_eq_true]
        right
        refine ⟨hpm, ?_⟩
        rw [hv]
        simp only [hfw, Bool.and_eq_true, Nat.zero_add]
        refine ⟨?_, ?_⟩
        · have hA : Avail (wfData (gvnF f S) (coreInfo (gvnF f S))) d0 (fidx (keepG S) b.body j0) w := by
            refine ⟨d', fidx (keepG S) bw.body j1 + 1, gvn_dm hc hS hsw, ?_⟩
            rcases hpos with ⟨rfl, hj1⟩ | ⟨hne, ha⟩
            · left
              refine ⟨rfl, ?_⟩
              rw [hb] at hbw; cases hbw
              exact fidx_lt _ b.body hj1 hstw hkstw
            · right; exact ⟨hne, by rw [gvn_idom hc]; exact ha⟩
          exact availB_complete hW'.rank hA
        · simp only [EditCtx.pureAt]
          have hgd : (defMap (gvnF f S)).get? w = some (d', fidx (keepG S) bw.body j1 + 1) :=
            gvn_dm hc hS hsw
          rw [hgd]
          have hgb : (gvnF f S).blocks.toArray[d']? = some (gB S bw) := by simp [gvnF_get, hbw]
          simp only [hgb]
          have hbd : (gB S bw).body[fidx (keepG S) bw.body j1]? = some (renStmt S.find stw) := by
            simp [gB, getElem?_filter_fidx _ bw.body j1 stw hstw hkstw]
          simp only [hbd]
          obtain ⟨bw', stw', hbw', hstw', hrw, hnw, hpn⟩ := hpw
          rw [hbw] at hbw'; cases hbw'
          rw [hstw] at hstw'; cases hstw'
          simp [renStmt, hrw, hnw, hmap, isPure_mapOperands, hpm]
      · simp only [EditCtx.keepOk, Bool.and_eq_false_iff]
        left
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro he
        have hr : t.results = s.results := by
          have := congrArg Stmt.results he; simpa [renStmt] using this
        obtain ⟨jt, hjt⟩ := List.mem_iff_getElem?.1 ht
        have := site_unique hu
          (show (v, (d0, jt + 1)) ∈ defSites f from
            mem_defSites.2 ⟨d0, b, hb, .inr ⟨jt, t, hjt, by simp [hr, hv], rfl⟩⟩)
          (show (v, (d0, j0 + 1)) ∈ defSites f from
            mem_defSites.2 ⟨d0, b, hb, .inr ⟨j0, s, hj, by simp [hv], rfl⟩⟩)
        simp only [Prod.mk.injEq, Nat.add_right_cancel_iff, true_and] at this
        subst this
        rw [hj] at hjt; cases hjt
        rw [hk] at hkt; cases hkt
  · rintro ⟨v, d, t⟩ hv
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hv
    have hs : (v, (d, t)) ∈ defSites f :=
      (defMap_get_iff hu v _).1 (by rw [Std.HashMap.get?_eq_getElem?]; exact hv)
    simp only
    split
    · rename_i d'' t'' hg
      have hs'' := (defMap_get_iff (gvnF_unique hc hS) _ _).1 hg
      cases hvs : S[v]? with
      | none =>
        rw [find_none hvs] at hs''
        obtain ⟨bd, hbd, hs', -⟩ := gvn_site hc hS hs hvs
        have := site_unique (gvnF_unique hc hS) hs'' hs'
        simp only [Prod.mk.injEq] at this
        rw [this.1]; exact ancB_refl _ _ _
      | some w =>
        rw [find_chainFree hcf, hvs, Option.getD_some] at hs''
        obtain ⟨d0, j0, m, d', j1, n, hpv, -, hpw, -, hwS, -, hpos⟩ := hS v w hvs
        have := site_unique hu hs hpv.site
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        obtain ⟨bw, hbw, hsw, -⟩ := gvn_site hc hS hpw.site hwS
        have := site_unique (gvnF_unique hc hS) hs'' hsw
        simp only [Prod.mk.injEq] at this
        rw [this.1]
        rcases hpos with ⟨rfl, -⟩ | ⟨-, ha⟩
        · exact ancB_refl _ _ _
        · rw [hidom]; exact ancB_complete hc.wf.rank ha
    · rfl

end OutFacts

/-- **Completeness of the GVN stage**: on a well-formed function, GVN's output passes `check` and
the edit validator with GVN's substitution, so `Opt.optimizeReport` never stops at a GVN stage. -/
theorem gvn_complete {g : Function} {info : Info} (h : check g = .ok info) (local? : Inst → Bool) :
    check (gvnFull g info local?).1 = .ok (coreInfo (gvnFull g info local?).1) ∧
      editOk (gvnFull g info local?).2.2.find g (gvnFull g info local?).1 info
        (coreInfo (gvnFull g info local?).1) = true := by
  have hc := checked_of_check h
  obtain ⟨hS, he⟩ := gvnFull_spec hc local?
  rw [he]
  exact ⟨gvn_check hc hS, gvn_editOk hc hS⟩

end Opt

namespace Opt.CompleteGvnWitness

open Clif

/-- `v1` recomputes `v0`. -/
def fn : Function where
  name := "w"
  sig := {}
  blocks := [{ id := 0, body := [{ results := [0], inst := .iconst .i32 7 },
    { results := [1], inst := .iconst .i32 7 }], term := .ret [1] }]

theorem checks : (match check fn with
    | .ok i => (gvnFull fn i (fun _ => false)).2.1 == 1
    | .error _ => false) = true := by native_decide

/-- Non-vacuity of `gvn_complete`: `fn` is well-formed, GVN removes `v1`, and the stage is
accepted. -/
theorem witness : ∃ i i', check fn = .ok i ∧ (gvnFull fn i (fun _ => false)).2.1 = 1 ∧
    check (gvnFull fn i (fun _ => false)).1 = .ok i' ∧
    editOk (gvnFull fn i (fun _ => false)).2.2.find fn (gvnFull fn i (fun _ => false)).1 i i' = true := by
  have h := checks
  split at h
  · rename_i i hi
    exact ⟨i, _, hi, by simpa using h, (gvn_complete hi _).1, (gvn_complete hi _).2⟩
  · cases h

end Opt.CompleteGvnWitness

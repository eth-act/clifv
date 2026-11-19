import FV.Opt.Proof.MidValSpec

/-!
# The block walk of `checkCert`, case by case (#1119, module (5), part 2)

Specifications of the pieces of `CC.blockOk` (`FV/Opt/MidValCert.lean`) in the form the
simulation proof uses: `pureOk_spec`, `resOk_spec`, `gPre_spec` (`g`'s pure prefix is a list of
`nop`s and checked pure statements followed by a skeleton statement or the end),
`nextSkel_of_gPre`, the walk's cases (`walk_nil_spec`, `walk_nop`, `walk_pure_spec`,
`walk_skel_spec`: a matched statement or an accepted removal), `removeOk_spec`, `blockOk_spec`
and `entryOk_spec`.
-/

namespace Opt.MidVal

open Clif

/-- The end of a block's walk: equal terminators on terms, and the entry facts of every
successor among the facts at the end (after a `try_call`, without the memory facts). -/
def EndOk (c : CC) (bi : Nat) (fb gb : Block) (S : List Fact) : Prop :=
  mapTerm c.ef fb.term = mapTerm c.eg gb.term ∧
    ∀ s ∈ termSuccs fb.term, ∃ si, c.index s = some si ∧
      ∀ F ∈ c.factsAt si, F ∈ (if fb.term.isTry then kill S else S)

/-- A pure statement checked by `pureOk`: its single result's term is the node of its operands'
terms (or the normaliser's term for it), typed, at a site no later than `bound`. -/
structure PureOk (c : CC) (env : ValueId → Nat) (ty : ValueId → Option Ty) (st : Stmt)
    (bound : Nat × Nat) (t : Nat) : Prop where
  res : st.results.length = 1
  term : ∀ r ∈ st.results, env r = t
  typed : floatTyped ty st.inst = true
  node : c.tm t = some (.node (mapOperands env st.inst)) ∨
    ((c.norm c.cert.tms (mapOperands env st.inst)).isSome ∧
      c.norm c.cert.tms (mapOperands env st.inst) = c.tm t)
  site : c.le (c.siteOf t) bound = true

theorem pureOk_spec {c : CC} {env : ValueId → Nat} {ty : ValueId → Option Ty} {st : Stmt}
    {bound : Nat × Nat} {t : Nat} (h : c.pureOk env ty st bound = some t) :
    PureOk c env ty st bound t := by
  unfold CC.pureOk at h
  cases hr : st.results with
  | nil => simp [hr] at h
  | cons r rs =>
    cases rs with
    | cons _ _ => simp [hr] at h
    | nil =>
      simp only [hr] at h
      by_cases hc : (floatTyped ty st.inst &&
          (c.tm (env r) == some (Tm.node (mapOperands env st.inst)) ||
            (c.norm c.cert.tms (mapOperands env st.inst)).isSome &&
              c.norm c.cert.tms (mapOperands env st.inst) == c.tm (env r)) &&
          c.le (c.siteOf (env r)) bound) = true
      · simp only [hc, ite_true, Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨h1, h2⟩, h3⟩ := hc
        refine ⟨by rw [hr]; rfl, fun r' hr' => by rw [hr] at hr'; simp at hr'; rw [hr'], h1, ?_, h3⟩
        rcases h2 with h2 | ⟨h2, h2'⟩
        · exact .inl h2
        · exact .inr ⟨h2, h2'⟩
      · simp only [hc, Bool.false_eq_true, ite_false] at h
        cases h

theorem resOk_spec {c : CC} {env : ValueId → Nat} {rs : List ValueId} {bi k : Nat}
    (h : c.resOk env rs bi k = true) :
    ∀ j r, rs[j]? = some r → c.tm (env r) = some (.res bi k j) := by
  intro j r hr
  simp only [CC.resOk, List.all_eq_true, beq_iff_eq] at h
  exact h (r, j) (List.mem_zipIdx_iff_getElem?.2 (by simpa using hr))

/-- A statement of `g`'s pure prefix. -/
def GPreStmt (c : CC) (bound : Nat × Nat) (S : List Fact) (st : Stmt) : Prop :=
  st.inst = .nop ∨ (st.inst ≠ .nop ∧ pureK st.inst = true ∧ ∃ t, PureOk c c.eg c.gty st bound t ∧
    (partialK st.inst = true → Fact.defd t ∈ S))

/-- The next statement of `g` after its pure prefix: none or a skeleton statement. -/
def SkelHead : List Stmt → Prop
  | [] => True
  | t :: _ => t.inst ≠ .nop ∧ pureK t.inst = false

theorem gPre_spec {c : CC} {bound : Nat × Nat} {S : List Fact} :
    ∀ (gs : List Stmt) (k' : Nat) (rest : List Stmt) (k'' : Nat),
      c.gPre bound S gs k' = some (rest, k'') →
      ∃ pre, gs = pre ++ rest ∧ k'' = k' + pre.length ∧ (∀ st ∈ pre, GPreStmt c bound S st) ∧
        SkelHead rest
  | [], k', rest, k'', h => by
    simp only [CC.gPre, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨[], by simp, by simp, ?_, trivial⟩
    intro st hst; simp at hst
  | t :: ts, k', rest, k'', h => by
    unfold CC.gPre at h
    by_cases hn : t.inst = .nop
    · simp only [hn, beq_self_eq_true, ite_true] at h
      obtain ⟨pre, h1, h2, h3, h4⟩ := gPre_spec ts (k' + 1) rest k'' h
      refine ⟨t :: pre, by simp [h1], by simp [h2]; omega, fun st hst => ?_, h4⟩
      rcases List.mem_cons.1 hst with rfl | hst
      · exact .inl hn
      · exact h3 st hst
    · have hn' : (t.inst == .nop) = false := by simpa using hn
      simp only [hn', Bool.false_eq_true, ite_false] at h
      by_cases hp : pureK t.inst = true
      · simp only [hp, ite_true] at h
        split at h
        · rename_i tt htt
          by_cases hq : (!partialK t.inst || S.contains (.defd tt)) = true
          · simp only [hq, ite_true] at h
            obtain ⟨pre, h1, h2, h3, h4⟩ := gPre_spec ts (k' + 1) rest k'' h
            refine ⟨t :: pre, by simp [h1], by simp [h2]; omega, fun st hst => ?_, h4⟩
            rcases List.mem_cons.1 hst with rfl | hst
            · refine .inr ⟨hn, hp, tt, pureOk_spec htt, fun hpk => ?_⟩
              simp only [hpk, Bool.not_true, Bool.false_or, List.contains_iff_mem] at hq
              exact hq
            · exact h3 st hst
          · simp only [hq, Bool.false_eq_true, ite_false] at h
            cases h
        · cases h
      · simp only [hp, Bool.false_eq_true, ite_false, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[], by simp, by simp, ?_, ⟨hn, by simpa using hp⟩⟩
        intro st hst; simp at hst

theorem nextSkel_append {pre rest : List Stmt} (hpre : ∀ st ∈ pre, st.inst = .nop ∨ pureK st.inst = true) :
    nextSkel (pre ++ rest) = nextSkel rest := by
  induction pre with
  | nil => rfl
  | cons st pre ih =>
    have h := hpre st (by simp)
    have h' : (st.inst == .nop || pureK st.inst) = true := by
      rcases h with h | h <;> simp [h]
    simp only [List.cons_append, nextSkel, h', ite_true]
    exact ih fun s hs => hpre s (by simp [hs])

theorem nextSkel_skelHead {t : Stmt} {ts : List Stmt} (h : SkelHead (t :: ts)) :
    nextSkel (t :: ts) = some t := by
  obtain ⟨h1, h2⟩ := h
  have : (t.inst == .nop || pureK t.inst) = false := by simp [h1, h2]
  simp [nextSkel, this]

theorem GPreStmt.nopOrPure {c : CC} {bound : Nat × Nat} {S : List Fact} {st : Stmt}
    (h : GPreStmt c bound S st) : st.inst = .nop ∨ pureK st.inst = true := by
  rcases h with h | ⟨_, h, _⟩
  · exact .inl h
  · exact .inr h

/-! ## The walk -/

theorem walk_nil_spec {c : CC} {bi : Nat} {gs : List Stmt} {k k' : Nat} {S Send : List Fact}
    (h : c.walk bi [] gs k k' S = some Send) :
    Send = S ∧ ∃ k'', c.gPre (bi, k) S gs k' = some ([], k'') := by
  simp only [CC.walk] at h
  split at h
  · rename_i k'' hg
    cases h
    exact ⟨rfl, k'', hg⟩
  · cases h

theorem walk_nop {c : CC} {bi : Nat} {s : Stmt} {fs gs : List Stmt} {k k' : Nat} {S : List Fact}
    (h : s.inst = .nop) : c.walk bi (s :: fs) gs k k' S = c.walk bi fs gs (k + 1) k' S := by
  simp [CC.walk, h]

theorem walk_pure_spec {c : CC} {bi : Nat} {s : Stmt} {fs gs : List Stmt} {k k' : Nat}
    {S Send : List Fact} (hn : s.inst ≠ .nop) (hp : pureK s.inst = true)
    (h : c.walk bi (s :: fs) gs k k' S = some Send) :
    ∃ t, PureOk c c.ef c.fty s (bi, k + 1) t ∧
      c.walk bi fs gs (k + 1) k' (if partialK s.inst then .defd t :: S else S) = some Send := by
  have hn' : (s.inst == .nop) = false := by simpa using hn
  simp only [CC.walk, hn', hp, Bool.false_eq_true, ite_false, ite_true] at h
  split at h
  · rename_i t ht
    exact ⟨t, pureOk_spec ht, h⟩
  · cases h

/-- A matched skeleton statement (`walk`'s `matched` case). -/
structure Matched (c : CC) (bi : Nat) (s : Stmt) (gs : List Stmt) (k k' : Nat) (S : List Fact)
    (t : Stmt) (ts : List Stmt) (k'' : Nat) : Prop where
  ops : mapOperands c.ef s.inst = mapOperands c.eg t.inst
  len : s.results.length = t.results.length
  pre : c.gPre (bi, k) S gs k' = some (t :: ts, k'')
  resF : c.resOk c.ef s.results bi k = true
  resG : c.resOk c.eg t.results bi k = true

theorem walk_skel_spec {c : CC} {bi : Nat} {s : Stmt} {fs gs : List Stmt} {k k' : Nat}
    {S Send : List Fact} (hn : s.inst ≠ .nop) (hp : pureK s.inst = false)
    (h : c.walk bi (s :: fs) gs k k' S = some Send) :
    (∃ t ts k'', Matched c bi s gs k k' S t ts k'' ∧
      c.walk bi fs ts (k + 1) (k'' + 1)
        (afterKeep (mapOperands c.ef s.inst) (s.results.head?.map c.ef) S) = some Send) ∨
    ((∀ t, nextSkel gs = some t →
        ¬ (mapOperands c.ef s.inst = mapOperands c.eg t.inst ∧ s.results.length = t.results.length)) ∧
      c.removeOk bi k s S (mapOperands c.ef s.inst) = true ∧
      c.walk bi fs gs (k + 1) k' S = some Send) := by
  have hn' : (s.inst == .nop) = false := by simpa using hn
  simp only [CC.walk, hn', hp, Bool.false_eq_true, ite_false] at h
  -- the removal branch, shared by "no next skeleton" and "not matched"
  have hrem : ∀ (hm : ∀ t, nextSkel gs = some t →
      ¬ (mapOperands c.ef s.inst = mapOperands c.eg t.inst ∧ s.results.length = t.results.length)),
      (if c.removeOk bi k s S (mapOperands c.ef s.inst) = true then c.walk bi fs gs (k + 1) k' S
        else none) = some Send →
      (∃ t ts k'', Matched c bi s gs k k' S t ts k'' ∧
        c.walk bi fs ts (k + 1) (k'' + 1)
          (afterKeep (mapOperands c.ef s.inst) (s.results.head?.map c.ef) S) = some Send) ∨
      ((∀ t, nextSkel gs = some t →
          ¬ (mapOperands c.ef s.inst = mapOperands c.eg t.inst ∧ s.results.length = t.results.length)) ∧
        c.removeOk bi k s S (mapOperands c.ef s.inst) = true ∧
        c.walk bi fs gs (k + 1) k' S = some Send) := fun hm h' => by
    by_cases hr : c.removeOk bi k s S (mapOperands c.ef s.inst) = true
    · rw [if_pos hr] at h'
      exact .inr ⟨hm, hr, h'⟩
    · rw [if_neg hr] at h'
      cases h'
  obtain hns | ⟨t0, hns⟩ : nextSkel gs = none ∨ ∃ t0, nextSkel gs = some t0 := by
    cases nextSkel gs <;> simp
  · simp only [hns, Bool.false_eq_true, ite_false] at h
    exact hrem (fun t ht => by rw [hns] at ht; cases ht) h
  · simp only [hns] at h
    by_cases hm : (mapOperands c.ef s.inst == mapOperands c.eg t0.inst &&
        s.results.length == t0.results.length) = true
    · rw [if_pos hm] at h
      cases hg : c.gPre (bi, k) S gs k' with
      | none => simp [hg] at h
      | some p =>
        obtain ⟨rest, k''⟩ := p
        cases rest with
        | nil => simp [hg] at h
        | cons t ts =>
          simp only [hg] at h
          by_cases hr : (c.resOk c.ef s.results bi k && c.resOk c.eg t.results bi k) = true
          · rw [if_pos hr] at h
            simp only [Bool.and_eq_true] at hr
            obtain ⟨pre, hgs, -, hpre, hsk⟩ := gPre_spec gs k' (t :: ts) k'' hg
            have hns' : nextSkel gs = some t := by
              rw [hgs, nextSkel_append (fun st hst => (hpre st hst).nopOrPure)]
              exact nextSkel_skelHead hsk
            rw [hns] at hns'
            cases hns'
            simp only [Bool.and_eq_true, beq_iff_eq] at hm
            exact .inl ⟨t0, ts, k'', ⟨hm.1, hm.2, hg, hr.1, hr.2⟩, h⟩
          · rw [if_neg hr] at h
            cases h
    · rw [if_neg hm] at h
      refine hrem (fun t ht => ?_) h
      rw [hns] at ht
      cases ht
      simpa using hm

/-! ## Removals -/

/-- The cases of `removeOk` (module doc of `FV/Opt/MidValCert.lean`). -/
theorem removeOk_spec {c : CC} {bi k : Nat} {s : Stmt} {S : List Fact} {i : Inst}
    (h : c.removeOk bi k s S i = true) :
    (∃ op ty fl p off r, i = .load op ty fl p off ∧ s.results = [r] ∧
      (Fact.mem p off ty (loadKind op) fl.endianness (c.ef r) ∈ S ∨
        (fl.trapCode = none ∧ c.tm (c.ef r) = some (.poison bi k)))) ∨
    (∃ op ty fl x p off, i = .store op ty fl x p off ∧
      Fact.mem p off ty (storeKind op) fl.endianness x ∈ S) ∨
    (mergeK i = true ∧ ((∃ r, s.results = [r] ∧ Fact.eqn i (some (c.ef r)) ∈ S) ∨
      (s.results = [] ∧ Fact.eqn i none ∈ S))) := by
  unfold CC.removeOk at h
  split at h
  · rename_i op ty fl p off
    split at h
    · rename_i r hr
      simp only [Bool.or_eq_true, List.contains_iff_mem, Bool.and_eq_true, Option.isNone_iff_eq_none,
        beq_iff_eq] at h
      exact .inl ⟨op, ty, fl, p, off, r, rfl, hr, h⟩
    · cases h
  · rename_i op ty fl x p off
    simp only [List.contains_iff_mem] at h
    exact .inr (.inl ⟨op, ty, fl, x, p, off, rfl, h⟩)
  · simp only [Bool.and_eq_true] at h
    obtain ⟨hm, h⟩ := h
    refine .inr (.inr ⟨hm, ?_⟩)
    split at h
    · rename_i r hr
      simp only [List.contains_iff_mem] at h
      exact .inl ⟨r, hr, h⟩
    · rename_i hr
      simp only [List.contains_iff_mem] at h
      exact .inr ⟨hr, h⟩
    · cases h

/-! ## Blocks -/

/-- What `blockOk` checks. -/
structure BlockOk (c : CC) (bi : Nat) (fb gb : Block) : Prop where
  paramTys : fb.params.map (·.2) = gb.params.map (·.2)
  paramsF : ∀ i p, fb.params[i]? = some p → c.tm (c.ef p.1) = some (.param bi i)
  paramsG : ∀ i p, gb.params[i]? = some p → c.tm (c.eg p.1) = some (.param bi i)
  walk : ∃ Send, c.walk bi fb.body gb.body 0 0 (c.factsAt bi) = some Send ∧ EndOk c bi fb gb Send

theorem blockOk_spec {c : CC} {bi : Nat} {fb gb : Block} (h : c.blockOk bi fb gb = true) :
    BlockOk c bi fb gb := by
  unfold CC.blockOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun i p hp => ?_, fun i p hp => ?_, ?_⟩
  · simpa using h2 (p, i) (List.mem_zipIdx_iff_getElem?.2 (by simpa using hp))
  · simpa using h3 (p, i) (List.mem_zipIdx_iff_getElem?.2 (by simpa using hp))
  · split at h4
    · rename_i Send hw
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h4
      obtain ⟨ht, hs⟩ := h4
      refine ⟨Send, hw, ht, fun s hs' => ?_⟩
      have := hs s hs'
      split at this
      · rename_i si hsi
        simp only [List.all_eq_true, List.contains_iff_mem] at this
        exact ⟨si, hsi, this⟩
      · cases this
    · cases h4

theorem entryOk_spec {c : CC} {b : Nat} (h : c.entryOk b = true) :
    ∀ F ∈ c.factsAt b, ∀ t ∈ F.terms, (c.siteOf t).1 ≠ b ∧ c.anc (c.siteOf t).1 b = true := by
  intro F hF t ht
  simp only [CC.entryOk, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact h F hF t ht

end Opt.MidVal

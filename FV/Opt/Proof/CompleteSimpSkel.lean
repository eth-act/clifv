import FV.Opt.Proof.CompleteSimpRules

/-!
# Completeness of simplify: skeleton statements and terminators

`SRun`: a sequence of rules-phase steps (`RStep`) and `materialize` runs (`MRun`) inside one
statement, with the statements emitted so far. `skelStmt_ok`/`skelTerm_ok`: under
`Opt.SkelRulesOk` (and `Opt.SimpRulesOk` for the nodes the skeleton rules make), the outcome of a
skeleton statement or terminator is what `Opt.simpOk` expects (`SkelRes`, `TermRes`).
-/

namespace Opt

open Clif

section Skel

variable {f : Function} {idom : Array (Option Nat)} {allowed : Inst → Bool} {bi : Nat}
  {B : ValueId → Prop}

/-- Rules-phase steps and `materialize` runs inside one statement (module doc). -/
structure SRun (f : Function) (idom : Array (Option Nat)) (allowed : Inst → Bool) (bi : Nat)
    (B : ValueId → Prop) (V : Nat → Option Block) (st st' : SState) (new : List Stmt) : Prop where
  inv : RInv f (emitV V bi new) B (fun _ => False) st'
  good : ∀ y, Good st B y → Good st' B y
  known : ∀ y, st.known y = true → st'.known y = true
  typesKnown : ∀ y, st.known y = true → st'.types.get? y = st.types.get? y
  types : ∀ y t, st.types.get? y = some t → st'.types.get? y = some t
  avail : ∀ y d, st.avail.get? y = some d → st'.avail.get? y = some d
  availNew : ∀ y d, st'.avail.get? y = some d →
    st.avail.get? y = some d ∨ (d = bi ∧ ∃ s ∈ new, y ∈ s.results)
  defsKeep : ∀ y n, st.defs.get? y = some n → st.avail.contains y = true →
    st'.defs.get? y = some n
  nodes : ∀ y n', st'.defs.get? y = some n' → st.known y = true →
    st.defs.get? y = some n' ∨ ∀ z ∈ operands n', Good st' B z
  alts : st'.alts = st.alts
  stmts : ∀ b, V bi = some b → ∀ j s, new[j]? = some s →
    NewOk idom (emitV V bi new) bi (b.body.length + j) allowed B st' s

theorem RInv.of_mrun {V : Nat → Option Block} {X : ValueId → Prop} {st st' : SState}
    {new : List Stmt} (h : RInv f V B X st) (hm : MRun f idom allowed bi B V st st' new) :
    RInv f (emitV V bi new) B X st' := by
  obtain ⟨d, a, t, c, nx, rfl⟩ := hm.step.shape
  refine ⟨hm.inv, h.noPartial, fun n w hw => ?_, fun x ms hx m hm' => ?_⟩
  · obtain ⟨e1, e2, e3⟩ := h.memo n w hw
    exact ⟨e1.imp (hm.good w) id, hm.step.known w e2, by rw [hm.step.typesKnown w e2]; exact e3⟩
  · obtain ⟨e1, e2⟩ := h.alts x ms hx m hm'
    exact ⟨hm.step.known m e1, by
      rw [hm.step.typesKnown m e1, hm.step.typesKnown x (h.m.altsKnown x ms hx)]; exact e2⟩

theorem SRun.of_mrun {V : Nat → Option Block} {st st' : SState} {new : List Stmt}
    (h : RInv f V B (fun _ => False) st) (hm : MRun f idom allowed bi B V st st' new) :
    SRun f idom allowed bi B V st st' new := by
  obtain ⟨d, a, t, c, nx, rfl⟩ := hm.step.shape
  exact ⟨h.of_mrun hm, hm.good, fun y hy => hm.step.known y hy, hm.step.typesKnown, hm.step.types,
    hm.step.avail, hm.step.availNew, hm.step.defsKeep,
    fun y n' hy _ => hm.nodes y n' hy, rfl, hm.stmts⟩

theorem SRun.of_rstep {V : Nat → Option Block} {st st' : SState}
    (h : RInv f V B (fun _ => False) st') (hs : RStep B st st') :
    SRun f idom allowed bi B V st st' [] := by
  refine ⟨by rw [emitV_nil]; exact h, hs.good, fun y hy => hs.known hy, hs.typesKnown, hs.types,
    fun y d hy => by rw [hs.avail]; exact hy, fun y d hy => .inl (by rw [← hs.avail]; exact hy),
    fun y n hy _ => hs.defs y n hy, fun y n' hy hk => ?_, hs.alts, fun _ _ j s hs => by simp at hs⟩
  rcases hs.defsNew y n' hy with h1 | h1
  · exact .inl h1
  · rw [hk] at h1; cases h1

theorem SRun.trans {V : Nat → Option Block} {st st1 st2 : SState} {n1 n2 : List Stmt}
    (h1 : SRun f idom allowed bi B V st st1 n1) (h2 : SRun f idom allowed bi B (emitV V bi n1) st1 st2 n2) :
    SRun f idom allowed bi B V st st2 (n1 ++ n2) := by
  refine ⟨by rw [← emitV_append]; exact h2.inv, fun y h => h2.good y (h1.good y h),
    fun y h => h2.known y (h1.known y h),
    fun y hy => (h2.typesKnown y (h1.known y hy)).trans (h1.typesKnown y hy),
    fun y t h => h2.types y t (h1.types y t h), fun y d h => h2.avail y d (h1.avail y d h),
    fun y d h => ?_, fun y n h ha => ?_, fun y n' hy hk => ?_, h2.alts.trans h1.alts,
    fun b hb j s hs => ?_⟩
  · rcases h2.availNew y d h with h | ⟨rfl, s, hs, hy⟩
    · rcases h1.availNew y d h with h | ⟨rfl, s, hs, hy⟩
      · exact .inl h
      · exact .inr ⟨rfl, s, List.mem_append_left _ hs, hy⟩
    · exact .inr ⟨rfl, s, List.mem_append_right _ hs, hy⟩
  · refine h2.defsKeep y n (h1.defsKeep y n h ha) ?_
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 ha)
    exact (hm_contains_iff _ _).2 (by rw [h1.avail y d hd]; rfl)
  · rcases h2.nodes y n' hy (h1.known y hk) with h | h
    · rcases h1.nodes y n' h hk with h' | h'
      · exact .inl h'
      · exact .inr fun z hz => h2.good z (h' z hz)
    · exact .inr h
  · rw [← emitV_append]
    rcases Nat.lt_or_ge j n1.length with hj | hj
    · rw [List.getElem?_append_left hj] at hs
      exact (h1.stmts b hb j s hs).mono' h2.defsKeep h2.avail h2.good
    · rw [List.getElem?_append_right hj] at hs
      have hb1 : emitV V bi n1 bi = some { b with body := b.body ++ n1 } := by simp [emitV, hb]
      have := h2.stmts _ hb1 (j - n1.length) s hs
      simp only [List.length_append] at this
      rwa [show b.body.length + n1.length + (j - n1.length) = b.body.length + j by omega] at this

theorem notSym_mapOperands (τ : ValueId → ValueId) (i : Inst) :
    notSym (mapOperands τ i) = notSym i := by cases i <;> rfl

theorem AvailAt.le {V : Nat → Option Block} {i k k' : Nat} {x : ValueId}
    (h : AvailAt idom V i k x) (hk : k ≤ k') : AvailAt idom V i k' x := by
  obtain ⟨d, t, hd, h | h⟩ := h
  · exact ⟨d, t, hd, .inl ⟨h.1, Nat.le_trans h.2 hk⟩⟩
  · exact ⟨d, t, hd, .inr h⟩

theorem runSkel_cand {skel : SkeletonFn} {rules : SimplifyFn} {st : SState}
    {i : Isle.Opt.SkelInst} {c : Isle.Opt.SkelSimp} (h : (runSkel skel rules allowed st i).1 = some c) :
    skelCandidate i = true := by
  unfold runSkel at h
  cases hc : skelCandidate i
  · simp [hc] at h
  · rfl

/-- A replacement instruction `i` of the skeleton instruction `i0`, placed at index `k`. -/
def RepInst (idom : Array (Option Nat)) (V : Nat → Option Block) (bi k : Nat)
    (skelOk : Inst → Bool) (B : ValueId → Prop) (st : SState) (i0 i : Inst) : Prop :=
  (∀ y ∈ operands i, Good st B y ∧ AvailAt idom V bi k y) ∧
    i.resultTypes (fun _ => none) (fun _ => none) = i0.resultTypes (fun _ => none) (fun _ => none) ∧
    isPure i = false ∧ notSym i = true ∧
    ((∃ n τ, skelOk n = true ∧ i = mapOperands τ n) ∨ ∃ τ, i = mapOperands τ i0)

/-- A result-free instruction of a `two` outcome, placed at index `k` or later. -/
def TwoInst (idom : Array (Option Nat)) (V : Nat → Option Block) (bi k : Nat)
    (skelOk : Inst → Bool) (B : ValueId → Prop) (st : SState) (a : Inst) : Prop :=
  (∀ y ∈ operands a, Good st B y ∧ AvailAt idom V bi k y) ∧
    a.resultTypes (fun _ => none) (fun _ => none) = some [] ∧ notSym a = true ∧
    ∃ n τ, skelOk n = true ∧ a = mapOperands τ n

/-- The outcome of a skeleton statement `u` (`fin`: its final statements, placed at index `k` of
the view `V`; `sub`: its renamings). -/
def SkelRes (idom : Array (Option Nat)) (V : Nat → Option Block) (bi : Nat)
    (skelOk : Inst → Bool) (B : ValueId → Prop) (st : SState) (k : Nat) (u : Stmt)
    (fin : List Stmt) (sub : List (ValueId × ValueId)) : SkelOut → Prop
  | .keep => fin = [u] ∧ sub = []
  | .remove => fin = [] ∧ sub = [] ∧ u.results = [] ∧ skelCandidate (.inst u.inst) = true
  | .removeWithVal v => fin = [] ∧ skelCandidate (.inst u.inst) = true ∧
      ∃ r, u.results = [r] ∧ sub = [(r, v)] ∧ Good st B v ∧ AvailAt idom V bi k v ∧
        st.types.get? v = st.types.get? r
  | .replace i => fin = [{ results := u.results, inst := i }] ∧ sub = [] ∧
      skelCandidate (.inst u.inst) = true ∧ RepInst idom V bi k skelOk B st u.inst i
  | .two a c => fin = [{ inst := a }, { inst := c }] ∧ sub = [] ∧ u.results = [] ∧
      skelCandidate (.inst u.inst) = true ∧ TwoInst idom V bi k skelOk B st a ∧
        TwoInst idom V bi k skelOk B st c

theorem rename_mem {m : List (ValueId × ValueId)} {xs : List ValueId} (hmap : m.map Prod.fst = xs)
    {y : ValueId} (hy : y ∈ xs) : ∃ p ∈ m, p.1 = y ∧ rename m y = p.2 := by
  rw [← hmap] at hy
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (lookup_isSome' hy)
  exact ⟨(y, z), lookup_mem hz, rfl, by simp [rename, hz]⟩

theorem SRun.trans0 {V : Nat → Option Block} {st st1 st2 : SState} {n : List Stmt}
    (h1 : SRun f idom allowed bi B V st st1 []) (h2 : SRun f idom allowed bi B V st1 st2 n) :
    SRun f idom allowed bi B V st st2 n := by
  have := h1.trans (n2 := n) (by rw [emitV_nil]; exact h2)
  simpa using this

/-- A rewritten operand list: every operand of `mapOperands (rename m) i` is placeable and
available. -/
theorem renamed_ops {V : Nat → Option Block} {st : SState} {m : List (ValueId × ValueId)}
    {xs : List ValueId} {i : Inst} (hmap : m.map Prod.fst = xs) (hops : operands i ⊆ xs)
    (hps : ∀ p ∈ m, Good st B p.2 ∧ AvailHere idom V bi p.2) :
    ∀ y ∈ operands (mapOperands (rename m) i), Good st B y ∧ AvailHere idom V bi y := by
  intro y hy
  rw [operands_mapOperands, List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨p, hp, -, he⟩ := rename_mem hmap (hops hx)
  rw [he]; exact hps p hp

variable {cfg : Cfg} {rules : SimplifyFn} {skel : SkeletonFn} {skelOk : Inst → Bool}

/-- **A skeleton statement** (`skelStmt`) under the rule obligations (module doc). -/
theorem skelStmt_ok (hR : SimpRulesOk rules) (hK : SkelRulesOk skel) :
    ∀ fuel st u stmts sub st' o (V : Nat → Option Block) b,
      RInv f V B (fun _ => False) st → V bi = some b → (∀ y ∈ operands u.inst, Good st B y) →
      (∀ r ∈ u.results, st.known r = true) →
      skelStmt skel rules allowed skelOk cfg bi fuel st u = (stmts, sub, st', o) →
      ∃ pre fin, stmts.toList = pre ++ fin ∧ SRun f cfg.idom allowed bi B V st st' pre ∧
        SkelRes cfg.idom (emitV V bi pre) bi skelOk B st' (b.body.length + pre.length) u fin sub o := by
  intro fuel
  induction fuel with
  | zero =>
    intro st u stmts sub st' o V b h hb _ _ hs
    simp only [skelStmt, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    exact ⟨[], [u], by simp, SRun.of_rstep h (RStep.refl st), rfl, rfl⟩
  | succ fuel ih =>
    intro st u stmts sub st' o V b h hb hops hres hs
    rw [skelStmt] at hs
    obtain ⟨hI1, hS1, hc⟩ := runSkel_ok (V := V) (i := .inst u.inst) hR hK allowed h hops
    have hcand := fun c (hc' : (runSkel skel rules allowed st (.inst u.inst)).1 = some c) =>
      runSkel_cand (allowed := allowed) hc'
    generalize runSkel skel rules allowed st (.inst u.inst) = r at hI1 hS1 hc hcand hs
    obtain ⟨c, st1⟩ := r
    simp only at hI1 hS1 hc hcand hs
    have hR1 : SRun f cfg.idom allowed bi B V st st1 [] :=
      SRun.of_rstep hI1 hS1
    have hkeep : ∀ stmts sub st' o, (#[u], ([] : List (ValueId × ValueId)), st1, SkelOut.keep) =
        (stmts, sub, st', o) → ∃ pre fin, stmts.toList = pre ++ fin ∧
          SRun f cfg.idom allowed bi B V st st' pre ∧
          SkelRes cfg.idom (emitV V bi pre) bi skelOk B st' (b.body.length + pre.length) u fin sub o := by
      intro stmts sub st' o he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      exact ⟨[], [u], by simp, hR1, rfl, rfl⟩
    have hres1 : ∀ r ∈ u.results, st1.known r = true := fun r hr => hS1.known (hres r hr)
    rcases c with _ | c
    · exact hkeep _ _ _ _ hs
    have hcd := hcand c rfl
    have hco := hc c rfl
    rcases c with _ | v | j | ⟨j2, v2⟩ | c | ⟨a, c⟩
    · -- remove
      simp only at hs
      split at hs
      · rename_i hemp
        simp only [Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
        exact ⟨[], [], by simp, hR1, rfl, rfl, by simpa using hemp, hcd⟩
      · exact hkeep _ _ _ _ hs
    · -- removeWithVal
      simp only at hs
      split at hs
      · rename_i r hr
        split at hs
        · exact hkeep _ _ _ _ hs
        rename_i hty
        split at hs
        · rename_i v' st2 out hm
          simp only [Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
          obtain ⟨new, hout, hrun, hg2, hh2, ht2⟩ := mat_spec _ _ _ _ _ _ _ _ b hI1.m hb hco hm
          simp only [List.nil_append] at hout
          refine ⟨new, [], by simp [hout], hR1.trans0 (SRun.of_mrun hI1 hrun), rfl, hcd, r, hr, rfl,
            hg2, by simpa using hh2.at_end (b := { b with body := b.body ++ new }) (by simp [emitV, hb]), ?_⟩
          have hrk : st1.known r = true := hres1 r (by rw [hr]; simp)
          rw [ht2, hrun.step.typesKnown r hrk]
          simpa using hty
        · exact hkeep _ _ _ _ hs
      · exact hkeep _ _ _ _ hs
    · -- replace
      rcases j with j | t'
      · simp only at hs
        split at hs
        · exact hkeep _ _ _ _ hs
        rename_i hchk
        simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false, beq_iff_eq] at hchk
        obtain ⟨hsk, hsame⟩ := hchk
        obtain ⟨hpj, hsj, hgj⟩ := hco
        split at hs
        · rename_i m st2 out hm
          obtain ⟨hrun, hmap, hps⟩ := matAll_spec hI1.m hb hgj hm
          have hb2 : emitV V bi out.toList bi = some { b with body := b.body ++ out.toList } := by
            simp [emitV, hb]
          have hops2 := renamed_ops (i := j) hmap (fun y hy => hy)
            (fun p hp => ⟨(hps p hp).1, (hps p hp).2.1⟩)
          generalize hrec : skelStmt skel rules allowed skelOk cfg bi fuel st2
            { u with inst := mapOperands (rename m) j } = rr at hs
          obtain ⟨more, sub2, st3, o2⟩ := rr
          simp only [Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
          obtain ⟨pre2, fin2, hmore, hrun2, hres2⟩ := ih st2
            { u with inst := mapOperands (rename m) j } more sub2 st3 o2 _ _
            (hI1.of_mrun hrun) hb2 (fun y hy => (hops2 y hy).1)
            (fun r hr => hrun.step.known r (hres1 r hr)) hrec
          have hall := hR1.trans0 ((SRun.of_mrun hI1 hrun).trans hrun2)
          refine ⟨out.toList ++ pre2, fin2, by simp [hmore], hall, ?_⟩
          rw [← emitV_append]
          have hk : b.body.length + (out.toList ++ pre2).length =
              (b.body ++ out.toList).length + pre2.length := by simp; omega
          rw [hk]
          rcases o2 with _ | _ | v | i | ⟨a, c⟩
          · -- the replacement is kept
            obtain ⟨rfl, rfl⟩ := hres2
            refine ⟨rfl, rfl, hcd, fun y hy => ⟨hrun2.good y (hops2 y hy).1, ?_⟩, ?_, ?_, ?_,
              .inl ⟨j, rename m, hsk, rfl⟩⟩
            · have := ((hops2 y hy).2.at_end hb2).emit bi pre2
              exact this.le (by simp)
            · rw [resultTypes_mapOperands]; exact hsame
            · rw [isPure_mapOperands]; exact hpj
            · rw [notSym_mapOperands]; exact hsj
          · exact ⟨hres2.1, hres2.2.1, hres2.2.2.1, hcd⟩
          · obtain ⟨h1, -, h3⟩ := hres2
            exact ⟨h1, hcd, h3⟩
          · obtain ⟨h1, h2, -, h4, h5, h6, h7, h8⟩ := hres2
            refine ⟨h1, h2, hcd, h4, by rw [h5, resultTypes_mapOperands]; exact hsame, h6, h7, ?_⟩
            rcases h8 with h8 | ⟨τ, rfl⟩
            · exact .inl h8
            · exact .inl ⟨j, τ ∘ rename m, hsk, mapOperands_comp _ _ _⟩
          · obtain ⟨h1, h2, h3, -, h5, h6⟩ := hres2
            exact ⟨h1, h2, h3, hcd, h5, h6⟩
        · exact hkeep _ _ _ _ hs
      · exact hkeep _ _ _ _ hs
    · -- replaceWithVal: not applied to instructions
      exact hkeep _ _ _ _ hs
    · -- replaceBranchCond
      simp only at hs
      split at hs
      · exact hkeep _ _ _ _ hs
      rename_i i hi
      split at hs
      · rename_i m st2 out hm
        obtain ⟨hrun, hmap, hps⟩ := matAll_spec hI1.m hb (fun y hy => by simp at hy; subst hy; exact hco) hm
        have hb2 : emitV V bi out.toList bi = some { b with body := b.body ++ out.toList } := by
          simp [emitV, hb]
        -- `i` is the conditional trap with the new condition
        have hiops : operands i ⊆ [c] := by
          intro y hy
          split at hi
          · simp only [Option.some.injEq] at hi; subst hi; simpa [operands] using hy
          · simp only [Option.some.injEq] at hi; subst hi; simpa [operands] using hy
          · cases hi
        have hops2 := renamed_ops (i := i) hmap hiops (fun p hp => ⟨(hps p hp).1, (hps p hp).2.1⟩)
        have hi0 : (∃ τ, i = mapOperands τ u.inst) ∧ isPure i = false ∧ notSym i = true ∧
            i.resultTypes (fun _ => none) (fun _ => none) = u.inst.resultTypes (fun _ => none) (fun _ => none) := by
          split at hi
          · simp only [Option.some.injEq] at hi; subst hi
            rename_i heq; rw [heq]; exact ⟨⟨fun _ => c, rfl⟩, rfl, rfl, rfl⟩
          · simp only [Option.some.injEq] at hi; subst hi
            rename_i heq; rw [heq]; exact ⟨⟨fun _ => c, rfl⟩, rfl, rfl, rfl⟩
          · cases hi
        obtain ⟨⟨τ0, hτ0⟩, hpi, hsi, hti⟩ := hi0
        generalize hrec : skelStmt skel rules allowed skelOk cfg bi fuel st2
          { u with inst := mapOperands (rename m) i } = rr at hs
        obtain ⟨more, sub2, st3, o2⟩ := rr
        simp only [Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
        obtain ⟨pre2, fin2, hmore, hrun2, hres2⟩ := ih st2
          { u with inst := mapOperands (rename m) i } more sub2 st3 o2 _ _
          (hI1.of_mrun hrun) hb2 (fun y hy => (hops2 y hy).1)
          (fun r hr => hrun.step.known r (hres1 r hr)) hrec
        have hall := hR1.trans0 ((SRun.of_mrun hI1 hrun).trans hrun2)
        refine ⟨out.toList ++ pre2, fin2, by simp [hmore], hall, ?_⟩
        rw [← emitV_append]
        have hk : b.body.length + (out.toList ++ pre2).length =
            (b.body ++ out.toList).length + pre2.length := by simp; omega
        rw [hk]
        rcases o2 with _ | _ | v | i2 | ⟨a, c2⟩
        · obtain ⟨rfl, rfl⟩ := hres2
          refine ⟨rfl, rfl, hcd, fun y hy => ⟨hrun2.good y (hops2 y hy).1, ?_⟩, ?_, ?_, ?_,
            .inr ⟨rename m ∘ τ0, by rw [hτ0, mapOperands_comp]⟩⟩
          · have := ((hops2 y hy).2.at_end hb2).emit bi pre2
            exact this.le (by simp)
          · rw [resultTypes_mapOperands]; exact hti
          · rw [isPure_mapOperands]; exact hpi
          · rw [notSym_mapOperands]; exact hsi
        · exact ⟨hres2.1, hres2.2.1, hres2.2.2.1, hcd⟩
        · obtain ⟨h1, -, h3⟩ := hres2
          exact ⟨h1, hcd, h3⟩
        · obtain ⟨h1, h2, -, h4, h5, h6, h7, h8⟩ := hres2
          refine ⟨h1, h2, hcd, h4, by rw [h5, resultTypes_mapOperands]; exact hti, h6, h7, ?_⟩
          rcases h8 with h8 | ⟨τ, rfl⟩
          · exact .inl h8
          · exact .inr ⟨τ ∘ rename m ∘ τ0, by rw [hτ0, mapOperands_comp, mapOperands_comp]; rfl⟩
        · obtain ⟨h1, h2, h3, -, h5, h6⟩ := hres2
          exact ⟨h1, h2, h3, hcd, h5, h6⟩
      · exact hkeep _ _ _ _ hs
    · -- replaceWithTwo
      rcases a with a | ta
      · rcases c with c | tc
        · simp only at hs
          split at hs
          · exact hkeep _ _ _ _ hs
          rename_i hchk
          simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false, bne_iff_ne,
            ne_eq, Decidable.not_not, List.isEmpty_iff] at hchk
          obtain ⟨⟨⟨⟨hemp, hska⟩, hskc⟩, hta⟩, htc⟩ := hchk
          obtain ⟨⟨hpa, hsa, hga⟩, ⟨hpc, hsc, hgc⟩⟩ := hco
          split at hs
          · rename_i m st2 out hm
            simp only [Prod.mk.injEq] at hs
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
            obtain ⟨hrun, hmap, hps⟩ := matAll_spec hI1.m hb
              (fun y hy => by
                rcases List.mem_append.1 hy with hy | hy
                · exact hga y hy
                · exact hgc y hy) hm
            have hb2 : emitV V bi out.toList bi = some { b with body := b.body ++ out.toList } := by
              simp [emitV, hb]
            have hopsa := renamed_ops (i := a) hmap (fun y hy => List.mem_append_left _ hy)
              (fun p hp => ⟨(hps p hp).1, (hps p hp).2.1⟩)
            have hopsc := renamed_ops (i := c) hmap (fun y hy => List.mem_append_right _ hy)
              (fun p hp => ⟨(hps p hp).1, (hps p hp).2.1⟩)
            have hall := hR1.trans0 (SRun.of_mrun hI1 hrun)
            refine ⟨out.toList, _, by simp, hall, rfl, rfl, hemp, hcd, ⟨fun y hy => ⟨(hopsa y hy).1, ?_⟩,
              by rw [resultTypes_mapOperands]; exact hta, by rw [notSym_mapOperands]; exact hsa,
              a, rename m, hska, rfl⟩, ⟨fun y hy => ⟨(hopsc y hy).1, ?_⟩,
              by rw [resultTypes_mapOperands]; exact htc, by rw [notSym_mapOperands]; exact hsc,
              c, rename m, hskc, rfl⟩⟩
            · simpa using (hopsa y hy).2.at_end hb2
            · simpa using (hopsc y hy).2.at_end hb2
          · exact hkeep _ _ _ _ hs
        · exact hkeep _ _ _ _ hs
      · exact hkeep _ _ _ _ hs

end Skel

end Opt

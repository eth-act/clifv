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

variable {f : Function} {idom : Array (Option Nat)} {allowed skelOk : Inst → Bool} {bi : Nat}
  {B : ValueId → Prop}

/-- A conditional trap emitted in front of a rewritten terminator, at index `k`. -/
def TrapOk (idom : Array (Option Nat)) (V : Nat → Option Block) (bi k : Nat)
    (skelOk : Inst → Bool) (B : ValueId → Prop) (st : SState) (s : Stmt) : Prop :=
  s.results = [] ∧ isTrapLike s.inst = true ∧ (∃ n τ, skelOk n = true ∧ s.inst = mapOperands τ n) ∧
    ∀ y ∈ operands s.inst, Placed st B y ∧ AvailAt idom V bi k y

/-- Rules-phase steps and `materialize` runs inside one statement (module doc). -/
structure SRun (f : Function) (idom : Array (Option Nat)) (allowed skelOk : Inst → Bool) (bi : Nat)
    (B : ValueId → Prop) (V : Nat → Option Block) (st st' : SState) (new : List Stmt) : Prop where
  inv : RInv f (emitV V bi new) B (fun _ => False) (fun _ => False) st'
  good : ∀ y, Placed st B y → Placed st' B y
  known : ∀ y, st.known y = true → st'.known y = true
  typesKnown : ∀ y, st.known y = true → st'.types.get? y = st.types.get? y
  types : ∀ y t, st.types.get? y = some t → st'.types.get? y = some t
  avail : ∀ y d, st.avail.get? y = some d → st'.avail.get? y = some d
  availNew : ∀ y d, st'.avail.get? y = some d →
    st.avail.get? y = some d ∨ (d = bi ∧ ∃ s ∈ new, y ∈ s.results)
  defsKeep : ∀ y n, st.defs.get? y = some n → st.avail.contains y = true →
    st'.defs.get? y = some n
  nodes : ∀ y n', st'.defs.get? y = some n' → st.known y = true →
    st.defs.get? y = some n' ∨ ∀ z ∈ operands n', Placed st' B z
  alts : st'.alts = st.alts
  stmts : ∀ b, V bi = some b → ∀ j s, new[j]? = some s →
    NewOk idom (emitV V bi new) bi (b.body.length + j) allowed B st' s ∨
      TrapOk idom (emitV V bi new) bi (b.body.length + j) skelOk B st' s
  fresh : ∀ y n, st'.defs.get? y = some n → st.defs.get? y = some n ∨ maxValue f < y

theorem RInv.of_mrun {V : Nat → Option Block} {X : ValueId → Prop} {XN : Inst → Prop} {st st' : SState}
    {new : List Stmt} (h : RInv f V B X XN st) (hm : MRun f idom allowed bi B V st st' new) :
    RInv f (emitV V bi new) B X XN st' := by
  obtain ⟨d, a, t, c, nx, rfl⟩ := hm.step.shape
  refine ⟨hm.inv, h.noPartial, fun n w hw => ?_, fun x ms hx m hm' => ?_⟩
  · obtain ⟨e1, e2, e3⟩ := h.memo n w hw
    exact ⟨e1.imp (hm.good w) id, hm.step.known w e2, by rw [hm.step.typesKnown w e2]; exact e3⟩
  · obtain ⟨e1, e2⟩ := h.alts x ms hx m hm'
    exact ⟨hm.step.known m e1, by
      rw [hm.step.typesKnown m e1, hm.step.typesKnown x (h.m.altsKnown x ms hx)]; exact e2⟩

theorem SRun.of_mrun {V : Nat → Option Block} {st st' : SState} {new : List Stmt}
    (h : RInv f V B (fun _ => False) (fun _ => False) st) (hm : MRun f idom allowed bi B V st st' new) :
    SRun f idom allowed skelOk bi B V st st' new := by
  have hfn : st.fn = f := by have := hm.inv.fn; obtain ⟨_, _, _, _, _, e⟩ := hm.step.shape; rw [e] at this; exact this
  obtain ⟨d, a, t, c, nx, rfl⟩ := hm.step.shape
  exact ⟨h.of_mrun hm, hm.good, fun y hy => hm.step.known y hy, hm.step.typesKnown, hm.step.types,
    hm.step.avail, hm.step.availNew, hm.step.defsKeep,
    fun y n' hy _ => hm.nodes y n' hy, rfl, fun b hb j s hs => .inl (hm.stmts b hb j s hs),
    fun y n hy => by rw [← hfn]; exact hm.step.fresh y n hy⟩

theorem SRun.of_rstep {V : Nat → Option Block} {st st' : SState}
    (h : RInv f V B (fun _ => False) (fun _ => False) st') (hs : RStep B st st') :
    SRun f idom allowed skelOk bi B V st st' [] := by
  have hfn : st.fn = f := by rw [← hs.fn]; exact h.m.fn
  refine ⟨by rw [emitV_nil]; exact h, hs.good, fun y hy => hs.known hy, hs.typesKnown, hs.types,
    fun y d hy => by rw [hs.avail]; exact hy, fun y d hy => .inl (by rw [← hs.avail]; exact hy),
    fun y n hy _ => hs.defs y n hy, fun y n' hy hk => ?_, hs.alts, fun _ _ j s hs => by simp at hs,
    fun y n hy => by rw [← hfn]; exact hs.fresh y n hy⟩
  rcases hs.defsNew y n' hy with h1 | h1
  · exact .inl h1
  · rw [hk] at h1; cases h1

theorem SRun.trans {V : Nat → Option Block} {st st1 st2 : SState} {n1 n2 : List Stmt}
    (h1 : SRun f idom allowed skelOk bi B V st st1 n1) (h2 : SRun f idom allowed skelOk bi B (emitV V bi n1) st1 st2 n2) :
    SRun f idom allowed skelOk bi B V st st2 (n1 ++ n2) := by
  refine ⟨by rw [← emitV_append]; exact h2.inv, fun y h => h2.good y (h1.good y h),
    fun y h => h2.known y (h1.known y h),
    fun y hy => (h2.typesKnown y (h1.known y hy)).trans (h1.typesKnown y hy),
    fun y t h => h2.types y t (h1.types y t h), fun y d h => h2.avail y d (h1.avail y d h),
    fun y d h => ?_, fun y n h ha => ?_, fun y n' hy hk => ?_, h2.alts.trans h1.alts,
    fun b hb j s hs => ?_, fun y n hy => ?_⟩
  rotate_right
  · rcases h2.fresh y n hy with h | h
    · exact h1.fresh y n h
    · exact .inr h
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
      rcases h1.stmts b hb j s hs with h | ⟨e1, e2, e3, e4⟩
      · exact .inl (h.mono' h2.defsKeep h2.avail h2.good)
      · exact .inr ⟨e1, e2, e3, fun y hy => ⟨h2.good y (e4 y hy).1, (e4 y hy).2.emit bi n2⟩⟩
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
  (∀ y ∈ operands i, Placed st B y ∧ AvailAt idom V bi k y) ∧
    i.resultTypes (fun _ => none) (fun _ => none) = i0.resultTypes (fun _ => none) (fun _ => none) ∧
    isPure i = false ∧ notSym i = true ∧
    ((∃ n τ, skelOk n = true ∧ i = mapOperands τ n) ∨ ∃ τ, i = mapOperands τ i0)

/-- A result-free instruction of a `two` outcome, placed at index `k` or later. -/
def TwoInst (idom : Array (Option Nat)) (V : Nat → Option Block) (bi k : Nat)
    (skelOk : Inst → Bool) (B : ValueId → Prop) (st : SState) (a : Inst) : Prop :=
  (∀ y ∈ operands a, Placed st B y ∧ AvailAt idom V bi k y) ∧
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
      ∃ r, u.results = [r] ∧ sub = [(r, v)] ∧ Placed st B v ∧ AvailAt idom V bi k v ∧
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
    (h1 : SRun f idom allowed skelOk bi B V st st1 []) (h2 : SRun f idom allowed skelOk bi B V st1 st2 n) :
    SRun f idom allowed skelOk bi B V st st2 n := by
  have := h1.trans (n2 := n) (by rw [emitV_nil]; exact h2)
  simpa using this

/-- A rewritten operand list: every operand of `mapOperands (rename m) i` is placeable and
available. -/
theorem renamed_ops {V : Nat → Option Block} {st : SState} {m : List (ValueId × ValueId)}
    {xs : List ValueId} {i : Inst} (hmap : m.map Prod.fst = xs) (hops : operands i ⊆ xs)
    (hps : ∀ p ∈ m, Placed st B p.2 ∧ AvailHere idom V bi p.2) :
    ∀ y ∈ operands (mapOperands (rename m) i), Placed st B y ∧ AvailHere idom V bi y := by
  intro y hy
  rw [operands_mapOperands, List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨p, hp, -, he⟩ := rename_mem hmap (hops hx)
  rw [he]; exact hps p hp

variable {cfg : Cfg} {rules : SimplifyFn} {skel : SkeletonFn}

/-- **A skeleton statement** (`skelStmt`) under the rule obligations (module doc). -/
theorem skelStmt_ok (hR : SimpRulesOk rules) (hK : SkelRulesOk skel) :
    ∀ fuel st u stmts sub st' o (V : Nat → Option Block) b,
      RInv f V B (fun _ => False) (fun _ => False) st → V bi = some b → (∀ y ∈ operands u.inst, Placed st B y) →
      (∀ r ∈ u.results, st.known r = true) →
      skelStmt skel rules allowed skelOk cfg bi fuel st u = (stmts, sub, st', o) →
      ∃ pre fin, stmts.toList = pre ++ fin ∧ SRun f cfg.idom allowed skelOk bi B V st st' pre ∧
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
    have hR1 : SRun f cfg.idom allowed skelOk bi B V st st1 [] :=
      SRun.of_rstep hI1 hS1
    have hkeep : ∀ stmts sub st' o, (#[u], ([] : List (ValueId × ValueId)), st1, SkelOut.keep) =
        (stmts, sub, st', o) → ∃ pre fin, stmts.toList = pre ++ fin ∧
          SRun f cfg.idom allowed skelOk bi B V st st' pre ∧
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

theorem isBranch_mapTerm (σ : ValueId → ValueId) (t : Terminator) :
    isBranch (mapTerm σ t) = isBranch t := by cases t <;> rfl

theorem isTrapLike_mapOperands (σ : ValueId → ValueId) (i : Inst) :
    isTrapLike (mapOperands σ i) = isTrapLike i := by cases i <;> rfl

theorem args_sub_termOperands {t : Terminator} {bc : BlockCall} (h : bc ∈ termCalls t)
    {y : ValueId} (hy : y ∈ bc.args) : y ∈ termOperands t := by
  cases t <;> simp_all [termCalls, termOperands]
  all_goals first
    | (rcases h with rfl | rfl <;> simp_all)
    | (rcases h with rfl | h
       · simp_all
       · exact .inr (.inr ⟨bc, h, hy⟩))

/-- Adding a statement without results keeps the state facts. -/
theorem MInv.noResult {V : Nat → Option Block} {st : SState} (h : MInv f V B st) {s : Stmt}
    (hs : s.results = []) : MInv f (emitV V bi [s]) B st := by
  have hd : ∀ y d t, DefAt (emitV V bi [s]) y d t → DefAt V y d t := by
    intro y d t hy
    rcases hy.of_emit with hy' | ⟨b, -, -, j, s', -, hj, hyr⟩
    · exact hy'
    · have : s' = s := by
        rcases j with _ | j
        · simpa using hj.symm
        · simp at hj
      rw [this, hs] at hyr; cases hyr
  exact ⟨h.fn, h.maxLt, h.knownLt, h.typesFresh, h.defsTy, h.altsKnown,
    fun x d hx hb => by obtain ⟨t, ht⟩ := h.availDef x d hx hb; exact ⟨t, ht.emit bi [s]⟩,
    fun x d t hx => h.defAvail x d t (hd x d t hx), h.newBig, h.badLe,
    fun x d t d' t' h1 h2 => h.uniq x d t d' t' (hd x d t h1) (hd x d' t' h2)⟩

theorem SRun.trap {V : Nat → Option Block} {st : SState} {b : Block}
    (h : RInv f V B (fun _ => False) (fun _ => False) st) (hb : V bi = some b) {s : Stmt}
    (hs : TrapOk idom V bi b.body.length skelOk B st s) :
    SRun f idom allowed skelOk bi B V st st [s] := by
  refine ⟨⟨h.m.noResult hs.1, h.noPartial, h.memo, h.alts⟩, fun _ h => h, fun _ h => h,
    fun _ _ => rfl, fun _ _ h => h, fun _ _ h => h, fun _ _ h => .inl h, fun _ _ h _ => h,
    fun _ _ h _ => .inl h, rfl, fun b' hb' j s' hj => ?_, fun _ _ h => .inl h⟩
  rw [hb] at hb'; cases hb'
  rcases j with _ | j
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    rw [← hj]
    obtain ⟨e1, e2, e3, e4⟩ := hs
    exact .inr ⟨e1, e2, e3, fun y hy => ⟨(e4 y hy).1, by simpa using (e4 y hy).2.emit bi [s]⟩⟩
  · simp at hj

/-- The outcome of a terminator (`skelTerm`): `extra` statements, then `t''` (placed after the
statements of the view `V`). -/
def TermRes (idom : Array (Option Nat)) (V : Nat → Option Block) (bi k : Nat) (B : ValueId → Prop)
    (st : SState) (t : Terminator) (extra : List Stmt) (t'' : Terminator) (ch : Bool) : Prop :=
  (ch = false → extra = [] ∧ t'' = t) ∧
  (ch = true → skelCandidate (.term t) = true ∧ isBranch t'' = true ∧
    (∀ y ∈ termOperands t'', Placed st B y ∧ AvailAt idom V bi k y) ∧
    (∀ bc' ∈ termCalls t'', ∃ bc ∈ termCalls t, bc'.block = bc.block ∧
      bc'.args.map (fun x => st.types.get? x) = bc.args.map (fun x => st.types.get? x)) ∧
    ∀ x d tb, t'' = .brTable x d tb → st.types.get? x = some .i32)

/-- A terminator replacement `t1 = mapTerm (rename m) t'` of `t`, with `t'` satisfying the
obligation in the state `st1`, seen in a later state `st3`. -/
theorem replTerm_facts {st1 st2 st3 : SState} {t t' : Terminator} {m : List (ValueId × ValueId)}
    {V : Nat → Option Block} {xs : List ValueId}
    (hok : SkelTermOk (fun x => st1.types.get? x) (Placed st1 B) t t')
    (hmap : m.map Prod.fst = xs) (hsub : termOperands t' ⊆ xs)
    (hps : ∀ p ∈ m, Placed st2 B p.2 ∧ AvailHere idom V bi p.2 ∧ st2.types.get? p.2 = st1.types.get? p.1)
    (ht : ∀ y ∈ termOperands t, st1.known y = true)
    (hk3 : ∀ y, st1.known y = true → st3.types.get? y = st1.types.get? y)
    (hk23 : ∀ y, st2.known y = true → st3.types.get? y = st2.types.get? y) :
    isBranch (mapTerm (rename m) t') = true ∧
    (∀ y ∈ termOperands (mapTerm (rename m) t'), Placed st2 B y ∧ AvailHere idom V bi y) ∧
    (∀ bc' ∈ termCalls (mapTerm (rename m) t'), ∃ bc ∈ termCalls t, bc'.block = bc.block ∧
      bc'.args.map (fun x => st3.types.get? x) = bc.args.map (fun x => st3.types.get? x)) ∧
    ∀ x d tb, mapTerm (rename m) t' = .brTable x d tb → st3.types.get? x = some .i32 := by
  obtain ⟨hbr, hops, hcalls, hbt⟩ := hok
  have hren : ∀ y ∈ termOperands t', Placed st2 B (rename m y) ∧ AvailHere idom V bi (rename m y) ∧
      st3.types.get? (rename m y) = st1.types.get? y := by
    intro y hy
    obtain ⟨p, hp, h1, h2⟩ := rename_mem hmap (hsub hy)
    rw [h2]
    obtain ⟨e1, e2, e3⟩ := hps p hp
    exact ⟨e1, e2, by rw [hk23 _ e1.known, e3, h1]⟩
  refine ⟨by rw [isBranch_mapTerm]; exact hbr, fun y hy => ?_, fun bc' hbc' => ?_, fun x d tb he => ?_⟩
  · rw [termOperands_mapTerm, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨(hren z hz).1, (hren z hz).2.1⟩
  · rw [termCalls_mapTerm, List.mem_map] at hbc'
    obtain ⟨bc0, hbc0, rfl⟩ := hbc'
    obtain ⟨bc, hbc, hbl, hargs⟩ := hcalls bc0 hbc0
    refine ⟨bc, hbc, hbl, ?_⟩
    simp only [mapBlockCall, List.map_map]
    have e1 : bc0.args.map ((fun x => st3.types.get? x) ∘ rename m) =
        bc0.args.map (fun x => st1.types.get? x) :=
      List.map_congr_left (fun y hy => (hren y (args_sub_termOperands hbc0 hy)).2.2)
    have e2 : bc.args.map (fun x => st3.types.get? x) = bc.args.map (fun x => st1.types.get? x) :=
      List.map_congr_left (fun y hy => hk3 y (ht y (args_sub_termOperands hbc hy)))
    rw [e1, e2, hargs]
  · cases t' <;> simp only [mapTerm, reduceCtorEq] at he
    rename_i x0 d0 tb0
    simp only [Terminator.brTable.injEq] at he
    obtain ⟨rfl, -, -⟩ := he
    rw [(hren x0 (by simp [termOperands])).2.2]
    exact hbt x0 d0 tb0 rfl

/-- Composing a terminator replacement `t1` of `t` with the outcome of `t1`. -/
theorem termRes_compose {V : Nat → Option Block} {b : Block} {st3 : SState}
    {t t1 t'' : Terminator} {pre extra2 : List Stmt} {ch2 : Bool}
    (hb : V bi = some b) (hcand : skelCandidate (.term t) = true)
    (h1 : isBranch t1 = true)
    (h2 : ∀ y ∈ termOperands t1, Placed st3 B y ∧ AvailHere idom (emitV V bi pre) bi y)
    (h3 : ∀ bc' ∈ termCalls t1, ∃ bc ∈ termCalls t, bc'.block = bc.block ∧
      bc'.args.map (fun x => st3.types.get? x) = bc.args.map (fun x => st3.types.get? x))
    (h4 : ∀ x d tb, t1 = .brTable x d tb → st3.types.get? x = some .i32)
    (hin : TermRes idom (emitV (emitV V bi pre) bi extra2) bi
      (b.body.length + pre.length + extra2.length) B st3 t1 extra2 t'' ch2) :
    TermRes idom (emitV V bi (pre ++ extra2)) bi (b.body.length + (pre ++ extra2).length) B st3 t
      (pre ++ extra2) t'' true := by
  rw [← emitV_append, List.length_append, ← Nat.add_assoc]
  constructor
  · intro h; cases h
  intro _
  refine ⟨hcand, ?_⟩
  cases ch2 with
  | false =>
    obtain ⟨rfl, rfl⟩ := hin.1 rfl
    simp only [emitV_nil, List.length_nil, Nat.add_zero]
    refine ⟨h1, fun y hy => ⟨(h2 y hy).1, ?_⟩, h3, h4⟩
    have := (h2 y hy).2.at_end (b := { b with body := b.body ++ pre }) (by simp [emitV, hb])
    simpa using this
  | true =>
    obtain ⟨-, e2, e3, e4, e5⟩ := hin.2 rfl
    refine ⟨e2, e3, fun bc' hbc' => ?_, e5⟩
    obtain ⟨bc1, hbc1, hb1, ha1⟩ := e4 bc' hbc'
    obtain ⟨bc, hbc, hb2, ha2⟩ := h3 bc1 hbc1
    exact ⟨bc, hbc, hb1.trans hb2, ha1.trans ha2⟩

/-- **A terminator** (`skelTerm`) under the rule obligations (module doc). -/
theorem skelTerm_ok (hR : SimpRulesOk rules) (hK : SkelRulesOk skel) :
    ∀ fuel st t extra t'' st' ch (V : Nat → Option Block) b,
      RInv f V B (fun _ => False) (fun _ => False) st → V bi = some b →
      (∀ y ∈ termOperands t, Placed st B y ∧ AvailHere cfg.idom V bi y) →
      skelTerm skel rules allowed skelOk cfg bi fuel st t = (extra, t'', st', ch) →
      SRun f cfg.idom allowed skelOk bi B V st st' extra.toList ∧
        TermRes cfg.idom (emitV V bi extra.toList) bi (b.body.length + extra.toList.length) B st' t
          extra.toList t'' ch := by
  intro fuel
  induction fuel with
  | zero =>
    intro st t extra t'' st' ch V b h hb _ hs
    simp only [skelTerm, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    exact ⟨SRun.of_rstep h (RStep.refl st), fun _ => ⟨rfl, rfl⟩, fun h => by cases h⟩
  | succ fuel ih =>
    intro st t extra t'' st' ch V b h hb hops hs
    rw [skelTerm] at hs
    obtain ⟨hI1, hS1, hc⟩ := runSkel_ok (V := V) (i := .term t) hR hK allowed h
      (fun y hy => (hops y hy).1)
    have hcand := fun c (hc' : (runSkel skel rules allowed st (.term t)).1 = some c) =>
      runSkel_cand (allowed := allowed) hc'
    generalize runSkel skel rules allowed st (.term t) = r at hI1 hS1 hc hcand hs
    obtain ⟨c, st1⟩ := r
    simp only at hI1 hS1 hc hcand hs
    have hR1 : SRun f cfg.idom allowed skelOk bi B V st st1 [] := SRun.of_rstep hI1 hS1
    have hkeep : ∀ extra t'' st' ch, (#[], t, st1, false) = (extra, t'', st', ch) →
        SRun f cfg.idom allowed skelOk bi B V st st' extra.toList ∧
        TermRes cfg.idom (emitV V bi extra.toList) bi (b.body.length + extra.toList.length) B st' t
          extra.toList t'' ch := by
      intro extra t'' st' ch he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      exact ⟨hR1, fun _ => ⟨rfl, rfl⟩, fun h => by cases h⟩
    have hops1 : ∀ y ∈ termOperands t, st1.known y = true :=
      fun y hy => hS1.known (hops y hy).1.known
    rcases c with _ | c
    · exact hkeep _ _ _ _ hs
    have hcd := hcand c rfl
    have hco := hc c rfl
    rcases c with _ | v | j | ⟨j2, v2⟩ | c | ⟨a, c⟩
    · exact hkeep _ _ _ _ hs
    · exact hkeep _ _ _ _ hs
    · -- replace
      rcases j with j | t'
      · exact hkeep _ _ _ _ hs
      simp only at hs
      split at hs
      · rename_i m st2 out hm
        obtain ⟨hrun, hmap, hps⟩ := matAll_spec hI1.m hb hco.2.1 hm
        have hb2 : emitV V bi out.toList bi = some { b with body := b.body ++ out.toList } := by
          simp [emitV, hb]
        have hf0 := replTerm_facts (st3 := st2) (V := emitV V bi out.toList) hco hmap (fun _ h => h) hps hops1
          (fun y hy => hrun.step.typesKnown y hy) (fun _ _ => rfl)
        generalize hrec : skelTerm skel rules allowed skelOk cfg bi fuel st2
          (mapTerm (rename m) t') = rr at hs
        obtain ⟨more, t3, st3, ch2⟩ := rr
        simp only [Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
        obtain ⟨hrun2, hres2⟩ := ih st2 _ more t3 st3 ch2 _ _ (hI1.of_mrun hrun) hb2
          hf0.2.1 hrec
        have hf := replTerm_facts (st3 := st3) (V := emitV V bi out.toList) hco hmap (fun _ h => h) hps hops1
          (fun y hy => (hrun2.typesKnown y (hrun.step.known y hy)).trans (hrun.step.typesKnown y hy))
          (fun y hy => hrun2.typesKnown y hy)
        refine ⟨by simpa using hR1.trans0 ((SRun.of_mrun hI1 hrun).trans hrun2), ?_⟩
        simp only [Array.toList_append]
        exact termRes_compose hb hcd hf.1 (fun y hy => ⟨hrun2.good y (hf.2.1 y hy).1, (hf.2.1 y hy).2⟩)
          hf.2.2.1 hf.2.2.2 (by simpa using hres2)
      · exact hkeep _ _ _ _ hs
    · exact hkeep _ _ _ _ hs
    · -- replaceBranchCond
      simp only at hs
      split at hs
      · rename_i c0 th el
        split at hs
        · rename_i m st2 out hm
          obtain ⟨hrun, hmap, hps⟩ := matAll_spec hI1.m hb
            (fun y hy => by simp only [List.mem_singleton] at hy; rw [hy]; exact hco) hm
          have hb2 : emitV V bi out.toList bi = some { b with body := b.body ++ out.toList } := by
            simp [emitV, hb]
          obtain ⟨p, hp, -, hp2⟩ := rename_mem hmap (List.mem_singleton_self c)
          obtain ⟨e1, e2, -⟩ := hps p hp
          have hargs : ∀ y ∈ th.args ++ el.args, y ∈ termOperands (.brif c0 th el) := by
            intro y hy
            show y ∈ (c0 :: th.args) ++ el.args
            rcases List.mem_append.1 hy with h | h
            · exact List.mem_append_left _ (List.mem_cons_of_mem _ h)
            · exact List.mem_append_right _ h
          have hops2 : ∀ y ∈ termOperands (.brif (rename m c) th el),
              Placed st2 B y ∧ AvailHere cfg.idom (emitV V bi out.toList) bi y := by
            intro y hy
            change y ∈ (rename m c :: th.args) ++ el.args at hy
            have : y = rename m c ∨ y ∈ th.args ++ el.args := by
              rcases List.mem_append.1 hy with h | h
              · rcases List.mem_cons.1 h with h | h
                · exact .inl h
                · exact .inr (List.mem_append_left _ h)
              · exact .inr (List.mem_append_right _ h)
            rcases this with hy | hy
            · rw [hy, hp2]; exact ⟨e1, e2⟩
            · exact ⟨hrun.good y (hS1.good y (hops y (hargs y hy)).1),
                (hops y (hargs y hy)).2.emit bi out.toList⟩
          generalize hrec : skelTerm skel rules allowed skelOk cfg bi fuel st2
            (.brif (rename m c) th el) = rr at hs
          obtain ⟨more, t3, st3, ch2⟩ := rr
          simp only [Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
          obtain ⟨hrun2, hres2⟩ := ih st2 _ more t3 st3 ch2 _ _ (hI1.of_mrun hrun) hb2 hops2 hrec
          refine ⟨by simpa using hR1.trans0 ((SRun.of_mrun hI1 hrun).trans hrun2), ?_⟩
          simp only [Array.toList_append]
          refine termRes_compose hb hcd rfl
            (fun y hy => ⟨hrun2.good y (hops2 y hy).1, (hops2 y hy).2⟩) (fun bc' hbc' => ?_)
            (fun x d tb he => by cases he) (by simpa using hres2)
          exact ⟨bc', by simpa [termCalls] using hbc', rfl, rfl⟩
        · exact hkeep _ _ _ _ hs
      · exact hkeep _ _ _ _ hs
    · -- replaceWithTwo
      rcases a with a | ta
      · rcases c with c | t'
        · exact hkeep _ _ _ _ hs
        simp only at hs
        split at hs
        · exact hkeep _ _ _ _ hs
        rename_i hchk
        simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hchk
        obtain ⟨hska, htl⟩ := hchk
        obtain ⟨⟨hpa, hsa, hga⟩, hok⟩ := hco
        split at hs
        · rename_i m st2 out hm
          obtain ⟨hrun, hmap, hps⟩ := matAll_spec hI1.m hb
            (fun y hy => by
              rcases List.mem_append.1 hy with hy | hy
              · exact hga y hy
              · exact hok.2.1 y hy) hm
          have hb2 : emitV V bi out.toList bi = some { b with body := b.body ++ out.toList } := by
            simp [emitV, hb]
          have hopsa := renamed_ops (i := a) hmap (fun y hy => List.mem_append_left _ hy)
            (fun p hp => ⟨(hps p hp).1, (hps p hp).2.1⟩)
          have hsub : termOperands t' ⊆ operands a ++ termOperands t' :=
            fun y hy => List.mem_append_right _ hy
          have hf0 := replTerm_facts (st3 := st2) (V := emitV V bi out.toList) hok hmap hsub hps
            hops1 (fun y hy => hrun.step.typesKnown y hy) (fun _ _ => rfl)
          let tr : Stmt := { inst := mapOperands (rename m) a }
          have htr : TrapOk cfg.idom (emitV V bi out.toList) bi (b.body ++ out.toList).length skelOk B
              st2 tr := by
            refine ⟨rfl, by simp only [tr]; rw [isTrapLike_mapOperands]; exact htl,
              ⟨a, rename m, hska, rfl⟩, fun y hy => ⟨(hopsa y hy).1, ?_⟩⟩
            exact (hopsa y hy).2.at_end hb2
          have hI2 := hI1.of_mrun hrun
          have hT := SRun.trap (allowed := allowed) hI2 hb2 htr
          have hb3 : emitV (emitV V bi out.toList) bi [tr] bi =
              some { b with body := b.body ++ out.toList ++ [tr] } := by simp [emitV, hb]
          generalize hrec : skelTerm skel rules allowed skelOk cfg bi fuel st2
            (mapTerm (rename m) t') = rr at hs
          obtain ⟨more, t3, st3, ch2⟩ := rr
          simp only [Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
          obtain ⟨hrun2, hres2⟩ := ih st2 _ more t3 st3 ch2 _ _ hT.inv hb3
            (fun y hy => ⟨(hf0.2.1 y hy).1, (hf0.2.1 y hy).2.emit bi [tr]⟩) hrec
          have hf := replTerm_facts (st3 := st3) (V := emitV V bi out.toList) hok hmap hsub hps hops1
            (fun y hy => (hrun2.typesKnown y (hrun.step.known y hy)).trans (hrun.step.typesKnown y hy))
            (fun y hy => hrun2.typesKnown y hy)
          have hall := hR1.trans0 ((SRun.of_mrun hI1 hrun).trans (hT.trans hrun2))
          refine ⟨by simpa using hall, ?_⟩
          have hres2' : TermRes cfg.idom (emitV (emitV V bi (out.toList ++ [tr])) bi more.toList) bi
              (b.body.length + (out.toList ++ [tr]).length + more.toList.length) B st3
              (mapTerm (rename m) t') more.toList t3 ch2 := by
            have e : emitV (emitV V bi out.toList) bi [tr] = emitV V bi (out.toList ++ [tr]) :=
              emitV_append _ _ _ _
            rw [← e]; simpa [Nat.add_assoc] using hres2
          have := termRes_compose (pre := out.toList ++ [tr]) hb hcd hf.1
            (fun y hy => ⟨hrun2.good y (hf.2.1 y hy).1, by
              rw [← emitV_append]; exact (hf.2.1 y hy).2.emit bi [tr]⟩)
            hf.2.2.1 hf.2.2.2 hres2'
          simpa [tr] using this
        · exact hkeep _ _ _ _ hs
      · exact hkeep _ _ _ _ hs

end Skel

end Opt

import FV.Opt.Proof.SimpGraph

/-!
# Materialisation keeps the e-graph invariant (`Opt.materialize_spec`)

`materialize x` returns an available value `x'` with `x`'s value; the values it emits are
copies of graph nodes over available (materialised) operands. A fresh copy is a new graph node
(`gval_insert`); re-emitting a virtual value replaces its node by a copy over *twin* operands,
which keeps the valuation (`den_overwrite`).
-/

namespace Opt

open Clif

section Mat

variable {f : Function} {ρ : Valuation} {fr : Frame} {mem : Mem}

/-- How the state changes while values are materialised: the valuation and the known values
are kept, values become available, and the nodes of available values never change. -/
structure MGrow (ρ : Valuation) (fr : Frame) (mem : Mem) (st st' : SState) : Prop where
  fix : ∀ x, st.known x = true → gval ρ fr mem st' x = gval ρ fr mem st x
  known : ∀ x, st.known x = true → st'.known x = true
  solid : ∀ x, st.solid x = true → st'.solid x = true
  avail : ∀ x, st.avail.contains x = true → st'.avail.contains x = true
  availDefs : ∀ x, st.avail.contains x = true → st'.defs.get? x = st.defs.get? x
  /-- The node of a known value changes only when it becomes available. -/
  defs : ∀ x, st.known x = true → st'.avail.contains x = false → st'.defs.get? x = st.defs.get? x
  types : ∀ x, st.known x = true → st'.types.get? x = st.types.get? x
  alts : st'.alts = st.alts
  memo : st'.memo = st.memo
  fn : st'.fn = st.fn
  trap : st'.trapBlocks = st.trapBlocks
  remat : st'.rematConst = st.rematConst
  partialVals : st'.partialVals = st.partialVals

theorem MGrow.refl (st : SState) : MGrow ρ fr mem st st :=
  ⟨fun _ _ => rfl, fun _ h => h, fun _ h => h, fun _ h => h, fun _ _ => rfl, fun _ _ _ => rfl,
   fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem MGrow.trans {st1 st2 st3 : SState} (h1 : MGrow ρ fr mem st1 st2)
    (h2 : MGrow ρ fr mem st2 st3) : MGrow ρ fr mem st1 st3 :=
  ⟨fun x h => (h2.fix x (h1.known x h)).trans (h1.fix x h), fun x h => h2.known x (h1.known x h),
   fun x h => h2.solid x (h1.solid x h), fun x h => h2.avail x (h1.avail x h),
   fun x h => (h2.availDefs x (h1.avail x h)).trans (h1.availDefs x h),
   fun x h ha => by
     have ha2 : st2.avail.contains x = false := by
       cases hc : st2.avail.contains x with
       | false => rfl
       | true => rw [h2.avail x hc] at ha; cases ha
     exact (h2.defs x (h1.known x h) ha).trans (h1.defs x h ha2),
   fun x h => (h2.types x (h1.known x h)).trans (h1.types x h),
   h2.alts.trans h1.alts, h2.memo.trans h1.memo, h2.fn.trans h1.fn, h2.trap.trans h1.trap,
   h2.remat.trans h1.remat, h2.partialVals.trans h1.partialVals⟩

/-- The available values of a state (the domain of twins). -/
def SState.availP (st : SState) (x : ValueId) : Prop := st.avail.contains x = true

theorem Twin.grow {st st' : SState} (g : MGrow ρ fr mem st st') {y y' : ValueId}
    (h : Twin (fun x => st.defs.get? x) st.availP y y') :
    Twin (fun x => st'.defs.get? x) st'.availP y y' :=
  h.mono (fun x hx => g.avail x hx) (fun x hx => g.availDefs x hx)

theorem gval_twin {st : SState} {y y' : ValueId}
    (h : Twin (fun x => st.defs.get? x) st.availP y y') :
    gval ρ fr mem st y' = gval ρ fr mem st y :=
  den_twin (D := st.graph) h

theorem pureTyped_ops {tm : ValueId → Option Ty} {f : Function} {n : Inst} (hp : isPure n = true)
    (h : pureTyped tm f n = true) : ∀ u ∈ operands n, (tm u).isSome := by
  intro u hu
  cases n <;> simp only [isPure, Bool.false_eq_true] at hp <;> simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at hu <;>
    simp only [pureTyped, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  all_goals (try (rcases hu with rfl | rfl | rfl))
  all_goals (try (rcases hu with rfl | rfl))
  all_goals (try subst hu)
  all_goals (try simp_all)
  all_goals first
    | done
    | (rename_i h; obtain ⟨_, ⟨_, h3⟩ | h3⟩ := h <;> simp_all)
    | (rename_i h; split at h <;> simp_all)

/-- A well-typed node over defined values evaluates. -/
theorem typed_total {st : SState} (h : GInv f ρ fr mem st) (hE : GoodEnv f fr mem) {n : Inst}
    (hty : st.typedNode n = true) (hops : ∀ u ∈ operands n, ∃ a, gval ρ fr mem st u = some a) :
    ∃ a, evalNode (withRegs fr (gval ρ fr mem st)) mem n = some a ∧ SState.nodeTy n = some a.ty := by
  simp only [SState.typedNode, Bool.and_eq_true] at hty
  obtain ⟨hp, ht⟩ := hty
  rw [h.fn] at ht
  obtain ⟨v, hv⟩ := evalInst_total (f := f) (fr := withRegs fr (gval ρ fr mem st)) (mem := mem)
    hp ht hE.glob (fun x hx => by
      obtain ⟨a, ha⟩ := hops x hx
      obtain ⟨t, htx⟩ := Option.isSome_iff_exists.1 (pureTyped_ops hp ht x hx)
      exact ⟨a, ha, by rw [htx, h.types x t a htx ha]⟩) hE.slots
    (fun _ _ name _ _ _ _ => hE.syms name)
  have he : evalNode (withRegs fr (gval ρ fr mem st)) mem n = some v := by simp [evalNode, hv]
  exact ⟨v, he, evalNode_ty he⟩

theorem typedNode_congr {st st' : SState} {n : Inst} (hf : st'.fn = st.fn)
    (ht : ∀ u ∈ operands n, st'.types.get? u = st.types.get? u) :
    st'.typedNode n = st.typedNode n := by
  simp only [SState.typedNode, hf]
  congr 1
  cases n <;> simp_all [pureTyped, operands]

theorem emit_fields (st : SState) (bi : Nat) (x x' : ValueId) (n' : Inst) :
    (st.emit bi x x' n').defs = st.defs.insert x' n' ∧
    (st.emit bi x x' n').avail = st.avail.insert x' bi ∧
    (st.emit bi x x' n').types = (match st.types.get? x with
      | some t => st.types.insert x' t
      | none => st.types) ∧
    (st.emit bi x x' n').next = st.next ∧ (st.emit bi x x' n').alts = st.alts ∧
    (st.emit bi x x' n').memo = st.memo ∧ (st.emit bi x x' n').fn = st.fn ∧
    (st.emit bi x x' n').trapBlocks = st.trapBlocks ∧
    (st.emit bi x x' n').rematConst = st.rematConst ∧
    (st.emit bi x x' n').partialVals = st.partialVals ∧
    (st.emit bi x x' n').classes = st.classes :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hm_contains_insert' {β : Type} (m : Std.HashMap ValueId β) (k a : ValueId) (v : β) :
    (m.insert k v).contains a = true ↔ k = a ∨ m.contains a = true := by
  rw [Std.HashMap.contains_insert]; simp

/-- Emitting a fresh copy of the available `x` over twin operands. -/
theorem emit_fresh_spec {st : SState} (h : GInv f ρ fr mem st) {bi : Nat} {x : ValueId} {n : Inst}
    {τ : ValueId → ValueId} (hx : st.defs.get? x = some n) (hxa : st.avail.contains x = true)
    (hτ : ∀ u ∈ operands n, st.avail.contains (τ u) = true ∧
      Twin (fun z => st.defs.get? z) st.availP u (τ u)) :
    ∀ st', st' = ({ st with next := st.next + 1 } : SState).emit bi x st.next (mapOperands τ n) →
    GInv f ρ fr mem st' ∧ MGrow ρ fr mem st st' ∧ gval ρ fr mem st' st.next = gval ρ fr mem st x ∧
      st'.avail.contains st.next = true ∧
      Twin (fun z => st'.defs.get? z) st'.availP x st.next := by
  intro st' hst
  obtain ⟨ed, ea, et, enx, eal, em, ef, etr, er, ep, ec⟩ :=
    emit_fields ({ st with next := st.next + 1 } : SState) bi x st.next (mapOperands τ n)
  rw [← hst] at ed ea et enx eal em ef etr er ep ec
  simp only at ed ea et enx eal em ef etr er ep ec
  have hw : st.known st.next = false := by
    cases hk : st.known st.next with
    | false => rfl
    | true => exact absurd (h.fresh _ hk) (Nat.lt_irrefl _)
  have hxw : x ≠ st.next := fun he => by rw [he] at hxa; rw [known_of_avail hxa] at hw; cases hw
  have hval : evalNode (withRegs fr (gval ρ fr mem st)) mem (mapOperands τ n) = gval ρ fr mem st x := by
    rw [gval, den_node (D := st.graph) (by simpa [SState.graph] using hx)]
    exact evalNode_rename rfl rfl rfl (fun u hu => gval_twin (hτ u hu).2)
  obtain ⟨t, a, htx, hxv, hta⟩ : ∃ t a, st.types.get? x = some t ∧ gval ρ fr mem st x = some a ∧
      a.ty = t := by
    obtain ⟨a, h1, h2⟩ := h.tot x hxa
    exact ⟨_, a, h2, h1, rfl⟩
  have et' : st'.types = st.types.insert st.next t := by rw [et, htx]
  have hops : ∀ y ∈ operands (mapOperands τ n), st.known y = true := by
    intro y hy
    rw [operands_mapOperands, List.mem_map] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    exact known_of_avail (hτ u hu).1
  obtain ⟨hI, hfix, hkm, hsm, hkw, hnew⟩ := fresh_spec (st' := st') h hops ed
    (fun z hz => by rw [et', hm_get?_insert, if_neg (Ne.symm hz)])
    (fun t' a' ht' hv => by
      rw [et', hm_get?_insert, if_pos rfl] at ht'; cases ht'
      rw [hval, hxv] at hv; cases hv; exact hta)
    enx (fun z hz => by rw [ea]; simp [Std.HashMap.contains_insert, Ne.symm hz]) eal em ef ec
    (fun z _ => by rw [ep]) (fun _ => ⟨a, by rw [hval]; exact hxv, by rw [et', hm_get?_insert]; simp [hta]⟩)
  have hwa : st'.avail.contains st.next = true := by rw [ea, hm_contains_insert']; exact .inl rfl
  have hadx : ∀ z, st.avail.contains z = true → st'.defs.get? z = st.defs.get? z := by
    intro z hz
    have : z ≠ st.next := fun he => by rw [he] at hz; rw [known_of_avail hz] at hw; cases hw
    rw [ed, hm_get?_insert, if_neg (Ne.symm this)]
  have hav : ∀ z, st.avail.contains z = true → st'.avail.contains z = true := by
    intro z hz; rw [ea, hm_contains_insert']; exact .inr hz
  have g : MGrow ρ fr mem st st' :=
    ⟨hfix, hkm, hsm, hav, hadx, fun z hz _ => by
      have : z ≠ st.next := fun he => by rw [he] at hz; rw [hz] at hw; cases hw
      rw [ed, hm_get?_insert, if_neg (Ne.symm this)], fun z hz => by
      have : z ≠ st.next := fun he => by rw [he] at hz; rw [hz] at hw; cases hw
      rw [et', hm_get?_insert, if_neg (Ne.symm this)], eal, em, ef, etr, er, ep⟩
  refine ⟨hI, g, by rw [hnew, hval], hwa, ?_⟩
  refine .clone τ (hav x hxa) hwa (by rw [hadx x hxa]; exact hx) (by rw [ed, hm_get?_insert]; simp)
    (fun u hu => (hτ u hu).2.grow g)

/-- Emitting the virtual `x` (replacing its node by a copy over twin operands). -/
theorem emit_over_spec {st : SState} (h : GInv f ρ fr mem st) (hE : GoodEnv f fr mem) {bi : Nat}
    {x : ValueId} {n : Inst} {τ : ValueId → ValueId} (hx : st.defs.get? x = some n)
    (hxa : st.avail.contains x = false) (hty : st.typedNode n = true)
    (htx : (st.types.get? x).isSome = true)
    (hτ : ∀ u ∈ operands n, st.avail.contains (τ u) = true ∧
      Twin (fun z => st.defs.get? z) st.availP u (τ u)) :
    ∀ st', st' = st.emit bi x x (mapOperands τ n) →
    GInv f ρ fr mem st' ∧ MGrow ρ fr mem st st' ∧ gval ρ fr mem st' x = gval ρ fr mem st x ∧
      st'.avail.contains x = true := by
  intro st' hst
  obtain ⟨ed, ea, et, enx, eal, em, ef, etr, er, ep, ec⟩ := emit_fields st bi x x (mapOperands τ n)
  rw [← hst] at ed ea et enx eal em ef etr er ep ec
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 htx
  have et' : ∀ z, st'.types.get? z = st.types.get? z := by
    intro z
    rw [et, ht, hm_get?_insert]
    split
    · rename_i he; subst he; exact ht.symm
    · rfl
  have hgr : st'.graph = graphInsert st.graph x (mapOperands τ n) := by
    funext z
    simp only [SState.graph, graphInsert, ed, hm_get?_insert]
    by_cases hz : x = z
    · subst hz; simp
    · simp [hz, Ne.symm hz]
  have hg : gval ρ fr mem st' = gval ρ fr mem st := by
    simp only [gval, hgr]
    exact den_overwrite (S := st.availP) (by simpa [SState.graph] using hx)
      (by simp [SState.availP, hxa]) (fun u hu => (hτ u hu).2)
  have hkx : st.known x = true := known_of_defs hx
  have hk : ∀ z, st'.known z = st.known z := by
    intro z
    cases hkz : st.known z with
    | true =>
      simp only [SState.known, Bool.or_eq_true] at hkz ⊢
      rcases hkz with hkz | hkz
      · left; rw [ed, Std.HashMap.contains_insert]; simp [hkz]
      · right; rw [ea, Std.HashMap.contains_insert]; simp [hkz]
    | false =>
      obtain ⟨hd0, ha0⟩ := known_false hkz
      have hzx : z ≠ x := fun he => by rw [he] at hkz; rw [hkx] at hkz; cases hkz
      have h1 : st.defs.contains z = false := by
        rw [Std.HashMap.contains_eq_isSome_getElem?]; simpa using hd0
      simp only [SState.known, ed, ea, Std.HashMap.contains_insert, h1, ha0, Bool.or_false,
        Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      exact ⟨Ne.symm hzx, Ne.symm hzx⟩
  have hs : ∀ z, st'.solid z = st.solid z := by intro z; simp [SState.solid, hk, ep]
  have hxv : ∃ a, gval ρ fr mem st x = some a ∧ st.types.get? x = some a.ty := by
    have hn : ∀ u ∈ operands n, ∃ a, gval ρ fr mem st u = some a := by
      intro u hu
      obtain ⟨a, h1, -⟩ := h.tot _ (hτ u hu).1
      exact ⟨a, by rw [← gval_twin (hτ u hu).2]; exact h1⟩
    obtain ⟨a, ha, _⟩ := typed_total h hE hty hn
    have hgx : gval ρ fr mem st x = some a := by
      rw [gval, den_node (D := st.graph) (by simpa [SState.graph] using hx)]; exact ha
    exact ⟨a, hgx, by rw [ht, h.types x t a ht hgx]⟩
  have hdx : ∀ z, z ≠ x → st'.defs.get? z = st.defs.get? z := by
    intro z hz; rw [ed, hm_get?_insert, if_neg (Ne.symm hz)]
  have hav : ∀ z, st.avail.contains z = true → st'.avail.contains z = true := by
    intro z hz; rw [ea, hm_contains_insert']; exact .inr hz
  refine ⟨⟨ef.trans h.fn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨fun z _ => by rw [hg], fun z hz => by rw [hk]; exact hz, fun z hz => by rw [hs]; exact hz,
     hav, fun z hz => hdx z (fun he => by rw [he] at hz; rw [hz] at hxa; cases hxa),
     fun z _ hz => hdx z (fun he => by
       rw [he, ea, Std.HashMap.contains_insert] at hz; simp at hz),
     fun z _ => et' z, eal, em, ef, etr, er, ep⟩,
    by rw [hg], by rw [ea, hm_contains_insert']; exact .inl rfl⟩
  · intro z m hz y hy
    rw [hk]
    by_cases hzx : z = x
    · subst hzx
      rw [ed, hm_get?_insert, if_pos rfl] at hz; cases hz
      rw [operands_mapOperands, List.mem_map] at hy
      obtain ⟨u, hu, rfl⟩ := hy
      exact known_of_avail (hτ u hu).1
    · rw [hdx z hzx] at hz; exact h.closed z m hz y hy
  · intro z hz; rw [hk] at hz; rw [enx]; exact h.fresh z hz
  · intro z hz; rw [enx] at hz; exact h.freshρ z hz
  · intro z a hz
    obtain ⟨h1, h2⟩ := h.leaf z a hz
    have hzx : z ≠ x := fun he => by rw [he] at h2; rw [hx] at h2; cases h2
    exact ⟨hav z h1, by rw [hdx z hzx]; exact h2⟩
  · intro z hz
    rw [hg, et']
    rw [ea, hm_contains_insert'] at hz
    rcases hz with rfl | hz
    · exact hxv
    · exact h.tot z hz
  · intro z t' a hz hv; rw [hg] at hv; rw [et'] at hz; exact h.types z t' a hz hv
  · intro z ms hz; rw [hk, hg]; rw [eal] at hz; exact h.alts z ms hz
  · intro n' w hz; rw [hg]; rw [em] at hz
    obtain ⟨h1, h2⟩ := h.memo n' w hz
    exact ⟨fun y hy => by rw [hk]; exact h1 y hy, h2⟩
  · intro z hz; rw [hk]; rw [ep] at hz; exact h.partialKnown z hz
  · intro z hz; rw [hg, et']; rw [hs] at hz; exact h.solid z hz
  · intro k ms hz; rw [ec] at hz
    obtain ⟨o, ho, h2⟩ := h.classes k ms hz
    exact ⟨o, by rw [hs]; exact ho, by rw [hg]; exact h2⟩

theorem foldlM_option_inv {α β : Type} (g : β → α → Option β) (I : List α → β → Prop)
    (hstep : ∀ pre a c c', I pre c → g c a = some c' → I (pre ++ [a]) c') :
    ∀ (l pre : List α) (b b' : β), I pre b → l.foldlM g b = some b' → I (pre ++ l) b' := by
  intro l
  induction l with
  | nil => intro pre b b' hb h; simp only [List.foldlM, pure] at h; cases h; simpa using hb
  | cons a as ih =>
    intro pre b b' hb h
    simp only [List.foldlM] at h
    cases hg : g b a with
    | none => rw [hg] at h; cases h
    | some c =>
      rw [hg] at h
      have := ih (pre ++ [a]) c b' (hstep pre a b c hb hg) h
      simpa using this

theorem lookup_zip {u : ValueId} : ∀ (l l' : List ValueId), l.length = l'.length → u ∈ l →
    ∃ j : Nat, l[j]? = some u ∧ (l.zip l').lookup u = l'[j]?
  | [], _, _, hu => by cases hu
  | a :: as, [], hl, _ => by simp at hl
  | a :: as, b :: bs, hl, hu => by
    simp only [List.zip_cons_cons, List.lookup_cons]
    by_cases hua : u = a
    · subst hua; exact ⟨0, rfl, by simp⟩
    · have : (u == a) = false := by simpa using hua
      rw [this]
      obtain ⟨j, hj, hl'⟩ := lookup_zip as bs (by simpa using hl) (by simpa [hua] using hu)
      exact ⟨j + 1, by simpa using hj, by simpa using hl'⟩

/-- What `materialize` guarantees. -/
structure MatOK (ρ : Valuation) (fr : Frame) (mem : Mem) (st : SState) (x x' : ValueId)
    (st' : SState) : Prop where
  inv : GInv f ρ fr mem st'
  grow : MGrow ρ fr mem st st'
  known : st.known x = true
  val : gval ρ fr mem st' x' = gval ρ fr mem st x
  avail : st'.avail.contains x' = true
  twin : Twin (fun z => st'.defs.get? z) st'.availP x x'

variable {cfg : Cfg} {allowed : Inst → Bool} {bi : Nat}

theorem clone_spec (hE : GoodEnv f fr mem) {fuel : Nat}
    (ih : ∀ st out x x' st' out', GInv f ρ fr mem st →
      materialize cfg allowed bi fuel (st, out) x = some (x', st', out') →
      MatOK (f := f) ρ fr mem st x x' st')
    {st : SState} {out : Array Stmt} {x x' : ValueId} {st' : SState} {out' : Array Stmt}
    (h : GInv f ρ fr mem st)
    (hc : materialize.clone cfg allowed bi fuel st out x = some (x', st', out')) :
    MatOK (f := f) ρ fr mem st x x' st' := by
  rw [materialize.clone] at hc
  split at hc
  · cases hc
  rename_i n hx
  split at hc
  · cases hc
  rename_i hchk
  simp only [Bool.or_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none, not_or] at hchk
  obtain ⟨⟨-, hty⟩, htx⟩ := hchk
  have hkx : st.known x = true := known_of_defs hx
  have hknops : ∀ u ∈ operands n, st.known u = true := h.closed x n hx
  -- the operands
  let I : List ValueId → SState × Array Stmt × Array ValueId → Prop := fun pre acc =>
    GInv f ρ fr mem acc.1 ∧ MGrow ρ fr mem st acc.1 ∧ acc.2.2.toList.length = pre.length ∧
      ∀ (j : Nat) (u : ValueId), pre[j]? = some u → ∃ u', acc.2.2.toList[j]? = some u' ∧
        acc.1.avail.contains u' = true ∧ Twin (fun z => acc.1.defs.get? z) acc.1.availP u u'
  have hfold := foldlM_option_inv (I := I)
    (g := fun (acc : SState × Array Stmt × Array ValueId) y =>
      match materialize cfg allowed bi fuel (acc.1, acc.2.1) y with
      | none => none
      | some (y', st, out) => some (st, out, acc.2.2.push y'))
    (by
      intro pre a c c' hI hg
      obtain ⟨hI1, hI2, hI3, hI4⟩ := hI
      split at hg
      · cases hg
      rename_i y' st2 out2 hm
      cases hg
      have hok := ih _ _ _ _ _ _ hI1 hm
      refine ⟨hok.inv, hI2.trans hok.grow, by simp [hI3], fun j u hj => ?_⟩
      simp only [Array.toList_push]
      by_cases hjl : j < pre.length
      · rw [List.getElem?_append_left hjl] at hj
        obtain ⟨u', h1, h2, h3⟩ := hI4 j u hj
        refine ⟨u', by rw [List.getElem?_append_left (by rw [hI3]; exact hjl)]; exact h1,
          hok.grow.avail _ h2, h3.grow hok.grow⟩
      · have hjl' : j = pre.length := by
          have := (List.getElem?_eq_some_iff.1 hj).1
          simp at this; omega
        subst hjl'
        simp at hj; subst hj
        exact ⟨y', by simp [← hI3], hok.avail, hok.twin⟩)
    (operands n) [] (st, out, #[]) 
  split at hc
  · cases hc
  rename_i st1 out1 ops hf
  obtain ⟨h1, g1, hlen, hops⟩ := hfold _ ⟨h, MGrow.refl st, rfl, fun j u hj => by simp at hj⟩ hf
  simp only [List.nil_append] at hlen hops
  dsimp only at hc
  split at hc
  · cases hc
  rename_i hcyc
  -- the renaming of the operands
  let τ := fun y => (((operands n).zip ops.toList).lookup y).getD y
  have hτ : ∀ u ∈ operands n, st1.avail.contains (τ u) = true ∧
      Twin (fun z => st1.defs.get? z) st1.availP u (τ u) := by
    intro u hu
    obtain ⟨j, hj, hl⟩ := lookup_zip (operands n) ops.toList hlen.symm hu
    obtain ⟨u', h1', h2', h3'⟩ := hops j u hj
    have : τ u = u' := by simp only [τ, hl, h1']; rfl
    rw [this]; exact ⟨h2', h3'⟩
  have hren : renameOps n ops.toList = mapOperands τ n := rfl
  split at hc
  · -- a fresh copy of the available `x`
    rename_i hwas
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl, -⟩ := hc
    have hxa1 : st1.avail.contains x = true := g1.avail x hwas
    have hx1 : st1.defs.get? x = some n := by rw [g1.availDefs x hwas]; exact hx
    rw [hren]
    obtain ⟨i2, g2, v2, a2, t2⟩ := emit_fresh_spec (bi := bi) h1 hx1 hxa1 hτ _ rfl
    exact ⟨i2, g1.trans g2, hkx, by rw [v2, g1.fix x hkx], a2, t2⟩
  · -- the virtual `x`
    rename_i hwas
    simp only [Bool.not_eq_true] at hwas
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl, -⟩ := hc
    have hxa1 : st1.avail.contains x = false := by
      simp only [hwas, Bool.not_false, Bool.true_and, Bool.not_eq_true] at hcyc
      exact hcyc
    have hx1 : st1.defs.get? x = some n := by rw [g1.defs x hkx hxa1]; exact hx
    have hty1 : st1.typedNode n = true := by
      rw [typedNode_congr (g1.fn) (fun u hu => g1.types u (hknops u hu))]; simpa using hty
    have htx1 : (st1.types.get? x).isSome = true := by
      rw [g1.types x hkx]; exact Option.isSome_iff_ne_none.2 htx
    rw [hren]
    obtain ⟨i2, g2, v2, a2⟩ := emit_over_spec (bi := bi) h1 hE hx1 hxa1 hty1 htx1 hτ _ rfl
    exact ⟨i2, g1.trans g2, hkx, by rw [v2, g1.fix x hkx], a2, .refl x⟩

theorem materialize_spec (hE : GoodEnv f fr mem) : ∀ fuel st out x x' st' out',
    GInv f ρ fr mem st →
    materialize cfg allowed bi fuel (st, out) x = some (x', st', out') →
    MatOK (f := f) ρ fr mem st x x' st' := by
  intro fuel
  induction fuel with
  | zero => intro st out x x' st' out' _ h; simp [materialize] at h
  | succ fuel ih =>
    intro st out x x' st' out' hI h
    rw [materialize] at h
    split at h
    · rename_i d hd
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        have ha : st.avail.contains x = true := by
          rw [Std.HashMap.contains_eq_isSome_getElem?]
          simp only [Std.HashMap.get?_eq_getElem?] at hd; simp [hd]
        exact ⟨hI, MGrow.refl st, known_of_avail ha, rfl, ha, .refl x⟩
      · exact clone_spec hE ih hI h
    · exact clone_spec hE ih hI h

/-- `materializeAll`: every value is renamed to an available value with its value. -/
theorem materializeAll_spec (hE : GoodEnv f fr mem) {st : SState} {xs : List ValueId}
    {m : List (ValueId × ValueId)} {st' : SState} {out : Array Stmt} (h : GInv f ρ fr mem st)
    (hm : materializeAll cfg allowed bi st xs = some (m, st', out)) :
    GInv f ρ fr mem st' ∧ MGrow ρ fr mem st st' ∧ m.map Prod.fst = xs ∧
      ∀ p ∈ m, gval ρ fr mem st' p.2 = gval ρ fr mem st' p.1 ∧ st'.avail.contains p.2 = true ∧
        st'.known p.1 = true := by
  unfold materializeAll at hm
  let I : List ValueId → List (ValueId × ValueId) × SState × Array Stmt → Prop := fun pre acc =>
    GInv f ρ fr mem acc.2.1 ∧ MGrow ρ fr mem st acc.2.1 ∧ acc.1.map Prod.fst = pre ∧
      ∀ p ∈ acc.1, gval ρ fr mem acc.2.1 p.2 = gval ρ fr mem acc.2.1 p.1 ∧
        acc.2.1.avail.contains p.2 = true ∧ acc.2.1.known p.1 = true
  have := foldlM_option_inv _ I (by
    intro pre a c c' hI hg
    obtain ⟨m0, st0, out0⟩ := c
    obtain ⟨h1, g1, hmap, hps⟩ := hI
    simp only [bind, Option.bind] at hg
    split at hg
    · cases hg
    rename_i r hr
    obtain ⟨x', st1, out1⟩ := r
    simp only [pure, Option.some.injEq] at hg
    subst hg
    have hok := materialize_spec (cfg := cfg) (allowed := allowed) (bi := bi) hE _ _ _ _ _ _ _ h1 hr
    refine ⟨hok.inv, g1.trans hok.grow, by simp [hmap], fun p hp => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · obtain ⟨e1, e2, e3⟩ := hps p hp
      refine ⟨?_, hok.grow.avail _ e2, hok.grow.known _ e3⟩
      rw [hok.grow.fix _ (known_of_avail e2), hok.grow.fix _ e3]; exact e1
    · exact ⟨by rw [hok.val, hok.grow.fix _ hok.known], hok.avail, hok.grow.known _ hok.known⟩)
    xs [] _ _ ⟨h, MGrow.refl st, rfl, fun p hp => by cases hp⟩ hm
  exact this

theorem lookup_mem {m : List (ValueId × ValueId)} {y z : ValueId} (h : m.lookup y = some z) :
    (y, z) ∈ m := by
  induction m with
  | nil => simp at h
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.lookup_cons] at h
    split at h
    · rename_i hy; simp at hy; subst hy; cases h; simp
    · exact List.mem_cons_of_mem _ (ih h)

theorem lookup_isSome' {m : List (ValueId × ValueId)} {y : ValueId} (h : y ∈ m.map Prod.fst) :
    (m.lookup y).isSome := by
  induction m with
  | nil => simp at h
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.lookup_cons]
    split
    · rfl
    · rename_i hy
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with rfl | h
      · simp at hy
      · exact ih h

/-- The renaming by a `materializeAll` result. -/
theorem rename_spec {m : List (ValueId × ValueId)} {st : SState} {xs : List ValueId}
    (hmap : m.map Prod.fst = xs)
    (hps : ∀ p ∈ m, gval ρ fr mem st p.2 = gval ρ fr mem st p.1 ∧ st.avail.contains p.2 = true ∧
      st.known p.1 = true) :
    ∀ y ∈ xs, gval ρ fr mem st (rename m y) = gval ρ fr mem st y ∧
      st.avail.contains (rename m y) = true := by
  intro y hy
  rw [← hmap] at hy
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (lookup_isSome' hy)
  have := hps _ (lookup_mem hz)
  simp only [rename, hz, Option.getD_some]
  exact ⟨this.1, this.2.1⟩

end Mat

end Opt

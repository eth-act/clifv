import FV.Backend.Proof.SpillStep4

/-!
# Completeness of `checkAlloc` (1): monotonicity and the iteration's state invariant

`checkAlloc`'s fixpoint iteration (`CheckCtx.fixpoint`) starts from `entryState` and only meets
states, so its states hold at least what any verified in-states hold (in-states whose entry state
is below `entryState`). This file proves the two per-step facts:

* **Monotonicity** (`Sub x y`: `y` holds every symbol `x` holds, `x` is no larger): a block run
  (`runBlock_mono`) and an edge (`edge_mono`) that pass the checker from `x` pass it from `y`, with
  results again in `Sub`.
* **The iteration's state invariant** (`Good K N`: size `N`, every location a duplicate-free list
  of symbols from a universe of `K + calleeSaved.length` symbols): kept by a block run, an edge and
  `AState.meet` (`runBlock_good`, `edge_good`, `good_meet`), given that every operand vreg and every
  block parameter is below `K`. It bounds the total size of a state (`wt_le`), which bounds the
  number of rounds of the iteration (`SpillCheckAllocFix.lean`).
-/

namespace E2E.CheckComplete

open Backend Backend.Proof Backend.Proof.Spill

/-! ## The order -/

/-- `x ⊑ y`: `x` is no larger than `y` and every symbol `x` puts in a location, `y` puts there
too. -/
def Sub (x y : AState) : Prop := x.size ≤ y.size ∧ ∀ l s, s ∈ x.get l → s ∈ y.get l

theorem mem_get_lt {a : AState} {l : Loc} {s : Sym} (h : s ∈ a.get l) :
    ∃ i, l.index = some i ∧ i < a.size := by
  obtain ⟨i, hi, hs⟩ := AState.mem_get h
  refine ⟨i, hi, ?_⟩
  apply Classical.byContradiction
  intro hc
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at hs
  simp at hs

theorem sub_of_le {x y : AState} (hsz : x.size ≤ y.size) (h : x.le y = true) : Sub x y :=
  ⟨hsz, fun _ _ hs => AState.mem_get_le h hs⟩

theorem sub_put {x y : AState} (h : Sub x y) (l : Loc) {xs ys : List Sym}
    (hs : ∀ s ∈ xs, s ∈ ys) : Sub (x.put l xs) (y.put l ys) := by
  refine ⟨by rw [size_put, size_put]; exact h.1, fun l' s hm => ?_⟩
  rcases AState.mem_get_put hm with ⟨rfl, hx⟩ | ⟨hne, hx⟩
  · obtain ⟨i, hi, hlt⟩ := mem_get_lt hm
    rw [size_put] at hlt
    rw [get_put_self hi (by have := h.1; omega)]
    exact hs s hx
  · rw [get_put_ne (Ne.symm hne)]
    exact h.2 l' s hx

theorem sub_map {x y : AState} (h : Sub x y) (f : List Sym → List Sym) (hf : f [] = [])
    (hm : ∀ L L' : List Sym, (∀ s ∈ L, s ∈ L') → ∀ s ∈ f L, s ∈ f L') : Sub (x.map f) (y.map f) := by
  refine ⟨by simp only [Array.size_map]; exact h.1, fun l s hs => ?_⟩
  rw [get_map _ _ hf] at hs ⊢
  exact hm _ _ (h.2 l) s hs

theorem sub_filter {x y : AState} (h : Sub x y) (p : Sym → Bool) :
    Sub (x.map (·.filter p)) (y.map (·.filter p)) :=
  sub_map h _ rfl fun _ _ hL s hs => by
    rw [List.mem_filter] at hs ⊢
    exact ⟨hL s hs.1, hs.2⟩

theorem sub_define {x y : AState} (h : Sub x y) (l : Loc) (s : Sym) :
    Sub (x.define l s) (y.define l s) :=
  sub_put (sub_filter h _) l fun _ hs => hs

theorem sub_defineAll : ∀ (ds : List (Operand × Loc)) {x y : AState}, Sub x y →
    Sub (defineAll x ds) (defineAll y ds)
  | [], _, _, h => h
  | d :: ds, _, _, h => by
    simp only [defineAll, List.foldl_cons]
    exact sub_defineAll ds (sub_define h _ _)

theorem sub_clobberAll : ∀ (clob : List Reg) {x y : AState}, Sub x y →
    Sub (clobberAll x clob) (clobberAll y clob)
  | [], _, _, h => h
  | r :: clob, _, _, h => by
    simp only [clobberAll, List.foldl_cons]
    refine sub_clobberAll clob (sub_put h _ fun s hs => ?_)
    rw [List.mem_filter] at hs ⊢
    exact ⟨h.2 _ _ hs.1, hs.2⟩

theorem sub_transferOp {x y : AState} (h : Sub x y) (i : MInst) (P : List (Operand × Loc)) :
    Sub (transferOp i P x) (transferOp i P y) := by
  have h1 := sub_defineAll (atPos P .def .late)
    (sub_clobberAll i.clobbers (sub_defineAll (atPos P .def .early) h))
  unfold transferOp
  split
  · exact h1
  · exact sub_filter h1 _

theorem sub_parCopy {x y : AState} (h : Sub x y) (ps xs : List Nat) :
    Sub (x.parCopy ps xs) (y.parCopy ps xs) := by
  refine ⟨by simp only [AState.parCopy, Array.size_map]; exact h.1, fun l s hs => ?_⟩
  rcases AState.mem_get_parCopy hs with ⟨hs1, hn⟩ | ⟨p, z, hpz, rfl, hz⟩
  · exact mem_parCopy_keep (h.2 l s hs1) (fun p hp he => hn (he ▸ List.mem_map_of_mem hp))
  · exact mem_parCopy_add hpz (h.2 l _ hz)

theorem get_meet (x y : AState) (l : Loc) :
    (x.meet y).get l = (x.get l).filter fun s => (y.get l).contains s := by
  unfold AState.get AState.meet
  split
  · rename_i i _
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_mapIdx, Array.getD_eq_getD_getElem?]
    cases x[i]? <;> simp [Array.getD_eq_getD_getElem?]
  · rfl

theorem size_meet (x y : AState) : (x.meet y).size = x.size := by simp [AState.meet]

theorem sub_meet {z x y : AState} (h1 : Sub z x) (h2 : Sub z y) : Sub z (x.meet y) := by
  refine ⟨by rw [size_meet]; exact h1.1, fun l s hs => ?_⟩
  rw [get_meet, List.mem_filter]
  exact ⟨h1.2 l s hs, List.contains_iff_mem.mpr (h2.2 l s hs)⟩

theorem sub_meet_left (x y : AState) : Sub (x.meet y) x :=
  ⟨by rw [size_meet], fun _ _ hs => (AState.mem_get_meet hs).1⟩

theorem sub_trans {x y z : AState} (h1 : Sub x y) (h2 : Sub y z) : Sub x z :=
  ⟨Nat.le_trans h1.1 h2.1, fun l s hs => h2.2 l s (h1.2 l s hs)⟩

theorem sub_refl (x : AState) : Sub x x := ⟨Nat.le_refl _, fun _ _ hs => hs⟩

/-- A meet that changes nothing is an inclusion. -/
theorem le_of_meet_eq {x y : AState} (h : x.meet y = x) : x.le y = true :=
  le_of_mem fun l s hs => by
    rw [← h] at hs
    exact (AState.mem_get_meet hs).2

/-! ## Monotonicity of the checker's steps -/

section
variable (c : CheckCtx)

theorem retCheck_mono {w : String} {i : MInst} {x y : AState} (h : retCheck w i x = .ok ())
    (hs : Sub x y) : retCheck w i y = .ok () := by
  unfold retCheck at h ⊢
  split
  · rename_i us
    exact Spill.forM_ok fun r hr => needs_of (hs.2 _ _ (needs_ok (forM_ok h r hr)))
  · rfl

theorem stepOp_mono {w : String} {i : MInst} {ops : Array Operand} {allocs : Array Loc}
    {x x' y : AState} (h : c.stepOp w i ops allocs x = .ok x') (hs : Sub x y) :
    ∃ y', c.stepOp w i ops allocs y = .ok y' ∧ Sub x' y' := by
  obtain ⟨hst, he, hl, rfl, hr⟩ := stepOp_ok h
  have h1 : (atPos (ops.zip allocs).toList .use .early).forM
      (fun p => needs w y p.2 (.vreg p.1.vreg)) = .ok () :=
    Spill.forM_ok fun p hp => needs_of (hs.2 _ _ (he p hp))
  have h2 : (atPos (ops.zip allocs).toList .use .late).forM
      (fun p => needs w (defineAll y (atPos (ops.zip allocs).toList .def .early)) p.2
        (.vreg p.1.vreg)) = .ok () :=
    Spill.forM_ok fun p hp => needs_of ((sub_defineAll _ hs).2 _ _ (hl p hp))
  have hT := sub_transferOp hs i (ops.zip allocs).toList
  have h3 := retCheck_mono hr hT
  refine ⟨_, ?_, hT⟩
  unfold CheckCtx.stepOp
  simp only [hst, h1, h2, h3, bind, Except.bind, pure, Except.pure]
  rfl

theorem runItems_mono (vb : VBlock) : ∀ (its : List RItem) (next : Nat) (x x' y : AState),
    c.runItems vb next its x = .ok x' → Sub x y →
    ∃ y', c.runItems vb next its y = .ok y' ∧ Sub x' y'
  | [], next, x, x', y, h, hs => by
    obtain ⟨hn, rfl⟩ := runItems_nil h
    refine ⟨y, ?_, hs⟩
    unfold CheckCtx.runItems
    rw [ensure_true (by simpa using hn)]
    rfl
  | .move src dst :: its, next, x, x', y, h, hs => by
    have hm := h
    unfold CheckCtx.runItems at hm
    obtain ⟨-, hm⟩ := Except.seq_ok hm
    obtain ⟨x1, hm, -⟩ := Except.bind_ok hm
    obtain ⟨hcm, -⟩ := Except.seq_ok hm
    obtain ⟨hn, hr⟩ := runItems_move h
    obtain ⟨y', hy, hs'⟩ := runItems_mono its next _ x' (y.put dst (y.get src)) hr
      (sub_put hs dst (hs.2 src))
    refine ⟨y', ?_, hs'⟩
    unfold CheckCtx.runItems
    simp only [ensure_true (show (next != vb.insts.size) = true by simpa using hn),
      CheckCtx.stepMove, hcm, bind, Except.bind, pure, Except.pure]
    exact hy
  | .op k allocs :: its, next, x, x', y, h, hs => by
    obtain ⟨hn, rfl, i, ops, x1, hi, hops, hst, hr⟩ := runItems_op h
    obtain ⟨y1, hy1, hs1⟩ := stepOp_mono c hst hs
    obtain ⟨y', hy, hs'⟩ := runItems_mono its (k + 1) x1 x' y1 hr hs1
    refine ⟨y', ?_, hs'⟩
    unfold CheckCtx.runItems
    simp only [ensure_true (show (k != vb.insts.size) = true by simpa using hn),
      ensure_true (show (k == k) = true by simp), hi, hops, hy1, bind, Except.bind]
    exact hy

theorem runBlock_mono {b : Nat} {x x' y : AState} (h : c.runBlock b x = .ok x') (hs : Sub x y) :
    ∃ y', c.runBlock b y = .ok y' ∧ Sub x' y' := by
  obtain ⟨vb, items, hvb, hit, hr⟩ := runBlock_ok h
  obtain ⟨y', hy, hs'⟩ := runItems_mono c vb items.toList 0 x x' y hr hs
  refine ⟨y', ?_, hs'⟩
  unfold CheckCtx.runBlock
  rw [hvb, hit]
  exact hy

theorem forgetOps_nil (a : AState) : forgetOps a [] = a := by
  unfold forgetOps
  simp

/-- The dead-def forgetting of an edge is a `forgetOps` of operands independent of the state. -/
theorem edgeForget_eq (b s : Nat) : ∃ os, ∀ a, c.edgeForget b s a = forgetOps a os := by
  unfold CheckCtx.edgeForget
  rcases c.vc.blocks[b]? with _ | vb
  · exact ⟨[], fun a => (forgetOps_nil a).symm⟩
  dsimp only
  rcases vb.insts.back? with _ | i
  · exact ⟨[], fun a => (forgetOps_nil a).symm⟩
  dsimp only
  rcases i.normalDead with _ | ⟨j, n⟩
  · exact ⟨[], fun a => (forgetOps_nil a).symm⟩
  dsimp only
  by_cases hj : (c.succs[b]?.bind fun x => x[j]?) = some s
  · simp only [hj, ↓reduceIte]
    rcases i.operands with _ | ops
    · exact ⟨[], fun a => (forgetOps_nil a).symm⟩
    · exact ⟨_, fun a => rfl⟩
  · simp only [hj, ↓reduceIte]
    exact ⟨[], fun a => (forgetOps_nil a).symm⟩

theorem sub_edgeForget {b s : Nat} {x y : AState} (h : Sub x y) :
    Sub (c.edgeForget b s x) (c.edgeForget b s y) := by
  obtain ⟨os, hos⟩ := edgeForget_eq c b s
  rw [hos, hos]
  exact sub_filter h _

theorem edgeCopy_mono {b s : Nat} {x x' y : AState} (h : c.edgeCopy b s x = .ok x')
    (hs : Sub x y) : ∃ y', c.edgeCopy b s y = .ok y' ∧ Sub x' y' := by
  unfold CheckCtx.edgeCopy at h ⊢
  split at h
  · rename_i vb sb hb hsb
    simp only [hb, hsb]
    obtain ⟨h1, h⟩ := Except.seq_ok h
    simp only [h1, bind, Except.bind]
    split at h
    · rename_i he
      simp only [he, ↓reduceIte]
      exact ⟨y, rfl, by rw [← Except.ok.inj h]; exact hs⟩
    · rename_i he
      simp only [he, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨ps, hps, h⟩ := Except.bind_ok h
      obtain ⟨xs, hxs, h⟩ := Except.bind_ok h
      obtain ⟨h3, h⟩ := Except.seq_ok h
      simp only [hps, hxs, h3, pure, Except.pure]
      exact ⟨_, rfl, by rw [← Except.ok.inj h]; exact sub_parCopy hs ps xs⟩
  · cases h
  · cases h

theorem edge_mono {b s : Nat} {x x' y : AState} (h : c.edge b s x = .ok x') (hs : Sub x y) :
    ∃ y', c.edge b s y = .ok y' ∧ Sub x' y' :=
  edgeCopy_mono c h (sub_edgeForget c hs)

end

/-! ## The iteration's state invariant -/

/-- The symbols the iteration can produce: vregs below `K`, entry values of callee-saved
registers. -/
def SymIn (K : Nat) : Sym → Prop
  | .vreg v => v < K
  | .entry r => r ∈ calleeSaved

/-- A location's content in the iteration: duplicate-free, from the universe. -/
def GoodL (K : Nat) (L : List Sym) : Prop := L.Nodup ∧ ∀ s ∈ L, SymIn K s

/-- A state of the iteration: size `N`, every location `GoodL`. -/
def Good (K N : Nat) (a : AState) : Prop := a.size = N ∧ ∀ l, GoodL K (a.get l)

theorem goodL_filter {K : Nat} {L : List Sym} (h : GoodL K L) (p : Sym → Bool) :
    GoodL K (L.filter p) :=
  ⟨h.1.filter p, fun s hs => h.2 s (List.mem_filter.mp hs).1⟩

theorem get_put_cases (a : AState) (l l' : Loc) (xs : List Sym) :
    (a.put l xs).get l' = xs ∨ (a.put l xs).get l' = a.get l' := by
  by_cases hl : l = l'
  · subst hl
    cases hi : l.index with
    | none => right; simp [AState.put, hi]
    | some i =>
      by_cases hlt : i < a.size
      · left; exact get_put_self hi hlt xs
      · right
        have : a.setIfInBounds i xs = a := by simp [Array.setIfInBounds, hlt]
        simp [AState.put, hi, this]
  · right; exact get_put_ne hl xs

theorem good_put {K N : Nat} {a : AState} (h : Good K N a) (l : Loc) {xs : List Sym}
    (hx : GoodL K xs) : Good K N (a.put l xs) := by
  refine ⟨by rw [size_put]; exact h.1, fun l' => ?_⟩
  rcases get_put_cases a l l' xs with e | e <;> rw [e]
  · exact hx
  · exact h.2 l'

theorem good_map {K N : Nat} {a : AState} (h : Good K N a) (f : List Sym → List Sym)
    (hf : f [] = []) (hg : ∀ L, GoodL K L → GoodL K (f L)) : Good K N (a.map f) :=
  ⟨by simp only [Array.size_map]; exact h.1, fun l => by rw [get_map _ _ hf]; exact hg _ (h.2 l)⟩

theorem good_filter {K N : Nat} {a : AState} (h : Good K N a) (p : Sym → Bool) :
    Good K N (a.map (·.filter p)) :=
  good_map h _ rfl fun _ hL => goodL_filter hL p

theorem good_define {K N : Nat} {a : AState} (h : Good K N a) (l : Loc) {s : Sym}
    (hs : SymIn K s) : Good K N (a.define l s) :=
  good_put (good_filter h _) l ⟨List.nodup_singleton s, fun t ht => by
    rw [List.mem_singleton.mp ht]; exact hs⟩

theorem good_defineAll {K N : Nat} : ∀ (ds : List (Operand × Loc)) {a : AState}, Good K N a →
    (∀ d ∈ ds, d.1.vreg < K) → Good K N (defineAll a ds)
  | [], _, h, _ => h
  | d :: ds, _, h, hd => by
    simp only [defineAll, List.foldl_cons]
    exact good_defineAll ds (good_define h _ (hd d List.mem_cons_self))
      fun d' hd' => hd d' (List.mem_cons_of_mem _ hd')

theorem good_clobberAll {K N : Nat} : ∀ (clob : List Reg) {a : AState}, Good K N a →
    Good K N (clobberAll a clob)
  | [], _, h => h
  | r :: clob, a, h => by
    simp only [clobberAll, List.foldl_cons]
    exact good_clobberAll clob (good_put h _ (goodL_filter (h.2 _) _))

theorem good_transferOp {K N : Nat} {a : AState} (h : Good K N a) (i : MInst)
    (P : List (Operand × Loc)) (hP : ∀ d ∈ P, d.1.vreg < K) : Good K N (transferOp i P a) := by
  have hpos : ∀ p, ∀ d ∈ atPos P .def p, d.1.vreg < K := fun p d hd => hP d (mem_atPos.mp hd).1
  have h1 := good_defineAll (atPos P .def .late)
    (good_clobberAll i.clobbers (good_defineAll (atPos P .def .early) h (hpos _))) (hpos _)
  unfold transferOp
  split
  · exact h1
  · exact good_filter h1 _

/-- The vregs a parallel copy adds to a location are distinct parameters. -/
theorem adds_facts (L : List Sym) : ∀ (ps xs : List Nat), ps.Nodup →
    (((ps.zip xs).filterMap fun (p, x) =>
      if L.contains (Sym.vreg x) then some (Sym.vreg p) else none)).Nodup ∧
    ∀ s ∈ ((ps.zip xs).filterMap fun (p, x) =>
      if L.contains (Sym.vreg x) then some (Sym.vreg p) else none), ∃ p ∈ ps, s = .vreg p
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | p :: ps, x :: xs, hn => by
    rw [List.nodup_cons] at hn
    obtain ⟨ih1, ih2⟩ := adds_facts L ps xs hn.2
    rw [List.zip_cons_cons, List.filterMap_cons]
    have hrest : ∀ s ∈ ((ps.zip xs).filterMap fun (p, x) =>
        if L.contains (Sym.vreg x) then some (Sym.vreg p) else none), ∃ q ∈ p :: ps, s = .vreg q :=
      fun s hs => by
        obtain ⟨q, hq, e⟩ := ih2 s hs
        exact ⟨q, List.mem_cons_of_mem _ hq, e⟩
    dsimp only
    split
    · refine ⟨List.nodup_cons.mpr ⟨fun hm => ?_, ih1⟩, fun s hs => ?_⟩
      · obtain ⟨q, hq, e⟩ := ih2 _ hm
        cases e
        exact hn.1 hq
      · rcases List.mem_cons.mp hs with rfl | hs
        · exact ⟨p, List.mem_cons_self, rfl⟩
        · exact hrest s hs
    · exact ⟨ih1, hrest⟩

theorem good_parCopy {K N : Nat} {a : AState} (h : Good K N a) {ps xs : List Nat}
    (hn : ps.Nodup) (hK : ∀ p ∈ ps, p < K) : Good K N (a.parCopy ps xs) := by
  unfold AState.parCopy
  refine good_map h _ (by simp) fun L hL => ?_
  obtain ⟨hA1, hA2⟩ := adds_facts L ps xs hn
  have hk := goodL_filter hL fun s => !(ps.map Sym.vreg).contains s
  refine ⟨?_, fun s hs => ?_⟩
  · refine List.nodup_append.mpr ⟨hk.1, hA1.filter _, fun s hs t ht e => ?_⟩
    subst e
    have := (List.mem_filter.mp ht).2
    simp only [Bool.not_eq_true', List.contains_eq_false] at this
    -- `this : s ∉ kept`
    exact (by simpa using this : s ∉ _) hs
  · rcases List.mem_append.mp hs with hs | hs
    · exact hk.2 s hs
    · obtain ⟨p, hp, rfl⟩ := hA2 s (List.mem_filter.mp hs).1
      exact hK p hp

theorem good_meet {K N : Nat} {x : AState} (h : Good K N x) (y : AState) : Good K N (x.meet y) :=
  ⟨by rw [size_meet]; exact h.1, fun l => by rw [get_meet]; exact goodL_filter (h.2 l) _⟩

/-! ## Runs keep the invariant -/

/-- Every operand of every instruction of `vb` is below `K`. -/
def OpsBelow (K : Nat) (vb : VBlock) : Prop :=
  ∀ i ∈ vb.insts.toList, ∀ ops, i.operands = .ok ops → ∀ o ∈ ops.toList, o.vreg < K

section
variable (c : CheckCtx)

theorem runItems_good {K N : Nat} (vb : VBlock) (hK : OpsBelow K vb) :
    ∀ (its : List RItem) (next : Nat) (y y' : AState),
    c.runItems vb next its y = .ok y' → Good K N y → Good K N y'
  | [], _, _, _, h, hg => by
    obtain ⟨-, rfl⟩ := runItems_nil h
    exact hg
  | .move src dst :: its, next, y, y', h, hg => by
    obtain ⟨-, hr⟩ := runItems_move h
    exact runItems_good vb hK its next _ y' hr (good_put hg dst (hg.2 src))
  | .op k allocs :: its, _, y, y', h, hg => by
    obtain ⟨-, rfl, i, ops, y1, hi, hops, hst, hr⟩ := runItems_op h
    obtain ⟨-, -, -, rfl, -⟩ := stepOp_ok hst
    refine runItems_good vb hK its (k + 1) _ y' hr (good_transferOp hg i _ fun d hd => ?_)
    rw [Array.toList_zip] at hd
    exact hK i (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hi)) ops hops d.1
      (List.of_mem_zip hd).1

theorem runBlock_good {K N : Nat} {b : Nat} {y y' : AState} (h : c.runBlock b y = .ok y')
    (hK : ∀ vb, c.vc.blocks[b]? = some vb → OpsBelow K vb) (hg : Good K N y) : Good K N y' := by
  obtain ⟨vb, items, hvb, -, hr⟩ := runBlock_ok h
  exact runItems_good c vb (hK vb hvb) items.toList 0 y y' hr hg

theorem mapM_vregNum_mem : ∀ {rs : List Reg} {ns : List Nat}, rs.mapM vregNum = .ok ns →
    ∀ n ∈ ns, ∃ r ∈ rs, vregNum r = .ok n
  | [], ns, h, n, hn => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; cases hn
  | r :: rs, ns, h, n, hn => by
    rw [List.mapM_cons] at h
    obtain ⟨m, hm, h⟩ := Except.bind_ok h
    obtain ⟨ms, hms, h⟩ := Except.bind_ok h
    have e := Except.ok.inj h
    subst e
    rcases List.mem_cons.mp hn with rfl | hn
    · exact ⟨r, List.mem_cons_self, hm⟩
    · obtain ⟨r', hr', e⟩ := mapM_vregNum_mem hms n hn
      exact ⟨r', List.mem_cons_of_mem _ hr', e⟩

/-- Every parameter of block `s` that is a vreg is below `K`. -/
def ParamsBelow (K : Nat) (sb : VBlock) : Prop := ∀ r ∈ sb.params.toList, ∀ n, vregNum r = .ok n → n < K

theorem edge_good {K N : Nat} {b s : Nat} {y y' : AState} (h : c.edge b s y = .ok y')
    (hK : ∀ sb, c.vc.blocks[s]? = some sb → ParamsBelow K sb) (hg : Good K N y) :
    Good K N y' := by
  obtain ⟨os, hos⟩ := edgeForget_eq c b s
  have hg1 : Good K N (c.edgeForget b s y) := by rw [hos]; exact good_filter hg _
  unfold CheckCtx.edge CheckCtx.edgeCopy at h
  generalize c.edgeForget b s y = z at h hg1
  split at h
  · rename_i vb sb hb hsb
    obtain ⟨-, h⟩ := Except.seq_ok h
    split at h
    · rw [← Except.ok.inj h]; exact hg1
    · obtain ⟨ps, hps, h⟩ := Except.bind_ok h
      obtain ⟨xs, -, h⟩ := Except.bind_ok h
      obtain ⟨h3, h⟩ := Except.seq_ok h
      rw [← Except.ok.inj h]
      refine good_parCopy hg1 (by simpa using ensure_ok h3) fun p hp => ?_
      obtain ⟨r, hr, e⟩ := mapM_vregNum_mem hps p hp
      exact hK sb hsb r hr p e
  · cases h
  · cases h

end

/-! ## The size of a state -/

/-- The total number of symbols of a state. -/
def wt (a : AState) : Nat := (a.toList.map List.length).sum

/-- The universe of symbols. -/
def univ (K : Nat) : List Sym := (List.range K).map Sym.vreg ++ calleeSaved.map Sym.entry

theorem length_univ (K : Nat) : (univ K).length = K + calleeSaved.length := by
  simp [univ]

theorem mem_univ {K : Nat} {s : Sym} (h : SymIn K s) : s ∈ univ K := by
  cases s with
  | vreg v => exact List.mem_append_left _ (List.mem_map.mpr ⟨v, List.mem_range.mpr h, rfl⟩)
  | entry r => exact List.mem_append_right _ (List.mem_map.mpr ⟨r, h, rfl⟩)

theorem length_le_of_goodL {K : Nat} {L : List Sym} (h : GoodL K L) :
    L.length ≤ K + calleeSaved.length := by
  rw [← length_univ K]
  exact h.1.length_le_of_subset fun s hs => mem_univ (h.2 s hs)

theorem sum_le_mul : ∀ (L : List (List Sym)) (m : Nat), (∀ x ∈ L, x.length ≤ m) →
    (L.map List.length).sum ≤ L.length * m
  | [], _, _ => by simp
  | x :: L, m, h => by
    have := sum_le_mul L m fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hx := h x List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- **The size bound**: a state of the iteration has at most `N * (K + |calleeSaved|)` symbols. -/
theorem wt_le {K N : Nat} {a : AState} (h : Good K N a) : wt a ≤ N * (K + calleeSaved.length) := by
  unfold wt
  rw [← h.1, ← Array.length_toList]
  refine sum_le_mul _ _ fun x hx => ?_
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hx
  have : a.get (ofIndex i) = x := by
    rw [Array.length_toList] at hi
    simp [AState.get, index_ofIndex, Array.getD_eq_getD_getElem?, hi, ← e]
  rw [← this]
  exact length_le_of_goodL (h.2 _)

/-- Filtering every location never adds symbols, and removes one if it changes the state. -/
theorem wt_mapIdx_filter : ∀ (L : List (List Sym)) (p : Nat → Sym → Bool),
    ((L.mapIdx fun i s => s.filter (p i)).map List.length).sum ≤ (L.map List.length).sum ∧
    ((L.mapIdx fun i s => s.filter (p i)) ≠ L →
      ((L.mapIdx fun i s => s.filter (p i)).map List.length).sum < (L.map List.length).sum)
  | [], _ => by simp
  | x :: L, p => by
    obtain ⟨ih1, ih2⟩ := wt_mapIdx_filter L fun i => p (i + 1)
    rw [List.mapIdx_cons]
    simp only [List.map_cons, List.sum_cons]
    have hx := List.length_filter_le (p 0) x
    refine ⟨by omega, fun hne => ?_⟩
    by_cases hx' : x.filter (p 0) = x
    · have hL : (L.mapIdx fun i s => s.filter (p (i + 1))) ≠ L := by
        intro e; apply hne; rw [hx', e]
      have := ih2 hL
      omega
    · have : (x.filter (p 0)).length < x.length := by
        apply Classical.byContradiction
        intro hc
        exact hx' (List.filter_eq_self.mpr (List.filter_length_eq_length.mp (by omega)))
      omega

theorem wt_meet (x y : AState) : wt (x.meet y) ≤ wt x ∧ (x.meet y ≠ x → wt (x.meet y) < wt x) := by
  unfold wt AState.meet
  rw [Array.toList_mapIdx]
  obtain ⟨h1, h2⟩ := wt_mapIdx_filter x.toList fun i s => (y.getD i []).contains s
  refine ⟨h1, fun hne => h2 fun e => hne ?_⟩
  apply Array.ext'
  rw [Array.toList_mapIdx]
  exact e

end E2E.CheckComplete

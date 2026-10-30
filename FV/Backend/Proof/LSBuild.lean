import FV.Backend.Proof.LSFn
import FV.Backend.Proof.SpillLocal

/-!
# The Lean allocator's builder: structure of its output (V4b-3, #275)

`buildFacts`: `Ctx.build` succeeds with `rf` when every block's pieces (`Ctx.blockParts`) do; block
`b` of `rf` is the saves (block 0) followed by `blockItems` of its pieces with the restores of
`rf.saved`; the saved registers are callee-saved, distinct, and include every callee-saved
register some item mentions; every stack slot an item mentions is below `rf.spillSlots`.
`partsFacts`: the pieces of a block are its entry moves, then per instruction its argument
copies (the last one's only) and `Ctx.inst`. `termMoves_facts`: the entry moves are moves out of
fixed result registers of the only predecessor's terminator into the results' locations.
-/

namespace Backend.Proof.LS

open Backend Backend.LinearScan Backend.Proof Backend.Proof.Spill
open Backend.LinearScan.Ctx (Parts blockItems)

/-- The saves of the registers `L` (start of the entry block). -/
def savesOf (L : List Reg) : List RItem := L.map fun r => .move (.reg r) (.save r)

/-- The restores of the registers `L` (before a `Rets`). -/
def restoresOf (L : List Reg) : List RItem := L.map fun r => .move (.save r) (.reg r)

/-- What `Ctx.build c = .ok rf` establishes. -/
structure BuildFacts (vc : VCode) (c : LinearScan.Ctx) (rf : RFunc) : Prop where
  size : rf.blocks.size = vc.blocks.size
  block : ∀ (b : Nat) (vb : VBlock), vc.blocks[b]? = some vb → ∃ p, c.blockParts b = .ok p ∧
    rf.blocks[b]? = some (((if b = 0 then savesOf rf.saved else []) ++
      blockItems vb p (restoresOf rf.saved)).toArray)
  saved : ∀ r ∈ rf.saved, r ∈ calleeSaved
  savedNodup : rf.saved.Nodup
  notSaved : ∀ r ∈ calleeSaved, r ∉ rf.saved → ∀ (b : Nat) (vb : VBlock) (p : Parts),
    vc.blocks[b]? = some vb → c.blockParts b = .ok p → ∀ it ∈ blockItems vb p [], Loc.reg r ∉ it.locs
  slots : ∀ (b : Nat) (vb : VBlock) (p : Parts), vc.blocks[b]? = some vb → c.blockParts b = .ok p →
    ∀ it ∈ blockItems vb p [], ∀ l ∈ it.locs, ∀ (s : Nat) (cl : RegClass), l = .stack s cl →
      s < rf.spillSlots

private theorem foldl_le {α : Type} (f : Nat → α → Nat) (hf : ∀ m a, m ≤ f m a) :
    ∀ (l : List α) (m : Nat), m ≤ l.foldl f m
  | [], _ => Nat.le_refl _
  | a :: l, m => Nat.le_trans (hf m a) (foldl_le f hf l _)

/-- A bound every step meets for an element of the list holds for the fold. -/
private theorem le_foldl {α : Type} (f : Nat → α → Nat) (hf : ∀ m a, m ≤ f m a) {k : Nat}
    {a : α} (ha : ∀ m, k ≤ f m a) : ∀ (l : List α) (m : Nat), a ∈ l → k ≤ l.foldl f m
  | a' :: l, m, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (ha m) (foldl_le f hf l _)
    · exact le_foldl f hf ha l _ h

theorem buildFacts {vc : VCode} {c : LinearScan.Ctx} {rf : RFunc} (hf : FnOk vc c.fn)
    (h : c.build = .ok rf) : BuildFacts vc c rf := by
  unfold LinearScan.Ctx.build at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i parts hparts
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨hlen, hel⟩ := Prep.lmapM_ok hparts
  rw [List.length_range, hf.nblocks] at hlen
  have hpart : ∀ b vb, vc.blocks[b]? = some vb →
      ∃ p, c.blockParts b = .ok p ∧ parts[b]? = some p := by
    intro b vb hb
    have hb' : b < vc.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
    exact hel b b (List.getElem?_range (by rw [hf.nblocks]; exact hb'))
  have hzip : ∀ b vb p, vc.blocks[b]? = some vb → c.blockParts b = .ok p →
      (parts.zip c.fn.vc.blocks.toList)[b]? = some (p, vb) := by
    intro b vb p hb hp
    obtain ⟨p', hp', hpb⟩ := hpart b vb hb
    rw [hp] at hp'
    cases hp'
    rw [List.getElem?_zip_eq_some]
    exact ⟨hpb, by rw [hf.vc_eq]; simpa using hb⟩
  have hitems : ∀ b vb p, vc.blocks[b]? = some vb → c.blockParts b = .ok p →
      ∀ it ∈ blockItems vb p [], it ∈ (parts.zip c.fn.vc.blocks.toList).flatMap
        fun (x : Parts × VBlock) => blockItems x.2 x.1 [] := fun b vb p hb hp it hit =>
    List.mem_flatMap.mpr ⟨(p, vb), List.mem_of_getElem? (hzip b vb p hb hp), hit⟩
  refine ⟨?_, fun b vb hb => ?_, fun r hr => (List.mem_filter.mp hr).1,
    List.Pairwise.filter _ (by decide), fun r hr hns b vb p hb hp it hit hloc => ?_,
    fun b vb p hb hp it hit l hl s cl hls => ?_⟩
  · simp [List.length_zip, hlen, hf.vc_eq]
  · obtain ⟨p, hp, -⟩ := hpart b vb hb
    refine ⟨p, hp, ?_⟩
    rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_zipIdx, hzip b vb p hb hp]
    simp [savesOf, restoresOf]
  · apply hns
    refine List.mem_filter.mpr ⟨hr, ?_⟩
    simp only [Bool.or_eq_true, List.any_eq_true, List.contains_iff_mem]
    exact Or.inr ⟨it, hitems b vb p hb hp it hit, hloc⟩
  · subst hls
    apply Nat.lt_of_succ_le
    refine le_foldl _ (fun m a => foldl_le _ ?_ _ _) (fun m => le_foldl _ ?_ ?_ _ m hl) _ _
      (hitems b vb p hb hp it hit)
    · intro m l
      cases l <;> simp [Nat.le_max_left]
    · intro m l
      cases l <;> simp [Nat.le_max_left]
    · intro m
      exact Nat.le_max_right _ _

/-- The block's items with restores are those without, plus restores before a `Rets`. -/
theorem mem_blockItems {vb : VBlock} {p : Parts} {L : List Reg} {it : RItem}
    (h : it ∈ blockItems vb p (restoresOf L)) : it ∈ blockItems vb p [] ∨ it ∈ restoresOf L := by
  simp only [blockItems, List.mem_append, List.mem_flatMap] at h ⊢
  rcases h with h | ⟨⟨⟨args, io⟩, k⟩, hx, h⟩
  · exact Or.inl (Or.inl h)
  · simp only [List.mem_ite_nil_right] at h
    rcases h with (((h | h) | h) | h) | h
    · exact Or.inl (Or.inr ⟨_, hx, by simp [h]⟩)
    · exact Or.inl (Or.inr ⟨_, hx, by simp [h]⟩)
    · exact Or.inr h.2
    · exact Or.inl (Or.inr ⟨_, hx, by simp [h]⟩)
    · exact Or.inl (Or.inr ⟨_, hx, by simp [h]⟩)

/-- What `Ctx.blockParts c b = .ok p` establishes. -/
structure PartsFacts (c : LinearScan.Ctx) (b : Nat) (p : Parts) : Prop where
  entry : c.entryMoves b = .ok p.entry
  len : p.insts.length = c.fn.start.getD (b + 1) 0 - c.fn.start.getD b 0
  inst : ∀ (k : Nat) (args : List RItem) (io : IOut), p.insts[k]? = some (args, io) →
    c.inst (c.fn.start.getD b 0 + k) = .ok io ∧
    (c.fn.start.getD b 0 + k + 1 = c.fn.start.getD (b + 1) 0 →
      c.argMoves b (c.fn.start.getD b 0 + k) = .ok args) ∧
    (c.fn.start.getD b 0 + k + 1 ≠ c.fn.start.getD (b + 1) 0 → args = [])

theorem partsFacts {c : LinearScan.Ctx} {b : Nat} {p : Parts} (h : c.blockParts b = .ok p) :
    PartsFacts c b p := by
  simp only [LinearScan.Ctx.blockParts, bind, Except.bind] at h
  split at h
  · cases h
  rename_i entry he
  split at h
  · cases h
  rename_i insts hi
  cases h
  obtain ⟨hlen, hel⟩ := Prep.lmapM_ok hi
  simp only [List.length_range] at hlen
  refine ⟨he, hlen, fun k args io hk => ?_⟩
  dsimp only at hk ⊢
  have hk' : k < c.fn.start.getD (b + 1) 0 - c.fn.start.getD b 0 := by
    have := (List.getElem?_eq_some_iff.mp hk).1
    omega
  obtain ⟨y, hy, hy'⟩ := hel k k (List.getElem?_range hk')
  rw [hk] at hy'
  cases hy'
  by_cases hq : c.fn.start.getD b 0 + k + 1 = c.fn.start.getD (b + 1) 0
  · simp only [hq, beq_self_eq_true, ite_true] at hy
    cases ha : c.argMoves b (c.fn.start.getD b 0 + k) <;>
      cases hio : c.inst (c.fn.start.getD b 0 + k) <;>
      simp_all [pure, Except.pure]
  · simp only [hq, beq_iff_eq, ite_false] at hy
    cases hio : c.inst (c.fn.start.getD b 0 + k) <;> simp_all [pure, Except.pure]

/-- The items of a block from instruction `k` on. -/
def itemsFrom (vb : VBlock) (p : Parts) (L : List RItem) (k : Nat) : List RItem :=
  ((p.insts.drop k).zipIdx k).flatMap fun ((args, io), k) =>
    args ++ io.pre.map LinearScan.mv ++ (if vb.insts[k]? matches some (.rets _) then L else []) ++
      [.op k io.allocs] ++ io.post.map LinearScan.mv

theorem blockItems_eq (vb : VBlock) (p : Parts) (L : List RItem) :
    blockItems vb p L = p.entry ++ itemsFrom vb p L 0 := by
  unfold blockItems itemsFrom
  simp only [List.drop_zero]
  rfl

theorem itemsFrom_succ {vb : VBlock} {p : Parts} {L : List RItem} {k : Nat}
    {args : List RItem} {io : IOut} (h : p.insts[k]? = some (args, io)) :
    itemsFrom vb p L k = (args ++ io.pre.map LinearScan.mv ++
      (if vb.insts[k]? matches some (.rets _) then L else []) ++ [.op k io.allocs] ++
        io.post.map LinearScan.mv) ++ itemsFrom vb p L (k + 1) := by
  have hk : k < p.insts.length := (List.getElem?_eq_some_iff.mp h).1
  have hd : p.insts.drop k = (args, io) :: p.insts.drop (k + 1) := by
    rw [List.drop_eq_getElem_cons hk, (List.getElem?_eq_some_iff.mp h).2]
  unfold itemsFrom
  rw [hd, List.zipIdx_cons, List.flatMap_cons]

theorem itemsFrom_end {vb : VBlock} {p : Parts} {L : List RItem} {k : Nat}
    (h : p.insts.length ≤ k) : itemsFrom vb p L k = [] := by
  unfold itemsFrom
  rw [List.drop_of_length_le h]
  rfl

/-- Items from instruction `k + 1` on are items from `k` on. -/
theorem itemsFrom_mono {vb : VBlock} {p : Parts} {L : List RItem} {k : Nat} {it : RItem}
    (h : it ∈ itemsFrom vb p L (k + 1)) : it ∈ itemsFrom vb p L k := by
  cases hk : p.insts[k]? with
  | none =>
    rw [itemsFrom_end (by simp at hk; omega)] at h
    exact absurd h List.not_mem_nil
  | some x =>
    obtain ⟨args, io⟩ := x
    rw [itemsFrom_succ hk]
    exact List.mem_append_right _ h

theorem itemsFrom_zero {vb : VBlock} {p : Parts} {L : List RItem} :
    ∀ {k : Nat} {it : RItem}, it ∈ itemsFrom vb p L k → it ∈ itemsFrom vb p L 0
  | 0, _, h => h
  | _ + 1, _, h => itemsFrom_zero (itemsFrom_mono h)


/-- The items of instruction `k`'s piece are items of its block. -/
theorem piece_mem {vb : VBlock} {p : Parts} {L : List RItem} {k : Nat} {args : List RItem}
    {io : IOut} (h : p.insts[k]? = some (args, io)) :
    (∀ it ∈ args, it ∈ blockItems vb p L) ∧ (∀ m ∈ io.pre, LinearScan.mv m ∈ blockItems vb p L) ∧
      RItem.op k io.allocs ∈ blockItems vb p L ∧ (∀ m ∈ io.post, LinearScan.mv m ∈ blockItems vb p L) := by
  have hm : ∀ it, it ∈ args ++ io.pre.map LinearScan.mv ++
      (if vb.insts[k]? matches some (.rets _) then L else []) ++ [.op k io.allocs] ++
        io.post.map LinearScan.mv → it ∈ blockItems vb p L := by
    intro it hit
    rw [blockItems_eq]
    refine List.mem_append_right _ (itemsFrom_zero (k := k) ?_)
    rw [itemsFrom_succ h]
    exact List.mem_append_left _ hit
  refine ⟨fun it hit => hm _ ?_, fun m hm' => hm _ ?_, hm _ ?_, fun m hm' => hm _ ?_⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ hit)))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_map_of_mem hm'))))
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
  · exact List.mem_append_right _ (List.mem_map_of_mem hm')

theorem entry_mem {vb : VBlock} {p : Parts} {L : List RItem} : ∀ it ∈ p.entry,
    it ∈ blockItems vb p L := by
  intro it h
  rw [blockItems_eq]
  exact List.mem_append_left _ h

/-- The kept defs of `b`'s terminator live on the edge to `s` (`termEdgeDefs`). -/
def edgeDefs (vc : VCode) (succs : Array (Array Nat)) (b s : Nat) : List Operand :=
  match vc.blocks[b]?, succs[b]? with
  | some vb, some ss => match ss.toList.idxOf? s with
    | some j => (termEdgeDefs vb j).map (·.1)
    | none => []
  | _, _ => []

/-- One step of `Ctx.termMoves`'s fold. -/
private def termStep (c : LinearScan.Ctx) (s g0 : Nat) (ms : List (Loc × Loc)) (o : Operand) :
    Except String (List (Loc × Loc)) :=
  if !c.pl.cov o.vreg (pos g0 0) then pure ms else
  match o.con with
  | .fixed p =>
    if c.loc o.vreg != .reg p then
      if (c.fn.preds.getD s #[]).size != 1 then throw "terminator results into a join block"
      else pure ((.reg p, c.loc o.vreg) :: ms)
    else pure ms
  | _ => if (c.pl.regOf o.vreg).isNone then throw "spilled non-fixed terminator def" else pure ms

private theorem termMoves_eq (c : LinearScan.Ctx) (s g0 b : Nat) :
    c.termMoves s g0 b = (do
      let ms ← (edgeDefs c.fn.vc c.fn.succs b s).foldlM (termStep c s g0) []
      pure ms.reverse) := rfl

/-- A monotone `foldlM`: its result contains the start, keeps what each step produced, and every
new element comes from a step that added it. -/
private theorem foldlM_ok {α γ ε : Type} {F : List γ → α → Except ε (List γ)}
    (hF : ∀ acc a r, F acc a = .ok r → ∀ x ∈ acc, x ∈ r) :
    ∀ (l : List α) (acc r : List γ), l.foldlM F acc = .ok r →
      (∀ x ∈ acc, x ∈ r) ∧
      (∀ a ∈ l, ∃ acc' r', F acc' a = .ok r' ∧ ∀ x ∈ r', x ∈ r) ∧
      (∀ x ∈ r, x ∈ acc ∨ ∃ a ∈ l, ∃ acc' r', F acc' a = .ok r' ∧ x ∈ r' ∧ x ∉ acc')
  | [], acc, r, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨fun x hx => hx, fun a ha => absurd ha List.not_mem_nil, fun x hx => Or.inl hx⟩
  | a :: l, acc, r, h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    rename_i acc1 h1
    obtain ⟨i1, i2, i3⟩ := foldlM_ok hF l acc1 r h
    refine ⟨fun x hx => i1 x (hF _ _ _ h1 x hx), fun a' ha' => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.mp ha' with rfl | ha'
      · exact ⟨acc, acc1, h1, i1⟩
      · exact i2 a' ha'
    · rcases i3 x hx with hx1 | ⟨a', ha', rest⟩
      · by_cases hxa : x ∈ acc
        · exact Or.inl hxa
        · exact Or.inr ⟨a, List.mem_cons_self, acc, acc1, h1, hx1, hxa⟩
      · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', rest⟩

private theorem termStep_ok {c : LinearScan.Ctx} {s g0 : Nat} {acc r : List (Loc × Loc)}
    {o : Operand} (h : termStep c s g0 acc o = .ok r) :
    (∀ x ∈ acc, x ∈ r) ∧
    (∀ x ∈ r, x ∉ acc → ∃ p, o.con = .fixed p ∧ c.pl.cov o.vreg (pos g0 0) = true ∧
      (c.fn.preds.getD s #[]).size = 1 ∧ x = (.reg p, c.loc o.vreg)) ∧
    (c.pl.cov o.vreg (pos g0 0) = true →
      (∀ p, o.con = .fixed p → c.loc o.vreg ≠ .reg p → (.reg p, c.loc o.vreg) ∈ r) ∧
      ((∀ p, o.con ≠ .fixed p) → (c.pl.regOf o.vreg).isSome)) := by
  unfold termStep at h
  cases hc : c.pl.cov o.vreg (pos g0 0)
  · simp only [hc, Bool.not_false, ite_true, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨fun x hx => hx, fun x hx hn => absurd hx hn, fun h => nomatch h⟩
  simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false] at h
  cases hcon : o.con
  case fixed p =>
    simp only [hcon] at h
    by_cases hl : c.loc o.vreg = .reg p
    · simp only [hl, bne_self_eq_false, Bool.false_eq_true, ite_false, pure, Except.pure,
        Except.ok.injEq] at h
      subst h
      refine ⟨fun x hx => hx, fun x hx hn => absurd hx hn,
        fun _ => ⟨fun p' hp' hne => ?_, fun hn => absurd rfl (hn p)⟩⟩
      cases hp'
      exact absurd hl hne
    · by_cases hs : (c.fn.preds.getD s #[]).size = 1
      · simp only [hl, hs, bne_iff_ne, ne_eq, not_false_eq_true, ite_true, Nat.reduceBNe,
          Bool.false_eq_true, ite_false, pure, Except.pure, Except.ok.injEq] at h
        subst h
        refine ⟨fun x hx => List.mem_cons_of_mem _ hx, fun x hx hn => ?_,
          fun _ => ⟨fun p' hp' _ => ?_, fun hn => absurd rfl (hn p)⟩⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨p, rfl, rfl, hs, rfl⟩
          · exact absurd hx hn
        · cases hp'
          exact List.mem_cons_self
      · simp only [hl, hs, bne_iff_ne, ne_eq, not_false_eq_true, ite_true] at h
        cases h
  all_goals
    simp only [hcon] at h
    cases hn : (c.pl.regOf o.vreg).isNone
    · simp only [hn, Bool.false_eq_true, ite_false, pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine ⟨fun x hx => hx, fun x hx hn' => absurd hx hn',
        fun _ => ⟨fun p hp => (nomatch hp), fun _ => ?_⟩⟩
      cases h' : c.pl.regOf o.vreg <;> simp_all
    · simp only [hn, ite_true] at h
      cases h

/-- What `Ctx.termMoves` computes for a predecessor `b` of `s`. -/
private theorem termMoves_facts {vc : VCode} {c : LinearScan.Ctx} (hf : FnOk vc c.fn)
    {s g0 b : Nat} {l : List (Loc × Loc)} (h : c.termMoves s g0 b = .ok l) :
    (∀ x ∈ l, ∃ o p, o ∈ edgeDefs vc c.fn.succs b s ∧ o.con = .fixed p ∧
      c.pl.cov o.vreg (pos g0 0) = true ∧ (c.fn.preds.getD s #[]).size = 1 ∧
      x = (.reg p, c.loc o.vreg)) ∧
    (∀ o ∈ edgeDefs vc c.fn.succs b s, c.pl.cov o.vreg (pos g0 0) = true →
      (∀ p, o.con = .fixed p → c.loc o.vreg ≠ .reg p → (.reg p, c.loc o.vreg) ∈ l) ∧
      ((∀ p, o.con ≠ .fixed p) → (c.pl.regOf o.vreg).isSome)) := by
  rw [termMoves_eq, hf.vc_eq] at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i ms hms
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨-, hall, hsrc⟩ := foldlM_ok (fun _ _ _ hr => (termStep_ok hr).1) _ _ _ hms
  refine ⟨fun x hx => ?_, fun o ho hcov => ?_⟩
  · rw [List.mem_reverse] at hx
    rcases hsrc x hx with hx | ⟨o, ho, acc', r', hr', hxr, hxa⟩
    · exact absurd hx List.not_mem_nil
    · obtain ⟨p, hp, hc, hs, rfl⟩ := (termStep_ok hr').2.1 x hxr hxa
      exact ⟨o, p, ho, hp, hc, hs, rfl⟩
  · obtain ⟨acc', r', hr', hsub⟩ := hall o ho
    have := (termStep_ok hr').2.2 hcov
    exact ⟨fun p hp hne => List.mem_reverse.mpr (hsub _ (this.1 p hp hne)), this.2⟩

private theorem eq_single {a : Array Nat} {b : Nat} (hs : a.size = 1) (hb : b ∈ a.toList) :
    a = #[b] := by
  rcases a with ⟨l⟩
  simp only [List.size_toArray] at hs
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hs
  simp only [List.mem_singleton] at hb
  subst hb
  rfl

/-- The entry moves of a block move fixed result registers of its only predecessor's terminator
into the results' locations; every such result live at the block's start that is not in its
register is moved; a live non-fixed result has a register. -/
theorem entryMoves_facts {vc : VCode} {c : LinearScan.Ctx} (hf : FnOk vc c.fn) {s : Nat}
    {its : List RItem} (h : c.entryMoves s = .ok its) :
    ∃ ms, its = (cleanMoves ms).map LinearScan.mv ∧
      (∀ m ∈ ms, ∃ b o p, c.fn.preds.getD s #[] = #[b] ∧ o ∈ edgeDefs vc c.fn.succs b s ∧
        o.con = .fixed p ∧ c.pl.cov o.vreg (pos (c.fn.start.getD s 0) 0) = true ∧
        m = (.reg p, c.loc o.vreg)) ∧
      (∀ b ∈ (c.fn.preds.getD s #[]).toList, ∀ o ∈ edgeDefs vc c.fn.succs b s,
        c.pl.cov o.vreg (pos (c.fn.start.getD s 0) 0) = true →
        (∀ p, o.con = .fixed p → c.loc o.vreg ≠ .reg p → (.reg p, c.loc o.vreg) ∈ ms) ∧
        ((∀ p, o.con ≠ .fixed p) → (c.pl.regOf o.vreg).isSome)) := by
  unfold LinearScan.Ctx.entryMoves at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i msl hmsl
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨hlen, hel⟩ := Prep.lmapM_ok hmsl
  refine ⟨msl.flatten, rfl, fun m hm => ?_, fun b hb o ho hcov => ?_⟩
  · obtain ⟨l, hl, hml⟩ := List.mem_flatten.mp hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
    have hi' : i < (c.fn.preds.getD s #[]).toList.length := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨l', hl', hil'⟩ := hel i _ (List.getElem?_eq_getElem hi')
    rw [hi] at hil'
    cases hil'
    obtain ⟨o, p, ho, hp, hc, hs, rfl⟩ := (termMoves_facts hf hl').1 m hml
    exact ⟨_, o, p, eq_single hs (List.getElem_mem hi'), ho, hp, hc, rfl⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    obtain ⟨l, hl, hil⟩ := hel i b hi
    have := (termMoves_facts hf hl).2 o ho hcov
    exact ⟨fun p hp hne => List.mem_flatten.mpr ⟨l, List.mem_of_getElem? hil, this.1 p hp hne⟩,
      this.2⟩

end Backend.Proof.LS

import FV.Backend.Proof.SpillStep4Inst

/-!
# The in-states of the spill allocation (V4 (a), step 4)

`inState vc succs preds D b` (`SpillInvariant.lean`'s module doc): the home of every vreg of
`D b` holds it; on entry to block 0 the callee-saved registers hold their entry values, on entry
to every other block their save slots; on entry to a block whose only predecessor ends in a
terminator with defs live on the edge (a `try_call`), the registers of those defs (`entryPairs`,
what `spillEntryStores` stores) hold them. `inState_entryOk`: the entry block's in-state is
`EntryOk`. `entryPairs_facts`: the entry stores move allocatable registers into the homes of
pairwise distinct vregs.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof

section
variable (vc : VCode) (succs preds : Array (Array Nat)) (D : Nat → Nat → Bool)

/-- The defs (with their registers) the entry stores of block `s` store when `b` is its only
predecessor. -/
def entryPairsOf (b s : Nat) : List (Operand × Loc) :=
  match vc.blocks[b]?, succs[b]? with
  | some vb, some ss =>
    match List.idxOf? s ss.toList with
    | some j => termEdgeDefs vb j
    | none => []
  | _, _ => []

/-- The defs (with their registers) the entry stores of block `s` store (`spillEntryStores`,
`entryStored`). -/
def entryPairs (s : Nat) : List (Operand × Loc) :=
  match preds[s]? with
  | some ps => if ps.size = 1 then entryPairsOf vc succs ps[0]! s else []
  | none => []

/-- The content of each location in the in-state of block `b`. -/
def inContent (b : Nat) : Loc → List Sym
  | .reg r => (if b = 0 ∧ r ∈ calleeSaved then [.entry r] else []) ++
      (((entryPairs vc succs preds b).filter fun x => x.2 == .reg r).map fun x => .vreg x.1.vreg)
  | .save r => if b ≠ 0 ∧ r ∈ calleeSaved then [.entry r] else []
  | .stack n c => ((List.range vc.classes.size).filter fun v =>
      (spillHomes vc)[(v, c)]? == some n && vc.classes[v]? == some c && D b v).map .vreg

/-- **The in-state of block `b`.** -/
def inState (b : Nat) : AState := mkState (stN vc) (inContent vc succs preds D b)

/-- The in-states of all blocks. -/
def insOf : Array (Option AState) :=
  Array.ofFn (n := vc.blocks.size) fun b => some (inState vc succs preds D b)

end

section
variable {vc : VCode} {succs preds : Array (Array Nat)} {D : Nat → Nat → Bool}

theorem insOf_get {b : Nat} (hb : b < vc.blocks.size) :
    (insOf vc succs preds D)[b]? = some (some (inState vc succs preds D b)) := by
  simp [insOf, hb]

theorem entryPairs_one {s b : Nat} (hp : preds[s]? = some #[b]) :
    entryPairs vc succs preds s = entryPairsOf vc succs b s := by
  simp [entryPairs, hp]

theorem entryPairs_ne {s : Nat} (h : ∀ b, preds[s]? ≠ some #[b]) :
    entryPairs vc succs preds s = [] := by
  unfold entryPairs
  rcases hp : preds[s]? with _ | ⟨_ | ⟨b, _ | ⟨b', l⟩⟩⟩
  · rfl
  · rfl
  · exact absurd hp (h b)
  · simp

theorem spillEntryStores_one {h : Homes} {s b : Nat} (hp : preds[s]? = some #[b]) :
    spillEntryStores h vc succs preds s =
      match vc.blocks[b]?, succs[b]? with
      | some vb, some ss =>
        match List.idxOf? s ss.toList with
        | some j => (termEdgeDefs vb j).map fun (o, l) => RItem.move l (spillHome h o.vreg o.cls)
        | none => []
      | _, _ => [] := by
  unfold spillEntryStores; rw [hp]; rfl

theorem spillEntryStores_ne {h : Homes} {s : Nat} (hn : ∀ b, preds[s]? ≠ some #[b]) :
    spillEntryStores h vc succs preds s = [] := by
  unfold spillEntryStores
  rcases hp : preds[s]? with _ | ⟨_ | ⟨b, _ | ⟨b', l⟩⟩⟩
  · rfl
  · rfl
  · exact absurd hp (hn b)
  · rfl

theorem entryStored_one {s b : Nat} (hp : preds[s]? = some #[b]) :
    entryStored vc succs preds s =
      match vc.blocks[b]?, succs[b]? with
      | some vb, some ss =>
        match List.idxOf? s ss.toList with
        | some j => (termEdgeDefs vb j).map (·.1.vreg)
        | none => []
      | _, _ => [] := by
  unfold entryStored; rw [hp]; rfl

theorem entryStored_ne {s : Nat} (hn : ∀ b, preds[s]? ≠ some #[b]) :
    entryStored vc succs preds s = [] := by
  unfold entryStored
  rcases hp : preds[s]? with _ | ⟨_ | ⟨b, _ | ⟨b', l⟩⟩⟩
  · rfl
  · rfl
  · exact absurd hp (hn b)
  · rfl

theorem spillEntryStores_eq (s : Nat) :
    spillEntryStores (spillHomes vc) vc succs preds s =
      ((entryPairs vc succs preds s).map
        fun x => (x.2, spillHome (spillHomes vc) x.1.vreg x.1.cls)).map mv := by
  by_cases hb : ∃ b, preds[s]? = some #[b]
  · obtain ⟨b, hp⟩ := hb
    rw [spillEntryStores_one hp, entryPairs_one hp]
    unfold entryPairsOf
    rcases vc.blocks[b]? with _ | vb <;> rcases succs[b]? with _ | ss <;> try rfl
    dsimp only
    rcases List.idxOf? s ss.toList with _ | j
    · rfl
    · simp only [List.map_map]; rfl
  · have hn : ∀ b, preds[s]? ≠ some #[b] := fun b h => hb ⟨b, h⟩
    rw [spillEntryStores_ne hn, entryPairs_ne hn]; rfl

theorem entryStored_eq (s : Nat) :
    entryStored vc succs preds s = (entryPairs vc succs preds s).map (·.1.vreg) := by
  by_cases hb : ∃ b, preds[s]? = some #[b]
  · obtain ⟨b, hp⟩ := hb
    rw [entryStored_one hp, entryPairs_one hp]
    unfold entryPairsOf
    rcases vc.blocks[b]? with _ | vb <;> rcases succs[b]? with _ | ss <;> try rfl
    dsimp only
    rcases List.idxOf? s ss.toList with _ | j <;> rfl
  · have hn : ∀ b, preds[s]? ≠ some #[b] := fun b h => hb ⟨b, h⟩
    rw [entryStored_ne hn, entryPairs_ne hn]; rfl

theorem entryPairs_nil {s : Nat} (h : preds[s]? = some #[]) : entryPairs vc succs preds s = [] :=
  entryPairs_ne fun b hb => by rw [h] at hb; cases hb

theorem entryPairs_spec {s : Nat} {x : Operand × Loc} (h : x ∈ entryPairs vc succs preds s) :
    ∃ b vb ss j, preds[s]? = some #[b] ∧ vc.blocks[b]? = some vb ∧ succs[b]? = some ss ∧
      List.idxOf? s ss.toList = some j ∧ x ∈ termEdgeDefs vb j := by
  by_cases hb : ∃ b, preds[s]? = some #[b]
  · obtain ⟨b, hp⟩ := hb
    rw [entryPairs_one hp] at h
    unfold entryPairsOf at h
    revert h
    rcases hvb : vc.blocks[b]? with _ | vb <;> rcases hss : succs[b]? with _ | ss <;>
      intro h <;> try cases h
    dsimp only at h
    revert h
    rcases hj : List.idxOf? s ss.toList with _ | j <;> intro h
    · cases h
    · exact ⟨b, vb, ss, j, hp, hvb, hss, hj, h⟩
  · rw [entryPairs_ne fun b h => hb ⟨b, h⟩] at h; cases h

theorem termEdgeDefs_spec {vb : VBlock} {j : Nat} {x : Operand × Loc} (h : x ∈ termEdgeDefs vb j) :
    ∃ T ops, vb.insts.back? = some T ∧ T.isTerminator = true ∧ T.operands = .ok ops ∧
      x ∈ keptPairs T (ops.zip (spillLocs ops T.clobbers)).toList ∧
      ∀ jn n, T.normalDead = some (jn, n) → j = jn →
        x ∈ (keptPairs T (ops.zip (spillLocs ops T.clobbers)).toList).take n := by
  unfold termEdgeDefs at h
  split at h
  · cases h
  rename_i T hT
  split at h
  · cases h
  rename_i ht
  split at h
  · cases h
  rename_i ops hops
  refine ⟨T, ops, hT, by simpa using ht, hops, ?_, ?_⟩
  · split at h
    · split at h
      · exact List.mem_of_mem_take h
      · exact h
    · exact h
  · intro jn n hnd hj
    split at h
    · rename_i jn' n' hnd'
      rw [hnd] at hnd'
      cases hnd'
      simp only [hj, BEq.rfl, ↓reduceIte] at h
      exact h
    · rename_i hnd'
      rw [hnd] at hnd'
      cases hnd'

/-! ## Membership in the in-states -/

theorem inReg_mem {b : Nat} {r : Reg} {x : Sym} (h : x ∈ inContent vc succs preds D b (.reg r)) :
    (b = 0 ∧ r ∈ calleeSaved ∧ x = .entry r) ∨
      ∃ y ∈ entryPairs vc succs preds b, y.2 = .reg r ∧ x = .vreg y.1.vreg := by
  simp only [inContent, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq] at h
  rcases h with h | ⟨y, ⟨hy, he⟩, rfl⟩
  · by_cases hc : b = 0 ∧ r ∈ calleeSaved
    · simp only [hc, and_self, ↓reduceIte] at h
      exact .inl ⟨hc.1, hc.2, List.mem_singleton.mp h⟩
    · simp only [hc, ↓reduceIte] at h; cases h
  · exact .inr ⟨y, hy, he, rfl⟩

theorem inReg_entry {b : Nat} {r : Reg} (hb : b = 0) (hr : r ∈ calleeSaved) :
    Sym.entry r ∈ inContent vc succs preds D b (.reg r) := by
  simp [inContent, hb, hr]

theorem inReg_pair {b : Nat} {r : Reg} {y : Operand × Loc} (hy : y ∈ entryPairs vc succs preds b)
    (he : y.2 = .reg r) : Sym.vreg y.1.vreg ∈ inContent vc succs preds D b (.reg r) := by
  simp only [inContent, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq]
  exact .inr ⟨y, ⟨hy, he⟩, rfl⟩

theorem inSave_mem {b : Nat} {r : Reg} {x : Sym} (h : x ∈ inContent vc succs preds D b (.save r)) :
    b ≠ 0 ∧ r ∈ calleeSaved ∧ x = .entry r := by
  simp only [inContent] at h
  by_cases hc : b ≠ 0 ∧ r ∈ calleeSaved
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h
    exact ⟨hc.1, hc.2, List.mem_singleton.mp h⟩
  · simp only [hc, ↓reduceIte] at h; cases h

theorem inSave_entry {b : Nat} {r : Reg} (hb : b ≠ 0) (hr : r ∈ calleeSaved) :
    Sym.entry r ∈ inContent vc succs preds D b (.save r) := by
  simp [inContent, hb, hr]

theorem inStack_mem {b n : Nat} {c : RegClass} {x : Sym}
    (h : x ∈ inContent vc succs preds D b (.stack n c)) :
    ∃ v, x = .vreg v ∧ (spillHomes vc)[(v, c)]? = some n ∧ vc.classes[v]? = some c ∧ D b v = true := by
  simp only [inContent, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨v, ⟨-, ⟨h1, h2⟩, h3⟩, rfl⟩ := h
  exact ⟨v, rfl, h1, h2, h3⟩

theorem inStack_vreg {b n v : Nat} {c : RegClass} (h1 : (spillHomes vc)[(v, c)]? = some n)
    (h2 : vc.classes[v]? = some c) (h3 : D b v = true) :
    Sym.vreg v ∈ inContent vc succs preds D b (.stack n c) := by
  simp only [inContent, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq, List.mem_range]
  exact ⟨v, ⟨(Array.getElem?_eq_some_iff.mp h2).1, ⟨h1, h2⟩, h3⟩, rfl⟩

theorem save_index_all : calleeSaved.all (fun r => match (Loc.save r).index with
    | some i => decide (i < 128)
    | none => false) = true := by decide

theorem save_index {r : Reg} (hr : r ∈ calleeSaved) :
    ∃ i, (Loc.save r).index = some i ∧ i < 128 := by
  have := List.all_eq_true.mp save_index_all r hr
  revert this
  cases (Loc.save r).index with
  | some i => intro h; exact ⟨i, rfl, by simpa using h⟩
  | none => intro h; cases h

theorem save_index_lt {r : Reg} (hr : r ∈ calleeSaved) :
    ∃ i, (Loc.save r).index = some i ∧ i < stN vc := by
  obtain ⟨i, h1, h2⟩ := save_index hr
  exact ⟨i, h1, by unfold stN; omega⟩

/-- The in-state of block `b` is `Good` for `D b`, with the save slots on entry to a block other
than the entry. -/
theorem inState_home {b v n : Nat} {c : RegClass} (hD : D b v = true)
    (hc : vc.classes[v]? = some c) (hn : (spillHomes vc)[(v, c)]? = some n) :
    Sym.vreg v ∈ (inState vc succs preds D b).get (.stack n c) := by
  obtain ⟨i, h1, h2⟩ := home_index_lt hn
  rw [inState, get_mkState h1 h2]
  exact inStack_vreg hn hc hD

theorem inState_save {b : Nat} {r : Reg} (hb : b ≠ 0) (hr : r ∈ calleeSaved) :
    Sym.entry r ∈ (inState vc succs preds D b).get (.save r) := by
  obtain ⟨i, h1, h2⟩ := save_index_lt (vc := vc) hr
  rw [inState, get_mkState h1 h2]
  exact inSave_entry hb hr

theorem inState_reg0 {r : Reg} (hr : r ∈ calleeSaved) :
    Sym.entry r ∈ (inState vc succs preds D 0).get (.reg r) := by
  obtain ⟨i, h1, h2⟩ := reg_index_lt (vc := vc) (calleeSaved_ok r hr).1
  rw [inState, get_mkState h1 h2]
  exact inReg_entry rfl hr

theorem inState_pair {b : Nat} {r : Reg} (ha : r.allocatable = true) {y : Operand × Loc}
    (hy : y ∈ entryPairs vc succs preds b) (he : y.2 = .reg r) :
    Sym.vreg y.1.vreg ∈ (inState vc succs preds D b).get y.2 := by
  obtain ⟨i, h1, h2⟩ := reg_index_lt (vc := vc) ha
  rw [he, inState, get_mkState h1 h2]
  exact inReg_pair hy he

/-- **The entry block's in-state is `EntryOk`.** -/
theorem inState_entryOk (h0 : preds[0]? = some #[]) : EntryOk (inState vc succs preds D 0) := by
  have hnil := entryPairs_nil (vc := vc) (succs := succs) h0
  refine ⟨fun l r h => ?_, fun l l' v h h' => ?_⟩
  · have hm := (mem_get_mkState h).1
    cases l with
    | reg r' =>
      rcases inReg_mem hm with ⟨-, hr, he⟩ | ⟨y, hy, -⟩
      · cases he; exact ⟨hr, rfl⟩
      · rw [hnil] at hy; cases hy
    | save r' => exact absurd (inSave_mem hm).1 (by simp)
    | stack n c =>
      obtain ⟨v, he, -⟩ := inStack_mem hm
      cases he
  · have hm := (mem_get_mkState h).1
    have hm' := (mem_get_mkState h').1
    have stk : ∀ l, Sym.vreg v ∈ inContent vc succs preds D 0 l →
        ∃ n c, l = .stack n c ∧ (spillHomes vc)[(v, c)]? = some n ∧ vc.classes[v]? = some c := by
      intro l hl
      cases l with
      | reg r' =>
        rcases inReg_mem hl with ⟨-, -, he⟩ | ⟨y, hy, -⟩
        · cases he
        · rw [hnil] at hy; cases hy
      | save r' => cases (inSave_mem hl).2.2
      | stack n c =>
        obtain ⟨w, he, h1, h2, -⟩ := inStack_mem hl
        cases he
        exact ⟨n, c, rfl, h1, h2⟩
    obtain ⟨n, c, rfl, h1, h2⟩ := stk l hm
    obtain ⟨n', c', rfl, h1', h2'⟩ := stk l' hm'
    rw [h2] at h2'
    cases h2'
    rw [h1] at h1'
    cases h1'
    rfl

end

end Backend.Proof.Spill

import FV.Backend.RegallocPerEdgeSpill

namespace Backend.Proof.PerEdgeSpill
open Backend
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- The dense table's actual optional home, including out-of-bounds keys. -/
def homeLookup (h : SpillHomesAt) (key : Nat) : Option Nat := (h.slots[key]?).join

/-- Internal dense-table invariant: allocated homes are in bounds and distinct. -/
def HomesValid (h : SpillHomesAt) : Prop :=
  (∀ key n,homeLookup h key = some n → n < h.size) ∧
  (∀ key other n,homeLookup h key = some n → homeLookup h other = some n → key = other)

private theorem grow_lookup (slots : Array (Option Nat)) (count key : Nat) :
    ((slots ++ Array.replicate count none)[key]?).join = (slots[key]?).join := by
  rw [Array.getElem?_append]
  split
  · rfl
  · rename_i outside
    have absent : slots[key]? = none := Array.getElem?_eq_none (by omega)
    rw [absent,Array.getElem?_replicate]
    split <;> rfl

private theorem insert_lookup (h : SpillHomesAt) (v : Nat) (c : RegClass)
    (absent : homeLookup h (spillHomeKeyAt v c) = none) (key : Nat) :
    homeLookup (h.insert v c) key =
      if key = spillHomeKeyAt v c then some h.size else homeLookup h key := by
  unfold SpillHomesAt.insert
  dsimp only
  change (h.slots[spillHomeKeyAt v c]?).join = none at absent
  rw [absent]
  simp only [Option.isSome,Bool.false_eq_true,ite_false,homeLookup]
  have bound : spillHomeKeyAt v c <
      (h.slots ++ Array.replicate (spillHomeKeyAt v c+1-h.slots.size) none).size := by
    simp only [Array.size_append,Array.size_replicate]
    omega
  by_cases same : key = spillHomeKeyAt v c
  · subst key
    simp only [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt bound,
      Option.join_some,ite_true]
  · rw [if_neg same,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne (Ne.symm same)]
    exact grow_lookup _ _ _

private theorem insert_valid {h : SpillHomesAt} (valid : HomesValid h) (v : Nat) (c : RegClass) :
    HomesValid (h.insert v c) := by
  cases found : homeLookup h (spillHomeKeyAt v c) with
  | some n =>
    have same : h.insert v c = h := by
      unfold SpillHomesAt.insert
      dsimp only
      change (h.slots[spillHomeKeyAt v c]?).join = some n at found
      rw [found]
      rfl
    rw [same]
    exact valid
  | none =>
    have size : (h.insert v c).size = h.size+1 := by
      unfold SpillHomesAt.insert
      dsimp only
      change (h.slots[spillHomeKeyAt v c]?).join = none at found
      rw [found]
      rfl
    constructor
    · intro key n atKey
      rw [insert_lookup h v c found] at atKey
      split at atKey
      · cases atKey; omega
      · have bound := valid.1 key n atKey; omega
    · intro key other n atKey atOther
      rw [insert_lookup h v c found] at atKey atOther
      split at atKey <;> split at atOther
      · omega
      · cases atKey
        have bound := valid.1 other h.size atOther
        omega
      · cases atOther
        have bound := valid.1 key h.size atKey
        omega
      · exact valid.2 key other n atKey atOther

private theorem insert_keep (h : SpillHomesAt) (v : Nat) (c : RegClass) {key n : Nat}
    (found : homeLookup h key = some n) : homeLookup (h.insert v c) key = some n := by
  cases atKey : homeLookup h (spillHomeKeyAt v c) with
  | none =>
    rw [insert_lookup h v c atKey]
    have different : key ≠ spillHomeKeyAt v c := by intro eq; rw [eq,atKey] at found; cases found
    rw [if_neg different,found]
  | some value =>
    unfold SpillHomesAt.insert
    dsimp only
    change (h.slots[spillHomeKeyAt v c]?).join = some value at atKey
    rw [atKey]
    exact found

private theorem insert_self (h : SpillHomesAt) (v : Nat) (c : RegClass) :
    ∃ n,homeLookup (h.insert v c) (spillHomeKeyAt v c) = some n := by
  cases found : homeLookup h (spillHomeKeyAt v c) with
  | none => exact ⟨h.size,by rw [insert_lookup h v c found,if_pos rfl]⟩
  | some n => exact ⟨n,insert_keep h v c found⟩

private theorem insert_mono (h : SpillHomesAt) (v : Nat) (c : RegClass) :
    h.size ≤ (h.insert v c).size := by
  unfold SpillHomesAt.insert
  dsimp only
  split <;> simp

/-- Distinct virtual-number/class pairs have distinct dense keys. -/
theorem spillHomeKeyAt_injective {v w : Nat} {c d : RegClass}
    (same : spillHomeKeyAt v c = spillHomeKeyAt w d) : v = w ∧ c = d := by
  cases c <;> cases d <;> simp only [spillHomeKeyAt] at same <;> first
  | exact ⟨by omega,rfl⟩
  | omega


private def keysOf (vc : VCode) (edges : Array (Array (Array Reg))) : List (Nat × RegClass) :=
  vc.blocks.toList.flatMap blockVregs ++ edges.toList.flatMap (fun row =>
    row.toList.flatMap (fun args => args.toList.map (fun r => (r.homeNum,r.homeCls))))
private def pairStep (h : SpillHomesAt) (key : Nat × RegClass) := h.insert key.1 key.2
private theorem homes_fold (vc : VCode) (edges : Array (Array (Array Reg))) :
    spillHomesAt vc edges = (keysOf vc edges).foldl pairStep {} := by
  simp only [keysOf,List.foldl_append,List.foldl_flatMap,List.foldl_map,Array.foldl_toList]
  rfl
private theorem fold_valid (keys : List (Nat × RegClass)) {h : SpillHomesAt} (valid : HomesValid h) :
    HomesValid (keys.foldl pairStep h) := by
  induction keys generalizing h with
  | nil => exact valid
  | cons key keys ih => exact ih (insert_valid valid key.1 key.2)
private theorem fold_keep (keys : List (Nat × RegClass)) {h : SpillHomesAt} {key n : Nat}
    (found : homeLookup h key = some n) : homeLookup (keys.foldl pairStep h) key = some n := by
  induction keys generalizing h with
  | nil => exact found
  | cons x keys ih => exact ih (insert_keep h x.1 x.2 found)
private theorem fold_self (keys : List (Nat × RegClass)) (h : SpillHomesAt) {key : Nat × RegClass}
    (member : key ∈ keys) : ∃ n,homeLookup (keys.foldl pairStep h) (spillHomeKeyAt key.1 key.2) = some n := by
  induction keys generalizing h with
  | nil => cases member
  | cons x keys ih =>
    rcases List.mem_cons.mp member with same | member
    · subst x
      obtain ⟨n,found⟩ := insert_self h key.1 key.2
      exact ⟨n,fold_keep keys found⟩
    · exact ih _ member

/-- Facts of the actual whole dense allocation, including outgoing-only keys.
These are proved allocator invariants, rather than source acceptance conditions. -/
structure HomesSpec (vc : VCode) (edges : Array (Array (Array Reg))) : Prop where
  valid : HomesValid (spillHomesAt vc edges)
  code : ∀ (b : Nat) (vb : VBlock),vc.blocks[b]? = some vb → ∀ key ∈ blockVregs vb,
    ∃ n,homeLookup (spillHomesAt vc edges) (spillHomeKeyAt key.1 key.2) = some n
  outgoing : ∀ (b j k : Nat) (row : Array (Array Reg)) (args : Array Reg) (r : Reg),
    edges[b]? = some row → row[j]? = some args → args[k]? = some r →
      ∃ n,homeLookup (spillHomesAt vc edges) (spillHomeKeyAt r.homeNum r.homeCls) = some n

/-- Every actual indexed spill-home allocation is bounded/injective and covers
all code and per-successor registers, including registers absent from code. -/
theorem spillHomesAt_spec (vc : VCode) (edges : Array (Array (Array Reg))) : HomesSpec vc edges := by
  have member (key : Nat × RegClass) (inside : key ∈ keysOf vc edges) :
      ∃ n,homeLookup (spillHomesAt vc edges) (spillHomeKeyAt key.1 key.2) = some n := by
    rw [homes_fold]
    exact fold_self _ _ inside
  constructor
  · rw [homes_fold]
    exact fold_valid _ ⟨fun key n found => by simp [homeLookup] at found,
      fun key other n found _ => by simp [homeLookup] at found⟩
  · intro b vb found key inside
    apply member key
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨vb,
      Array.mem_toList_iff.mpr (Array.mem_of_getElem? found),inside⟩)
  · intro b j k row args r atRow atArgs atReg
    apply member (r.homeNum,r.homeCls)
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨row,Array.mem_toList_iff.mpr (Array.mem_of_getElem? atRow),
      List.mem_flatMap.mpr ⟨args,Array.mem_toList_iff.mpr (Array.mem_of_getElem? atArgs),
        List.mem_map.mpr ⟨r,Array.mem_toList_iff.mpr (Array.mem_of_getElem? atReg),rfl⟩⟩⟩

/-- The maximum indexed argument-vector length used by the real allocator. -/
def maxArgsAt (edges : Array (Array (Array Reg))) : Nat :=
  edges.foldl (fun n row => row.foldl (fun n args => max n args.size) n) 0
private theorem fold_max_init (args : List (Array Reg)) (n : Nat) :
    n ≤ args.foldl (fun n args => max n args.size) n := by
  induction args generalizing n with
  | nil => exact Nat.le_refl _
  | cons a args ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
private theorem fold_max_mem (args : List (Array Reg)) (n : Nat) {a : Array Reg} (inside : a ∈ args) :
    a.size ≤ args.foldl (fun n args => max n args.size) n := by
  induction args generalizing n with
  | nil => cases inside
  | cons b args ih =>
    rcases List.mem_cons.mp inside with same | inside
    · subst b; exact Nat.le_trans (Nat.le_max_right _ _) (fold_max_init _ _)
    · exact ih _ inside
private theorem rows_max_init (rows : List (Array (Array Reg))) (n : Nat) :
    n ≤ rows.foldl (fun n row => row.foldl (fun n args => max n args.size) n) n := by
  induction rows generalizing n with
  | nil => exact Nat.le_refl _
  | cons row rows ih =>
    have first : n ≤ row.foldl (fun n args => max n args.size) n := by
      simpa only [Array.foldl_toList] using fold_max_init row.toList n
    exact Nat.le_trans first (ih _)
private theorem rows_max_mem (rows : List (Array (Array Reg))) (n : Nat)
    {row : Array (Array Reg)} {args : Array Reg} (atRow : row ∈ rows) (atArgs : args ∈ row.toList) :
    args.size ≤ rows.foldl (fun n row => row.foldl (fun n args => max n args.size) n) n := by
  induction rows generalizing n with
  | nil => cases atRow
  | cons r rows ih =>
    rcases List.mem_cons.mp atRow with same | inside
    · subst r
      have first : args.size ≤ row.foldl (fun n args => max n args.size) n := by
        simpa only [Array.foldl_toList] using fold_max_mem row.toList n atArgs
      exact Nat.le_trans first (rows_max_init _ _)
    · exact ih _ inside

/-- Every real outgoing vector fits the allocator's reserved temporary area;
all actual homes lie strictly below it. This is derived from the real folds. -/
theorem spillAllocAt_storage (vc : VCode) (edges : Array (Array (Array Reg))) :
    (spillAllocAt vc edges).spillSlots = (spillHomesAt vc edges).size + maxArgsAt edges ∧
    (∀ key n,homeLookup (spillHomesAt vc edges) key = some n → n < (spillHomesAt vc edges).size) ∧
    ∀ (b j : Nat) (row : Array (Array Reg)) (args : Array Reg),edges[b]? = some row → row[j]? = some args →
      args.size ≤ maxArgsAt edges := by
  refine ⟨?_,(spillHomesAt_spec vc edges).valid.1,?_⟩
  · unfold spillAllocAt maxArgsAt
    split <;> rfl
  · intro b j row args atRow atArgs
    unfold maxArgsAt
    rw [← Array.foldl_toList]
    exact rows_max_mem _ _ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? atRow))
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? atArgs))

end Backend.Proof.PerEdgeSpill


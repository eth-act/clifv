import FV.Backend.Proof.SpillInvariant

/-!
# Definite assignment and the spill allocation's availability sets

`SpillAvail vc D` (`SpillInvariant.lean`) mixes two facts about "the home of `v` holds `v`": no
instruction kills `v` without storing it (availability), and some instruction stored `v` on every
path from the function entry (definedness). `checkAlloc`'s fixpoint starts from no vreg held, so
the spill allocation's in-states that it accepts need sets with `D 0 = false`.

`DefAvail vc M` is the definedness half alone, with the same shape: `defInst` makes every def of
an instruction defined (stored or not), the entry stores and the edges as in `SpillAvail`.
`spillAvail_and`: availability sets `K` and definedness sets `M` give availability sets
`K ∧ M`; with `M 0 = false` their entry set is empty (`spillAvail_defined`).
-/

namespace Backend.Proof.Spill

open Backend

/-- Definedness after instruction `i` from definedness `A` before it: every def is defined. -/
def defInst (i : MInst) (A : Nat → Bool) (v : Nat) : Bool :=
  match i.operands with
  | .error _ => A v
  | .ok ops => if (ops.toList.filter (·.kind == .def)).any (·.vreg == v) then true else A v

/-- Definedness before instruction `k` of a block with instructions `insts`, from `A` at its
start. -/
def defAt (insts : Array MInst) (A : Nat → Bool) (k : Nat) : Nat → Bool :=
  (insts.toList.take k).foldl (fun A i => defInst i A) A

/-- Definedness on entry to block `b` after its entry stores, from the set `M b`. -/
def defStart (vc : VCode) (succs preds : Array (Array Nat)) (M : Nat → Nat → Bool) (b : Nat)
    (v : Nat) : Bool :=
  M b v || (entryStored vc succs preds b).contains v

/-- **Definedness sets** of `vc` (`M b v`: on entry to block `b`, `v` has been defined on every
path from the function entry): every use is defined where it is read, every edge delivers the
set of its target (a parameter is defined iff its branch argument is). -/
structure DefAvail (vc : VCode) (M : Nat → Nat → Bool) : Prop where
  /-- Every use is defined where it is read. -/
  uses : ∀ succs preds, vc.cfg = .ok (succs, preds) →
    ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst) (ops : Array Operand),
      vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
      ∀ o ∈ ops.toList, o.kind = .use →
        defAt vb.insts (defStart vc succs preds M b) k o.vreg = true
  /-- Every edge delivers the definedness set of its target. -/
  edges : ∀ succs preds, vc.cfg = .ok (succs, preds) →
    ∀ (b : Nat) (vb : VBlock) (ss : Array Nat) (s : Nat) (sb : VBlock),
      vc.blocks[b]? = some vb → succs[b]? = some ss → s ∈ ss.toList → vc.blocks[s]? = some sb →
      ∀ v, M s v = true →
        edgeAvail vb sb (defAt vb.insts (defStart vc succs preds M b) vb.insts.size) v = true

/-! ## Availability of the conjunction -/

theorem availInst_and (i : MInst) (A B : Nat → Bool) :
    availInst i (fun v => A v && B v) = fun v => availInst i A v && defInst i B v := by
  funext v
  unfold availInst defInst
  cases i.operands with
  | error _ => rfl
  | ok ops =>
    simp only
    by_cases h : ((ops.toList.filter (·.kind == .def)).any (·.vreg == v)) = true
    · simp only [h, ↓reduceIte, Bool.and_true]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem foldl_and : ∀ (l : List MInst) (A B : Nat → Bool),
    l.foldl (fun A i => availInst i A) (fun v => A v && B v) =
      fun v => l.foldl (fun A i => availInst i A) A v && l.foldl (fun A i => defInst i A) B v
  | [], _, _ => rfl
  | i :: l, A, B => by
    simp only [List.foldl_cons]
    rw [availInst_and]
    exact foldl_and l _ _

theorem availAt_and (insts : Array MInst) (A B : Nat → Bool) (k : Nat) :
    availAt insts (fun v => A v && B v) k = fun v => availAt insts A k v && defAt insts B k v :=
  foldl_and _ A B

theorem availStart_and (vc : VCode) (succs preds : Array (Array Nat)) (K M : Nat → Nat → Bool)
    (b : Nat) :
    availStart vc succs preds (fun b v => K b v && M b v) b =
      fun v => availStart vc succs preds K b v && defStart vc succs preds M b v := by
  funext v
  unfold availStart defStart
  show (K b v && M b v || _) = _
  cases K b v <;> cases M b v <;> cases (entryStored vc succs preds b).contains v <;> rfl

theorem edgeAvail_and (vb sb : VBlock) (A B : Nat → Bool) (v : Nat) :
    edgeAvail vb sb (fun v => A v && B v) v = (edgeAvail vb sb A v && edgeAvail vb sb B v) := by
  unfold edgeAvail
  split
  · split <;> rfl
  · rfl

/-- **Availability sets from availability and definedness**: `SpillAvail vc K` and
`DefAvail vc M` give `SpillAvail vc (K ∧ M)`. -/
theorem spillAvail_and {vc : VCode} {K M : Nat → Nat → Bool} (hK : SpillAvail vc K)
    (hM : DefAvail vc M) : SpillAvail vc (fun b v => K b v && M b v) := by
  refine ⟨fun succs preds hc b vb k i ops hb hi hops o ho hu => ?_,
    fun succs preds hc b vb ss s sb hb hss hs hsb v hv => ?_⟩
  · rw [availStart_and, availAt_and]
    simp only [Bool.and_eq_true]
    exact ⟨hK.uses succs preds hc b vb k i ops hb hi hops o ho hu,
      hM.uses succs preds hc b vb k i ops hb hi hops o ho hu⟩
  · simp only [Bool.and_eq_true] at hv
    rw [availStart_and, availAt_and, edgeAvail_and]
    simp only [Bool.and_eq_true]
    exact ⟨hK.edges succs preds hc b vb ss s sb hb hss hs hsb v hv.1,
      hM.edges succs preds hc b vb ss s sb hb hss hs hsb v hv.2⟩

/-- **Availability sets holding nothing on entry** from any availability sets and definedness
sets holding nothing on entry. -/
theorem spillAvail_defined {vc : VCode} {K M : Nat → Nat → Bool} (hK : SpillAvail vc K)
    (hM : DefAvail vc M) (h0 : ∀ v, M 0 v = false) :
    ∃ D, SpillAvail vc D ∧ ∀ v, D 0 v = false :=
  ⟨_, spillAvail_and hK hM, fun v => by simp [h0 v]⟩

end Backend.Proof.Spill

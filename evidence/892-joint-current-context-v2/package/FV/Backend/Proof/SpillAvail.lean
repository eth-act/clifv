import FV.Backend.Proof.SpillInvariant
import FV.Backend.Proof.SpillEdgesPrep

/-!
# The spill allocation's availability sets (V4 step 4, `SpillAvail`): reduction to `killFreeB`

`SpillAvail vc D` asks for must-availability sets: "the home of vreg `v` holds `v`" is lost only
where the allocated code kills a def without storing it (`unstored`: the defs of a terminator, the
scratch defs past `MInst.keptDefs`) and for a parameter whose branch argument is unavailable.
Since every home holds its vreg on entry to the function, a vreg that no instruction kills
(`killedOf vc`) is available everywhere. So with

* `killD vc b v := b = 0 ∨ v ∉ killedOf vc`,

`SpillAvail vc (killD vc)` follows from two syntactic facts, decided by `killFreeB vc`:

1. no instruction reads a killed vreg;
2. a branch argument that is a killed vreg is stored by its block's entry stores (`entryStored`:
   a `try_call`'s result, live on the edge to its edge block) and not killed in the block;

and the CFG facts `EdgesOk` (step 3: no edge into the entry block, branch arguments only on a
single-successor block with matching parameters, parameterless successors otherwise):
`spillAvail_of_killFree`.
-/

namespace Backend.Proof.Spill

open Backend

/-- The def vregs of `i` that `spillInst` does not store (`storedDefs`): every def of a
terminator, the scratch defs past `MInst.keptDefs`. -/
def unstored (i : MInst) : List Nat :=
  match i.operands with
  | .error _ => []
  | .ok ops => ((ops.toList.filter (·.kind == .def)).map (·.vreg)).filter
      fun v => !(storedDefs i ops).contains v

/-- The use vregs of `i`. -/
def useVregs (i : MInst) : List Nat :=
  match i.operands with
  | .error _ => []
  | .ok ops => (ops.toList.filter (·.kind == .use)).map (·.vreg)

/-- The vregs some instruction of `vc` kills (`unstored`). -/
def killedOf (vc : VCode) : List Nat :=
  vc.blocks.toList.flatMap fun vb => vb.insts.toList.flatMap unstored

/-- **The syntactic availability facts**: no instruction reads a killed vreg, and a killed branch
argument is stored by its block's entry stores and not killed in the block. -/
def killFreeB (vc : VCode) : Bool :=
  let K := killedOf vc
  vc.blocks.toList.all (fun vb => vb.insts.toList.all fun i => (useVregs i).all fun v => !K.contains v) &&
  match vc.cfg with
  | .error _ => true
  | .ok (succs, preds) =>
    (List.range vc.blocks.size).all fun b => match vc.blocks[b]? with
      | none => true
      | some vb => vb.branchArgs.toList.all fun a =>
          !K.contains a.homeNum ||
            ((entryStored vc succs preds b).contains a.homeNum &&
              vb.insts.toList.all fun i => !(unstored i).contains a.homeNum)

/-- The availability sets: everything at the entry block, the vregs no instruction kills
elsewhere. -/
def killD (vc : VCode) (b v : Nat) : Bool := b == 0 || !(killedOf vc).contains v

/-! ## Availability through instructions -/

theorem availInst_true {i : MInst} {A : Nat → Bool} {v : Nat} (hv : v ∉ unstored i)
    (hA : A v = true) : availInst i A v = true := by
  unfold availInst
  unfold unstored at hv
  split
  · exact hA
  · rename_i ops hops
    rw [hops] at hv
    simp only at hv
    split
    · rename_i hany
      cases hc : (storedDefs i ops).contains v
      · exfalso; apply hv
        simp only [List.mem_filter, List.mem_map]
        obtain ⟨o, ho, hov⟩ := List.any_eq_true.mp hany
        exact ⟨⟨o, List.mem_filter.mp ho, by simpa using hov⟩,
          by rw [hc]; rfl⟩
      · rfl
    · exact hA

theorem foldl_availInst_true {v : Nat} : ∀ (l : List MInst) (A : Nat → Bool),
    (∀ i ∈ l, v ∉ unstored i) → A v = true →
      (l.foldl (fun A i => availInst i A) A) v = true
  | [], _, _, hA => hA
  | i :: l, A, hl, hA => by
    rw [List.foldl_cons]
    exact foldl_availInst_true l _ (fun i' hi' => hl i' (List.mem_cons_of_mem _ hi'))
      (availInst_true (hl i List.mem_cons_self) hA)

theorem availAt_true {insts : Array MInst} {A : Nat → Bool} {v : Nat}
    (hk : ∀ i ∈ insts.toList, v ∉ unstored i) (hA : A v = true) (k : Nat) :
    availAt insts A k v = true :=
  foldl_availInst_true _ _ (fun i hi => hk i (List.mem_of_mem_take hi)) hA

theorem mem_killedOf {vc : VCode} {b : Nat} {vb : VBlock} (hb : vc.blocks[b]? = some vb)
    {i : MInst} (hi : i ∈ vb.insts.toList) {v : Nat} (hv : v ∈ unstored i) : v ∈ killedOf vc := by
  simp only [killedOf, List.mem_flatMap]
  exact ⟨vb, Array.mem_toList_iff.mpr (Array.mem_of_getElem? hb), i, hi, hv⟩

/-- A vreg no instruction kills is available wherever its start availability holds. -/
theorem availAt_notKilled {vc : VCode} {b : Nat} {vb : VBlock} (hb : vc.blocks[b]? = some vb)
    {A : Nat → Bool} {v : Nat} (hv : (killedOf vc).contains v = false) (hA : A v = true) (k : Nat) :
    availAt vb.insts A k v = true :=
  availAt_true (fun i hi hu => by
    have := mem_killedOf hb hi hu
    simp [this] at hv) hA k

/-! ## No edge into the entry block -/

theorem not_tgt0 {vc : VCode} {succs preds : Array (Array Nat)}
    (hc : vc.cfg = .ok (succs, preds)) (h0 : preds[0]? = some #[]) (hsz : 0 < vc.blocks.size)
    {b : Nat} {ss : Array Nat} (hss : succs[b]? = some ss) : 0 ∉ ss.toList := by
  intro hm
  have h := cfg_preds hc hsz
  rw [h0] at h
  have hnil : predsOf 0 succs.toList.zipIdx = [] := by
    have := congrArg (fun o => o.map Array.toList) h
    simpa using this.symm
  simp only [predsOf, List.flatMap_eq_nil_iff, List.replicate_eq_nil_iff,
    List.count_eq_zero] at hnil
  have hbm : (ss, b) ∈ succs.toList.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simpa using hss
  exact hnil _ hbm hm

/-! ## The reduction -/

/-- **`SpillAvail` from the syntactic facts**: under the CFG facts of step 3 (`EdgesOk`) and
`killFreeB`, the sets `killD vc` are availability sets of `vc`. -/
theorem spillAvail_of_killFree {vc : VCode} (hk : killFreeB vc = true)
    (hed : ∀ succs preds, vc.cfg = .ok (succs, preds) → EdgesOk vc succs preds) :
    SpillAvail vc (killD vc) := by
  unfold killFreeB at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨hU, hA⟩ := hk
  have hU' : ∀ (b : Nat) (vb : VBlock), vc.blocks[b]? = some vb → ∀ i ∈ vb.insts.toList,
      ∀ v ∈ useVregs i, (killedOf vc).contains v = false := by
    intro b vb hb i hi v hv
    have := List.all_eq_true.mp hU vb (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hb))
    have := List.all_eq_true.mp this i hi
    simpa using List.all_eq_true.mp this v hv
  refine ⟨?_, ?_⟩
  · intro succs preds _ b vb k i ops hb hi hops o ho hou
    have hi' : i ∈ vb.insts.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)
    have hnk := hU' b vb hb i hi' o.vreg (by
      simp only [useVregs, hops, List.mem_map, List.mem_filter]
      exact ⟨o, ⟨ho, by simp [hou]⟩, rfl⟩)
    exact availAt_notKilled hb hnk (by simp only [availStart, killD, hnk, Bool.not_false, Bool.or_true, Bool.true_or]) k
  · intro succs preds hc b vb ss s sb hb hss hs hsb v hD
    have he := hed succs preds hc
    have hsz : 0 < vc.blocks.size := Nat.pos_of_ne_zero he.entry.1
    have hs0 : s ≠ 0 := fun e => not_tgt0 hc he.entry.2.1 hsz hss (e ▸ hs)
    have hvk : (killedOf vc).contains v = false := by
      simpa [killD, hs0] using hD
    -- a vreg not killed is available at the end of `b`
    have hend : ∀ w, (killedOf vc).contains w = false →
        availAt vb.insts (availStart vc succs preds (killD vc) b) vb.insts.size w = true :=
      fun w hw => availAt_notKilled hb hw (by simp only [availStart, killD, hw, Bool.not_false, Bool.or_true, Bool.true_or]) _
    unfold edgeAvail
    split
    · rename_i k hk
      obtain ⟨hklt, hkget, -⟩ := List.idxOf?_eq_some_iff.mp hk
      by_cases hba : vb.branchArgs = #[]
      · have := he.noArgs b vb ss s sb hb hba hss hs hsb
        simp [this] at hklt
      · obtain ⟨-, t, tb, hst, htb, hsize, -, -⟩ := he.args b vb hb hba
        rw [hst] at hss
        cases hss
        have hst' : s = t := by simpa using hs
        subst hst'
        rw [hsb] at htb
        cases htb
        have hka : k < vb.branchArgs.size := by
          rw [← hsize]; simpa using hklt
        rw [Array.getElem?_eq_getElem hka]
        simp only
        cases hak : (killedOf vc).contains vb.branchArgs[k].homeNum
        · exact hend _ hak
        · -- a killed argument: stored on entry, not killed in the block
          rw [hc] at hA
          have hbr := List.all_eq_true.mp hA b
            (List.mem_range.mpr ((Array.getElem?_eq_some_iff.mp hb).1))
          rw [hb] at hbr
          have := List.all_eq_true.mp hbr vb.branchArgs[k] (Array.getElem_mem_toList hka)
          simp only [hak, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
            Bool.not_eq_true'] at this
          obtain ⟨hst, hno⟩ := this
          refine availAt_true (fun i hi hu => ?_) (by simp only [availStart, hst, Bool.or_true]) _
          have := hno i hi
          simp [hu] at this
    · exact hend v hvk

end Backend.Proof.Spill

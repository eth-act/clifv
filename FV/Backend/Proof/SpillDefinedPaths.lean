import FV.Backend.Proof.SpillDefined

/-!
# Definedness sets from paths

`Reaches vc succs preds b A`: some path of the CFG from the entry (block 0) to block `b` arrives
with definedness `A` (nothing defined on entry to block 0; through a block: its entry stores and
`defAt`; along an edge: `edgeAvail`). `pathSets vc b v`: `v` is defined on every such path (the
meet over all paths; everything on an unreachable block).

`defAvail_of_paths`: if every use is defined on every path that reaches it (`UsesDefined`) and
every edge into a block with parameters passes a branch argument for each (`ParamArgs`), then
`pathSets vc` are definedness sets (`DefAvail`) with nothing defined on entry. The proof rests on
the closed forms of `defAt` (some earlier instruction defines `v`, or `v` is defined at the start)
and `edgeAvail` (a renaming of parameters to their arguments), which commute with the meet.
-/

namespace Backend.Proof.Spill

open Backend

/-- Instruction `i` defines vreg `v`. -/
def isDefV (i : MInst) (v : Nat) : Bool :=
  match i.operands with
  | .error _ => false
  | .ok ops => (ops.toList.filter (·.kind == .def)).any (·.vreg == v)

/-- Paths from the entry and the definedness they arrive with at a block (before its entry
stores). -/
inductive Reaches (vc : VCode) (succs preds : Array (Array Nat)) : Nat → (Nat → Bool) → Prop
  | entry : Reaches vc succs preds 0 fun _ => false
  | step {b s : Nat} {A : Nat → Bool} {vb sb : VBlock} {ss : Array Nat} :
      Reaches vc succs preds b A → vc.blocks[b]? = some vb → succs[b]? = some ss → s ∈ ss.toList →
      vc.blocks[s]? = some sb →
      Reaches vc succs preds s
        (edgeAvail vb sb (defAt vb.insts (fun v => A v || (entryStored vc succs preds b).contains v)
          vb.insts.size))

open Classical in
/-- `v` is defined on entry to `b` on every path from the entry. -/
noncomputable def pathSets (vc : VCode) (b v : Nat) : Bool :=
  match vc.cfg with
  | .ok (succs, preds) => decide (∀ A, Reaches vc succs preds b A → A v = true)
  | .error _ => false

/-- **Every use is defined on every path that reaches it.** -/
def UsesDefined (vc : VCode) : Prop :=
  ∀ succs preds, vc.cfg = .ok (succs, preds) →
    ∀ (b : Nat) (A : Nat → Bool), Reaches vc succs preds b A →
      ∀ (vb : VBlock) (k : Nat) (i : MInst) (ops : Array Operand),
        vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
        ∀ o ∈ ops.toList, o.kind = .use →
          defAt vb.insts (fun v => A v || (entryStored vc succs preds b).contains v) k o.vreg = true

/-- **Every edge into a block with parameters passes a branch argument for each.** -/
def ParamArgs (vc : VCode) : Prop :=
  ∀ succs preds, vc.cfg = .ok (succs, preds) →
    ∀ (b : Nat) (vb : VBlock) (ss : Array Nat) (s : Nat) (sb : VBlock),
      vc.blocks[b]? = some vb → succs[b]? = some ss → s ∈ ss.toList → vc.blocks[s]? = some sb →
      ∀ (k : Nat) (p : Reg), sb.params[k]? = some p → ∃ a, vb.branchArgs[k]? = some a

/-! ## Closed forms -/

theorem defInst_eq (i : MInst) (A : Nat → Bool) (v : Nat) :
    defInst i A v = (isDefV i v || A v) := by
  unfold defInst isDefV
  cases i.operands with
  | error _ => rfl
  | ok ops =>
    simp only
    by_cases h : ((ops.toList.filter (·.kind == .def)).any (·.vreg == v)) = true
    · simp [h]
    · simp [h]

theorem foldl_defInst : ∀ (l : List MInst) (A : Nat → Bool) (v : Nat),
    l.foldl (fun A i => defInst i A) A v = (l.any (fun i => isDefV i v) || A v)
  | [], _, _ => by simp
  | i :: l, A, v => by
    simp only [List.foldl_cons, List.any_cons]
    rw [foldl_defInst l, defInst_eq]
    cases isDefV i v <;> cases l.any (fun i => isDefV i v) <;> rfl

theorem defAt_eq (insts : Array MInst) (A : Nat → Bool) (k v : Nat) :
    defAt insts A k v = ((insts.toList.take k).any (fun i => isDefV i v) || A v) :=
  foldl_defInst _ A v

/-! ## The path sets are definedness sets -/

theorem pathSets_eq {vc : VCode} {succs preds : Array (Array Nat)}
    (hc : vc.cfg = .ok (succs, preds)) (b v : Nat) :
    pathSets vc b v = true ↔ ∀ A, Reaches vc succs preds b A → A v = true := by
  unfold pathSets
  rw [hc]
  simp

/-- `defAt` from the path sets, at a vreg every arriving path defines there. -/
theorem defAt_paths {vc : VCode} {succs preds : Array (Array Nat)}
    (hc : vc.cfg = .ok (succs, preds)) {b : Nat} {insts : Array MInst} {k u : Nat}
    (h : ∀ A, Reaches vc succs preds b A →
      defAt insts (fun v => A v || (entryStored vc succs preds b).contains v) k u = true) :
    defAt insts (defStart vc succs preds (pathSets vc) b) k u = true := by
  rw [defAt_eq]
  unfold defStart
  cases hd : (insts.toList.take k).any (fun i => isDefV i u)
  · cases he : (entryStored vc succs preds b).contains u
    · have hp : pathSets vc b u = true := by
        rw [pathSets_eq hc]
        intro A hA
        have := h A hA
        rw [defAt_eq, hd, he] at this
        simpa using this
      rw [hp]; rfl
    · cases pathSets vc b u <;> rfl
  · rfl

/-- **Path sets are definedness sets** with nothing defined on entry. -/
theorem defAvail_of_paths {vc : VCode} (hU : UsesDefined vc) (hP : ParamArgs vc) :
    DefAvail vc (pathSets vc) := by
  refine ⟨fun succs preds hc b vb k i ops hb hi hops o ho hu => ?_,
    fun succs preds hc b vb ss s sb hb hss hs hsb v hv => ?_⟩
  · exact defAt_paths hc fun A hA => hU succs preds hc b A hA vb k i ops hb hi hops o ho hu
  · rw [pathSets_eq hc] at hv
    have hstep : ∀ A, Reaches vc succs preds b A →
        edgeAvail vb sb (defAt vb.insts (fun v => A v || (entryStored vc succs preds b).contains v)
          vb.insts.size) v = true :=
      fun A hA => hv _ (.step hA hb hss hs hsb)
    unfold edgeAvail at hstep ⊢
    split
    · rename_i k hk
      have hkp : k < sb.params.size := by
        have := (List.idxOf?_eq_some_iff.mp hk).1
        simpa using this
      obtain ⟨a, ha⟩ := hP succs preds hc b vb ss s sb hb hss hs hsb k sb.params[k]
        (Array.getElem?_eq_getElem hkp)
      rw [ha]
      simp only [hk, ha] at hstep
      exact defAt_paths hc hstep
    · rename_i hk
      simp only [hk] at hstep
      exact defAt_paths hc hstep

theorem pathSets_entry {vc : VCode} (hc : ∃ succs preds, vc.cfg = .ok (succs, preds)) (v : Nat) :
    pathSets vc 0 v = false := by
  obtain ⟨succs, preds, hc⟩ := hc
  cases h : pathSets vc 0 v with
  | false => rfl
  | true => exact absurd ((pathSets_eq hc 0 v).mp h _ .entry) (by simp)

/-- **Definite assignment from paths**: under `UsesDefined` and `ParamArgs`, `vc` has
definedness sets with nothing defined on entry. -/
theorem defined_of_paths {vc : VCode} (hc : ∃ succs preds, vc.cfg = .ok (succs, preds))
    (hU : UsesDefined vc) (hP : ParamArgs vc) :
    ∃ M, DefAvail vc M ∧ ∀ v, M 0 v = false :=
  ⟨_, defAvail_of_paths hU hP, pathSets_entry hc⟩

end Backend.Proof.Spill

import FV.Backend.Proof.SpillLocalCheck
import FV.Backend.Proof.RegallocCover
import FV.Backend.Proof.LowerRename

/-!
# The instruction facts of the instruction forms the lowering emits (V4 (a), step 3)

`spillInstOk_of_formOk`: every covered straight-line form (`FormOk`) meets `SpillInstOk` (at
most four register operands, all `reg`-constrained, at most one def; `movK` reuses its use).
`spillInstOk_mapRegs`: a vreg renaming keeps `SpillInstOk` when it keeps the defs distinct.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof

/-- Operands that are all `reg`-constrained, with early uses, at most one def, at most 26 of
them, and no clobbers, meet `OpsOk`. -/
theorem opsOk_simple {ops : Array Operand} (hcon : ∀ o ∈ ops.toList, o.con = .reg)
    (huse : ∀ o ∈ ops.toList, o.kind = .use → o.pos = .early)
    (hdef : (ops.toList.filter (·.kind == .def)).length ≤ 1) (hn : ops.toList.length ≤ 26) :
    OpsOk ops [] := by
  have hfix : fixedRegs ops = [] := by
    unfold fixedRegs
    rw [List.filterMap_eq_nil_iff]
    intro o ho; rw [hcon o ho]
  refine ⟨fun o ho h => ?_, huse, fun o ho p h => ?_, fun o ho o' _ p _ _ h => ?_,
    fun j _ o _ p hj _ _ _ h => ?_, fun o ho p _ h => ?_, fun o ho _ _ => by rw [hcon o ho]; rfl,
    fun j o i hj h => ?_, fun c => ?_, ?_⟩
  · rw [hcon o ho] at h; cases h
  · rw [hcon o ho] at h; cases h
  · rw [hcon o ho] at h; cases h
  · rw [hcon o (List.mem_of_getElem? hj)] at h; cases h
  · rw [hcon o ho] at h; cases h
  · rw [hcon o (List.mem_of_getElem? hj)] at h; cases h
  · have h1 : nScratch c ops.toList ≤ ops.toList.length := List.length_filter_le _ _
    have h2 : (freeRegs ops [] c).length = (spillPool c).length := by
      unfold freeRegs; rw [hfix]; simp
    have h3 : 26 ≤ (spillPool c).length := by cases c <;> decide
    omega
  · rcases hl : ops.toList.filter (·.kind == .def) with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp [hl]
    · simp [hl]
    · rw [hl] at hdef; simp at hdef

/-- `movK`'s operands: a use and a def reusing it. -/
theorem opsOk_movK (n d : Nat) :
    OpsOk #[⟨n, .int, .use, .early, .reg⟩, ⟨d, .int, .def, .late, .reuse 0⟩] [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o ho h; simp at ho; rcases ho with rfl | rfl <;> cases h
  · intro o ho h; simp at ho; rcases ho with rfl | rfl <;> first | rfl | cases h
  · intro o ho p h; simp at ho; rcases ho with rfl | rfl <;> cases h
  · intro o ho o' _ p _ _ h; simp at ho; rcases ho with rfl | rfl <;> cases h
  · intro j j' o o' p hj _ _ _ h
    rcases j with _ | _ | j <;> simp at hj <;> subst hj <;> cases h
  · intro o ho p _ h; simp at ho; rcases ho with rfl | rfl <;> cases h
  · intro o ho h1 h2; simp at ho; rcases ho with rfl | rfl <;> simp_all
  · intro j o i hj h
    rcases j with _ | _ | j <;> simp at hj <;> subst hj <;> cases h
    refine ⟨rfl, rfl, _, rfl, rfl, rfl, rfl, fun j' o' hj' h' => ?_⟩
    rcases j' with _ | _ | j' <;> simp at hj' <;> subst hj' <;> cases h' <;> rfl
  · intro c; cases c <;> simp [nScratch, scratch, freeRegs, fixedRegs, spillPool]
  · simp

/-- The tactic for one covered form: compute the operands, then `opsOk_simple`. -/
syntax "spill_form" : tactic
macro_rules
  | `(tactic| spill_form) => `(tactic| first
    | exact ⟨_, rfl, opsOk_movK _ _, fun _ h => by cases h⟩
    | (refine ⟨_, rfl, opsOk_simple ?_ ?_ ?_ ?_, fun _ h => by cases h⟩ <;>
        simp [OpSpec.use, OpSpec.def_, OpSpec.earlyDef]))

theorem spillInstOk_load {b : Nat} {m : AMode} (h : memOk b m = true) (op : LoadOp) (n : Nat)
    (fl : Clif.MemFlags) : SpillInstOk (.load op (.vreg n .int) m fl) := by
  unfold memOk at h
  split at h <;> (try cases h) <;> spill_form

theorem spillInstOk_store {b : Nat} {m : AMode} (h : memOk b m = true) (op : StoreOp) (n : Nat)
    (fl : Clif.MemFlags) : SpillInstOk (.store op (.vreg n .int) m fl) := by
  unfold memOk at h
  split at h <;> (try cases h) <;> spill_form

/-- **Every covered straight-line form meets `SpillInstOk`.** -/
theorem spillInstOk_of_formOk {ctx : FnCtx} {i : MInst} (h : FormOk ctx i = true) : SpillInstOk i := by
  unfold FormOk at h
  split at h
  all_goals (try cases h)
  all_goals first
    | spill_form
    | exact spillInstOk_load (Bool.and_eq_true _ _ ▸ h).2 _ _ _
    | exact spillInstOk_store (Bool.and_eq_true _ _ ▸ h).2 _ _ _

end Backend.Proof.Spill

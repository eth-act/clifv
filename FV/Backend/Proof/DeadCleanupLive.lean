import FV.Backend.Proof.DeadCleanupStructure
import FV.Backend.Proof.VCodeSem

namespace Backend.DeadCleanup
open Backend.Proof

/-- The register files agree where the remainder of the block can read them. -/
def Agree {V : Type} (live : List Nat) (a b : Nat → V) : Prop :=
  ∀ n ∈ live, a n = b n

/-- Actual operand definitions, rather than the incomplete ABI-free `MInst.defs`
view, justify removing a definition whose result is dead. -/
theorem discard_dead {m : MInst} {live : List Nat} (h : discard m live = true) :
    ∀ n ∈ defs m, n ∉ live := by
  simp only [discard, Bool.and_eq_true, List.all_eq_true] at h
  intro n hn
  have hd := h.2 n hn
  simpa using hd

theorem discard_pure {m : MInst} {live : List Nat} (h : discard m live = true) :
    pureForm m = true := by
  simp only [discard, Bool.and_eq_true] at h
  exact h.1.1.1.1

theorem retained_uses {V : Type} {nregs : Nat} {m : MInst} {live : List Nat}
    {a b : Nat → V} (h : Agree (uses nregs m ++ live.filter (fun n => !(defs m).contains n)) a b)
    {ops : Array Operand} (hop : m.operands = .ok ops) :
    (ops.toList.filter Operand.isUse).map (a ·.vreg) =
      (ops.toList.filter Operand.isUse).map (b ·.vreg) := by
  apply List.map_congr_left
  intro op hm
  apply h op.vreg
  apply List.mem_append_left
  simp only [uses, hop]
  exact List.mem_map.mpr ⟨op, hm, rfl⟩

private theorem writeV_frame {V : Type} (rho : Nat → V) (dv : List (Operand × V)) (n : Nat)
    (h : ∀ p ∈ dv, p.1.vreg ≠ n) : writeV rho dv n = rho n := by
  induction dv generalizing rho with
  | nil => rfl
  | cons p dv ih =>
    simp only [writeV, List.foldl_cons] at ih ⊢
    rw [ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    simp only [upd]
    rw [ite_eq_right (Ne.symm (h p (List.mem_cons_self ..)))]

/-- A discarded instruction's actual early/late writes cannot change a live
register. This uses no assumption about its arithmetic result. -/
theorem discard_updates_agree {V : Type} {m : MInst} {live : List Nat}
    {ops : Array Operand} (hd : discard m live = true) (hop : m.operands = .ok ops)
    (rho : Nat → V) (outs : List V) :
    Agree live rho (writeV
      (writeV rho (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isEarly)))
      (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isLate))) := by
  intro n hn
  have hdead := discard_dead hd
  have hframe : ∀ p ∈ (ops.toList.filter Operand.isDef).zip outs, p.1.vreg ≠ n := by
    intro p hp he
    apply hdead n _ hn
    simp only [defs, hop]
    exact List.mem_map.mpr ⟨p.1, (List.of_mem_zip hp).1, he⟩
  rw [writeV_frame _ _ _ (fun p hp => hframe p (List.mem_filter.mp hp).1),
      writeV_frame _ _ _ (fun p hp => hframe p (List.mem_filter.mp hp).1)]

private theorem writeV_equal_at {V : Type} {a b : Nat → V} {n : Nat}
    (h : a n = b n) (dv : List (Operand × V)) : writeV a dv n = writeV b dv n := by
  induction dv generalizing a b with
  | nil => exact h
  | cons p dv ih =>
    simp only [writeV, List.foldl_cons]
    apply ih
    simp only [upd]
    split
    · rfl
    · exact h

private theorem writeV_equal_defined {V : Type} (a b : Nat → V) {n : Nat}
    (dv : List (Operand × V)) (hn : n ∈ dv.map (·.1.vreg)) :
    writeV a dv n = writeV b dv n := by
  induction dv generalizing a b with
  | nil => simp at hn
  | cons p dv ih =>
    simp only [List.map_cons, List.mem_cons] at hn
    simp only [writeV, List.foldl_cons]
    rcases hn with he | ht
    · apply writeV_equal_at
      simp [upd, he]
    · exact ih _ _ ht

/-- Retaining an instruction with identical inputs and results restores
agreement on its live definitions, including both operand positions. -/
theorem retained_updates_agree {V : Type} {nregs : Nat} {m : MInst} {live : List Nat}
    {ops : Array Operand} (hop : m.operands = .ok ops) {a b : Nat → V}
    (ha : Agree (uses nregs m ++ live.filter (fun n => !(defs m).contains n)) a b)
    (outs : List V) (hlen : outs.length = (ops.toList.filter Operand.isDef).length) :
    Agree live
      (writeV (writeV a (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isEarly)))
        (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isLate)))
      (writeV (writeV b (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isEarly)))
        (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isLate))) := by
  intro n hn
  by_cases hd : n ∈ defs m
  · simp only [defs, hop] at hd
    obtain ⟨op, hm, hv⟩ := List.mem_map.mp hd
    have hm' : op ∈ ((ops.toList.filter Operand.isDef).zip outs).map Prod.fst := by
      rw [List.map_fst_zip (by omega)]
      exact hm
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hm'
    have hpv : p.1.vreg = n := by rw [he]; exact hv
    cases hpos : p.1.pos with
    | early =>
      apply writeV_equal_at
      apply writeV_equal_defined
      exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, by simp [Operand.isEarly, hpos]⟩, hpv⟩
    | late =>
      apply writeV_equal_defined
      exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, by simp [Operand.isLate, hpos]⟩, hpv⟩
  · apply writeV_equal_at
    apply writeV_equal_at
    apply ha n
    apply List.mem_append_right
    exact List.mem_filter.mpr ⟨hn, by simpa using hd⟩

/-! Non-vacuity: a real retained ABI return makes its input live. A dead `mvn`
has an actual virtual definition which is absent from the live-out set. -/

example : ∀ a b : Nat → Nat, Agree (uses 4 liveBic ++ [3].filter
    (fun n => !(defs liveBic).contains n)) a b →
    Agree [3] (writeV a [(⟨3, .int, .def, .late, .reg⟩, 9)])
      (writeV b [(⟨3, .int, .def, .late, .reg⟩, 9)]) := by
  intro a b h
  exact retained_updates_agree (nregs := 4) (m := liveBic) rfl h [9] rfl

example : discard deadMvn [3] = true ∧ 2 ∈ defs deadMvn ∧ 2 ∉ [3] := by decide
example : ∀ a b : Nat → Nat, Agree (uses 4 liveReturn) a b →
    a 3 = b 3 := by
  intro a b h
  exact h 3 (by decide)

end Backend.DeadCleanup

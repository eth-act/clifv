import FV.Backend.Proof.SpillLocal
import FV.Backend.Proof.RegallocOperands
import FV.Backend.Proof.IselCtlTerm
import FV.E2E.RegLevelPush
import FV.Backend.Proof.SpillLocalState
import FV.Backend.Proof.PairsC

/-!
# The spill allocator's facts on float `Args`/`Rets` (S11e5 Stage C, slice 5)

The typed lowering's entry `Args` and `gen_return`'s `Rets` have pairs of either class
(`argPairsC`): an int vreg in x0..x8 (`Args`; `Rets`: x0..x7, and x8 for an `sret` function's
struct pointer, #587), an `f32`/`f64` vreg in v0..v7 (AAPCS64, `sigArgLocs`, `retRegsC`,
`retRegsK`). `spillInstOk_argsC`, `spillInstOk_retsC`: with distinct registers (and, for `Args`,
distinct vregs) they meet `SpillInstOk`; the integer `spillInstOk_rets` is the instance with int
pairs (`spillInstOk_rets_of_C`). The fixed v0..v7
are allocatable, of class float and outside `calleeSaved` (only v8–v15, whose low 64 bits are
callee-saved, are).
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof

/-- A fixed argument register of class `c`: `x k` (`k ≤ 8`) for an int vreg, `v k` (`k < 8`) for
a float vreg. -/
def ArgRegC (c : RegClass) (r : Reg) : Prop :=
  (c = .int ∧ ∃ k, k ≤ 8 ∧ r = .x k) ∨ (c = .float ∧ ∃ k, k < 8 ∧ r = .v k)

/-- A fixed return register of class `c`: `x k` (`k < 8`) for an int vreg, `v k` (`k < 8`) for a
float vreg. -/
def RetRegC (c : RegClass) (r : Reg) : Prop :=
  (c = .int ∧ ∃ k, k < 8 ∧ r = .x k) ∨ (c = .float ∧ ∃ k, k < 8 ∧ r = .v k)

theorem x_alloc9C : ∀ k < 9, (Reg.x k).allocatable = true ∧ Reg.x k ∉ calleeSaved := by decide

theorem v_alloc8 : ∀ k < 8, (Reg.v k).allocatable = true ∧ Reg.v k ∉ calleeSaved := by decide

theorem argRegC_facts {c : RegClass} {r : Reg} (h : ArgRegC c r) :
    r.allocatable = true ∧ r.realClass? = some c ∧ r ∉ calleeSaved := by
  rcases h with ⟨rfl, k, hk, rfl⟩ | ⟨rfl, k, hk, rfl⟩
  · exact ⟨(x_alloc9C k (by omega)).1, rfl, (x_alloc9C k (by omega)).2⟩
  · exact ⟨(v_alloc8 k hk).1, rfl, (v_alloc8 k hk).2⟩

theorem retRegC_argRegC {c : RegClass} {r : Reg} (h : RetRegC c r) : ArgRegC c r := by
  rcases h with ⟨h1, k, hk, h2⟩ | h
  · exact .inl ⟨h1, k, by omega, h2⟩
  · exact .inr h

theorem nodup_getElem?_inj {α : Type} {l : List α} (h : l.Nodup) {i j : Nat} {a : α}
    (hi : l[i]? = some a) (hj : l[j]? = some a) : i = j := by
  obtain ⟨hi1, -⟩ := List.getElem?_eq_some_iff.mp hi
  exact (List.Nodup.getElem?_inj hi1 h).mp (hi.trans hj.symm)

/-- **A `Rets` of class-matched, distinct return registers** (x0..x8, v0..v7: `ArgRegC`) meets
`SpillInstOk`. -/
theorem spillInstOk_retsC {ns : List (Nat × RegClass × Reg)} (hr : ∀ q ∈ ns, ArgRegC q.2.1 q.2.2)
    (hnd : (ns.map (·.2.2)).Nodup) : SpillInstOk (.rets (argPairsC ns)) := by
  have mem : ∀ o ∈ (retOpsC ns).toArray.toList, ∃ q ∈ ns,
      o = ⟨q.1, q.2.1, .use, .early, .fixed q.2.2⟩ := by
    intro o ho
    simp only [retOpsC, List.toList_toArray, List.mem_map] at ho
    obtain ⟨q, hq, rfl⟩ := ho
    exact ⟨q, hq, rfl⟩
  have memj : ∀ (j : Nat) (o : Operand), (retOpsC ns).toArray.toList[j]? = some o → ∃ q ∈ ns,
      o = ⟨q.1, q.2.1, .use, .early, .fixed q.2.2⟩ := fun j o hj => mem o (List.mem_of_getElem? hj)
  have nodef : ∀ o ∈ (retOpsC ns).toArray.toList, o.kind = .use := by
    intro o ho; obtain ⟨q, -, rfl⟩ := mem o ho; rfl
  refine ⟨_, operands_retsC ns, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro o ho h; obtain ⟨q, -, rfl⟩ := mem o ho; cases h
  · intro o ho _; obtain ⟨q, -, rfl⟩ := mem o ho; rfl
  · intro o ho p h; obtain ⟨q, hq, rfl⟩ := mem o ho
    cases h
    have := argRegC_facts (hr q hq)
    exact ⟨this.1, this.2.1⟩
  · intro o ho o' ho' p _ _ h h'
    obtain ⟨q, hq, rfl⟩ := mem o ho
    obtain ⟨q', hq', rfl⟩ := mem o' ho'
    injection h with h; injection h' with h'
    rw [inj_of_nodup_map hnd hq hq' (h.trans h'.symm)]
  · intro j j' o o' p hj _ hd
    obtain ⟨q, -, rfl⟩ := memj j o hj; cases hd
  · intro o ho p hd; rw [nodef o ho] at hd; cases hd
  · intro o ho hd; rw [nodef o ho] at hd; cases hd
  · intro j o i hj h; obtain ⟨q, -, rfl⟩ := memj j o hj; cases h
  · intro c
    have : nScratch c (retOpsC ns).toArray.toList = 0 := by
      unfold nScratch
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro o ho; obtain ⟨q, -, rfl⟩ := mem o ho; simp [scratch]
    omega
  · have : (retOpsC ns).toArray.toList.filter (·.kind == .def) = [] := by
      rw [List.filter_eq_nil_iff]; intro o ho; simp [nodef o ho]
    rw [this]; exact List.nodup_nil
  · intro us _ o ho
    obtain ⟨q, hq, rfl⟩ := mem o ho
    exact ⟨q.2.2, rfl, (argRegC_facts (hr q hq)).2.2⟩

/-- **An `Args` of class-matched, distinct argument registers and distinct vregs** meets
`SpillInstOk`. -/
theorem spillInstOk_argsC {ns : List (Nat × RegClass × Reg)} (hr : ∀ q ∈ ns, ArgRegC q.2.1 q.2.2)
    (hnd : (ns.map (·.2.2)).Nodup) (hv : (ns.map (·.1)).Nodup) :
    SpillInstOk (.args (argPairsC ns)) := by
  have mem : ∀ o ∈ (argOpsC ns).toArray.toList, ∃ q ∈ ns,
      o = ⟨q.1, q.2.1, .def, .late, .fixed q.2.2⟩ := by
    intro o ho
    simp only [argOpsC, List.toList_toArray, List.mem_map] at ho
    obtain ⟨q, hq, rfl⟩ := ho
    exact ⟨q, hq, rfl⟩
  have isdef : ∀ o ∈ (argOpsC ns).toArray.toList, o.kind = .def := by
    intro o ho; obtain ⟨q, -, rfl⟩ := mem o ho; rfl
  have hcl : (MInst.args (argPairsC ns)).clobbers = [] := rfl
  refine ⟨_, operands_argsC ns, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro o ho h; obtain ⟨q, -, rfl⟩ := mem o ho; cases h
  · intro o ho hu; rw [isdef o ho] at hu; cases hu
  · intro o ho p h; obtain ⟨q, hq, rfl⟩ := mem o ho
    cases h
    have := argRegC_facts (hr q hq)
    exact ⟨this.1, this.2.1⟩
  · intro o ho o' _ p hu _ _ _; rw [isdef o ho] at hu; cases hu
  · intro j j' o o' p hj hj' _ _ hc hc'
    simp only [argOpsC, List.toList_toArray, List.getElem?_map, Option.map_eq_some_iff] at hj hj'
    obtain ⟨q, hq, rfl⟩ := hj
    obtain ⟨q', hq', rfl⟩ := hj'
    simp only [Constraint.fixed.injEq] at hc hc'
    have e1 : (ns.map (·.2.2))[j]? = some p := by simp [hq, hc]
    have e2 : (ns.map (·.2.2))[j']? = some p := by simp [hq', hc']
    exact nodup_getElem?_inj hnd e1 e2
  · intro o _ p _ _; rw [hcl]; exact List.not_mem_nil
  · intro o ho _ hp; obtain ⟨q, -, rfl⟩ := mem o ho; cases hp
  · intro j o i hj h
    obtain ⟨q, -, rfl⟩ := mem o (List.mem_of_getElem? hj); cases h
  · intro c
    have : nScratch c (argOpsC ns).toArray.toList = 0 := by
      unfold nScratch
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro o ho; obtain ⟨q, -, rfl⟩ := mem o ho; simp [scratch]
    omega
  · have : (argOpsC ns).toArray.toList.filter (·.kind == .def) = argOpsC ns := by
      rw [List.toList_toArray, List.filter_eq_self]; intro o ho; simp [isdef o (by simpa using ho)]
    rw [this]
    simpa [argOpsC, Function.comp_def] using hv
  · intro us h; cases h

theorem retPairs_eq_argPairsC (ns : List (Nat × Reg)) :
    retPairs ns = argPairsC (ns.map fun q => (q.1, RegClass.int, q.2)) := by
  simp [retPairs, argPairsC, Function.comp_def]

/-- The integer `spillInstOk_rets` is an instance of `spillInstOk_retsC`. -/
theorem spillInstOk_rets_of_C {ns : List (Nat × Reg)} (hr : ∀ q ∈ ns, ∃ k, k < 8 ∧ q.2 = .x k)
    (hnd : (ns.map (·.2)).Nodup) : SpillInstOk (.rets (retPairs ns)) := by
  rw [retPairs_eq_argPairsC]
  refine spillInstOk_retsC (fun q hq => ?_) (by simpa [Function.comp_def] using hnd)
  simp only [List.mem_map] at hq
  obtain ⟨q0, hq0, rfl⟩ := hq
  exact retRegC_argRegC (.inl ⟨rfl, hr q0 hq0⟩)

end Backend.Proof.Spill

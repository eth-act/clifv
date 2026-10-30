import FV.Backend.Proof.SpillLocal
import FV.E2E.RegLevelPush

/-!
# `SpillInstOk`, decided (S11e5 Stage C, slice 6)

`spillInstOkB i`: the operand facts `OpsOk` of `i`'s operands and clobbers (`opsOkB`) and the
`Rets` condition of `SpillInstOk`, as an executable check; `spillInstOk_of_spillInstOkB`: sound.
`ctlSpillB vc` decides the control-form premise of the typed spill theorems
(`spillLocalOk_of_pipelineT`) on a VCode (`ctlSpill_of_ctlSpillB`), so it can be checked at run
time or by `native_decide` in witnesses.
-/

namespace Backend.Proof.Spill

open Backend

/-- **`OpsOk`, decided.** -/
def opsOkB (ops : Array Operand) (clob : List Reg) : Bool :=
  let l := ops.toList
  let n := l.length
  l.all (fun o => decide (o.con ≠ .stack)) &&
  l.all (fun o => decide (o.kind = .use → o.pos = .early)) &&
  l.all (fun o => match o.con with
    | .fixed p => p.allocatable && decide (p.realClass? = some o.cls)
    | _ => true) &&
  l.all (fun o => l.all fun o' => match o.con, o'.con with
    | .fixed p, .fixed p' => decide (o.kind = .use → o'.kind = .use → p = p' → o.vreg = o'.vreg)
    | _, _ => true) &&
  (List.range n).all (fun j => (List.range n).all fun j' => match l[j]?, l[j']? with
    | some o, some o' => match o.con, o'.con with
      | .fixed p, .fixed p' => decide (o.kind = .def → o'.kind = .def → p = p' → j = j')
      | _, _ => true
    | _, _ => true) &&
  l.all (fun o => match o.con with
    | .fixed p => decide (o.kind = .def → p ∉ clob)
    | _ => true) &&
  l.all (fun o => decide (o.kind = .def → o.pos = .early → scratch o.con = true)) &&
  (List.range n).all (fun j => match l[j]? with
    | some o => match o.con with
      | .reuse i => decide (o.kind = .def) && decide (o.pos = .late) &&
          (match l[i]? with
            | some oi => decide (oi.kind = .use) && scratch oi.con && decide (oi.cls = o.cls)
            | none => false) &&
          (List.range n).all fun j' => match l[j']? with
            | some o' => decide (o'.con = .reuse i → j' = j)
            | none => true
      | _ => true
    | none => true) &&
  decide (nScratch .int l ≤ (freeRegs ops clob .int).length) &&
  decide (nScratch .float l ≤ (freeRegs ops clob .float).length) &&
  decide ((l.filter (·.kind == .def)).map (·.vreg)).Nodup

theorem idx_lt_of_getElem? {α : Type} {l : List α} {j : Nat} {a : α} (h : l[j]? = some a) : j < l.length :=
  (List.getElem?_eq_some_iff.mp h).1

/-- **Soundness of `opsOkB`.** -/
theorem opsOk_of_opsOkB {ops : Array Operand} {clob : List Reg} (h : opsOkB ops clob = true) :
    OpsOk ops clob := by
  simp only [opsOkB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9i⟩, h9f⟩, h10⟩ := h
  refine ⟨fun o ho => of_decide_eq_true (h1 o ho), fun o ho => of_decide_eq_true (h2 o ho),
    fun o ho p hp => ?_, fun o ho o' ho' p hk hk' hp hp' => ?_,
    fun j j' o o' p hj hj' hk hk' hp hp' => ?_, fun o ho p hk hp => ?_,
    fun o ho hk hpos => of_decide_eq_true (h7 o ho) hk hpos, fun j o i hj hr => ?_, fun c => ?_,
    of_decide_eq_true h10⟩
  · have := h3 o ho
    rw [hp] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  · have := h4 o ho o' ho'
    rw [hp, hp'] at this
    exact of_decide_eq_true this hk hk' rfl
  · have := h5 j (idx_lt_of_getElem? hj) j' (idx_lt_of_getElem? hj')
    rw [hj, hj'] at this
    simp only [hp, hp'] at this
    exact of_decide_eq_true this hk hk' trivial
  · have := h6 o ho
    rw [hp] at this
    exact of_decide_eq_true this hk
  · have := h8 j (idx_lt_of_getElem? hj)
    rw [hj] at this
    simp only [hr, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨⟨⟨hk, hpos⟩, hoi⟩, hu⟩ := this
    refine ⟨hk, hpos, ?_⟩
    cases hl : ops.toList[i]? with
    | none => rw [hl] at hoi; cases hoi
    | some oi =>
      rw [hl] at hoi
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hoi
      refine ⟨oi, rfl, hoi.1.1, hoi.1.2, hoi.2, fun j' o' hj' hr' => ?_⟩
      have := List.all_eq_true.mp hu j' (List.mem_range.mpr (idx_lt_of_getElem? hj'))
      rw [hj'] at this
      exact of_decide_eq_true this hr'
  · cases c
    · exact of_decide_eq_true h9i
    · exact of_decide_eq_true h9f

/-- **`SpillInstOk`, decided.** -/
def spillInstOkB (i : MInst) : Bool :=
  match i.operands with
  | .ok ops => opsOkB ops i.clobbers && (match i with
    | .rets _ => ops.toList.all fun o => match o.con with
      | .fixed p => decide (p ∉ calleeSaved)
      | _ => false
    | _ => true)
  | .error _ => false

/-- **Soundness of `spillInstOkB`.** -/
theorem spillInstOk_of_spillInstOkB {i : MInst} (h : spillInstOkB i = true) : SpillInstOk i := by
  unfold spillInstOkB at h
  split at h
  · rename_i ops hops
    simp only [Bool.and_eq_true] at h
    refine ⟨ops, hops, opsOk_of_opsOkB h.1, fun us hus o ho => ?_⟩
    subst hus
    have := List.all_eq_true.mp h.2 o ho
    split at this
    · rename_i p hp
      exact ⟨p, hp, by simpa using this⟩
    · cases this
  · cases h

/-- The control forms of `vc` meet `SpillInstOk`, decided. -/
def ctlSpillB (vc : VCode) : Bool :=
  vc.blocks.toList.all fun vb => vb.insts.toList.all fun i => !i.isCtl || spillInstOkB i

/-- **Soundness of `ctlSpillB`**: the control-form premise of `spillLocalOk_of_pipelineT`. -/
theorem ctlSpill_of_ctlSpillB {vc : VCode} (h : ctlSpillB vc = true) :
    ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i := by
  intro vb hvb i hi hc
  have := List.all_eq_true.mp (List.all_eq_true.mp h vb hvb) i hi
  rw [hc] at this
  exact spillInstOk_of_spillInstOkB (by simpa using this)

end Backend.Proof.Spill

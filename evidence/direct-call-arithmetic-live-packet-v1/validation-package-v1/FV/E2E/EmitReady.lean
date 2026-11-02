import FV.Backend.Proof.RelaxReady

/-!
# `layoutReadyB` is complete (V6b)

`FnAsm.layoutReadyB_of`: the converse of `FnAsm.layoutReadyB_sound` — the `Prop` premises of
`emitFunc_layout_total` (labels defined once, every used label defined, every instruction
encodable, `NearOk`, size under 128 MiB) make the check pass. The totality proofs of V6b
establish the `Prop` facts; this turns them into the `Bool` the compiler's readiness check and
`backend_correct_final_total_relaxed` use.
-/

namespace Backend

theorem nearB.go_of {m : Std.HashMap Lbl Nat} :
    ∀ (L : List Line) (pc : Nat),
    (∀ (j : Nat) (i : Insn) (tr : Option Clif.TrapCode) (t : Lbl) (reach align : Int) (o : Nat),
      L[j]? = some (.ins i tr) → i.pcRelSpec? = some (t, reach, align) → t ≠ .skip →
      (∀ x, i ≠ .b x) → (tr = none → i.relaxTarget? = none) → m[t]? = some o →
      -reach ≤ (o : Int) - (pc + lineOffset L j) ∧ (o : Int) - (pc + lineOffset L j) < reach) →
    nearB.go m L pc = true
  | [], _, _ => rfl
  | ln :: L, pc, h => by
    simp only [nearB.go, Bool.and_eq_true]
    refine ⟨?_, nearB.go_of L (pc + ln.size) fun j i tr t reach align o hj hs hsk hb hrx ho => ?_⟩
    · cases ln with
      | ins i tr =>
        simp only [Line.nearAt]
        cases hs : i.pcRelSpec? with
        | none => rfl
        | some spec =>
          obtain ⟨t, reach, align⟩ := spec
          simp only [Bool.or_eq_true, beq_iff_eq]
          by_cases hsk : t = .skip
          · exact .inl (.inl (.inl hsk))
          by_cases hb : i.isB = true
          · exact .inl (.inl (.inr hb))
          by_cases hrx : (tr.isNone && i.relaxTarget?.isSome) = true
          · exact .inl (.inr hrx)
          refine .inr ?_
          cases ho : m[t]? with
          | none => rfl
          | some o =>
            have hb' : ∀ x, i ≠ .b x := by
              rintro x rfl; exact hb rfl
            have hrx' : tr = none → i.relaxTarget? = none := by
              rintro rfl
              cases hr : i.relaxTarget? with
              | none => rfl
              | some _ => simp [hr] at hrx
            have := h 0 i tr t reach align o rfl hs hsk hb' hrx' ho
            simp only [lineOffset_zero] at this
            simpa using this
      | word => rfl
      | label => rfl
    · have := h (j + 1) i tr t reach align o (by simpa using hj) hs hsk hb hrx ho
      rw [lineOffset_cons_succ] at this
      constructor <;> push_cast at this ⊢ <;> omega

theorem nearB_of {L : List Line} (h : NearOk L) : nearB L = true := by
  unfold nearB
  split
  · rename_i m hm
    exact nearB.go_of L 0 fun j i tr t reach align o hj hs hsk hb hrx ho => by
      simpa using h m hm j i tr t reach align o hj hs hsk hb hrx ho
  · rfl

/-- **Completeness of `layoutReadyB`**: the premises of `emitFunc_layout_total` make it pass. -/
theorem FnAsm.layoutReadyB_of {fa : FnAsm} (hlab : ∃ m, labelOffsets fa.lines = .ok m)
    (hdef : ∀ ln ∈ fa.lines.toList, ∀ l ∈ ln.labelsUsed, Line.label l ∈ fa.lines.toList)
    (henc : ∀ i t, Line.ins i t ∈ fa.lines.toList → i.encodable = true)
    (hnear : NearOk fa.lines.toList) (hsz : fa.size < 2 ^ 27) : fa.layoutReadyB = true := by
  obtain ⟨m, hm⟩ := hlab
  unfold FnAsm.layoutReadyB
  rw [hm]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, nearB_of hnear⟩, hsz⟩
  rw [← Array.all_toList, List.all_eq_true]
  intro ln hln
  simp only [Line.readyB, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (hdef ln hln l hl)
    simp [labelOffsets_label hm hj]
  · cases ln with
    | ins i t => exact henc i t hln
    | word => rfl
    | label => rfl

end Backend

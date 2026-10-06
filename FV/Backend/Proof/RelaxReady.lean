import FV.Backend.Proof.RelaxLayout

/-!
# M6: a decidable layout-readiness check

`FnAsm.layoutReadyB` packages the premises of `emitFunc_layout_total` as one `Bool` (linear
in the lines, with `Std.HashMap` lookups): the labels are defined once, every label operand
names a defined label, every instruction's non-label operands encode, the PC-relative forms
relaxation does not handle reach their labels (`nearB`), and the function is under 128 MiB.

* `nearB_sound`, `FnAsm.layoutReadyB_sound`: the checks imply the `Prop` premises.
* `emitFunc_layout_ready`: a function `emitFunc` produced that passes the check lays out.
* `emitFunc_of_emitPre`: `emitFunc` succeeds when `emitPre` does.
-/

namespace Backend

/-- Whether `i` is an unconditional `b` (which reaches ±128 MiB). -/
def Insn.isB : Insn → Bool
  | .b _ => true
  | _ => false

/-- A line at byte offset `pc` satisfies `NearOk`'s condition under the label map `m`. -/
def Line.nearAt (m : Std.HashMap Lbl Nat) (ln : Line) (pc : Nat) : Bool :=
  match ln with
  | .ins i tr =>
    match i.pcRelSpec? with
    | some (t, reach, _) =>
      t == .skip || i.isB || (tr.isNone && i.relaxTarget?.isSome) ||
        match m[t]? with
        | some o => decide (-reach ≤ (o : Int) - pc ∧ (o : Int) - pc < reach)
        | none => true
    | none => true
  | _ => true

/-- `nearB` from byte offset `pc` under the label map `m`. -/
def nearB.go (m : Std.HashMap Lbl Nat) : List Line → Nat → Bool
  | [], _ => true
  | ln :: rest, pc => ln.nearAt m pc && go m rest (pc + ln.size)

/-- Decidable `NearOk`. -/
def nearB (L : List Line) : Bool :=
  match labelOffsets.go L 0 {} with
  | .ok m => nearB.go m L 0
  | .error _ => true

private theorem nearB.go_sound {m : Std.HashMap Lbl Nat} :
    ∀ (L : List Line) (pc : Nat), nearB.go m L pc = true →
    ∀ (j : Nat) (i : Insn) (tr : Option Clif.TrapCode) (t : Lbl) (reach align : Int) (o : Nat),
    L[j]? = some (.ins i tr) → i.pcRelSpec? = some (t, reach, align) → t ≠ .skip →
    (∀ x, i ≠ .b x) → (tr = none → i.relaxTarget? = none) → m[t]? = some o →
    -reach ≤ (o : Int) - (pc + lineOffset L j) ∧ (o : Int) - (pc + lineOffset L j) < reach
  | [], _, _, j, _, _, _, _, _, _, hj, _, _, _, _, _ => by simp at hj
  | ln :: L, pc, h, j, i, tr, t, reach, align, o, hj, hs, hsk, hb, hrx, ho => by
    simp only [nearB.go, Bool.and_eq_true] at h
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      have hib : i.isB = false := by
        cases i <;> simp only [Insn.isB]
        exact absurd rfl (hb _)
      have hnr : (tr.isNone && i.relaxTarget?.isSome) = false := by
        cases tr
        · simp [hrx rfl]
        · rfl
      have hsk' : (t == Lbl.skip) = false := by simpa using hsk
      have h1 := h.1
      simp only [Line.nearAt, hs, hsk', hib, hnr, ho, Bool.false_or, decide_eq_true_eq] at h1
      simpa using h1
    | succ j =>
      have := nearB.go_sound L (pc + ln.size) h.2 j i tr t reach align o (by simpa using hj)
        hs hsk hb hrx ho
      rw [lineOffset_cons_succ]
      constructor <;> push_cast at this ⊢ <;> omega

theorem nearB_sound {L : List Line} (h : nearB L = true) : NearOk L := by
  intro m hm j i tr t reach align o hj hs hsk hb hrx ho
  simp only [nearB, hm] at h
  simpa using nearB.go_sound L 0 h j i tr t reach align o hj hs hsk hb hrx ho

/-- A line's label operands are defined in `m` and its non-label operands encode. -/
def Line.readyB (m : Std.HashMap Lbl Nat) (ln : Line) : Bool :=
  ln.labelsUsed.all (fun l => m[l]?.isSome) &&
    match ln with
    | .ins i _ => i.encodable
    | _ => true

/-- The premises of `emitFunc_layout_total` as one check. -/
def FnAsm.layoutReadyB (fa : FnAsm) : Bool :=
  match labelOffsets fa.lines with
  | .ok m => fa.lines.all (·.readyB m) && nearB fa.lines.toList && decide (fa.size < 2 ^ 27)
  | .error _ => false

theorem FnAsm.layoutReadyB_sound {fa : FnAsm} (h : fa.layoutReadyB = true) :
    (∃ m, labelOffsets fa.lines = .ok m) ∧
    (∀ ln ∈ fa.lines.toList, ∀ l ∈ ln.labelsUsed, Line.label l ∈ fa.lines.toList) ∧
    (∀ i t, Line.ins i t ∈ fa.lines.toList → i.encodable = true) ∧
    NearOk fa.lines.toList ∧ fa.size < 2 ^ 27 := by
  unfold FnAsm.layoutReadyB at h
  split at h
  · rename_i m hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hall, hnear⟩, hsz⟩ := h
    have hall' : ∀ ln ∈ fa.lines.toList, ln.readyB m = true := by
      intro ln hln
      rw [← Array.all_toList, List.all_eq_true] at hall
      exact hall ln hln
    refine ⟨⟨m, hm⟩, ?_, ?_, nearB_sound hnear, hsz⟩
    · intro ln hln l hl
      have := hall' ln hln
      simp only [Line.readyB, Bool.and_eq_true, List.all_eq_true] at this
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (this.1 l hl)
      obtain ⟨j, hj, -⟩ := (labelOffsets_spec hm l o).mp ho
      exact List.mem_of_getElem? hj
    · intro i t hit
      have := hall' _ hit
      simp only [Line.readyB, Bool.and_eq_true] at this
      exact this.2
  · simp at h

/-- **Layout succeeds** for a function `emitFunc` produced that passes `layoutReadyB`. -/
theorem emitFunc_layout_ready {k : Nat} {af : AFunc} {fa : FnAsm} (he : emitFunc k af = .ok fa)
    (h : fa.layoutReadyB = true) : ∃ fb, fa.layout = .ok fb := by
  obtain ⟨hlab, hdef, henc, hnear, hsz⟩ := FnAsm.layoutReadyB_sound h
  exact emitFunc_layout_total he hlab hdef henc hnear hsz

private theorem forIn_except_ne {α β : Type} {f : α → β → Except String (ForInStep β)}
    (hf : ∀ a b, ∃ b', f a b = .ok (.yield b')) :
    ∀ (L : List α) (b : β) (e : String), forIn L b f ≠ .error e
  | [], _, _ => nofun
  | a :: L, b, e => by
    obtain ⟨b', hb'⟩ := hf a b
    simp only [List.forIn_cons, hb', bind, Except.bind]
    exact forIn_except_ne hf L b' e

/-- `emitFunc` fails only if `emitPre` does (its loop over the lines never throws). -/
theorem emitFunc_of_emitPre {k : Nat} {af : AFunc} {pre : Array Line}
    (h : emitPre k af = .ok pre) : ∃ fa, emitFunc k af = .ok fa := by
  unfold emitFunc
  simp only [h, bind, Except.bind]
  rw [List.forIn_toArray]
  split
  · rename_i e he
    refine (forIn_except_ne ?_ _ _ _ he).elim
    intro ln s
    cases ln with
    | ins i t => cases t <;> exact ⟨_, rfl⟩
    | word => exact ⟨_, rfl⟩
    | label => exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

end Backend

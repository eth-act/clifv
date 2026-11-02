import FV.Backend.Asm

/-!
# The lines of Cranelift's callee-save pushes and pops (#479)

`pushLines`/`popLines` (`gen_clobber_save`/`gen_clobber_restore`) emit only plain
instruction lines: a pre-indexed `str`/`stp` (x or d) per push and a post-indexed `ldr`/`ldp`
per pop. Line-wise facts about the prologue and epilogue (`nearOkB`, relocation freedom, ...)
follow from these shapes.
-/

namespace Backend

/-- The instruction of a push line. -/
def PushInsn (int : Bool) (i : Insn) : Prop :=
  ∃ a b, i = (if int then .store .store64 a (.spPreIndexed (-16))
      else .fpuStore .size64 a (.spPreIndexed (-16))) ∨
    i = (if int then .stp a b (.spPreIndexed (-16)) else .fpuStoreP .size64 a b (.spPreIndexed (-16)))

/-- The instruction of a pop line. -/
def PopInsn (int : Bool) (i : Insn) : Prop :=
  ∃ a b, i = (if int then .load .uload64 a (.spPostIndexed 16)
      else .fpuLoad .size64 a (.spPostIndexed 16)) ∨
    i = (if int then .ldp a b (.spPostIndexed 16) else .fpuLoadP .size64 a b (.spPostIndexed 16))

theorem mem_pushLines {int : Bool} {rs : List Reg} {ln : Line} (h : ln ∈ pushLines int rs) :
    ∃ i, ln = .ins i none ∧ PushInsn int i := by
  unfold pushLines at h
  generalize pairsOf rs = q at h
  obtain ⟨ps, o⟩ := q
  simp only [List.mem_append, List.mem_map, List.mem_reverse] at h
  rcases h with h | ⟨⟨a, b⟩, -, rfl⟩
  · cases o with
    | none => cases h
    | some r =>
      simp only [List.mem_singleton] at h
      exact ⟨_, h, r, r, .inl rfl⟩
  · exact ⟨_, rfl, a, b, .inr rfl⟩

theorem mem_popLines {int : Bool} {rs : List Reg} {ln : Line} (h : ln ∈ popLines int rs) :
    ∃ i, ln = .ins i none ∧ PopInsn int i := by
  unfold popLines at h
  generalize pairsOf rs = q at h
  obtain ⟨ps, o⟩ := q
  simp only [List.mem_append, List.mem_map] at h
  rcases h with ⟨⟨a, b⟩, -, rfl⟩ | h
  · exact ⟨_, rfl, a, b, .inr rfl⟩
  · cases o with
    | none => cases h
    | some r =>
      simp only [List.mem_singleton] at h
      exact ⟨_, h, r, r, .inl rfl⟩

/-- A line of an `sp` adjustment: the `add`/`sub` (immediate or through `x16`) or a line of the
`x16` constant. -/
theorem mem_spAdjLines {sub : Bool} {size : Nat} {ln : Line} (h : ln ∈ spAdjLines sub size) :
    (∃ i, Imm12.ofNat? size = some i ∧
      ln = .ins (.aluImm12 (if sub then .sub else .add) true .sp .sp i)) ∨
    ln ∈ loadConst64 (.x 16) size ∨
    ln = .ins (.aluRRRExtend (if sub then .sub else .add) true .sp .sp (.x 16) .uxtx) := by
  unfold spAdjLines at h
  split at h
  · cases h
  · split at h
    · rename_i i hi
      simp only [List.mem_singleton] at h
      exact .inl ⟨i, hi, h⟩
    · rcases List.mem_append.1 h with h | h
      · exact .inr (.inl h)
      · simp only [List.mem_singleton] at h
        exact .inr (.inr h)

end Backend

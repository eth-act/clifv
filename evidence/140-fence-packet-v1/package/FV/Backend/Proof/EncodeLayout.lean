import FV.Backend.Proof.EncodeBranch

/-!
# M5: layout correctness (`FnAsm.layout`)

Notation: `L = f.lines.toList`, `off j = lineOffset L j` (the byte offset of line `j`: the
sizes of the lines before it; instructions and jump-table words are 4 bytes, labels 0).

* `labelOffsets_spec`: the label map sends `l` to `o` iff some line `j` is `.label l` at
  `off j = o`; every label line of `l` is at that offset (labels are unique, else layout fails).
* `FnAsm.layout_word`: every code line `j` (instruction or jump-table word) is encoded at its
  own offset (`Line.encodeAt m (off j)`) and is word `off j / 4` of the output; conversely
  every output word is such a line (`FnAsm.layout_word_inv`); `4 * words.size = f.size`.
* `FnAsm.layout_insn`: word `off j / 4` decodes to exactly `toArmInst` of instruction `j`
  (with `decode_encode`).
* `FnAsm.layout_branch`: for a label-relative instruction (b, b.cond, cbz/cbnz, tbz/tbnz,
  adr) the decoded PC offset is `off j' - off j` for the target's label line `j'`, within the
  form's reach (the branch-range policy is a precondition of a successful layout).
* `FnAsm.layout_jumpTable`: a jump-table word is `off target - off base` (signed 32-bit).
* `FnAsm.layout_relocs`, `FnAsm.layout_traps`: relocation records and trap sites are exactly
  the instructions that carry a relocatable operand / a trap code, at their offsets; the trap
  table equals `emitFunc`'s (`f.traps`), and each trap site's word decodes to its instruction
  (for Cranelift traps, `udf #0xc11f`).
-/

namespace Backend

open Arm

/-! ## Offsets -/

@[simp] theorem lineOffset_zero (L : List Line) : lineOffset L 0 = 0 := by simp [lineOffset]

@[simp] theorem lineOffset_nil (j : Nat) : lineOffset [] j = 0 := by simp [lineOffset]

@[simp] theorem lineOffset_cons_succ (ln : Line) (L : List Line) (j : Nat) :
    lineOffset (ln :: L) (j + 1) = ln.size + lineOffset L j := by
  simp [lineOffset, List.take_succ_cons]

theorem Line.size_of_isLabel {ln : Line} : ln.isLabel = true → ln.size = 0 := by
  cases ln <;> simp [Line.isLabel, Line.size]

theorem Line.size_of_not_isLabel {ln : Line} : ln.isLabel = false → ln.size = 4 := by
  cases ln <;> simp [Line.isLabel, Line.size]

theorem codeLines_cons (ln : Line) (L : List Line) :
    codeLines (ln :: L) = if ln.isLabel then codeLines L else ln :: codeLines L := by
  cases h : ln.isLabel <;> simp [codeLines, h]

/-- A code line `j` is code word `off j / 4`. -/
theorem codeLines_of_line {L : List Line} {j : Nat} {ln : Line} (hj : L[j]? = some ln)
    (hl : ln.isLabel = false) :
    ∃ k, (codeLines L)[k]? = some ln ∧ lineOffset L j = 4 * k := by
  induction L generalizing j with
  | nil => simp at hj
  | cons ln0 L ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact ⟨0, by simp [codeLines_cons, hl], by simp⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      obtain ⟨k, hk, ho⟩ := ih hj
      rw [lineOffset_cons_succ, ho, codeLines_cons]
      cases h0 : ln0.isLabel
      · exact ⟨k + 1, by simpa using hk, by rw [Line.size_of_not_isLabel h0]; omega⟩
      · exact ⟨k, by simpa using hk, by rw [Line.size_of_isLabel h0]; omega⟩

/-- Code word `k` is a code line at offset `4 * k`. -/
theorem line_of_codeLines {L : List Line} {k : Nat} {ln : Line}
    (hk : (codeLines L)[k]? = some ln) :
    ∃ j, L[j]? = some ln ∧ ln.isLabel = false ∧ lineOffset L j = 4 * k := by
  induction L generalizing k with
  | nil => simp [codeLines] at hk
  | cons ln0 L ih =>
    rw [codeLines_cons] at hk
    cases h0 : ln0.isLabel
    · simp only [h0, Bool.false_eq_true, ite_false] at hk
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        exact ⟨0, rfl, h0, by simp⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at hk
        obtain ⟨j, hj, hl, ho⟩ := ih hk
        exact ⟨j + 1, by simpa using hj, hl, by
          rw [lineOffset_cons_succ, ho, Line.size_of_not_isLabel h0]; omega⟩
    · simp only [h0, ite_true] at hk
      obtain ⟨j, hj, hl, ho⟩ := ih hk
      exact ⟨j + 1, by simpa using hj, hl, by
        rw [lineOffset_cons_succ, ho, Line.size_of_isLabel h0]; omega⟩

/-! ## Labels -/

theorem labelOffsets_go_mono {L : List Line} {off : Nat} {m0 m : Std.HashMap Lbl Nat}
    (h : labelOffsets.go L off m0 = .ok m) {l : Lbl} {o : Nat} (hl : m0[l]? = some o) :
    m[l]? = some o := by
  induction L generalizing off m0 with
  | nil => simp only [labelOffsets.go, pure, Except.pure, Except.ok.injEq] at h; subst h; exact hl
  | cons ln L ih =>
    simp only [labelOffsets.go] at h
    split at h
    · rename_i l'
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · rename_i hc
        refine ih h ?_
        rw [Std.HashMap.getElem?_insert]
        split
        · rename_i heq
          have : l' = l := by simpa using heq
          subst this
          simp [Std.HashMap.contains_eq_isSome_getElem?, hl] at hc
        · exact hl
    · exact ih h hl

theorem labelOffsets_go_label {L : List Line} {off : Nat} {m0 m : Std.HashMap Lbl Nat}
    (h : labelOffsets.go L off m0 = .ok m) {j : Nat} {l : Lbl}
    (hj : L[j]? = some (.label l)) : m[l]? = some (off + lineOffset L j) := by
  induction L generalizing off m0 j with
  | nil => simp at hj
  | cons ln L ih =>
    simp only [labelOffsets.go] at h
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp only at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · exact labelOffsets_go_mono h (by simp)
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      rw [lineOffset_cons_succ]
      split at h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · rw [ih h hj, Line.size, Nat.zero_add]
      · rw [ih h hj, Nat.add_assoc]

theorem labelOffsets_go_inv {L : List Line} {off : Nat} {m0 m : Std.HashMap Lbl Nat}
    (h : labelOffsets.go L off m0 = .ok m) {l : Lbl} {o : Nat} (hl : m[l]? = some o) :
    m0[l]? = some o ∨ ∃ j, L[j]? = some (.label l) ∧ off + lineOffset L j = o := by
  induction L generalizing off m0 with
  | nil =>
    simp only [labelOffsets.go, pure, Except.pure, Except.ok.injEq] at h; subst h; exact .inl hl
  | cons ln L ih =>
    simp only [labelOffsets.go] at h
    split at h
    · rename_i l'
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · rcases ih h with h1 | ⟨j, hj, ho⟩
        · rw [Std.HashMap.getElem?_insert] at h1
          split at h1
          · rename_i heq
            have : l' = l := by simpa using heq
            subst this
            simp only [Option.some.injEq] at h1
            exact .inr ⟨0, by simp, by simp [h1]⟩
          · exact .inl h1
        · exact .inr ⟨j + 1, by simpa using hj, by simp [Line.size, ho]⟩
    · rcases ih h with h1 | ⟨j, hj, ho⟩
      · exact .inl h1
      · exact .inr ⟨j + 1, by simpa using hj, by rw [lineOffset_cons_succ]; omega⟩

/-- The label map: `l ↦ o` iff a line `.label l` is at offset `o`. -/
theorem labelOffsets_spec {lines : Array Line} {m : Std.HashMap Lbl Nat}
    (h : labelOffsets lines = .ok m) (l : Lbl) (o : Nat) :
    m[l]? = some o ↔
      ∃ j, lines.toList[j]? = some (.label l) ∧ lineOffset lines.toList j = o := by
  constructor
  · intro hl
    rcases labelOffsets_go_inv h hl with h1 | ⟨j, hj, ho⟩
    · simp at h1
    · exact ⟨j, hj, by simpa using ho⟩
  · rintro ⟨j, hj, rfl⟩
    simpa using labelOffsets_go_label h hj

/-- Every label line of `l` is at the offset the label map gives. -/
theorem labelOffsets_label {lines : Array Line} {m : Std.HashMap Lbl Nat}
    (h : labelOffsets lines = .ok m) {j : Nat} {l : Lbl}
    (hj : lines.toList[j]? = some (.label l)) : m[l]? = some (lineOffset lines.toList j) := by
  simpa using labelOffsets_go_label h hj

/-! ## Encoding the code lines -/

theorem encodeCode_spec {ctx : Nat → Line → String → String} {lbl : Lbl → Option Nat}
    {code : List Line} {acc ws : Array (BitVec 32)} (h : encodeCode ctx lbl code acc = .ok ws) :
    ws.size = acc.size + code.length ∧ (∀ k, k < acc.size → ws[k]? = acc[k]?) ∧
      ∀ k ln, code[k]? = some ln →
        ∃ w, ln.encodeAt lbl (4 * (acc.size + k)) = .ok w ∧ ws[acc.size + k]? = some w := by
  induction code generalizing acc with
  | nil =>
    simp only [encodeCode, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | cons ln code ih =>
    simp only [encodeCode] at h
    split at h
    · rename_i w hw
      obtain ⟨h1, h2, h3⟩ := ih h
      simp only [Array.size_push] at h1 h2 h3
      refine ⟨by simp [h1]; omega, fun k hk => ?_, fun k ln' hk => ?_⟩
      · rw [h2 k (by omega), Array.getElem?_push_lt hk, Array.getElem?_eq_getElem hk]
      · cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          refine ⟨w, by simpa using hw, ?_⟩
          rw [Nat.add_zero, h2 acc.size (by omega), Array.getElem?_push_size]
        | succ k =>
          simp only [List.getElem?_cons_succ] at hk
          obtain ⟨w', hw', hw''⟩ := h3 k ln' hk
          exact ⟨w', by rw [← hw']; congr 1; omega, by rw [← hw'']; congr 1; omega⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## Relocations and trap sites of the code lines -/

theorem mem_codeRelocs {code : List Line} {r : Reloc} :
    r ∈ codeRelocs code ↔ ∃ k i t, code[k]? = some (.ins i t) ∧
      i.reloc? = some (r.type, r.sym, r.addend) ∧ r.offset = 4 * k := by
  simp only [codeRelocs, List.mem_filterMap, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨ln, k⟩, hk, hr⟩
    cases ln with
    | ins i t =>
      simp only [Option.map_eq_some_iff] at hr
      obtain ⟨⟨type, sym, addend⟩, hi, rfl⟩ := hr
      exact ⟨k, i, t, hk, hi, rfl⟩
    | word => simp at hr
    | label => simp at hr
  · rintro ⟨k, i, t, hk, hi, ho⟩
    refine ⟨(.ins i t, k), hk, ?_⟩
    cases r
    simp_all

theorem mem_codeTraps {code : List Line} {s : TrapSite} :
    s ∈ codeTraps code ↔ ∃ k i, code[k]? = some (.ins i (some s.code)) ∧ s.offset = 4 * k := by
  simp only [codeTraps, List.mem_filterMap, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨ln, k⟩, hk, hs⟩
    cases ln with
    | ins i t =>
      cases t with
      | none => simp at hs
      | some c =>
        simp only [Option.some.injEq] at hs
        subst hs
        exact ⟨k, i, hk, rfl⟩
    | word => simp at hs
    | label => simp at hs
  · rintro ⟨k, i, hk, ho⟩
    refine ⟨(.ins i (some s.code), k), hk, ?_⟩
    cases s
    simp_all

theorem sField_ok {what : String} {n : Nat} {i : Int} {v : BitVec (n + 1)}
    (h : sField what (n + 1) i = .ok v) : v.toInt = i := by
  unfold sField at h
  split at h
  · rename_i hr
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact bmod_ofInt_toInt n i (by simpa using hr.1) (by simpa using hr.2)
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## `FnAsm.layout` -/

theorem FnAsm.layout_unfold {f : FnAsm} {b : FnBin} (h : f.layout = .ok b) :
    ∃ m ctx, labelOffsets f.lines = .ok m ∧
      encodeCode ctx (m[·]?) (codeLines f.lines.toList) #[] = .ok b.words ∧
      4 * b.words.size = f.size ∧
      b.relocs = codeRelocs (codeLines f.lines.toList) ∧
      b.traps = codeTraps (codeLines f.lines.toList) ∧ b.traps = f.traps := by
  unfold FnAsm.layout at h
  simp only [bind_eq_ok] at h
  obtain ⟨m, hm, ws, hws, hb⟩ := h
  have hm' : labelOffsets f.lines = .ok m := by
    cases hl : labelOffsets f.lines <;> simp_all [Except.mapError]
  by_cases h1 : 4 * ws.size = f.size
  · by_cases h2 : codeTraps (codeLines f.lines.toList) = f.traps
    · simp only [h1, h2, bne_self_eq_false, Bool.false_eq_true, ite_false, pure, Except.pure,
        Except.ok.injEq] at hb
      subst hb
      exact ⟨m, _, hm', hws, h1, rfl, h2.symm, rfl⟩
    · simp [h1, h2, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hb
  · simp [h1, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hb

/-- A successful layout resolved the labels. -/
theorem FnAsm.layout_labelOffsets {f : FnAsm} {b : FnBin} (h : f.layout = .ok b) :
    ∃ m, labelOffsets f.lines = .ok m := by
  obtain ⟨m, _, hm, _⟩ := FnAsm.layout_unfold h
  exact ⟨m, hm⟩

theorem FnAsm.layout_size {f : FnAsm} {b : FnBin} (h : f.layout = .ok b) :
    4 * b.words.size = f.size ∧ b.words.size = (codeLines f.lines.toList).length := by
  obtain ⟨m, _, _, hw, hs, _⟩ := FnAsm.layout_unfold h
  exact ⟨hs, by simpa using (encodeCode_spec hw).1⟩

/-- **Placement.** Every code line `j` (instruction or jump-table word) is encoded at its own
offset `off j` (a multiple of 4) and is word `off j / 4` of the function. -/
theorem FnAsm.layout_word {f : FnAsm} {b : FnBin} {m : Std.HashMap Lbl Nat}
    (h : f.layout = .ok b) (hm : labelOffsets f.lines = .ok m) {j : Nat} {ln : Line}
    (hj : f.lines.toList[j]? = some ln) (hl : ln.isLabel = false) :
    lineOffset f.lines.toList j % 4 = 0 ∧
      ∃ w, ln.encodeAt (m[·]?) (lineOffset f.lines.toList j) = .ok w ∧
        b.words[lineOffset f.lines.toList j / 4]? = some w := by
  obtain ⟨m', _, hm', hw, _⟩ := FnAsm.layout_unfold h
  rw [hm] at hm'
  cases hm'
  obtain ⟨k, hk, ho⟩ := codeLines_of_line hj hl
  obtain ⟨_, _, h3⟩ := encodeCode_spec hw
  obtain ⟨w, hw1, hw2⟩ := h3 k ln hk
  simp only [List.size_toArray, List.length_nil, Nat.zero_add] at hw1 hw2
  refine ⟨by omega, w, by rw [ho]; simpa using hw1, ?_⟩
  rw [ho, Nat.mul_div_cancel_left _ (by decide)]
  simpa using hw2

/-- Conversely, every word of the function is a code line at offset `4 * k`. -/
theorem FnAsm.layout_word_inv {f : FnAsm} {b : FnBin} {m : Std.HashMap Lbl Nat}
    (h : f.layout = .ok b) (hm : labelOffsets f.lines = .ok m) {k : Nat} {w : BitVec 32}
    (hk : b.words[k]? = some w) :
    ∃ j ln, f.lines.toList[j]? = some ln ∧ ln.isLabel = false ∧
      lineOffset f.lines.toList j = 4 * k ∧ ln.encodeAt (m[·]?) (4 * k) = .ok w := by
  obtain ⟨m', _, hm', hw, _⟩ := FnAsm.layout_unfold h
  rw [hm] at hm'
  cases hm'
  obtain ⟨h1, _, h3⟩ := encodeCode_spec hw
  simp only [List.size_toArray, List.length_nil, Nat.zero_add] at h1 h3
  have hlt : k < (codeLines f.lines.toList).length := by
    have := (Array.getElem?_eq_some_iff.mp hk).1; omega
  obtain ⟨ln, hln⟩ : ∃ ln, (codeLines f.lines.toList)[k]? = some ln :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  obtain ⟨w', hw1, hw2⟩ := h3 k ln hln
  rw [hk] at hw2
  cases hw2
  obtain ⟨j, hj, hl, ho⟩ := line_of_codeLines hln
  exact ⟨j, ln, hj, hl, ho, hw1⟩

/-- **Instructions.** The word at an instruction's offset decodes to exactly the instruction
`toArmInst` specifies at that offset (M5 `decode_encode` + placement). -/
theorem FnAsm.layout_insn {f : FnAsm} {b : FnBin} {m : Std.HashMap Lbl Nat}
    (h : f.layout = .ok b) (hm : labelOffsets f.lines = .ok m) {j : Nat} {i : Insn}
    {t : Option Clif.TrapCode} (hj : f.lines.toList[j]? = some (.ins i t)) :
    lineOffset f.lines.toList j % 4 = 0 ∧
      ∃ w a, b.words[lineOffset f.lines.toList j / 4]? = some w ∧
        i.toArmInst ⟨lineOffset f.lines.toList j, (m[·]?)⟩ = .ok a ∧ decode_raw_inst w = some a := by
  obtain ⟨h4, w, hw, hk⟩ := FnAsm.layout_word h hm hj rfl
  obtain ⟨a, ha, hd⟩ := Insn.decode_encode hw
  exact ⟨h4, w, a, hk, ha, hd⟩

/-- **Label-relative operands.** For b, b.cond, cbz/cbnz, tbz/tbnz and adr at line `j` with
target `l`: the target label exists, and for every line `j'` defining `l`, the decoded
instruction's PC offset is `off j' - off j`, within the form's reach and aligned. -/
theorem FnAsm.layout_branch {f : FnAsm} {b : FnBin} {m : Std.HashMap Lbl Nat}
    (h : f.layout = .ok b) (hm : labelOffsets f.lines = .ok m) {j : Nat} {i : Insn}
    {t : Option Clif.TrapCode} (hj : f.lines.toList[j]? = some (.ins i t)) {l : Lbl}
    {reach align : Int} (hs : i.pcRelSpec? = some (l, reach, align)) (hsk : l ≠ .skip) :
    ∃ w a, b.words[lineOffset f.lines.toList j / 4]? = some w ∧ decode_raw_inst w = some a ∧
      (∃ j' : Nat, f.lines.toList[j']? = some (Line.label l)) ∧
      ∀ j' : Nat, f.lines.toList[j']? = some (.label l) →
        let d := (lineOffset f.lines.toList j' : Int) - lineOffset f.lines.toList j
        a.pcRelOffset? = some d ∧ -reach ≤ d ∧ d < reach ∧ align ∣ d := by
  obtain ⟨_, w, a, hk, ha, hd⟩ := FnAsm.layout_insn h hm hj
  obtain ⟨o, hl, hoff, h1, h2, h3⟩ := Insn.toArmInst_pcRel ha hs
  rw [Env.target_of_ne hsk] at hl
  obtain ⟨j', hj', ho⟩ := (labelOffsets_spec hm l o).mp hl
  refine ⟨w, a, hk, hd, ⟨j', hj'⟩, fun j'' hj'' => ?_⟩
  have := labelOffsets_label hm hj''
  simp only at hl hoff h1 h2 h3
  rw [hl, Option.some.injEq] at this
  subst this
  exact ⟨hoff, h1, h2, h3⟩

/-- **Jump tables.** A `.word target base` line is `off target - off base` (signed 32-bit),
for the (unique) offsets of the two labels. -/
theorem FnAsm.layout_jumpTable {f : FnAsm} {b : FnBin} {m : Std.HashMap Lbl Nat}
    (h : f.layout = .ok b) (hm : labelOffsets f.lines = .ok m) {j : Nat} {t base : Lbl}
    (hj : f.lines.toList[j]? = some (.word t base)) :
    ∃ w, b.words[lineOffset f.lines.toList j / 4]? = some w ∧
      (∃ jt jb : Nat, f.lines.toList[jt]? = some (Line.label t) ∧
        f.lines.toList[jb]? = some (Line.label base)) ∧
      ∀ jt jb : Nat, f.lines.toList[jt]? = some (.label t) → f.lines.toList[jb]? = some (.label base) →
        w.toInt = (lineOffset f.lines.toList jt : Int) - lineOffset f.lines.toList jb := by
  obtain ⟨_, w, hw, hk⟩ := FnAsm.layout_word h hm hj rfl
  simp only [Line.encodeAt] at hw
  split at hw
  · rename_i ot ob hot hob
    obtain ⟨jt, hjt, _⟩ := (labelOffsets_spec hm t ot).mp hot
    obtain ⟨jb, hjb, _⟩ := (labelOffsets_spec hm base ob).mp hob
    refine ⟨w, hk, ⟨jt, jb, hjt, hjb⟩, fun jt' jb' hjt' hjb' => ?_⟩
    have e1 := labelOffsets_label hm hjt'
    have e2 := labelOffsets_label hm hjb'
    rw [hot, Option.some.injEq] at e1
    rw [hob, Option.some.injEq] at e2
    subst e1 e2
    exact sField_ok hw
  · simp [throw, throwThe, MonadExceptOf.throw] at hw

/-- **Relocations.** The relocation records are exactly the instructions with a relocatable
operand, at their offsets (type, symbol and addend from `Insn.reloc?`). -/
theorem FnAsm.layout_relocs {f : FnAsm} {b : FnBin} (h : f.layout = .ok b) (r : Reloc) :
    r ∈ b.relocs ↔ ∃ j i t, f.lines.toList[j]? = some (.ins i t) ∧
      i.reloc? = some (r.type, r.sym, r.addend) ∧ lineOffset f.lines.toList j = r.offset := by
  obtain ⟨_, _, _, _, _, hr, _⟩ := FnAsm.layout_unfold h
  rw [hr, mem_codeRelocs]
  constructor
  · rintro ⟨k, i, t, hk, hi, ho⟩
    obtain ⟨j, hj, _, hoj⟩ := line_of_codeLines hk
    exact ⟨j, i, t, hj, hi, by omega⟩
  · rintro ⟨j, i, t, hj, hi, ho⟩
    obtain ⟨k, hk, hoj⟩ := codeLines_of_line hj rfl
    exact ⟨k, i, t, hk, hi, by omega⟩

/-- **Trap sites.** The trap table is `emitFunc`'s, and it lists exactly the instructions that
carry a trap code, at their offsets. -/
theorem FnAsm.layout_traps {f : FnAsm} {b : FnBin} (h : f.layout = .ok b) :
    b.traps = f.traps ∧ ∀ s, s ∈ b.traps ↔
      ∃ j i, f.lines.toList[j]? = some (.ins i (some s.code)) ∧
        lineOffset f.lines.toList j = s.offset := by
  obtain ⟨_, _, _, _, _, _, ht, ht'⟩ := FnAsm.layout_unfold h
  refine ⟨ht', fun s => ?_⟩
  rw [ht, mem_codeTraps]
  constructor
  · rintro ⟨k, i, hk, ho⟩
    obtain ⟨j, hj, _, hoj⟩ := line_of_codeLines hk
    exact ⟨j, i, hj, by omega⟩
  · rintro ⟨j, i, hj, ho⟩
    obtain ⟨k, hk, hoj⟩ := codeLines_of_line hj rfl
    exact ⟨k, i, hk, by omega⟩

/-- Each trap site's word decodes to its instruction (for Cranelift's traps `udf #0xc11f`,
`RES (Udf {imm16 := 0xc11f})`). -/
theorem FnAsm.layout_trap_word {f : FnAsm} {b : FnBin} {m : Std.HashMap Lbl Nat}
    (h : f.layout = .ok b) (hm : labelOffsets f.lines = .ok m) {s : TrapSite}
    (hs : s ∈ b.traps) :
    ∃ j i w a, f.lines.toList[j]? = some (.ins i (some s.code)) ∧
      lineOffset f.lines.toList j = s.offset ∧ b.words[s.offset / 4]? = some w ∧
      i.toArmInst ⟨s.offset, (m[·]?)⟩ = .ok a ∧ decode_raw_inst w = some a := by
  obtain ⟨j, i, hj, ho⟩ := ((FnAsm.layout_traps h).2 s).mp hs
  obtain ⟨_, w, a, hk, ha, hd⟩ := FnAsm.layout_insn h hm hj
  rw [ho] at hk ha
  exact ⟨j, i, w, a, hj, ho, hk, ha, hd⟩

/-- `udf #0xc11f` decodes to `UDF #0xc11f` (the model's `Trap` outcome). -/
example (env : Env) : (Insn.udf 0xc11f).toArmInst env = .ok (.RES (.Udf { imm16 := 0xc11f })) := by
  rfl

end Backend

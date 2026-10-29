module

public import FV.Backend.Encode

@[expose] public section

/-!
# M5 proof infrastructure: `decode_raw_inst ∘ armBits` per encoding class

`decode_raw_inst` (`FV/Arm/Decode.lean`) first dispatches on `op0 = i<31>` and
`op1 = i<28:25>` to a group decoder, and each group decoder is a `match_bv`: a chain of
`if (extractLsb' … i == lit) && … then some (C {f := extractLsb' … i, …}) else …`.

* `decode_raw_inst_of_*`: the top-level dispatch, under a hypothesis on `op1` (`op0` is
  case-split inside the proof, so the hypothesis is a plain bit-vector fact).
* `decode_class d g`: the uniform tactic for a goal
  `decode_raw_inst (armBits (.G (.C x))) = some (ArmInst.G (.C x)).norm` (generic in the
  structure `x`, i.e. in every field). It substitutes the encoded concatenation, rewrites
  with the dispatch lemma `d`, and unfolds the group decoder `g`. Extraction and
  concatenation-equality lemmas recover the fields and reject incompatible fixed bits.
  Remaining conditionals are split only after this normalization; their hypotheses are
  normalized in the same way. One-bit dispatch alternatives use `eq_zero_or_eq_one`.
  All proofs are kernel checked, without SAT certificates or native evaluation.
-/

namespace Backend

open Arm

theorem decode_of_armBits {a : ArmInst}
    (h : ∀ w, armBits a = w → decode_raw_inst w = some a.norm) :
    decode_raw_inst (armBits a) = some a.norm := h _ rfl

theorem decode_raw_inst_of_dpi (i : BitVec 32)
    (h : i.extractLsb' 25 4 = 8#4 ∨ i.extractLsb' 25 4 = 9#4) :
    decode_raw_inst i = decode_data_proc_imm i := by
  have h0 := BitVec.eq_zero_or_eq_one (i.extractLsb' 31 1)
  rcases h0 with h0 | h0 <;> rcases h with h | h <;> simp [decode_raw_inst, h0, h]

theorem decode_raw_inst_of_br (i : BitVec 32)
    (h : i.extractLsb' 25 4 = 10#4 ∨ i.extractLsb' 25 4 = 11#4) :
    decode_raw_inst i = decode_branch i := by
  have h0 := BitVec.eq_zero_or_eq_one (i.extractLsb' 31 1)
  rcases h0 with h0 | h0 <;> rcases h with h | h <;> simp [decode_raw_inst, h0, h]

theorem decode_raw_inst_of_dpr (i : BitVec 32)
    (h : i.extractLsb' 25 4 = 13#4 ∨ i.extractLsb' 25 4 = 5#4) :
    decode_raw_inst i = decode_data_proc_reg i := by
  have h0 := BitVec.eq_zero_or_eq_one (i.extractLsb' 31 1)
  rcases h0 with h0 | h0 <;> rcases h with h | h <;> simp [decode_raw_inst, h0, h]

theorem decode_raw_inst_of_dpsfp (i : BitVec 32)
    (h : i.extractLsb' 25 4 = 7#4 ∨ i.extractLsb' 25 4 = 15#4) :
    decode_raw_inst i = decode_data_proc_sfp i := by
  have h0 := BitVec.eq_zero_or_eq_one (i.extractLsb' 31 1)
  rcases h0 with h0 | h0 <;> rcases h with h | h <;> simp [decode_raw_inst, h0, h]

theorem decode_raw_inst_of_ldst (i : BitVec 32)
    (h : i.extractLsb' 25 4 = 4#4 ∨ i.extractLsb' 25 4 = 12#4 ∨ i.extractLsb' 25 4 = 6#4 ∨
      i.extractLsb' 25 4 = 14#4) :
    decode_raw_inst i = decode_ldst_inst i := by
  have h0 := BitVec.eq_zero_or_eq_one (i.extractLsb' 31 1)
  rcases h0 with h0 | h0 <;> rcases h with h | h | h | h <;> simp [decode_raw_inst, h0, h]

theorem decode_raw_inst_of_reserved (i : BitVec 32)
    (h : i.extractLsb' 31 1 = 0#1 ∧ i.extractLsb' 25 4 = 0#4) :
    decode_raw_inst i = decode_reserved i := by
  simp [decode_raw_inst, h.1, h.2]

/-- Compare an encoded concatenation by its high and low fields. -/
private theorem append_eq_split {m n : Nat} (a : BitVec m) (b : BitVec n)
    (c : BitVec (m + n)) :
    (a ++ b = c) ↔ a = c.extractLsb' n m ∧ b = c.extractLsb' 0 n := by
  constructor
  · intro h
    constructor
    · simpa only [BitVec.extractLsb'_append_eq_left] using
        congrArg (BitVec.extractLsb' n m) h
    · simpa only [BitVec.extractLsb'_append_eq_right] using
        congrArg (BitVec.extractLsb' 0 n) h
  · rintro ⟨rfl, rfl⟩
    exact BitVec.extractLsb'_append_extractLsb'

-- Concrete nonzero fields witness the concatenation comparison.
example : 1#2 = (6#4).extractLsb' 2 2 ∧ 2#2 = (6#4).extractLsb' 0 2 :=
  (append_eq_split 1#2 2#2 6#4).mp (by decide)

/-- See the module docstring. `d`: dispatch lemma, `g`: group decoder. -/
macro "decode_class " d:ident g:ident : tactic => do
  let fields ← `(tactic| (
    repeat' first
    | (rw [BitVec.extractLsb'_append_eq_ite] <;> simp)
    | (rw [append_eq_split] <;> simp)
    all_goals try exact BitVec.eq_zero_or_eq_one _
    all_goals repeat' split
    all_goals (
      repeat' first
      | (rw [BitVec.extractLsb'_append_eq_ite] at * <;> simp_all)
      | (rw [append_eq_split] at * <;> simp_all)
      all_goals exact BitVec.eq_zero_or_eq_one _)))
  `(tactic| (
    set_option maxHeartbeats 4000000 in
    set_option maxRecDepth 100000 in
    (refine decode_of_armBits fun w hw => ?_
     simp only [armBits] at hw
     subst w
     simp only [ArmInst.norm]
     rw [$d:ident _ (by $fields:tactic)]
     simp only [$g:ident]
     all_goals $fields:tactic)))

end Backend

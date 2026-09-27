import FV.Backend.Encode

/-!
# M5 proof infrastructure: `decode_raw_inst ∘ armBits` per encoding class

`decode_raw_inst` (`FV/Arm/Decode.lean`) first dispatches on `op0 = i<31>` and
`op1 = i<28:25>` to a group decoder, and each group decoder is a `match_bv`: a chain of
`if (extractLsb' … i == lit) && … then some (C {f := extractLsb' … i, …}) else …`.

* `decode_raw_inst_of_*`: the top-level dispatch, under a hypothesis on `op1` (`op0` is
  case-split inside the proof, so the hypothesis is a plain bit-vector fact).
* `decode_class d g`: the uniform tactic for a goal
  `decode_raw_inst (armBits (.G (.C x))) = some (ArmInst.G (.C x)).norm` (generic in the
  structure `x`, i.e. in every field). It names the word `w` with `hw : armBits … = w`
  (so no term is duplicated), rewrites with the dispatch lemma `d` (its side condition by
  `bv_decide` from `hw`), unfolds the group decoder `g`, splits every `if`, and closes each
  branch: a pattern that must not match (or must match) is refuted by `bv_decide` from its
  condition and `hw`; the matching branch is closed by `congr` and `bv_decide` per field
  (`extractLsb' lo n w = x.f`). All reasoning is about one 32-bit word, so each `bv_decide`
  call is small.
-/

namespace Backend

open Arm

theorem decode_of_armBits {a : ArmInst}
    (h : ∀ w, armBits a = w → decode_raw_inst w = some a.norm) :
    decode_raw_inst (armBits a) = some a.norm := h _ rfl

theorem decode_raw_inst_of_dpi (i : BitVec 32)
    (h : i.extractLsb' 25 4 = 8#4 ∨ i.extractLsb' 25 4 = 9#4) :
    decode_raw_inst i = decode_data_proc_imm i := by
  have h0 : i.extractLsb' 31 1 = 0#1 ∨ i.extractLsb' 31 1 = 1#1 := by bv_decide
  rcases h0 with h0 | h0 <;> rcases h with h | h <;> simp [decode_raw_inst, h0, h]

theorem decode_raw_inst_of_br (i : BitVec 32)
    (h : i.extractLsb' 25 4 = 10#4 ∨ i.extractLsb' 25 4 = 11#4) :
    decode_raw_inst i = decode_branch i := by
  have h0 : i.extractLsb' 31 1 = 0#1 ∨ i.extractLsb' 31 1 = 1#1 := by bv_decide
  rcases h0 with h0 | h0 <;> rcases h with h | h <;> simp [decode_raw_inst, h0, h]

theorem decode_raw_inst_of_dpr (i : BitVec 32)
    (h : i.extractLsb' 25 4 = 13#4 ∨ i.extractLsb' 25 4 = 5#4) :
    decode_raw_inst i = decode_data_proc_reg i := by
  have h0 : i.extractLsb' 31 1 = 0#1 ∨ i.extractLsb' 31 1 = 1#1 := by bv_decide
  rcases h0 with h0 | h0 <;> rcases h with h | h <;> simp [decode_raw_inst, h0, h]

theorem decode_raw_inst_of_dpsfp (i : BitVec 32)
    (h : i.extractLsb' 25 4 = 7#4 ∨ i.extractLsb' 25 4 = 15#4) :
    decode_raw_inst i = decode_data_proc_sfp i := by
  have h0 : i.extractLsb' 31 1 = 0#1 ∨ i.extractLsb' 31 1 = 1#1 := by bv_decide
  rcases h0 with h0 | h0 <;> rcases h with h | h <;> simp [decode_raw_inst, h0, h]

theorem decode_raw_inst_of_ldst (i : BitVec 32)
    (h : i.extractLsb' 25 4 = 4#4 ∨ i.extractLsb' 25 4 = 12#4 ∨ i.extractLsb' 25 4 = 6#4 ∨
      i.extractLsb' 25 4 = 14#4) :
    decode_raw_inst i = decode_ldst_inst i := by
  have h0 : i.extractLsb' 31 1 = 0#1 ∨ i.extractLsb' 31 1 = 1#1 := by bv_decide
  rcases h0 with h0 | h0 <;> rcases h with h | h | h | h <;> simp [decode_raw_inst, h0, h]

theorem decode_raw_inst_of_reserved (i : BitVec 32)
    (h : i.extractLsb' 31 1 = 0#1 ∧ i.extractLsb' 25 4 = 0#4) :
    decode_raw_inst i = decode_reserved i := by
  simp [decode_raw_inst, h.1, h.2]

/-- See the module docstring. `d`: dispatch lemma, `g`: group decoder. -/
macro "decode_class " d:ident g:ident : tactic => `(tactic| (
  refine decode_of_armBits fun w hw => ?_
  simp only [armBits] at hw
  simp only [ArmInst.norm]
  rw [$d:ident _ (by bv_decide)]
  simp only [$g:ident]
  repeat' split
  all_goals first | (congr <;> bv_decide) | bv_decide))

end Backend

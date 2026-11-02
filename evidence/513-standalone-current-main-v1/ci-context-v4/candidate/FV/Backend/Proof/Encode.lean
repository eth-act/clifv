import FV.Backend.Proof.EncodeDPI
import FV.Backend.Proof.EncodeBR
import FV.Backend.Proof.EncodeDPR
import FV.Backend.Proof.EncodeDPSFP
import FV.Backend.Proof.EncodeLDST
import FV.Backend.Proof.EncodeRES
import FV.Arm.Exec

/-!
# M5: the encoder is proven against the Lean Arm model's decoder

* `decode_armBits`: `decode_raw_inst (armBits a) = some a.norm` for **every** `a : ArmInst`
  (every encoding class of the model, every field value; `ArmInst.norm` resets the `_fixed`
  fields, which `armBits` does not read, to the decoder's values).
* `Insn.decode_encode`: for every `Insn` (every form the backend emits, including the
  aliases `mov`, `cset`, `lsl/lsr/asr/ror #imm`, `cmp`/`cmn`/`tst` …) at every position `env`:
  if the encoder produces a word `w`, the decoder reads `w` back as exactly the instruction
  `toArmInst` specifies (PLAN.md §3.4 "decode (encode i) = i"; `Insn` is not the decoder's
  output type because of the aliases, so the statement goes through `toArmInst`).
* `Insn.sem`, `Insn.stepi_eq_sem`: the semantic link for M7. `stepi` on an error-free state
  whose program holds `w = encode i` at `PC` executes `Insn.sem i = exec_inst (toArmInst i)`.
-/

namespace Backend

open Arm

theorem decode_armBits (a : ArmInst) : decode_raw_inst (armBits a) = some a.norm := by
  cases a with
  | DPI x => exact decode_armBits_DPI x
  | BR x => exact decode_armBits_BR x
  | DPR x => exact decode_armBits_DPR x
  | DPSFP x => exact decode_armBits_DPSFP x
  | LDST x => exact decode_armBits_LDST x
  | RES x => exact decode_armBits_RES x

theorem _root_.Arm.ArmInst.norm_norm (a : ArmInst) : a.norm.norm = a.norm := by
  cases a <;> rename_i x <;> cases x <;> rfl

theorem Insn.toArmInst_norm {env : Env} {i : Insn} {a : ArmInst}
    (h : i.toArmInst env = .ok a) : a.norm = a := by
  simp only [Insn.toArmInst] at h
  cases hf : i.armFields env with
  | error e => simp [hf, Functor.map, Except.map] at h
  | ok b =>
    simp only [hf, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact ArmInst.norm_norm b

theorem Insn.encode_eq_ok {env : Env} {i : Insn} {w : BitVec 32} :
    i.encode env = .ok w ↔ ∃ a, i.toArmInst env = .ok a ∧ armBits a = w := by
  simp only [Insn.encode]
  cases h : i.toArmInst env <;> simp [Functor.map, Except.map]

/-- **M5.** Decoding the encoder's word gives back exactly the instruction `toArmInst`
specifies, for every `Insn` and position. -/
theorem Insn.decode_encode {env : Env} {i : Insn} {w : BitVec 32}
    (h : i.encode env = .ok w) :
    ∃ a, i.toArmInst env = .ok a ∧ decode_raw_inst w = some a := by
  obtain ⟨a, ha, rfl⟩ := Insn.encode_eq_ok.mp h
  exact ⟨a, ha, by rw [decode_armBits, Insn.toArmInst_norm ha]⟩

/-- `decode_encode` with the instruction named. -/
theorem Insn.decode_encode_of {env : Env} {i : Insn} {a : ArmInst} {w : BitVec 32}
    (ha : i.toArmInst env = .ok a) (hw : i.encode env = .ok w) :
    decode_raw_inst w = some a := by
  obtain ⟨a', ha', hd⟩ := Insn.decode_encode hw
  rw [ha] at ha'
  cases ha'
  exact hd

/-- `Insn.decodeOk` (the executable check run by `lean-backend-encode-test decode`) holds
for every instruction the encoder accepts. -/
theorem Insn.decodeOk_of_encode {env : Env} {i : Insn} {w : BitVec 32}
    (h : i.encode env = .ok w) : i.decodeOk env = true := by
  obtain ⟨a, ha, rfl⟩ := Insn.encode_eq_ok.mp h
  simp [Insn.decodeOk, ha, decode_armBits, Insn.toArmInst_norm ha]

/-- The meaning of an instruction on the Arm model: execute the instruction `toArmInst`
specifies (`.error` when the encoder rejects the operands). -/
def Insn.sem (env : Env) (i : Insn) (s : ArmState) : Except String ArmState :=
  (exec_inst · s) <$> i.toArmInst env

/-- **Semantic link (M7).** One `stepi` on an error-free state whose program holds, at `PC`,
the word the encoder produced for `i` executes `Insn.sem i`. -/
theorem Insn.stepi_eq_sem {env : Env} {i : Insn} {w : BitVec 32} {s : ArmState}
    (herr : r .ERR s = .None) (hfetch : fetch_inst (r .PC s) s = some w)
    (henc : i.encode env = .ok w) :
    i.sem env s = .ok (stepi s) := by
  obtain ⟨a, ha, hd⟩ := Insn.decode_encode henc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ w a herr rfl hfetch hd]
  simp [Insn.sem, ha, Functor.map, Except.map]

end Backend

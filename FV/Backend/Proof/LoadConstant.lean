import FV.Backend.LoadConstant
import FV.Backend.Proof.RegallocMem
import FV.Backend.Proof.LogicImmComplete

/-!
# `loadConstLines` (Cranelift's `Inst::load_constant`) on the Arm model

`steps_loadConstLines`: the twin of `steps_loadConst64` (`FV/Backend/Proof/RegallocMem.lean`,
same statement shape): every line of `loadConstLines (x n) v` encodes, `x n` ends as `v`
(mod 2^64), the pc advances by 4 per line, and nothing else changes (flags included: `orr`
with an immediate does not set them).

Route. Each emitted instruction (64- and 32-bit `movz`/`movn`/`movk`, `orr xd, xzr, #imm`)
encodes and writes only `x n`, with the value `lcVal` (`ExecX`, `exec_movWide`, `exec_movk'`,
`exec_orr`; the bitmask decodes back to `v` by `Cov.logicImmComplete`). The value of `x n` is
then followed by its four halfwords (`Rz`, `hwVal`): the 32-bit forms clear the upper half,
`movn` complements, `movk` replaces one halfword. `hw_loadConstLines`: the halfwords at the end
are those of `v`; in the general case the first instruction sets the kept halfword and the
ignored value elsewhere (`movSeq_hw`), and some halfword is kept, as all-ignored values are
caught by cases 1 to 3 (`general_ne`).

Also: `loadConstLines_length` (≤ 4 lines), the shape lemma `mem_loadConstLines` from which the
per-line twins in `FV/Backend/Proof/LoadConstantTwins.lean` follow, `loadConstLines_toArmInst`,
and `lines_orr_xzr` (case 3 is what `MInst.lines` emits for Cranelift's `AluRRImmLogic` `orr`
with `rn = zero_reg()`).
-/

namespace Backend.Proof
open Backend

namespace LoadConstant

/-- The value `x n` holds after one of `loadConstLines`' instructions, from its value `X`
before (`exec_move_wide_imm`, `exec_logical_imm`). -/
def lcVal : Insn → BitVec 64 → BitVec 64
  | .movWide .movZ true _ ⟨c, i⟩, _ => Arm.BitVec.partInstall (16 * i) 16 (BitVec.ofNat 16 c) 0#64
  | .movWide .movN true _ ⟨c, i⟩, _ =>
    ~~~(Arm.BitVec.partInstall (16 * i) 16 (BitVec.ofNat 16 c) 0#64)
  | .movWide .movZ false _ ⟨c, i⟩, _ =>
    (Arm.BitVec.partInstall (16 * i) 16 (BitVec.ofNat 16 c) 0#32).setWidth 64
  | .movWide .movN false _ ⟨c, i⟩, _ =>
    (~~~(Arm.BitVec.partInstall (16 * i) 16 (BitVec.ofNat 16 c) 0#32)).setWidth 64
  | .movk true _ ⟨c, i⟩, X => Arm.BitVec.partInstall (16 * i) 16 (BitVec.ofNat 16 c) X
  | .movk false _ ⟨c, i⟩, X =>
    (Arm.BitVec.partInstall (16 * i) 16 (BitVec.ofNat 16 c) (X.setWidth 32)).setWidth 64
  | .logicImm _ _ _ _ v, _ => BitVec.ofNat 64 v
  | _, X => X

/-- `i` encodes, writes `x n := lcVal i (x n)`, advances the pc by 4 and changes nothing
else. -/
def ExecX (n : Nat) (i : Insn) : Prop :=
  ∀ env : Env, ∃ ai, i.toArmInst env = .ok ai ∧ ∀ s : Arm.ArmState,
    Arm.exec_inst ai s = Arm.w .PC (Arm.r .PC s + 4#64)
      (Arm.w (.GPR (BitVec.ofNat 5 n)) (lcVal i (Arm.r (.GPR (BitVec.ofNat 5 n)) s)) s)

theorem exec_movWide {n c i : Nat} (hn : n ≤ 30) (hc : c < 2 ^ 16) (op : MoveWideOp)
    (hop : op = .movZ ∨ op = .movN) (w : Bool) (hi : i < if w then 4 else 2) :
    ExecX n (.movWide op w (.x n) ⟨c, i⟩) := by
  intro env
  refine ⟨.DPI (.Move_wide_imm {
    sf := b1 w, opc := (if op == .movZ then 2 else 0),
    hw := BitVec.ofNat 2 i, imm16 := BitVec.ofNat 16 c, Rd := BitVec.ofNat 5 n }), ?_, fun s => ?_⟩
  · have : ¬ (if w then 4 else 2) ≤ i := by omega
    simp [Insn.toArmInst, Insn.armFields, Reg.encZR, hn, uField, hc, Arm.ArmInst.norm, this]
  · have hpos : (BitVec.ofNat 2 i ++ 0#4).toNat = 16 * i := by
      rw [BitVec.toNat_append]
      have : i < 4 := by cases w <;> simp at hi <;> omega
      simp [Nat.shiftLeft_eq, Nat.mod_eq_of_lt this]; omega
    have hb : (BitVec.ofNat 2 i).getLsbD 1 = true → w = true := by
      intro h; cases w
      · simp at hi; rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp at h
      · rfl
    rcases hop with rfl | rfl <;> cases w <;>
    simp [Arm.exec_inst, Arm.DPI.exec_move_wide_imm, Arm.write_gpr_zr, ofNat5_ne31 hn,
      Arm.write_gpr, Arm.write_pc, Arm.read_pc, hpos, lcVal, b1] <;> simp_all <;> rfl

theorem exec_movk' {n c i : Nat} (hn : n ≤ 30) (hc : c < 2 ^ 16) (w : Bool)
    (hi : i < if w then 4 else 2) : ExecX n (.movk w (.x n) ⟨c, i⟩) := by
  intro env
  refine ⟨.DPI (.Move_wide_imm {
    sf := b1 w, opc := 3, hw := BitVec.ofNat 2 i, imm16 := BitVec.ofNat 16 c,
    Rd := BitVec.ofNat 5 n }), ?_, fun s => ?_⟩
  · have : ¬ (if w then 4 else 2) ≤ i := by omega
    simp [Insn.toArmInst, Insn.armFields, Reg.encZR, hn, uField, hc, Arm.ArmInst.norm, this]
  · have hpos : (BitVec.ofNat 2 i ++ 0#4).toNat = 16 * i := by
      rw [BitVec.toNat_append]
      have : i < 4 := by cases w <;> simp at hi <;> omega
      simp [Nat.shiftLeft_eq, Nat.mod_eq_of_lt this]; omega
    have hb : (BitVec.ofNat 2 i).getLsbD 1 = true → w = true := by
      intro h; cases w
      · simp at hi; rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp at h
      · rfl
    cases w <;>
    simp [Arm.exec_inst, Arm.DPI.exec_move_wide_imm, Arm.write_gpr_zr, ofNat5_ne31 hn,
      Arm.write_gpr, Arm.write_pc, Arm.read_pc, Arm.read_gpr_zr, Arm.read_gpr, hpos, lcVal,
      b1] <;> simp_all <;> rfl

/-- What `bitmaskOk` gives: the encoding and its decoding (`bitmaskOk_spec`,
`FV/Backend/Proof/RefinesInsts2.lean`). -/
theorem bitmaskOk_dec {M : Nat} {is64 : Bool} {v : Nat} {e : BitVec M}
    (h : bitmaskOk M is64 v e = true) :
    ∃ N immr imms tm, bitmaskEnc? is64 v = some (N, immr, imms) ∧
      Arm.decode_bit_masks N imms immr true M = some (e, tm) ∧ (is64 = false → N = 0#1) := by
  unfold bitmaskOk at h
  split at h
  · cases h
  · rename_i N immr imms hb
    split at h
    · cases h
    · rename_i wm tm hd
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      obtain ⟨hN, rfl⟩ := h
      exact ⟨N, immr, imms, tm, hb, hd, fun h64 => by simpa [h64] using hN⟩

theorem exec_orr {n v : Nat} (hn : n ≤ 30) (h : bitmaskOk 64 true v (BitVec.ofNat 64 v) = true) :
    ExecX n (.logicImm .orr true (.x n) .xzr v) := by
  intro env
  obtain ⟨N, immr, imms, tm, hb, hd, -⟩ := bitmaskOk_dec h
  refine ⟨.DPI (.Logical_imm {
    sf := 1, opc := 1, N := N, immr := immr, imms := imms, Rn := 31#5,
    Rd := BitVec.ofNat 5 n }), ?_, fun s => ?_⟩
  · simp [Insn.toArmInst, Insn.armFields, Reg.encZR, Reg.encSP, hn, hb, ALUOp.logic?,
      Arm.ArmInst.norm, b1]
  · simp [Arm.exec_inst, Arm.DPI.exec_logical_imm, hd, Arm.DPI.decode_op,
      Arm.DPI.exec_logical_imm_op, Arm.read_gpr_zr, Arm.write_gpr, Arm.write_pc, Arm.read_pc,
      lcVal]
    exact Arm.w_of_w_commute (by simp)

/-! ## Register values by halfwords -/

/-- The `w`-bit value `Y` has halfwords `H` (`H j` for `j < w / 16`, bits above 16 of `H j`
ignored). -/
def Rz (w : Nat) (Y : BitVec w) (H : Nat → Nat) : Prop :=
  ∀ b < w, Y.getLsbD b = (H (b / 16)).testBit (b % 16)

theorem testBit_halfword (v j k : Nat) (hk : k < 16) :
    (halfword v j).testBit k = v.testBit (16 * j + k) := by
  unfold halfword
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hk, Nat.add_comm]

theorem rz_zero (w : Nat) : Rz w 0#w (fun _ => 0) := by
  intro b _; simp

theorem rz_ofNat (v : Nat) : Rz 64 (BitVec.ofNat 64 v) (halfword v) := by
  intro b hb
  rw [testBit_halfword _ _ _ (Nat.mod_lt _ (by decide)), Nat.div_add_mod]
  simp only [BitVec.getLsbD_ofNat, hb, decide_true, Bool.true_and]

theorem rz_partInstall {w i c : Nat} {X : BitVec w} {H : Nat → Nat} (h : Rz w X H) :
    Rz w (Arm.BitVec.partInstall (16 * i) 16 (BitVec.ofNat 16 c) X)
      (fun j => if j = i then c else H j) := by
  intro b hb
  simp only [Arm.BitVec.partInstall, BitVec.truncate_eq_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, hb, decide_true,
    Bool.true_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, Bool.not_and, Bool.not_not,
    BitVec.getLsbD_ofNat]
  by_cases h1 : b / 16 = i
  · have e1 : ¬ b < 16 * i := by omega
    have e2 : b - 16 * i < 16 := by omega
    have e3 : b - 16 * i = b % 16 := by omega
    simp [h1, e1, e3, show b % 16 < w by omega, show b % 16 < 16 by omega]
  · rw [h b hb]
    by_cases h2 : b < 16 * i
    · simp [h1, h2]
    · have e2 : ¬ b - 16 * i < 16 := by omega
      simp [h1, h2, e2]

theorem rz_not {w : Nat} {X : BitVec w} {H : Nat → Nat} (hH : ∀ j, H j < 2 ^ 16)
    (h : Rz w X H) : Rz w (~~~X) (fun j => 2 ^ 16 - 1 - H j) := by
  intro b hb
  have hk : b % 16 < 16 := Nat.mod_lt _ (by decide)
  have e : (2 ^ 16 - 1 - H (b / 16)) = (~~~(BitVec.ofNat 16 (H (b / 16)))).toNat := by
    simp [BitVec.toNat_not, Nat.mod_eq_of_lt (hH _)]
  show _ = (2 ^ 16 - 1 - H (b / 16)).testBit (b % 16)
  rw [BitVec.getLsbD_not, h b hb, e, ← BitVec.getLsbD, BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
  simp [hk, hb]

theorem rz_down {X : BitVec 64} {H : Nat → Nat} (h : Rz 64 X H) : Rz 32 (X.setWidth 32) H := by
  intro b hb
  rw [BitVec.getLsbD_setWidth, h b (by omega)]
  simp [hb]

theorem rz_up {Y : BitVec 32} {H : Nat → Nat} (h : Rz 32 Y H) :
    Rz 64 (Y.setWidth 64) (fun j => if j < 2 then H j else 0) := by
  intro b hb
  rw [BitVec.getLsbD_setWidth]
  by_cases h1 : b < 32
  · rw [h b h1]; simp [show b / 16 < 2 by omega, hb]
  · rw [BitVec.getLsbD_of_ge Y b (by omega)]; simp [show ¬ b / 16 < 2 by omega]

theorem rz_congr {w : Nat} {Y : BitVec w} {H G : Nat → Nat} (h : Rz w Y H)
    (e : ∀ j, j < w / 16 → H j = G j) (hw : w % 16 = 0) : Rz w Y G := by
  intro b hb
  rw [h b hb, e _ (by omega)]

theorem eq_of_rz {Y Z : BitVec 64} {H : Nat → Nat} (h1 : Rz 64 Y H) (h2 : Rz 64 Z H) : Y = Z := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [h1 b hb, h2 b hb]

/-- The halfwords of `x n` after one of `loadConstLines`' instructions, from its halfwords `H`
before (the halfword view of `lcVal`). -/
def hwVal : Insn → (Nat → Nat) → Nat → Nat
  | .movWide .movZ true _ ⟨c, i⟩, _ => fun j => if j = i then c else 0
  | .movWide .movN true _ ⟨c, i⟩, _ => fun j => 2 ^ 16 - 1 - if j = i then c else 0
  | .movWide .movZ false _ ⟨c, i⟩, _ => fun j => if j < 2 then (if j = i then c else 0) else 0
  | .movWide .movN false _ ⟨c, i⟩, _ =>
    fun j => if j < 2 then 2 ^ 16 - 1 - (if j = i then c else 0) else 0
  | .movk true _ ⟨c, i⟩, H => fun j => if j = i then c else H j
  | .movk false _ ⟨c, i⟩, H => fun j => if j < 2 then (if j = i then c else H j) else 0
  | .logicImm _ _ _ _ v, _ => halfword v
  | _, H => H

/-- `hwVal i` describes `lcVal i`. -/
def RzOk (i : Insn) : Prop :=
  ∀ (X : BitVec 64) (H : Nat → Nat), Rz 64 X H → Rz 64 (lcVal i X) (hwVal i H)

theorem ite_lt {j i c : Nat} (hc : c < 2 ^ 16) : (if j = i then c else 0) < 2 ^ 16 := by
  split <;> omega

theorem rzOk_movWide {r : Reg} {c i : Nat} (hc : c < 2 ^ 16) (op : MoveWideOp)
    (hop : op = .movZ ∨ op = .movN) (w : Bool) : RzOk (.movWide op w r ⟨c, i⟩) := by
  intro X H _
  rcases hop with rfl | rfl <;> cases w
  · exact rz_up (rz_partInstall (rz_zero 32))
  · exact rz_partInstall (rz_zero 64)
  · exact rz_up (rz_not (fun _ => ite_lt hc) (rz_partInstall (rz_zero 32)))
  · exact rz_not (fun _ => ite_lt hc) (rz_partInstall (rz_zero 64))

theorem rzOk_movk {r : Reg} {c i : Nat} (w : Bool) : RzOk (.movk w r ⟨c, i⟩) := by
  intro X H h
  cases w
  · exact rz_up (rz_partInstall (rz_down h))
  · exact rz_partInstall h

theorem rzOk_logicImm {op : ALUOp} {w : Bool} {r r' : Reg} (v : Nat) :
    RzOk (.logicImm op w r r' v) := fun _ _ _ => rz_ofNat v

/-! ## Running a list of such lines -/

/-- `lcVal` of a line (the identity on labels and words). -/
def lineVal : Line → BitVec 64 → BitVec 64
  | .ins i _, X => lcVal i X
  | _, X => X

/-- `hwVal` of a line. -/
def lineHw : Line → (Nat → Nat) → Nat → Nat
  | .ins i _, H => hwVal i H
  | _, H => H

theorem steps_execX {n : Nat} (s : Arm.ArmState) :
    ∀ (ls : List Line) (env : Env) (P X : BitVec 64),
      (∀ ln ∈ ls, ∃ i, ln = .ins i none ∧ ExecX n i) →
      StepsOk env ls (pcx s n P X)
        (pcx s n (P + BitVec.ofNat 64 (4 * ls.length)) (ls.foldl (fun X ln => lineVal ln X) X))
  | [], env, P, X, _ => by simp [StepsOk]
  | ln :: ls, env, P, X, h => by
    obtain ⟨i, rfl, hi⟩ := h ln (by simp)
    obtain ⟨ai, ha, he⟩ := hi env
    have he := he (pcx s n P X)
    obtain ⟨f1, f2, f3, f4⟩ := pcx_facts s n P X
    rw [f4, pcx_step] at he
    obtain ⟨g1, g2, g3, -⟩ := pcx_facts s n (P + 4#64) (lcVal i X)
    refine steps_cons ha (by rw [he, g1, f1]) (by rw [he, g2, f2]) (by rw [he, g3, f3]) ?_
    rw [he]
    have := steps_execX s ls { env with pc := env.pc + 4 } (P + 4#64) (lcVal i X)
      (fun l hl => h l (by simp [hl]))
    simp only [List.length_cons, List.foldl_cons, lineVal] at this ⊢
    have e : P + 4#64 + BitVec.ofNat 64 (4 * ls.length) =
        P + BitVec.ofNat 64 (4 * (ls.length + 1)) := by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
    rw [e] at this
    exact this

theorem pcx_self (s : Arm.ArmState) (n : Nat) :
    pcx s n (Arm.r .PC s) (Arm.r (.GPR (BitVec.ofNat 5 n)) s) = s := by
  simp only [pcx, Arm.w_irrelevant]

/-- Lines each of which is an `ExecX n` instruction run as `StepsOk` from any state: `x n`
ends as their `lineVal` fold, the pc advances by 4 per line, nothing else changes. -/
theorem steps_lines {n : Nat} (env : Env) (ls : List Line)
    (h : ∀ ln ∈ ls, ∃ i, ln = .ins i none ∧ ExecX n i) (s : Arm.ArmState) :
    StepsOk env ls s (pcx s n (Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length))
      (ls.foldl (fun X ln => lineVal ln X) (Arm.r (.GPR (BitVec.ofNat 5 n)) s))) := by
  have := steps_execX s ls env (Arm.r .PC s) (Arm.r (.GPR (BitVec.ofNat 5 n)) s) h
  rw [pcx_self] at this
  exact this

theorem rz_fold : ∀ (ls : List Line), (∀ ln ∈ ls, ∃ i, ln = .ins i none ∧ RzOk i) →
    ∀ (X : BitVec 64) (H : Nat → Nat), Rz 64 X H →
      Rz 64 (ls.foldl (fun X ln => lineVal ln X) X) (ls.foldl (fun H ln => lineHw ln H) H)
  | [], _, X, H, h => h
  | ln :: ls, hl, X, H, h => by
    obtain ⟨i, rfl, hi⟩ := hl ln (by simp)
    exact rz_fold ls (fun l h' => hl l (by simp [h'])) _ _ (hi X H h)

/-! ## The halfwords `loadConstLines` leaves -/

theorem halfword_lt (v j : Nat) : halfword v j < 2 ^ 16 := Nat.mod_lt _ (by decide)

/-- `MoveWideConst::maybe_from_u64(u) = Some(imm)`: `u` is `imm.bits` in halfword
`imm.shift`. -/
theorem mwc_spec {u : Nat} {imm : MoveWideConst} (hu : u < 2 ^ 64)
    (h : MoveWideConst.ofNat? u = some imm) :
    imm.bits < 2 ^ 16 ∧ imm.shift < 4 ∧
      ∀ j < 4, halfword u j = if j = imm.shift then imm.bits else 0 := by
  have hm : mask64 u = u := Nat.mod_eq_of_lt hu
  unfold MoveWideConst.ofNat? at h
  rw [hm] at h
  dsimp only at h
  simp only [Nat.reducePow] at hu
  split at h
  · cases h; simp only [Nat.reducePow] at *
    refine ⟨by omega, by omega, ?_⟩
    intro j hj; rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [halfword] <;> omega
  split at h
  · cases h; rename_i h1 h2; simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
    simp only [Nat.reducePow] at *
    refine ⟨by omega, by omega, ?_⟩
    intro j hj; rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [halfword] <;> omega
  split at h
  · cases h; rename_i h1 h2 h3; simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h3
    simp only [Nat.reducePow] at *
    refine ⟨by omega, by omega, ?_⟩
    intro j hj; rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [halfword] <;> omega
  split at h
  · cases h; rename_i h1 h2 h3 h4; simp only [beq_iff_eq] at h4
    simp only [Nat.reducePow] at *
    refine ⟨by omega, by omega, ?_⟩
    intro j hj; rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [halfword] <;> omega
  · cases h

theorem halfword_compl {u j : Nat} (hu : u < 2 ^ 64) (hj : j < 4) :
    halfword (2 ^ 64 - 1 - u) j = 2 ^ 16 - 1 - halfword u j := by
  simp only [Nat.reducePow] at hu
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp [halfword] <;> omega

theorem mem_kept {v n ig : Nat} {p : Nat × Nat} :
    p ∈ keptHalfwords v n ig ↔ p.1 < n ∧ halfword v p.1 ≠ ig ∧ p.2 = halfword v p.1 := by
  obtain ⟨i, c⟩ := p
  simp only [keptHalfwords, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨a, ha, h⟩
    split at h
    · cases h
    · rename_i hne; cases h; simp only [beq_iff_eq] at hne; exact ⟨ha, hne, rfl⟩
  · rintro ⟨ha, hne, rfl⟩
    exact ⟨i, ha, by simp [hne]⟩

theorem kept_nil {v n ig : Nat} (h : keptHalfwords v n ig = []) : ∀ j < n, halfword v j = ig := by
  intro j hj
  refine Classical.byContradiction fun hne => ?_
  have : (j, halfword v j) ∈ keptHalfwords v n ig := mem_kept.2 ⟨hj, hne, rfl⟩
  rw [h] at this; cases this

/-- The `movk`s of the general case install their halfwords over `G`. -/
theorem fold_movk (rd : Reg) (is64 : Bool) (v : Nat) :
    ∀ (R : List (Nat × Nat)) (G : Nat → Nat),
      (∀ p ∈ R, p.2 = halfword v p.1 ∧ (is64 = false → p.1 < 2)) →
      (is64 = false → ∀ j, 2 ≤ j → G j = 0) →
      ∀ j, (R.map fun p => Line.ins (.movk is64 rd ⟨p.2, p.1⟩)).foldl
          (fun H ln => lineHw ln H) G j = if j ∈ R.map Prod.fst then halfword v j else G j
  | [], G, _, _, j => by simp
  | (i, c) :: R, G, hR, hG, j => by
    obtain ⟨hc, hi⟩ := hR (i, c) (by simp)
    simp only at hc hi
    have ih := fold_movk rd is64 v R (hwVal (.movk is64 rd ⟨c, i⟩) G)
      (fun p hp => hR p (by simp [hp]))
      (fun h64 j hj => by subst h64; simp [hwVal]; omega) j
    rw [List.map_cons, List.foldl_cons]
    show List.foldl _ (hwVal _ G) _ j = _
    rw [ih]
    simp only [List.map_cons, List.mem_cons]
    cases is64
    · have := hi rfl
      by_cases h1 : j ∈ R.map Prod.fst
      · simp [h1]
      · by_cases h2 : j = i
        · subst h2; simp [hwVal, h1, hc, this]
        · by_cases h3 : j < 2
          · simp [hwVal, h1, h2, h3]
          · simp [hwVal, h1, h2, h3, hG rfl j (by omega)]
    · by_cases h1 : j ∈ R.map Prod.fst
      · simp [h1]
      · by_cases h2 : j = i
        · subst h2; simp [hwVal, h1, hc]
        · simp [hwVal, h1, h2]

/-- The general case leaves `v`'s halfwords: the first instruction sets the kept halfword `i0`
and the ignored value elsewhere below `n` (0 above, at 32 bits), the `movk`s set the other
kept halfwords. -/
theorem movSeq_hw (rd : Reg) {v n ig : Nat} (is64 inv : Bool) (hn : n = if is64 then 4 else 2)
    (hig : ig = if inv then 2 ^ 16 - 1 else 0) (hv32 : is64 = false → v < 2 ^ 32)
    (hne : keptHalfwords v n ig ≠ []) (H : Nat → Nat) :
    ∀ j < 4, (movSeqLines rd is64 inv (keptHalfwords v n ig)).foldl
      (fun H ln => lineHw ln H) H j = halfword v j := by
  intro j hj
  have hmem : ∀ p, p ∈ keptHalfwords v n ig ↔ _ := fun p => mem_kept (p := p)
  generalize hK : keptHalfwords v n ig = ks at hne hmem
  obtain ⟨⟨i0, c0⟩, R, rfl⟩ : ∃ p R, ks = p :: R := by
    cases ks with
    | nil => exact absurd rfl hne
    | cons p R => exact ⟨p, R, rfl⟩
  obtain ⟨hi0, hne0, hc0⟩ := (hmem (i0, c0)).1 (by simp)
  simp only at hi0 hne0 hc0
  have hc0lt : c0 < 2 ^ 16 := hc0 ▸ halfword_lt v i0
  -- the first instruction
  have hG : ∀ j, (j < 4 ∨ is64 = false) →
      lineHw (.ins (if inv then .movWide .movN is64 rd ⟨2 ^ 16 - 1 - c0, i0⟩
        else .movWide .movZ is64 rd ⟨c0, i0⟩)) H j =
      if j = i0 then c0 else if j < n then ig else 0 := by
    intro j hj
    subst hn hig
    cases is64 <;> cases inv <;> simp at hi0 hj ⊢ <;>
      by_cases h1 : j = i0 <;> by_cases h2 : j < 2 <;> simp [lineHw, hwVal, h1, h2, hi0] <;> omega
  simp only [movSeqLines, List.foldl_cons]
  rw [fold_movk rd is64 v R _ (fun p hp => by
      obtain ⟨h1, -, h2⟩ := (hmem p).1 (by simp [hp])
      exact ⟨h2, fun h64 => by subst hn; simp [h64] at h1; omega⟩)
    (fun h64 j hj2 => by
      rw [hG j (.inr h64)]; subst hn; simp [h64] at hi0 ⊢
      have : j ≠ i0 := by omega
      simp [this]; omega) j, hG j (.inl hj)]
  by_cases h1 : j ∈ R.map Prod.fst
  · simp [h1]
  · simp only [h1, ite_false]
    by_cases h2 : j = i0
    · simp [h2, hc0]
    · simp only [h2, ite_false]
      by_cases h3 : j < n
      · simp only [h3, ite_true]
        refine (Classical.byContradiction fun h4 => ?_)
        have := (hmem (j, halfword v j)).2 ⟨h3, Ne.symm h4, rfl⟩
        simp only [List.mem_cons, Prod.mk.injEq] at this
        rcases this with ⟨h5, -⟩ | h5
        · exact h2 h5
        · exact h1 (List.mem_map.2 ⟨_, h5, rfl⟩)
      · simp only [h3, ite_false]
        cases is64
        · have := hv32 rfl
          simp at hn; subst hn
          simp only [Nat.reducePow] at this
          rcases (show j = 2 ∨ j = 3 by omega) with rfl | rfl <;> simp [halfword] <;> omega
        · simp at hn; omega

/-- The general case is reached only with a kept halfword: all halfwords ignored would make
`value` `0`, `2^64 - 1` (cases 1, 2) or `2^32 - 1` (a bitmask immediate, case 3). -/
theorem general_ne {v n ig : Nat} (hv : v < 2 ^ 64) (h1 : MoveWideConst.ofNat? v = none)
    (h2 : MoveWideConst.ofNat? (2 ^ 64 - 1 - v) = none) (h3 : ImmLogic.ofNat? v .size64 = none)
    (is64 inv : Bool) (hn : n = if is64 then 4 else 2) (hig : ig = if inv then 2 ^ 16 - 1 else 0)
    (hv32 : is64 = false → v < 2 ^ 32) : keptHalfwords v n ig ≠ [] := by
  intro hk
  have h := kept_nil hk
  subst hn hig
  simp only [Nat.reducePow] at hv hv32
  cases is64 <;> cases inv <;> simp only [Bool.false_eq_true, ite_true, ite_false] at h
  · have e0 := h 0 (by decide); have e1 := h 1 (by decide); have := hv32 rfl
    simp [halfword] at e0 e1
    have : v = 0 := by omega
    subst this; simp [MoveWideConst.ofNat?, mask64] at h1
  · have e0 := h 0 (by decide); have e1 := h 1 (by decide); have := hv32 rfl
    simp [halfword] at e0 e1
    have : v = 2 ^ 32 - 1 := by omega
    subst this; revert h3; decide
  · have e0 := h 0 (by decide); have e1 := h 1 (by decide)
    have e2 := h 2 (by decide); have e3 := h 3 (by decide)
    simp [halfword] at e0 e1 e2 e3
    have : v = 0 := by omega
    subst this; simp [MoveWideConst.ofNat?, mask64] at h1
  · have e0 := h 0 (by decide); have e1 := h 1 (by decide)
    have e2 := h 2 (by decide); have e3 := h 3 (by decide)
    simp [halfword] at e0 e1 e2 e3
    have : 2 ^ 64 - 1 - v = 0 := by omega
    rw [this] at h2; simp [MoveWideConst.ofNat?, mask64] at h2

theorem mask64_lt' (v : Nat) : mask64 v < 2 ^ 64 := Nat.mod_lt _ (by decide)

theorem mask64_mask64 (v : Nat) : mask64 (mask64 v) = mask64 v := Nat.mod_eq_of_lt (mask64_lt' v)

/-- `ImmLogic::maybe_from_u64(u, I64) = Some(imml)`: `imml` holds `u` itself. -/
theorem immLogic_eq {u : Nat} {i : ImmLogic} (h : ImmLogic.ofNat? u .size64 = some i) :
    i = ⟨u, .size64⟩ := by
  unfold ImmLogic.ofNat? at h
  dsimp only at h
  split at h
  · cases h; rfl
  · cases h

/-- `loadConstLines` by cases. -/
theorem loadConstLines_cases (rd : Reg) (v : Nat) :
    (∃ imm, MoveWideConst.ofNat? (mask64 v) = some imm ∧
      loadConstLines rd v = [.ins (.movWide .movZ true rd imm)]) ∨
    (MoveWideConst.ofNat? (mask64 v) = none ∧ ∃ imm,
      MoveWideConst.ofNat? (2 ^ 64 - 1 - mask64 v) = some imm ∧
      loadConstLines rd v = [.ins (.movWide .movN true rd imm)]) ∨
    (∃ i, ImmLogic.ofNat? (mask64 v) .size64 = some i ∧
      loadConstLines rd v = [.ins (.logicImm .orr true rd .xzr (mask64 v))]) ∨
    (MoveWideConst.ofNat? (mask64 v) = none ∧
      MoveWideConst.ofNat? (2 ^ 64 - 1 - mask64 v) = none ∧
      ImmLogic.ofNat? (mask64 v) .size64 = none ∧
      loadConstLines rd v = generalLines rd (mask64 v)) := by
  unfold loadConstLines
  dsimp only
  rcases h1 : MoveWideConst.ofNat? (mask64 v) with _ | imm
  · rcases h2 : MoveWideConst.ofNat? (2 ^ 64 - 1 - mask64 v) with _ | imm
    · rcases h3 : ImmLogic.ofNat? (mask64 v) .size64 with _ | i
      · exact .inr (.inr (.inr ⟨rfl, rfl, rfl, rfl⟩))
      · exact .inr (.inr (.inl ⟨i, rfl, rfl⟩))
    · exact .inr (.inl ⟨rfl, imm, rfl, rfl⟩)
  · exact .inl ⟨imm, rfl, rfl⟩

/-- **The halfwords** `loadConstLines` leaves are those of `value` (mod 2^64), from any start. -/
theorem hw_loadConstLines (rd : Reg) (v : Nat) (H : Nat → Nat) :
    ∀ j < 4, (loadConstLines rd v).foldl (fun H ln => lineHw ln H) H j = halfword (mask64 v) j := by
  intro j hj
  have hu := mask64_lt' v
  rcases loadConstLines_cases rd v with ⟨⟨c, i⟩, h1, e⟩ | ⟨-, ⟨c, i⟩, h2, e⟩ | ⟨-, -, e⟩ |
    ⟨h1, h2, h3, e⟩ <;> rw [e]
  · obtain ⟨-, -, he⟩ := mwc_spec hu h1
    simp only [List.foldl_cons, List.foldl_nil, lineHw, hwVal]
    rw [he j hj]
  · have hu' : 2 ^ 64 - 1 - mask64 v < 2 ^ 64 := by omega
    obtain ⟨-, -, he⟩ := mwc_spec hu' h2
    simp only [List.foldl_cons, List.foldl_nil, lineHw, hwVal]
    have := halfword_compl hu hj
    have := halfword_lt (mask64 v) j
    rw [← he j hj]; omega
  · simp [lineHw, hwVal]
  · unfold generalLines
    dsimp only
    exact movSeq_hw rd _ _ rfl rfl (fun h => by simpa using h)
      (general_ne hu h1 h2 h3 _ _ rfl rfl (fun h => by simpa using h)) H j hj

/-- Every line of `loadConstLines (x n) v` is an instruction (no trap code) that encodes and
writes only `x n` (`ExecX`), with its halfword view (`RzOk`). -/
theorem good_loadConstLines {n : Nat} (hn : n ≤ 30) (v : Nat) :
    ∀ ln ∈ loadConstLines (.x n) v, ∃ i, ln = .ins i none ∧ ExecX n i ∧ RzOk i := by
  intro ln hln
  have hu := mask64_lt' v
  rcases loadConstLines_cases (.x n) v with ⟨⟨c, i⟩, h1, e⟩ | ⟨-, ⟨c, i⟩, h2, e⟩ |
    ⟨i, h3, e⟩ | ⟨-, -, -, e⟩ <;> rw [e] at hln
  · obtain ⟨hc, hi, -⟩ := mwc_spec hu h1
    simp only [List.mem_singleton] at hln; subst hln
    exact ⟨_, rfl, exec_movWide hn hc _ (.inl rfl) true (by simpa using hi),
      rzOk_movWide hc _ (.inl rfl) true⟩
  · have hu' : 2 ^ 64 - 1 - mask64 v < 2 ^ 64 := by omega
    obtain ⟨hc, hi, -⟩ := mwc_spec hu' h2
    simp only [List.mem_singleton] at hln; subst hln
    exact ⟨_, rfl, exec_movWide hn hc _ (.inr rfl) true (by simpa using hi),
      rzOk_movWide hc _ (.inr rfl) true⟩
  · simp only [List.mem_singleton] at hln; subst hln
    have e3 := immLogic_eq h3
    subst e3
    have hok : logicImmOk .orr .size64 ⟨mask64 v, .size64⟩ = true :=
      Cov.logicImmComplete ⟨mask64 v, .size64⟩ .size64 .orr h3 (by decide)
    rw [show logicImmOk .orr .size64 ⟨mask64 v, .size64⟩ =
      bitmaskOk 64 true (mask64 (mask64 v)) (BitVec.ofNat 64 (mask64 v)) from rfl,
      mask64_mask64] at hok
    exact ⟨_, rfl, exec_orr hn hok, rzOk_logicImm _⟩
  · unfold generalLines at hln
    dsimp only at hln
    generalize (decide (2 ^ 32 ≤ mask64 v)) = is64 at hln
    generalize (decide (countZeroHalfWords (mask64 v) (if is64 = true then 4 else 2) <
      countZeroHalfWords (if is64 = true then 2 ^ 64 - 1 - mask64 v else 2 ^ 32 - 1 - mask64 v)
        (if is64 = true then 4 else 2))) = inv at hln
    generalize hK : keptHalfwords (mask64 v) (if is64 = true then 4 else 2)
      (if inv = true then 2 ^ 16 - 1 else 0) = ks at hln
    have hmem : ∀ p ∈ ks, p.1 < (if is64 = true then 4 else 2) ∧ p.2 < 2 ^ 16 := by
      intro p hp
      rw [← hK] at hp
      obtain ⟨h1, -, h2⟩ := mem_kept.1 hp
      exact ⟨h1, h2 ▸ halfword_lt _ _⟩
    cases ks with
    | nil => cases hln
    | cons p R =>
      obtain ⟨i0, c0⟩ := p
      obtain ⟨hi0, hc0⟩ := hmem (i0, c0) (by simp)
      simp only [movSeqLines, List.mem_cons, List.mem_map] at hln
      rcases hln with rfl | ⟨⟨i, c⟩, hp, rfl⟩
      · cases inv
        · exact ⟨_, rfl, exec_movWide hn hc0 _ (.inl rfl) is64 hi0, rzOk_movWide hc0 _ (.inl rfl) _⟩
        · have : 2 ^ 16 - 1 - c0 < 2 ^ 16 := by omega
          exact ⟨_, rfl, exec_movWide hn this _ (.inr rfl) is64 hi0,
            rzOk_movWide this _ (.inr rfl) _⟩
      · obtain ⟨hi, hc⟩ := hmem (i, c) (by simp [hp])
        exact ⟨_, rfl, exec_movk' hn hc is64 hi, rzOk_movk _⟩

/-- Case 3 emits what `MInst.lines` emits for Cranelift's
`AluRRImmLogic { alu_op: Orr, size: Size64, rd, rn: zero_reg(), imml }`. -/
theorem lines_orr_xzr (c : FnCtx) (ps : PState) (rd : Reg) {v : Nat} {i : ImmLogic}
    (h : ImmLogic.ofNat? v .size64 = some i) :
    MInst.lines c (.aluRRImmLogic .orr .size64 rd .xzr i) ps =
      .ok ([.ins (.logicImm .orr true rd .xzr (mask64 v))], ps) := by
  rw [immLogic_eq h]
  rfl

end LoadConstant

open LoadConstant

/-- **The constant load** `loadConstLines (x n) v` (Cranelift's `Inst::load_constant`): every
line encodes, `x n` ends as `v` (mod 2^64), the pc advances by 4 per line, nothing else
changes (the twin of `steps_loadConst64`). -/
theorem steps_loadConstLines (env : Env) {n : Nat} (hn : n ≤ 30) (v : Nat) (s : Arm.ArmState) :
    StepsOk env (loadConstLines (.x n) v) s
      (pcx s n (Arm.r .PC s + BitVec.ofNat 64 (4 * (loadConstLines (.x n) v).length))
        (BitVec.ofNat 64 v)) := by
  have hg := good_loadConstLines hn v
  have hs := steps_lines env _ (fun ln h => let ⟨i, e, he, _⟩ := hg ln h; ⟨i, e, he⟩) s
  have hv : (loadConstLines (.x n) v).foldl (fun X ln => lineVal ln X)
      (Arm.r (.GPR (BitVec.ofNat 5 n)) s) = BitVec.ofNat 64 v := by
    generalize Arm.r (.GPR (BitVec.ofNat 5 n)) s = X
    have h0 : Rz 64 X (halfword X.toNat) := fun b _ => by
      rw [testBit_halfword _ _ _ (Nat.mod_lt _ (by decide)), Nat.div_add_mod]; rfl
    have h1 := rz_fold _ (fun ln h => let ⟨i, e, _, hr⟩ := hg ln h; ⟨i, e, hr⟩) X _ h0
    have h2 := rz_congr h1 (fun j hj => hw_loadConstLines _ v _ j (by omega)) rfl
    rw [eq_of_rz h2 (rz_ofNat (mask64 v))]
    apply BitVec.eq_of_toNat_eq
    simp [mask64]
  rw [hv] at hs
  exact hs

theorem movSeqLines_length (rd : Reg) (is64 inv : Bool) :
    ∀ ks : List (Nat × Nat), (movSeqLines rd is64 inv ks).length = ks.length
  | [] => rfl
  | _ :: _ => by simp [movSeqLines]

/-- At most 4 lines (the twin of `loadConst64_length`). -/
theorem loadConstLines_length (rd : Reg) (v : Nat) : (loadConstLines rd v).length ≤ 4 := by
  rcases loadConstLines_cases rd v with ⟨_, -, e⟩ | ⟨-, _, -, e⟩ | ⟨_, -, e⟩ | ⟨-, -, -, e⟩ <;>
    rw [e] <;> try simp
  unfold generalLines
  dsimp only
  rw [movSeqLines_length]
  refine Nat.le_trans (List.length_filterMap_le _ _) ?_
  simp only [List.length_range]
  split <;> omega

/-- The instruction forms of `loadConstLines rd v`: `movz`/`movn`, `movk` or `orr _, xzr, #_`,
all with destination `rd`. -/
def LcForm (rd : Reg) (i : Insn) : Prop :=
  (∃ op w imm, i = .movWide op w rd imm) ∨ (∃ w imm, i = .movk w rd imm) ∨
    ∃ val, i = .logicImm .orr true rd .xzr val

theorem ite_movWide (b : Prop) [Decidable b] (w : Bool) (rd : Reg) (x y : MoveWideConst) :
    ∃ op w' imm, (if b then Insn.movWide .movN w rd x else .movWide .movZ w rd y) =
      .movWide op w' rd imm := by
  by_cases h : b <;> simp [h]

/-- **The shape of `loadConstLines`**: every line is an instruction without a trap code, of one
of the `LcForm` forms. The per-property twins of the `loadConst64` lemmas follow from this
alone (`FV/Backend/Proof/LoadConstantTwins.lean`). -/
theorem mem_loadConstLines {rd : Reg} {v : Nat} {ln : Line} (h : ln ∈ loadConstLines rd v) :
    ∃ i, ln = .ins i none ∧ LcForm rd i := by
  rcases loadConstLines_cases rd v with ⟨_, -, e⟩ | ⟨-, _, -, e⟩ | ⟨_, -, e⟩ | ⟨-, -, -, e⟩ <;>
    rw [e] at h
  · simp only [List.mem_singleton] at h; exact ⟨_, h, .inl ⟨_, _, _, rfl⟩⟩
  · simp only [List.mem_singleton] at h; exact ⟨_, h, .inl ⟨_, _, _, rfl⟩⟩
  · simp only [List.mem_singleton] at h; exact ⟨_, h, .inr (.inr ⟨_, rfl⟩)⟩
  · unfold generalLines at h
    dsimp only at h
    generalize keptHalfwords _ _ _ = ks at h
    cases ks with
    | nil => cases h
    | cons p R =>
      simp only [movSeqLines, List.mem_cons, List.mem_map] at h
      rcases h with rfl | ⟨q, -, rfl⟩
      · exact ⟨_, rfl, .inl (ite_movWide _ _ _ _ _)⟩
      · exact ⟨_, rfl, .inr (.inl ⟨_, _, rfl⟩)⟩

/-- Every line encodes at any `env` (`ExecX`), for a destination `x n`, `n ≤ 30`. -/
theorem loadConstLines_toArmInst {n : Nat} (hn : n ≤ 30) (v : Nat) (env : Env) :
    ∀ i t, Line.ins i t ∈ loadConstLines (.x n) v → ∃ ai, i.toArmInst env = .ok ai := by
  intro i t h
  obtain ⟨i', e, hx, -⟩ := good_loadConstLines hn v _ h
  cases e
  obtain ⟨ai, ha, -⟩ := hx env
  exact ⟨ai, ha⟩

/-- `loadConstLines` is never empty (for `ArmAllocLS`'s use of `loadConst64_eq`). -/
theorem loadConstLines_ne_nil (rd : Reg) (v : Nat) : loadConstLines rd v ≠ [] := by
  rcases loadConstLines_cases rd v with ⟨_, -, e⟩ | ⟨-, _, -, e⟩ | ⟨_, -, e⟩ |
    ⟨h1, h2, h3, e⟩ <;> rw [e] <;> try simp
  unfold generalLines
  dsimp only
  have := general_ne (mask64_lt' v) h1 h2 h3 (decide (2 ^ 32 ≤ mask64 v))
    (decide (countZeroHalfWords (mask64 v) (if decide (2 ^ 32 ≤ mask64 v) = true then 4 else 2) <
      countZeroHalfWords (if decide (2 ^ 32 ≤ mask64 v) = true then 2 ^ 64 - 1 - mask64 v
        else 2 ^ 32 - 1 - mask64 v) (if decide (2 ^ 32 ≤ mask64 v) = true then 4 else 2)))
    rfl rfl (fun h => by simpa using h)
  revert this
  generalize keptHalfwords _ _ _ = ks
  intro h
  cases ks with
  | nil => exact absurd rfl h
  | cons _ _ => simp [movSeqLines]

end Backend.Proof

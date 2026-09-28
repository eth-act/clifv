import FV.Backend.Proof.RefinesInsts
import FV.Backend.Proof.RegallocInstsFP

/-!
# `Refines` for the remaining covered forms (M6 proof)

`RefAt` lemmas (see `RefinesInsts.lean`) for the forms whose Arm run needs more than the
`csimp_rules` unfolding:

* bitfield moves (`UBFM`/`SBFM` with symbolic `immr`/`imms`, as `bitfieldMove`, the immediate
  shifts `lsl`/`lsr`/`asr` and the extensions): `dbm64`/`dbm32` compute Arm's
  `DecodeBitMasks` for the non-immediate case (`len` from `highest_set_bit`), `bfm_core` is the
  bitwise identity between the masked Arm result and `bfmVal`, `exec_bfm64`/`exec_bfm32` state
  the instruction's effect (used by the `ref_*` runs before `exec_bitfield` is unfolded), and
  `bfm_lsr`/`bfm_asr`/`bfm_lsl`/`bfm_sxt`/`bfm_uxt` reduce `bfmVal` to the shift/extension;
* `ror` immediate (`EXTR Rd, Rn, Rn`): `extract_dup_ror`;
* `movn`: `pi_movw` (the `MOVN` immediate installed into zero);
* logical immediates: `bitmaskOk_spec` (from the per-instruction check `logicImmOk` of
  `FormOk`: the encoding exists and decodes to the operand);
* `cnt`/`addv`/`addp`/`umov`: the element loops of the Arm model unrolled (`cnt_aux_8`,
  `addv_aux_8`, `addp_aux_8`, `elem_get_sw64`), bit-blasted by `bv_decide`.
-/

namespace Backend.Proof

open Backend

/-! ## Vector forms -/

@[csimp_rules] theorem cnt_aux_8 (x : BitVec 64) : Arm.DPSFP.cnt_aux 0 8 x 0#64 = cntBytes x := by
  rw [Arm.DPSFP.cnt_aux, if_neg (by decide)]
  rw [Arm.DPSFP.cnt_aux, if_neg (by decide)]
  rw [Arm.DPSFP.cnt_aux, if_neg (by decide)]
  rw [Arm.DPSFP.cnt_aux, if_neg (by decide)]
  rw [Arm.DPSFP.cnt_aux, if_neg (by decide)]
  rw [Arm.DPSFP.cnt_aux, if_neg (by decide)]
  rw [Arm.DPSFP.cnt_aux, if_neg (by decide)]
  rw [Arm.DPSFP.cnt_aux, if_neg (by decide)]
  rw [Arm.DPSFP.cnt_aux, if_pos (by decide)]
  simp only [cntBytes, byteOf, Arm.elem_set, Arm.elem_get]
  generalize (x.extractLsb' 0 8).cpop = c0
  generalize (x.extractLsb' 8 8).cpop = c1
  generalize (x.extractLsb' 16 8).cpop = c2
  generalize (x.extractLsb' 24 8).cpop = c3
  generalize (x.extractLsb' 32 8).cpop = c4
  generalize (x.extractLsb' 40 8).cpop = c5
  generalize (x.extractLsb' 48 8).cpop = c6
  generalize (x.extractLsb' 56 8).cpop = c7
  simp only [Arm.BitVec.partInstall]
  bv_decide

@[csimp_rules] theorem addv_aux_8 (x : BitVec 64) :
    (Arm.DPSFP.addv_aux 0 8 8 x 0#8).setWidth 128 = (addvBytes x).setWidth 128 := by
  rw [Arm.DPSFP.addv_aux, if_neg (by decide)]
  rw [Arm.DPSFP.addv_aux, if_neg (by decide)]
  rw [Arm.DPSFP.addv_aux, if_neg (by decide)]
  rw [Arm.DPSFP.addv_aux, if_neg (by decide)]
  rw [Arm.DPSFP.addv_aux, if_neg (by decide)]
  rw [Arm.DPSFP.addv_aux, if_neg (by decide)]
  rw [Arm.DPSFP.addv_aux, if_neg (by decide)]
  rw [Arm.DPSFP.addv_aux, if_neg (by decide)]
  rw [Arm.DPSFP.addv_aux, if_pos (by decide)]
  simp only [addvBytes, byteOf, Arm.elem_get]
  bv_decide

@[csimp_rules] theorem addp_aux_8 (n m : BitVec 64) :
    Arm.DPSFP.addp_aux 0 8 8 (m ++ n) 0#64 = addpBytes n m := by
  rw [Arm.DPSFP.addp_aux, if_neg (by decide)]
  rw [Arm.DPSFP.addp_aux, if_neg (by decide)]
  rw [Arm.DPSFP.addp_aux, if_neg (by decide)]
  rw [Arm.DPSFP.addp_aux, if_neg (by decide)]
  rw [Arm.DPSFP.addp_aux, if_neg (by decide)]
  rw [Arm.DPSFP.addp_aux, if_neg (by decide)]
  rw [Arm.DPSFP.addp_aux, if_neg (by decide)]
  rw [Arm.DPSFP.addp_aux, if_neg (by decide)]
  rw [Arm.DPSFP.addp_aux, if_pos (by decide)]
  simp only [addpBytes, byteOf, Arm.elem_get, Arm.elem_set, Arm.BitVec.partInstall]
  bv_decide

@[csimp_rules] theorem elem_get_sw64 (a : BitVec 128) (k : Nat) (h : k < 8) :
    Arm.elem_get (a.setWidth 64) k 8 = a.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [Arm.elem_get, hi, Nat.mul_comm k 8]
  intro; omega

attribute [csimp_rules] Arm.reduce_lowest_set_bit

/-! ## `movn`, `ror` -/

@[csimp_rules] theorem pi_movw (b s n : Nat) (hb : b < 65536) :
    Arm.BitVec.partInstall s 16 (BitVec.ofNat 16 b) 0#n = BitVec.ofNat n b <<< s := by
  simp only [Arm.BitVec.partInstall, BitVec.zero_and, BitVec.zero_or]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt hb]

theorem extract_dup_ror {n : Nat} (x : BitVec n) (amt : Nat) (h : amt < n) :
    (x ++ x).extractLsb' amt n = x.rotateRight amt := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_rotateRight]
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    Nat.mod_eq_of_lt h]
  by_cases h1 : amt + i < n
  · simp [h1, show i < n - amt by omega]
  · simp [h1, show ¬ i < n - amt by omega, show i - (n - amt) < n by omega,
      show amt + i - n = i - (n - amt) by omega]


/-! ## Bitfield moves -/

theorem hsb64 (s : BitVec 6) : Arm.highest_set_bit (1#1 ++ ~~~s) = 6 := by
  unfold Arm.highest_set_bit
  rw [Arm.highest_set_bit.go]
  have : Arm.BitVec.lsb (1#1 ++ ~~~s) (1 + 6 - 1) = 1#1 := by
    simp only [Arm.BitVec.lsb]; bv_decide
  simp [this]

/-- `decode_bit_masks` (non-immediate) with the element length `len` given. -/
theorem dbm_len (immN : BitVec 1) (imms immr : BitVec 6) (M len : Nat)
    (hlen : Arm.highest_set_bit (immN ++ ~~~imms) = len)
    (hv : Arm.invalid_bit_masks immN imms false M = false)
    (hd : (1 <<< len) * (M / (1 <<< len)) = M) :
    Arm.decode_bit_masks immN imms immr false M =
      some (BitVec.cast hd (BitVec.replicate (M / (1 <<< len))
          (((BitVec.allOnes ((imms &&& (BitVec.allOnes len).setWidth 6).toNat + 1)).setWidth
            (1 <<< len)).rotateRight (immr &&& (BitVec.allOnes len).setWidth 6).toNat)),
        BitVec.cast hd (BitVec.replicate (M / (1 <<< len))
          ((BitVec.allOnes ((BitVec.extractLsb' 0 len ((imms &&& (BitVec.allOnes len).setWidth 6) -
            (immr &&& (BitVec.allOnes len).setWidth 6))).toNat + 1)).setWidth (1 <<< len)))) := by
  subst hlen
  unfold Arm.decode_bit_masks
  simp only [hv, Bool.false_eq_true, dite_false]
  rfl

theorem bfm_core {n : Nat} (x : BitVec n) (r s : Nat) (hr : r < n) (hs : s < n) (sg : Bool) :
    ((if sg then (BitVec.replicate n (x.extractLsb' s 1)).cast (Nat.one_mul n) else 0#n) &&&
        ~~~((BitVec.allOnes ((s + n - r) % n + 1)).setWidth n) |||
      ((x.rotateRight r &&& ((BitVec.allOnes (s + 1)).setWidth n).rotateRight r) &&&
        (BitVec.allOnes ((s + n - r) % n + 1)).setWidth n)) =
      bfmVal (if sg then .sBfm else .uBfm) x r s := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_allOnes, BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hr, hi, decide_true,
    Bool.true_and]
  unfold bfmVal
  by_cases hrs : r ≤ s
  · have hd : (s + n - r) % n = s - r := by
      rw [show s + n - r = (s - r) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp only [hd, hrs, if_true]
    cases sg
    · simp only [Bool.false_eq_true, if_false, BitVec.getLsbD_zero, Bool.false_and, Bool.false_or,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
      by_cases h1 : i < n - r <;> by_cases h2 : i < s - r + 1 <;>
        simp [h1, h2, hi, Nat.mod_one, show r + (s - r) = s by omega] <;> omega
    · simp only [if_true, BitVec.getLsbD_cast, BitVec.getLsbD_replicate, BitVec.getLsbD_signExtend,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.msb_eq_getLsbD_last]
      by_cases h1 : i < n - r <;> by_cases h2 : i < s - r + 1 <;>
        simp [h1, h2, hi, Nat.mod_one, show r + (s - r) = s by omega] <;> omega
  · have hd : (s + n - r) % n = s + n - r := Nat.mod_eq_of_lt (by omega)
    simp only [hd, hrs, if_false]
    cases sg
    · simp only [Bool.false_eq_true, if_false, BitVec.getLsbD_zero, Bool.false_and, Bool.false_or,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft]
      by_cases h1 : i < n - r <;> by_cases h2 : i < s + n - r + 1 <;>
        by_cases h3 : i - (n - r) < s + 1 <;>
        simp [h1, h2, h3, hi, Nat.mod_one, show i - (n - r) < n by omega] <;> omega
    · simp only [if_true, BitVec.getLsbD_cast, BitVec.getLsbD_replicate, BitVec.getLsbD_signExtend,
        BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.msb_eq_getLsbD_last]
      by_cases h1 : i < n - r <;> by_cases h2 : i < s + n - r + 1 <;>
        by_cases h3 : i - (n - r) < s + 1 <;>
        simp [h1, h2, h3, hi, Nat.mod_one, show i - (n - r) < n by omega] <;> omega

theorem ibm64 (s : BitVec 6) : Arm.invalid_bit_masks 1#1 s false 64 = false := by
  unfold Arm.invalid_bit_masks
  simp [hsb64, Arm.BitVec.width]

theorem dbm64 (r s : Nat) (hr : r < 64) (hs : s < 64) :
    Arm.decode_bit_masks 1#1 (BitVec.ofNat 6 s) (BitVec.ofNat 6 r) false 64 =
      some (((BitVec.allOnes (s + 1)).setWidth 64).rotateRight r,
        (BitVec.allOnes ((s + 64 - r) % 64 + 1)).setWidth 64) := by
  rw [dbm_len _ _ _ 64 6 (hsb64 _) (ibm64 _) (by decide)]
  have e0 : (BitVec.allOnes 6).setWidth 6 = BitVec.allOnes 6 := BitVec.setWidth_eq _
  have e1 : (BitVec.ofNat 6 s &&& (BitVec.allOnes 6).setWidth 6).toNat = s := by
    rw [e0, BitVec.and_allOnes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]
  have e2 : (BitVec.ofNat 6 r &&& (BitVec.allOnes 6).setWidth 6).toNat = r := by
    rw [e0, BitVec.and_allOnes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have e3 : (BitVec.extractLsb' 0 6 ((BitVec.ofNat 6 s &&& (BitVec.allOnes 6).setWidth 6) -
      (BitVec.ofNat 6 r &&& (BitVec.allOnes 6).setWidth 6))).toNat = (s + 64 - r) % 64 := by
    rw [e0, BitVec.and_allOnes, BitVec.and_allOnes, ext0, BitVec.setWidth_eq, BitVec.toNat_sub,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · simp only [BitVec.getLsbD_cast, BitVec.getLsbD_replicate, BitVec.getLsbD_rotateRight,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, e1, e2, Nat.reduceShiftLeft, Nat.reduceDiv,
      Nat.reduceMul, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hr, hi, decide_true, Bool.true_and]
  · simp only [BitVec.getLsbD_cast, BitVec.getLsbD_replicate, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_allOnes, e3, Nat.reduceShiftLeft, Nat.reduceDiv, Nat.reduceMul,
      Nat.mod_eq_of_lt hi, hi, decide_true, Bool.true_and]

@[csimp_rules ↓ high] theorem exec_bfm64 (opc : BitVec 2) (hopc : opc = 0#2 ∨ opc = 2#2) (immr imms : Nat)
    (hr : immr < 64) (hs : imms < 64) (Rn Rd : BitVec 5) (st : Arm.ArmState) :
    Arm.DPI.exec_bitfield (Arm.Bitfield_cls.mk 1#1 opc 0b100110#6 1#1 (BitVec.ofNat 6 immr)
        (BitVec.ofNat 6 imms) Rn Rd) st =
      Arm.write_pc (Arm.read_pc (Arm.write_gpr_zr 64 Rd (bfmVal (if opc = 0#2 then .sBfm else .uBfm)
          (Arm.read_gpr_zr 64 Rn st) immr imms) st) + 4#64)
        (Arm.write_gpr_zr 64 Rd (bfmVal (if opc = 0#2 then .sBfm else .uBfm)
          (Arm.read_gpr_zr 64 Rn st) immr imms) st) := by
  rcases hopc with rfl | rfl <;> unfold Arm.DPI.exec_bitfield <;>
    simp (config := {decide := true}) only [dreduceIte, false_or, false_and, if_false]
  all_goals simp only [dbm64 immr imms hr hs]
  · have hv := bfm_core (Arm.read_gpr_zr 64 Rn st) immr imms hr hs true
    simp only [ite_true, Arm.BitVec.ror, Arm.BitVec.lsb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr,
      Nat.mod_eq_of_lt hs, show (2 ^ 6 : Nat) = 64 from rfl, BitVec.zero_eq, BitVec.zero_and,
      BitVec.zero_or] at hv ⊢
    rw [hv]
  · have hv := bfm_core (Arm.read_gpr_zr 64 Rn st) immr imms hr hs false
    simp only [ite_true, Bool.false_eq_true, if_false, Arm.BitVec.ror, Arm.BitVec.lsb,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs, show (2 ^ 6 : Nat) = 64 from rfl,
      BitVec.zero_eq, BitVec.zero_and, BitVec.zero_or, show (2#2 = 0#2) = False by decide] at hv ⊢
    rw [hv]

theorem hsb32 (s : Nat) (hs : s < 32) : Arm.highest_set_bit (0#1 ++ ~~~BitVec.ofNat 6 s) = 5 := by
  unfold Arm.highest_set_bit
  rw [Arm.highest_set_bit.go, Arm.highest_set_bit.go]
  have hs' : BitVec.ofNat 6 s < 32#6 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat]; simp; omega
  have h6 : Arm.BitVec.lsb (0#1 ++ ~~~BitVec.ofNat 6 s) (1 + 6 - 1) = 0#1 := by
    simp only [Arm.BitVec.lsb]; bv_decide
  have h5 : Arm.BitVec.lsb (0#1 ++ ~~~BitVec.ofNat 6 s) (1 + 6 - 1 - 1) = 1#1 := by
    generalize BitVec.ofNat 6 s = y at hs' ⊢
    simp only [Arm.BitVec.lsb]; bv_decide
  simp [h6, h5]

theorem ibm32 (s : Nat) (hs : s < 32) : Arm.invalid_bit_masks 0#1 (BitVec.ofNat 6 s) false 32 = false := by
  unfold Arm.invalid_bit_masks
  simp [hsb32 s hs, Arm.BitVec.width]

theorem dbm32 (r s : Nat) (hr : r < 32) (hs : s < 32) :
    Arm.decode_bit_masks 0#1 (BitVec.ofNat 6 s) (BitVec.ofNat 6 r) false 32 =
      some (((BitVec.allOnes (s + 1)).setWidth 32).rotateRight r,
        (BitVec.allOnes ((s + 32 - r) % 32 + 1)).setWidth 32) := by
  rw [dbm_len _ _ _ 32 5 (hsb32 s hs) (ibm32 s hs) (by decide)]
  have e1 : (BitVec.ofNat 6 s &&& (BitVec.allOnes 5).setWidth 6).toNat = s := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_allOnes]
    rw [Nat.mod_eq_of_lt (by omega : s < 2 ^ 6)]
    show s &&& 31 = s
    rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have e2 : (BitVec.ofNat 6 r &&& (BitVec.allOnes 5).setWidth 6).toNat = r := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_allOnes]
    rw [Nat.mod_eq_of_lt (by omega : r < 2 ^ 6)]
    show r &&& 31 = r
    rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have e3 : (BitVec.extractLsb' 0 5 ((BitVec.ofNat 6 s &&& (BitVec.allOnes 5).setWidth 6) -
      (BitVec.ofNat 6 r &&& (BitVec.allOnes 5).setWidth 6))).toNat = (s + 32 - r) % 32 := by
    rw [ext0, BitVec.toNat_setWidth, BitVec.toNat_sub, e1, e2]
    omega
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · simp only [BitVec.getLsbD_cast, BitVec.getLsbD_replicate, BitVec.getLsbD_rotateRight,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, e1, e2, Nat.reduceShiftLeft, Nat.reduceDiv,
      Nat.reduceMul, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hr, hi, decide_true, Bool.true_and]
  · simp only [BitVec.getLsbD_cast, BitVec.getLsbD_replicate, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_allOnes, e3, Nat.reduceShiftLeft, Nat.reduceDiv, Nat.reduceMul,
      Nat.mod_eq_of_lt hi, hi, decide_true, Bool.true_and]

@[csimp_rules ↓ high] theorem exec_bfm32 (opc : BitVec 2) (hopc : opc = 0#2 ∨ opc = 2#2) (immr imms : Nat)
    (hr : immr < 32) (hs : imms < 32) (Rn Rd : BitVec 5) (st : Arm.ArmState) :
    Arm.DPI.exec_bitfield (Arm.Bitfield_cls.mk 0#1 opc 0b100110#6 0#1 (BitVec.ofNat 6 immr)
        (BitVec.ofNat 6 imms) Rn Rd) st =
      Arm.write_pc (Arm.read_pc (Arm.write_gpr_zr 32 Rd (bfmVal (if opc = 0#2 then .sBfm else .uBfm)
          (Arm.read_gpr_zr 32 Rn st) immr imms) st) + 4#64)
        (Arm.write_gpr_zr 32 Rd (bfmVal (if opc = 0#2 then .sBfm else .uBfm)
          (Arm.read_gpr_zr 32 Rn st) immr imms) st) := by
  have l5r := lsb5_of_lt hr
  have l5s := lsb5_of_lt hs
  rcases hopc with rfl | rfl <;> unfold Arm.DPI.exec_bitfield <;>
    simp (config := {decide := true}) only [dreduceIte, false_or, false_and, true_and, l5r, l5s,
      ne_eq, not_true, or_self, if_false]
  all_goals simp only [dbm32 immr imms hr hs]
  · have hv := bfm_core (Arm.read_gpr_zr 32 Rn st) immr imms hr hs true
    simp only [ite_true, Arm.BitVec.ror, Arm.BitVec.lsb, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show immr < 2 ^ 6 by omega), Nat.mod_eq_of_lt (show imms < 2 ^ 6 by omega),
      BitVec.zero_eq, BitVec.zero_and, BitVec.zero_or] at hv ⊢
    rw [hv]
  · have hv := bfm_core (Arm.read_gpr_zr 32 Rn st) immr imms hr hs false
    simp only [ite_true, Bool.false_eq_true, if_false, Arm.BitVec.ror, Arm.BitVec.lsb,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show immr < 2 ^ 6 by omega),
      Nat.mod_eq_of_lt (show imms < 2 ^ 6 by omega),
      BitVec.zero_eq, BitVec.zero_and, BitVec.zero_or, show (2#2 = 0#2) = False by decide] at hv ⊢
    rw [hv]

/-! ## Logical immediates -/

/-- What the per-instruction check `bitmaskOk` gives: the encoding and its decoding. -/
theorem bitmaskOk_spec {M : Nat} {is64 : Bool} {v : Nat} {e : BitVec M} (h : bitmaskOk M is64 v e = true) :
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

/-! ## The `RefAt` lemmas -/

/-- A form `ispec` leaves unspecified refines trivially. -/
theorem refAt_none' (F : BitVec 64 → Prop) (ctx : FnCtx) {i : MInst} {us : List CV}
    (h : ∀ w, ispec i us w = none) : RefAt F ctx i us :=
  fun w _ _ _ _ hs => by rw [h] at hs; cases hs

/-- `ref_body` without the final matching step (for forms that rewrite first). -/
syntax "ref_pre" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| ref_pre) => `(tactic| (
    intro w outs w' ctl he h
    ss_tac
    all_goals (simp (config := {decide := true}) [ispec, rrrVal, aluVal, shiftVal, mulAddVal,
      aluShiftable, extendVal, movWideVal, movKVal, *] at h)
    all_goals (try simp only [awc_sub, Arm.fst_AddWithCarry_eq_add] at h)
    all_goals (try dsimp only [OperandSize.bits, opnd, lo64] at h)
    all_goals (revert h; try simp only [and_imp])
    all_goals intros
    all_goals subst_vars
    all_goals (try (exfalso; omega))
    all_goals (simp (config := {decide := true}) [csimp_rules, he, Arm.w_program, imm12_enc,
      sw_ofNat, le_false, ↓dsh_lsl, ↓dsh_lsr, ↓dsh_asr, ↓dsh_ror, lsb5_of_lt, and32_of_lt,
      mod64_of_lt32, mod_of_lt', nzcv_n, nzcv_z, nzcv_c, nzcv_v, Arm.reduceDecodeBitMasks, *])))

@[csimp_rules] theorem bfm_lsr {n : Nat} (x : BitVec n) (amt k : Nat) (hk : k + 1 = n) (h : amt < n) :
    bfmVal .uBfm x amt k = x >>> amt := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [bfmVal, show amt ≤ k by omega, if_true, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  by_cases h1 : i < k - amt + 1
  · simp [h1]
  · simp [h1, BitVec.getLsbD_of_ge x (amt + i) (by omega)]

@[csimp_rules] theorem bfm_asr {n : Nat} (x : BitVec n) (amt k : Nat) (hk : k + 1 = n) (h : amt < n) :
    bfmVal .sBfm x amt k = x.sshiftRight amt := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [bfmVal, show amt ≤ k by omega, if_true, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_sshiftRight, hi,
    decide_true, Bool.true_and, BitVec.msb_eq_getLsbD_last]
  by_cases h1 : i < k - amt + 1 <;> by_cases h2 : amt + i < n <;>
    simp [h1, h2, show ¬ n ≤ i by omega, show k - amt + 1 - 1 < k - amt + 1 by omega,
      show amt + (k - amt + 1 - 1) = n - 1 by omega] <;> (try omega)
  rw [show amt + (k - amt) = n - 1 by omega]

@[csimp_rules] theorem bfm_lsl {n : Nat} (x : BitVec n) (amt k : Nat) (hk : k = n - 1 - amt)
    (h : amt < n) : bfmVal .uBfm x ((n - amt) % n) k = x <<< amt := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rcases Nat.eq_zero_or_pos amt with rfl | hpos
  · simp only [Nat.sub_zero, Nat.mod_self, bfmVal, Nat.zero_le, if_true, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and,
      Nat.zero_add, Nat.sub_zero]
    simp [show i < k + 1 by omega]
  · have hm : (n - amt) % n = n - amt := Nat.mod_eq_of_lt (by omega)
    simp only [hm, bfmVal, show ¬ n - amt ≤ k by omega, if_false, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, show n - (n - amt) = amt by omega]
    by_cases h1 : i < amt <;> simp [h1] <;> (try omega)
    simp [show i - amt < n by omega, show i - amt < k + 1 by omega]

@[csimp_rules] theorem bfm_sxt {n : Nat} (x : BitVec n) (k : Nat) :
    bfmVal .sBfm x 0 k = (x.setWidth (k + 1)).signExtend n := by
  simp [bfmVal]

@[csimp_rules] theorem bfm_uxt {n : Nat} (x : BitVec n) (k : Nat) :
    bfmVal .uBfm x 0 k = (x.setWidth (k + 1)).setWidth n := by
  simp [bfmVal]

variable (F : BitVec 64 → Prop) (ctx : FnCtx)

set_option maxHeartbeats 4000000 in
theorem ref_aluRRRShift_xd (op : ALUOp) (sz : OperandSize) (n m : Nat) (sh : ShiftOpAndAmt) (a b : CV) :
    RefAt F ctx (.aluRRRShift op sz .xzr (.vreg n .int) (.vreg m .int) sh) [a, b] := by
  obtain ⟨so, amt⟩ := sh
  cases op <;> cases sz <;> cases so <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_aluRRRShift_xn (op : ALUOp) (sz : OperandSize) (d m : Nat) (sh : ShiftOpAndAmt) (b : CV) :
    RefAt F ctx (.aluRRRShift op sz (.vreg d .int) .xzr (.vreg m .int) sh) [b] := by
  obtain ⟨so, amt⟩ := sh
  cases op <;> cases sz <;> cases so <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_movN (d : Nat) (imm : MoveWideConst) (sz : OperandSize) :
    RefAt F ctx (.movWide .movN (.vreg d .int) imm sz) [] := by
  obtain ⟨bits, sh⟩ := imm
  rcases sh with _ | _ | _ | _ | sh <;> cases sz <;> ref_tac

theorem ref_movWide' (op : MoveWideOp) (d : Nat) (imm : MoveWideConst) (sz : OperandSize) :
    RefAt F ctx (.movWide op (.vreg d .int) imm sz) [] := by
  cases op
  · exact ref_movWide F ctx d imm sz
  · exact ref_movN F ctx d imm sz

set_option maxHeartbeats 4000000 in
theorem ref_movToFpu (sz : ScalarSize) (d n : Nat) (a : CV) :
    RefAt F ctx (.movToFpu (.vreg d .float) (.vreg n .int) sz) [a] := by
  cases sz
  all_goals first
    | ref_tac
    | exact refAt_none' F ctx (fun w => by simp [ispec])

set_option maxHeartbeats 4000000 in
theorem ref_vecMisc (op : VecMisc2) (sz : VectorSize) (d n : Nat) (a : CV) :
    RefAt F ctx (.vecMisc op (.vreg d .float) (.vreg n .float) sz) [a] := by
  cases op; cases sz
  all_goals first
    | ref_tac
    | exact refAt_none' F ctx (fun w => by simp [ispec])

set_option maxHeartbeats 4000000 in
theorem ref_vecLanes (op : VecLanesOp) (sz : VectorSize) (d n : Nat) (a : CV) :
    RefAt F ctx (.vecLanes op (.vreg d .float) (.vreg n .float) sz) [a] := by
  cases op <;> cases sz
  all_goals first
    | ref_tac
    | exact refAt_none' F ctx (fun w => by simp [ispec])

set_option maxHeartbeats 4000000 in
theorem ref_vecRRR (op : VecALUOp) (sz : VectorSize) (d n m : Nat) (a b : CV) :
    RefAt F ctx (.vecRRR op (.vreg d .float) (.vreg n .float) (.vreg m .float) sz) [a, b] := by
  cases op; cases sz
  all_goals first
    | ref_tac
    | exact refAt_none' F ctx (fun w => by simp [ispec])

set_option maxHeartbeats 4000000 in
theorem ref_movFromVec (idx : Nat) (sz : ScalarSize) (d n : Nat) (a : CV) :
    RefAt F ctx (.movFromVec (.vreg d .int) (.vreg n .float) idx sz) [a] := by
  by_cases hs : sz = .size8 ∧ idx < 16
  · obtain ⟨rfl, hi⟩ := hs
    iterate 16 (rcases idx with _ | idx; · ref_tac)
    omega
  · exact refAt_none' F ctx (fun w => by cases sz <;> simp_all [ispec])

set_option maxHeartbeats 4000000 in
theorem ref_bitfieldMove (sz : OperandSize) (op : BfmOp) (d n immr imms : Nat) (a : CV) :
    RefAt F ctx (.bitfieldMove sz op (.vreg d .int) (.vreg n .int) immr imms) [a] := by
  cases sz <;> cases op <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_aluRRImmShift (op : ALUOp) (hop : shiftOpOk op = true) (sz : OperandSize) (d n amt : Nat)
    (a : CV) : RefAt F ctx (.aluRRImmShift op sz (.vreg d .int) (.vreg n .int) amt) [a] := by
  have h1 : (64 - amt) % 64 < 64 := Nat.mod_lt _ (by decide)
  have h2 : 63 - amt < 64 := by omega
  have h3 : (32 - amt) % 32 < 32 := Nat.mod_lt _ (by decide)
  have h4 : 31 - amt < 32 := by omega
  cases op <;> simp [shiftOpOk] at hop <;> cases sz
  all_goals first
    | (ref_pre <;> rw [extract_dup_ror _ _ ‹_›] <;> ref_fin)
    | ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_extend (d n : Nat) (sg : Bool) (fb tb : Nat) (a : CV) :
    RefAt F ctx (.extend (.vreg d .int) (.vreg n .int) sg fb tb) [a] := by
  by_cases hc : (fb = 8 ∧ tb = 16) ∨ ((fb = 8 ∨ fb = 16 ∨ fb = 32) ∧ (tb = 32 ∨ tb = 64) ∧ fb < tb)
  · rcases hc with ⟨rfl, rfl⟩ | ⟨h1 | h1 | h1, h2 | h2, h3⟩ <;> subst_vars <;>
      (try (exfalso; omega)) <;> cases sg <;> ref_tac
  · refine refAt_none' F ctx (fun w => ?_)
    by_cases h3 : fb = 8 <;> by_cases h4 : tb = 16 <;> simp_all [ispec] <;> omega

set_option maxHeartbeats 4000000 in
theorem ref_aluRRImmLogic (op : ALUOp) (hop : logicOpOk op = true) (sz : OperandSize) (d n : Nat)
    (imm : ImmLogic) (hchk : logicImmOk op sz imm = true) (a : CV) :
    RefAt F ctx (.aluRRImmLogic op sz (.vreg d .int) (.vreg n .int) imm) [a] := by
  cases op <;> simp [logicOpOk] at hop <;> cases sz <;>
    obtain ⟨N, immr, imms, tm, hb, hd, hN⟩ := bitmaskOk_spec hchk <;> clear hchk <;>
    (try (obtain rfl := hN rfl)) <;> clear hN <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_aluRRImmLogic_xd (sz : OperandSize) (n : Nat) (imm : ImmLogic)
    (hchk : logicImmOk .andS sz imm = true) (a : CV) :
    RefAt F ctx (.aluRRImmLogic .andS sz .xzr (.vreg n .int) imm) [a] := by
  cases sz <;> obtain ⟨N, immr, imms, tm, hb, hd, hN⟩ := bitmaskOk_spec hchk <;> clear hchk <;>
    (try (obtain rfl := hN rfl)) <;> clear hN <;> ref_tac

set_option maxHeartbeats 4000000 in
theorem ref_aluRRImmLogic_xn (op : ALUOp) (hop : logicOpOk op = true) (sz : OperandSize) (d : Nat)
    (imm : ImmLogic) (hchk : logicImmOk op sz imm = true) :
    RefAt F ctx (.aluRRImmLogic op sz (.vreg d .int) .xzr imm) [] := by
  cases op <;> simp [logicOpOk] at hop <;> cases sz <;>
    obtain ⟨N, immr, imms, tm, hb, hd, hN⟩ := bitmaskOk_spec hchk <;> clear hchk <;>
    (try (obtain rfl := hN rfl)) <;> clear hN <;> ref_tac
end Backend.Proof

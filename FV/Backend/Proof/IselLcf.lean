import FV.Backend.Proof.IselFamAluBBase

/-!
# `load_constant_full`: the `movz`/`movn` + `movk` sequence materialises its value

`Backend.loadConstantFull bits signExt extendTo value st` (the transcription of Cranelift's
`load_constant_full`) computes the constant `lcfValue …` (masked and extended), picks `movz` or
`movn` with the fewest remaining 16-bit slices, then patches every differing slice with a
`movk`. `lcf_run`: the emitted code has `CodeShape` and every run of it (under any `isem`
refining `ispec`) leaves `lcfValue …` in the result vreg.

Arithmetic is on `Nat` 16-bit slices (`slice16`, `replace16`: `load_constant_full`'s `get`,
`replace`); with the slice index and the operation width made concrete every fact is linear
arithmetic with literal divisors (`omega`), and `movk`'s bit masking is a `bv_decide` identity.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- 16-bit slice `i` of `v`. -/
def slice16 (v i : Nat) : Nat := (v / 2 ^ (i * 16)) % 2 ^ 16

/-- `v` with slice `sh` replaced by `new`. -/
def replace16 (old new sh : Nat) : Nat := old - slice16 old sh * 2 ^ (sh * 16) + new * 2 ^ (sh * 16)

/-- The value `load_constant_full` materialises. -/
def lcfValue (bits : Nat) (signExt : Bool) (extendTo : OperandSize) (value : Nat) : Nat :=
  let value := mask64 value
  match extendTo, signExt with
  | .size32, true => if bits < 32 then u64 (sextFrom bits value) % 2 ^ 32 else value
  | .size32, false => if bits < 32 then value % 2 ^ bits else value
  | .size64, true => if bits < 64 then u64 (sextFrom bits value) else value
  | .size64, false => if bits < 64 then value % 2 ^ bits else value

/-- The operation size `load_constant_full` uses for `value`. -/
def lcfSize (value : Nat) : OperandSize := if value / 2 ^ 32 == 0 then .size32 else .size64

/-- A `movz`/`movn` candidate: the value after the first instruction, the op, the first slice. -/
def lcfCand (value K : Nat) (op : MoveWideOp) (base : Nat) : Nat × MoveWideOp × Nat :=
  let first := ((List.range K).find? fun i => slice16 (Nat.xor base value) i != 0).getD 0
  (replace16 base (slice16 value first) first, op, first)

/-- The chosen first instruction. -/
def lcfFirst (value : Nat) (size : OperandSize) : Nat × MoveWideOp × Nat :=
  let cz := lcfCand value (size.bits / 16) .movZ 0
  let cn := lcfCand value (size.bits / 16) .movN (2 ^ size.bits - 1)
  let cnt (b : Nat) := ((List.range 4).filter fun i => slice16 (Nat.xor b value) i != 0).length
  if cnt cn.1 < cnt cz.1 then cn else cz

/-- One `movk` step. -/
def lcfStep (value first : Nat) (size : OperandSize) (acc : Reg × LState × Nat) (sh : Nat) :
    Reg × LState × Nat :=
  if sh ≤ first then acc else
  let b := slice16 value sh
  if b != slice16 acc.2.2 sh then
    ((acc.2.1.fresh .int).1,
      (acc.2.1.fresh .int).2.emit (.movK (acc.2.1.fresh .int).1 acc.1 ⟨b, sh⟩ size),
      replace16 acc.2.2 b sh)
  else acc

theorem lcf_eq (bits : Nat) (sg : Bool) (sz : OperandSize) (v : Nat) (st : LState) :
    loadConstantFull bits sg sz v st =
      let value := lcfValue bits sg sz v
      let size := lcfSize value
      let c := lcfFirst value size
      let imm : MoveWideConst :=
        ⟨match c.2.1 with
          | .movZ => slice16 value c.2.2
          | .movN => 2 ^ 16 - 1 - slice16 value c.2.2, c.2.2⟩
      let st1 := (st.fresh .int).2.emit (.movWide c.2.1 (st.fresh .int).1 imm size)
      let r := (List.range (size.bits / 16)).foldl (lcfStep value c.2.2 size)
        ((st.fresh .int).1, st1, c.1)
      (r.1, r.2.1) := by
  unfold loadConstantFull
  rfl

/-! ## Slice arithmetic -/

theorem slice16_xor (a b i : Nat) :
    slice16 (Nat.xor a b) i = Nat.xor (slice16 a i) (slice16 b i) := by
  unfold slice16
  change (a ^^^ b) / 2 ^ (i * 16) % 2 ^ 16 = (a / 2 ^ (i * 16) % 2 ^ 16) ^^^ (b / 2 ^ (i * 16) % 2 ^ 16)
  rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow]

theorem nat_xor_eq_zero {a b : Nat} : Nat.xor a b = 0 ↔ a = b := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have := congrArg (Nat.testBit · i) h
    change (a ^^^ b).testBit i = (0 : Nat).testBit i at this
    simp only [Nat.testBit_xor, Nat.zero_testBit] at this
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
  · rintro rfl; exact Nat.xor_self a

/-- The operation widths `load_constant_full` uses. -/
abbrev Wid (n : Nat) : Prop := n = 32 ∨ n = 64

theorem replace16_lt {n old new sh : Nat} (hn : Wid n) (ho : old < 2 ^ n) (hb : new < 2 ^ 16)
    (hs : sh < n / 16) : replace16 old new sh < 2 ^ n := by
  unfold replace16 slice16
  rcases hn with rfl | rfl
  · obtain rfl | rfl : sh = 0 ∨ sh = 1 := by omega
    all_goals simp only [Nat.reducePow, Nat.zero_mul, Nat.one_mul, Nat.pow_zero,
      Nat.div_one] at *; omega
  · obtain rfl | rfl | rfl | rfl : sh = 0 ∨ sh = 1 ∨ sh = 2 ∨ sh = 3 := by omega
    all_goals simp only [Nat.reducePow, Nat.zero_mul, Nat.one_mul, Nat.pow_zero,
      Nat.div_one] at *; omega

theorem slice16_replace16 {n old new sh i : Nat} (hn : Wid n) (ho : old < 2 ^ n)
    (hb : new < 2 ^ 16) (hs : sh < n / 16) (hi : i < n / 16) :
    slice16 (replace16 old new sh) i = if i = sh then new else slice16 old i := by
  unfold replace16 slice16
  rcases hn with rfl | rfl
  · obtain rfl | rfl : sh = 0 ∨ sh = 1 := by omega
    all_goals obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    all_goals simp only [Nat.reducePow, Nat.zero_mul, Nat.one_mul, Nat.pow_zero,
      Nat.div_one, reduceIte, Nat.reduceEqDiff] at *; omega
  · obtain rfl | rfl | rfl | rfl : sh = 0 ∨ sh = 1 ∨ sh = 2 ∨ sh = 3 := by omega
    all_goals obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals simp only [Nat.reducePow, Nat.zero_mul, Nat.one_mul, Nat.pow_zero,
      Nat.div_one, reduceIte, Nat.reduceEqDiff] at *; omega

theorem slice16_lt (v i : Nat) : slice16 v i < 2 ^ 16 := Nat.mod_lt _ (by decide)

theorem eq_of_slice16 {n x y : Nat} (hn : Wid n) (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    (h : ∀ i < n / 16, slice16 x i = slice16 y i) : x = y := by
  unfold slice16 at h
  rcases hn with rfl | rfl
  · have h0 := h 0 (by decide); have h1 := h 1 (by decide)
    simp only [Nat.reducePow, Nat.zero_mul, Nat.one_mul, Nat.pow_zero,
      Nat.div_one] at *; omega
  · have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
    have h3 := h 3 (by decide)
    simp only [Nat.reducePow, Nat.zero_mul, Nat.one_mul, Nat.pow_zero,
      Nat.div_one] at *; omega

/-! ## The first instruction -/

/-- What the candidate after the first instruction satisfies. -/
theorem lcfCand_spec {n value base : Nat} (hn : Wid n) (hv : value < 2 ^ n) (hb : base < 2 ^ n)
    (op : MoveWideOp) :
    let c := lcfCand value (n / 16) op base
    c.2.1 = op ∧ c.2.2 < n / 16 ∧ c.1 = replace16 base (slice16 value c.2.2) c.2.2 ∧
      c.1 < 2 ^ n ∧ ∀ i < n / 16, i ≤ c.2.2 → slice16 c.1 i = slice16 value i := by
  have hK : 0 < n / 16 := by rcases hn with rfl | rfl <;> decide
  have key : ∀ f, f < n / 16 → (∀ j < f, slice16 base j = slice16 value j) →
      f < n / 16 ∧ replace16 base (slice16 value f) f < 2 ^ n ∧
      ∀ i < n / 16, i ≤ f → slice16 (replace16 base (slice16 value f) f) i = slice16 value i := by
    intro f hf hlt
    refine ⟨hf, replace16_lt hn hb (slice16_lt _ _) hf, fun i hi hif => ?_⟩
    rw [slice16_replace16 hn hb (slice16_lt _ _) hf hi]
    split
    · subst_vars; rfl
    · exact hlt i (by omega)
  simp only [lcfCand, true_and]
  cases hf : (List.range (n / 16)).find? (fun i => slice16 (Nat.xor base value) i != 0) with
  | some f =>
    rw [List.find?_range_eq_some] at hf
    obtain ⟨-, hmem, hbefore⟩ := hf
    simp only [Option.getD_some]
    have hlt : ∀ j < f, slice16 base j = slice16 value j := by
      intro j hj
      have := hbefore j hj
      have h' : slice16 (base ^^^ value) j = 0 := by simpa using this
      rwa [show base ^^^ value = Nat.xor base value from rfl, slice16_xor, nat_xor_eq_zero] at h'
    obtain ⟨h1, h2, h3⟩ := key f (List.mem_range.mp hmem) hlt
    exact ⟨h1, h2, h3⟩
  | none =>
    rw [List.find?_range_eq_none] at hf
    simp only [Option.getD_none]
    have hall : ∀ j < n / 16, slice16 base j = slice16 value j := by
      intro j hj
      have := hf j hj
      have h' : slice16 (base ^^^ value) j = 0 := by simpa using this
      rwa [show base ^^^ value = Nat.xor base value from rfl, slice16_xor, nat_xor_eq_zero] at h'
    obtain ⟨h1, h2, h3⟩ := key 0 hK (fun j hj => absurd hj (Nat.not_lt_zero _))
    refine ⟨h1, h2, fun i hi _ => ?_⟩
    rw [slice16_replace16 hn hb (slice16_lt _ _) hK hi]
    split
    · subst_vars; rfl
    · exact hall i hi

/-! ## Instruction meanings on slices -/

theorem lo64_resX_toNat (sz : OperandSize) (r : BitVec sz.bits) : (lo64 (resX sz r)).toNat = r.toNat := by
  have h := opSize_bits_le sz
  simp only [lo64, resX, ofX, BitVec.toNat_setWidth]
  have h1 : r.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le r.isLt (Nat.pow_le_pow_right (by decide) h)
  have h2 : r.toNat < 2 ^ 128 := Nat.lt_trans h1 (by decide)
  simp only [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]

theorem opnd_of_lo64 {sz : OperandSize} {a : CV} {run : Nat} (ha : lo64 a = BitVec.ofNat 64 run) :
    opnd sz a = BitVec.ofNat sz.bits run := by
  unfold opnd; rw [ha]
  apply BitVec.eq_of_toNat_eq
  have h := opSize_bits_le sz
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)]

/-- The first instruction (`movz` from 0 / `movn` from all-ones) computes `replace16`. -/
theorem movWide_first {n base g f : Nat} (hn : Wid n) (op : MoveWideOp)
    (hbase : (op = .movZ ∧ base = 0) ∨ (op = .movN ∧ base = 2 ^ n - 1)) (hg : g < 2 ^ 16)
    (hf : f < n / 16) :
    let imm : MoveWideConst := ⟨match op with | .movZ => g | .movN => 2 ^ 16 - 1 - g, f⟩
    imm.bits < 2 ^ 16 ∧ 16 * imm.shift < n ∧ (movWideVal op n imm).toNat = replace16 base g f := by
  rcases hbase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    refine ⟨by simp only; omega, by simp only; rcases hn with rfl | rfl <;> omega, ?_⟩
    simp only [movWideVal, replace16, slice16, BitVec.toNat_shiftLeft, BitVec.toNat_not,
      BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.zero_div, Nat.zero_mod, Nat.zero_mul, Nat.sub_zero,
      Nat.zero_add]
    rcases hn with rfl | rfl
    · obtain rfl | rfl : f = 0 ∨ f = 1 := by omega
      all_goals simp only [Nat.reducePow, Nat.reduceMul, Nat.zero_mul, Nat.one_mul, Nat.pow_zero,
        Nat.div_one, Nat.mul_one] at *; omega
    · obtain rfl | rfl | rfl | rfl : f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 := by omega
      all_goals simp only [Nat.reducePow, Nat.reduceMul, Nat.zero_mul, Nat.one_mul, Nat.pow_zero,
        Nat.div_one, Nat.mul_one] at *; omega

theorem movK_ident {n j : Nat} (hn : Wid n) (hj : j < n / 16) (x : BitVec n) (y : BitVec 16) :
    movKVal x ⟨y.toNat, j⟩ =
      x - (((x >>> (16 * j)).setWidth 16).setWidth n <<< (16 * j)) + (y.setWidth n <<< (16 * j)) := by
  simp only [movKVal, BitVec.ofNat_toNat]
  rcases hn with rfl | rfl
  · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    all_goals simp only [Nat.reduceMul]; bv_decide
  · obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    all_goals simp only [Nat.reduceMul]; bv_decide

/-- `movk` computes `replace16`. -/
theorem movK_val {sz : OperandSize} {a : CV} {run b j : Nat} (ha : lo64 a = BitVec.ofNat 64 run)
    (hr : run < 2 ^ sz.bits) (hb : b < 2 ^ 16) (hj : j < sz.bits / 16) :
    lo64 (resX sz (movKVal (opnd sz a) ⟨b, j⟩)) = BitVec.ofNat 64 (replace16 run b j) := by
  have hn : Wid sz.bits := by cases sz <;> first | exact .inl rfl | exact .inr rfl
  rw [opnd_of_lo64 ha]
  have hy : (BitVec.ofNat 16 b).toNat = b := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  conv => lhs; rw [← hy]
  rw [movK_ident hn hj]
  apply BitVec.eq_of_toNat_eq
  rw [lo64_resX_toNat]
  have hrl : replace16 run b j < 2 ^ sz.bits := replace16_lt hn hr hb hj
  generalize sz.bits = n at *
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    replace16, slice16] at hrl ⊢
  rcases hn with rfl | rfl
  · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    all_goals simp only [Nat.reducePow, Nat.reduceMul, Nat.zero_mul, Nat.one_mul, Nat.pow_zero,
      Nat.div_one, Nat.mul_one] at *; omega
  · obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    all_goals simp only [Nat.reducePow, Nat.reduceMul, Nat.zero_mul, Nat.one_mul, Nat.pow_zero,
      Nat.div_one, Nat.mul_one] at *; omega

/-! ## Straight-line composition -/

theorem seqRun_fall_append {isem : Sem} {ms' : List MInst} {ρ' ρ'' : Nat → CV}
    {w' w'' : Arm.ArmState} (h2 : seqRun isem ms' ρ' w' = some (.fall ρ'' w'')) :
    ∀ (ms : List MInst) (ρ : Nat → CV) (w : Arm.ArmState),
      seqRun isem ms ρ w = some (.fall ρ' w') → seqRun isem (ms ++ ms') ρ w = some (.fall ρ'' w'')
  | [], ρ, w, h1 => by
    simp only [seqRun, Option.some.injEq, SeqEnd.fall.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact h2
  | i :: ms, ρ, w, h1 => by
    simp only [List.cons_append, seqRun] at h1 ⊢
    cases hops : i.operands with
    | error e => simp [hops] at h1
    | ok ops =>
      simp only [hops] at h1 ⊢
      cases hs : isem i (vuses ops ρ) w with
      | none => simp [hs] at h1
      | some r =>
        obtain ⟨outs, w1, ctl⟩ := r
        simp only [hs] at h1 ⊢
        by_cases hl : outs.length = (ops.toList.filter Operand.isDef).length
        · simp only [hl, ↓reduceIte] at h1 ⊢
          cases ctl
          case next =>
            simp only at h1 ⊢
            cases hr : seqRun isem ms (vdefUpd ops outs ρ) w1 with
            | none => simp [hr] at h1
            | some e =>
              rw [hr] at h1
              cases e with
              | fall a b =>
                simp only [Option.map_some, SeqEnd.succ, Option.some.injEq, SeqEnd.fall.injEq] at h1
                obtain ⟨rfl, rfl⟩ := h1
                rw [seqRun_fall_append h2 ms _ _ hr]; rfl
              | stop k i ops ρ w outs w' ctl => simp [SeqEnd.succ] at h1
          all_goals simp at h1
        · simp only [hl, ↓reduceIte] at h1; cases h1

section Run
variable {F : BitVec 64 → Prop} {isem : Sem}

theorem prun_append {ms ms' : List MInst} {ρ ρ' ρ'' : Nat → CV} (h1 : PRun F isem ms ρ ρ')
    (h2 : PRun F isem ms' ρ' ρ'') : PRun F isem (ms ++ ms') ρ ρ'' := by
  intro w
  obtain ⟨w1, e1, s1⟩ := h1 w
  obtain ⟨w2, e2, s2⟩ := h2 w1
  exact ⟨w2, seqRun_fall_append e2 ms ρ w e1, s2.trans' s1⟩

/-- One instruction with one (late) def `d` and no use. -/
theorem prun_r0 (hR : Refines F isem) {i : MInst} {ms : List MInst} {ρ ρ' : Nat → CV} {d : Nat}
    {r : CV} (hops : i.operands = .ok #[⟨d, .int, .def, .late, .reg⟩])
    (hs : ∀ w, ispec i [] w = some ([r], w, .next)) (ht : PRun F isem ms (upd ρ d r) ρ') :
    PRun F isem (i :: ms) ρ ρ' :=
  prun_cons hR hops hs rfl ht

/-- `movk`: one use `x`, one reuse-def `d`. -/
theorem prun_movk (hR : Refines F isem) {i : MInst} {ms : List MInst} {ρ ρ' : Nat → CV}
    {d x : Nat} {r : CV}
    (hops : i.operands = .ok #[⟨x, .int, .use, .early, .reg⟩, ⟨d, .int, .def, .late, .reuse 0⟩])
    (hs : ∀ w, ispec i [ρ x] w = some ([r], w, .next)) (ht : PRun F isem ms (upd ρ d r) ρ') :
    PRun F isem (i :: ms) ρ ρ' :=
  prun_cons hR hops hs rfl ht

end Run

theorem ispec_movWide {op : MoveWideOp} {d : Nat} {imm : MoveWideConst} {sz : OperandSize}
    (h : imm.bits < 2 ^ 16 ∧ 16 * imm.shift < sz.bits) (w : Arm.ArmState) :
    ispec (.movWide op (.vreg d .int) imm sz) [] w =
      some ([resX sz (movWideVal op sz.bits imm)], w, .next) := by
  show (if imm.bits < 2 ^ 16 ∧ 16 * imm.shift < sz.bits then _ else none) = _
  split
  · rfl
  · contradiction

theorem ispec_movK {d x : Nat} {imm : MoveWideConst} {sz : OperandSize} {a : CV}
    (h : imm.bits < 2 ^ 16 ∧ 16 * imm.shift < sz.bits) (w : Arm.ArmState) :
    ispec (.movK (.vreg d .int) (.vreg x .int) imm sz) [a] w =
      some ([resX sz (movKVal (opnd sz a) imm)], w, .next) := by
  show (if imm.bits < 2 ^ 16 ∧ 16 * imm.shift < sz.bits then _ else none) = _
  split
  · rfl
  · contradiction

theorem vdd_movWide (op : MoveWideOp) (d : Nat) (imm : MoveWideConst) (sz : OperandSize) :
    vdefs (.movWide op (.vreg d .int) imm sz) = [d] := rfl
theorem vdu_movWide (op : MoveWideOp) (d : Nat) (imm : MoveWideConst) (sz : OperandSize) :
    vuseNums (.movWide op (.vreg d .int) imm sz) = [] := rfl

theorem upd_same {α : Type} (ρ : Nat → α) (d : Nat) (x : α) : upd ρ d x d = x := by simp [upd]

/-! ## The whole sequence -/

theorem u64_lt' (i : Int) : u64 i < 2 ^ 64 := by unfold u64; omega

theorem lcfValue_lt (bits : Nat) (sg : Bool) (sz : OperandSize) (v : Nat) :
    lcfValue bits sg sz v < 2 ^ 64 := by
  have hm : mask64 v < 2 ^ 64 := Nat.mod_lt _ (by decide)
  unfold lcfValue
  cases sz <;> cases sg <;> simp only <;> split <;>
    first | exact hm | exact u64_lt' _ | exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hm | omega | (have := u64_lt' (sextFrom bits (mask64 v)); omega)

theorem lcfSize_spec (value : Nat) (hv : value < 2 ^ 64) :
    Wid (lcfSize value).bits ∧ value < 2 ^ (lcfSize value).bits := by
  unfold lcfSize
  split
  · rename_i h
    simp only [beq_iff_eq, Nat.div_eq_zero_iff] at h
    exact ⟨.inl rfl, by simp only [OperandSize.bits]; omega⟩
  · exact ⟨.inr rfl, hv⟩

theorem lcfFirst_spec {value : Nat} (size : OperandSize) (hn : Wid size.bits)
    (hv : value < 2 ^ size.bits) :
    let c := lcfFirst value size
    c.2.2 < size.bits / 16 ∧ c.1 < 2 ^ size.bits ∧
      (∀ i < size.bits / 16, i ≤ c.2.2 → slice16 c.1 i = slice16 value i) ∧
      ∃ base, ((c.2.1 = .movZ ∧ base = 0) ∨ (c.2.1 = .movN ∧ base = 2 ^ size.bits - 1)) ∧
        c.1 = replace16 base (slice16 value c.2.2) c.2.2 := by
  have hz := lcfCand_spec hn hv (Nat.two_pow_pos _) .movZ
  have hn' := lcfCand_spec hn hv (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos) .movN
  unfold lcfFirst
  dsimp only
  split
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hn'
    exact ⟨h2, h4, h5, _, .inr ⟨h1, rfl⟩, h3⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hz
    exact ⟨h2, h4, h5, _, .inl ⟨h1, rfl⟩, h3⟩

/-- Invariant of the `movk` loop after slice `j`. -/
def LcfInv (F : BitVec 64 → Prop) (isem : Sem) (st0 : LState) (value first n j : Nat)
    (acc : Reg × LState × Nat) : Prop :=
  ∃ ms d, acc.1 = .vreg d .int ∧ CodeShape st0 acc.2.1 ms d st0.nextVreg ∧
    d < acc.2.1.nextVreg ∧ acc.2.2 < 2 ^ n ∧
    (∀ i < n / 16, (i ≤ first ∨ i < j) → slice16 acc.2.2 i = slice16 value i) ∧
    ∀ ρ, ∃ ρ', PRun F isem ms ρ ρ' ∧ lo64 (ρ' d) = BitVec.ofNat 64 acc.2.2

section Loop
variable {F : BitVec 64 → Prop} {isem : Sem}

theorem lcf_step (hR : Refines F isem) {st0 : LState} {value first j : Nat} {size : OperandSize}
    (hn : Wid size.bits) (hj : j < size.bits / 16) {acc : Reg × LState × Nat}
    (h : LcfInv F isem st0 value first size.bits j acc) :
    LcfInv F isem st0 value first size.bits (j + 1) (lcfStep value first size acc j) := by
  obtain ⟨rd, st, run⟩ := acc
  obtain ⟨ms, d, hd, hsh, hdlt, hlt, hsl, hrun⟩ := h
  dsimp only at hd hsh hdlt hlt hsl hrun
  subst hd
  unfold lcfStep
  split
  · exact ⟨ms, d, rfl, hsh, hdlt, hlt, fun i hi h' => hsl i hi (by omega), hrun⟩
  · rename_i hjf
    dsimp only
    have hb := slice16_lt value j
    split
    · refine ⟨ms ++ [.movK (.vreg st.nextVreg .int) (.vreg d .int) ⟨slice16 value j, j⟩ size],
        st.nextVreg, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, by simp [LState.emit, LState.fresh],
        replace16_lt hn hlt hb hj, ?_, ?_⟩
      · simp [LState.emit, LState.fresh, hsh.emitted]
      · have := hsh.mono; simp only [LState.emit, LState.fresh]; omega
      · exact hsh.mono
      · intro mi hmi e he
        simp only [List.mem_append, List.mem_singleton] at hmi
        rcases hmi with hmi | rfl
        · have := hsh.defs mi hmi e he; simp only [LState.emit, LState.fresh]; omega
        · have : vdefs (.movK (.vreg st.nextVreg .int) (.vreg d .int) ⟨slice16 value j, j⟩ size) =
              [st.nextVreg] := rfl
          rw [this, List.mem_singleton] at he; subst he
          have := hsh.mono; simp only [LState.emit, LState.fresh]; omega
      · intro mi hmi u hu
        simp only [List.mem_append, List.mem_singleton] at hmi
        rcases hmi with hmi | rfl
        · exact hsh.uses mi hmi u hu
        · have : vuseNums (.movK (.vreg st.nextVreg .int) (.vreg d .int) ⟨slice16 value j, j⟩
              size) = [d] := rfl
          rw [this, List.mem_singleton] at hu; subst hu
          exact .inl hsh.res
      · intro i hi h'
        rw [slice16_replace16 hn hlt hb hj hi]
        split
        · subst_vars; rfl
        · exact hsl i hi (by omega)
      · intro ρ
        obtain ⟨ρ', hp, hv⟩ := hrun ρ
        have h16 : (⟨slice16 value j, j⟩ : MoveWideConst).bits < 2 ^ 16 ∧
            16 * (⟨slice16 value j, j⟩ : MoveWideConst).shift < size.bits :=
          ⟨hb, by simp only; omega⟩
        refine ⟨_, prun_append hp (prun_movk hR rfl (fun w => ispec_movK h16 w) (prun_nil _)), ?_⟩
        rw [upd_same]
        exact movK_val hv hlt hb hj
    · rename_i heq
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at heq
      refine ⟨ms, d, rfl, hsh, hdlt, hlt, fun i hi h' => ?_, hrun⟩
      by_cases hij : i = j
      · subst hij; exact heq.symm
      · exact hsl i hi (by omega)

theorem lcf_fold (hR : Refines F isem) {st0 : LState} {value first : Nat} {size : OperandSize}
    (hn : Wid size.bits) {init : Reg × LState × Nat}
    (h0 : LcfInv F isem st0 value first size.bits 0 init) :
    ∀ j, j ≤ size.bits / 16 →
      LcfInv F isem st0 value first size.bits j ((List.range j).foldl (lcfStep value first size) init)
  | 0, _ => h0
  | j + 1, hj => by
    rw [List.range_succ, List.foldl_append]
    exact lcf_step hR hn (by omega) (lcf_fold hR hn h0 j (by omega))

/-- **`load_constant_full`**: the emitted code has `CodeShape` (fresh defs, no outside uses) and
every run leaves `lcfValue …` in the result vreg. -/
theorem lcf_run (hR : Refines F isem) (bits : Nat) (sg : Bool) (sz : OperandSize) (v : Nat)
    (st : LState) :
    ∃ ms d, (loadConstantFull bits sg sz v st).1 = .vreg d .int ∧
      CodeShape st (loadConstantFull bits sg sz v st).2 ms d st.nextVreg ∧
      ∀ ρ, ∃ ρ', PRun F isem ms ρ ρ' ∧ lo64 (ρ' d) = BitVec.ofNat 64 (lcfValue bits sg sz v) := by
  rw [lcf_eq]
  dsimp only
  have hv64 := lcfValue_lt bits sg sz v
  generalize lcfValue bits sg sz v = value at *
  obtain ⟨hn, hv⟩ := lcfSize_spec value hv64
  generalize lcfSize value = size at *
  obtain ⟨hf, hc1, hcs, base, hbase, hceq⟩ := lcfFirst_spec size hn hv
  generalize lcfFirst value size = c at *
  obtain ⟨hi1, hi2, hival⟩ := movWide_first hn c.2.1 hbase (slice16_lt value c.2.2) hf
  have hn64 : 2 ^ size.bits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (opSize_bits_le size)
  have h0 : LcfInv F isem st value c.2.2 size.bits 0
      ((st.fresh .int).1, (st.fresh .int).2.emit (.movWide c.2.1 (st.fresh .int).1
        ⟨match c.2.1 with
          | .movZ => slice16 value c.2.2
          | .movN => 2 ^ 16 - 1 - slice16 value c.2.2, c.2.2⟩ size), c.1) := by
    refine ⟨[.movWide c.2.1 (.vreg st.nextVreg .int) ⟨match c.2.1 with
          | .movZ => slice16 value c.2.2
          | .movN => 2 ^ 16 - 1 - slice16 value c.2.2, c.2.2⟩ size], st.nextVreg, rfl,
      ⟨by simp [LState.emit, LState.fresh], by simp [LState.emit, LState.fresh], Nat.le_refl _, ?_, ?_⟩,
      by simp [LState.emit, LState.fresh], hc1, fun i hi h' => hcs i hi (by omega), ?_⟩
    · intro mi hmi e he
      simp only [List.mem_singleton] at hmi; subst hmi
      rw [vdd_movWide, List.mem_singleton] at he; subst he
      simp [LState.emit, LState.fresh]
    · intro mi hmi u hu
      simp only [List.mem_singleton] at hmi; subst hmi
      rw [vdu_movWide] at hu; cases hu
    · intro ρ
      refine ⟨_, prun_r0 hR rfl (fun w => ispec_movWide ⟨hi1, hi2⟩ w) (prun_nil _), ?_⟩
      rw [upd_same]
      apply BitVec.eq_of_toNat_eq
      rw [lo64_resX_toNat, hival, ← hceq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hc1 hn64)]
  have hK := lcf_fold hR hn h0 (size.bits / 16) (Nat.le_refl _)
  obtain ⟨ms, d, hd, hsh, -, hlt, hsl, hrun⟩ := hK
  refine ⟨ms, d, hd, hsh, fun ρ => ?_⟩
  obtain ⟨ρ', hp, hval⟩ := hrun ρ
  refine ⟨ρ', hp, ?_⟩
  rw [hval, eq_of_slice16 hn hlt hv (fun i hi => hsl i hi (.inr hi))]

end Loop

end Backend.Proof

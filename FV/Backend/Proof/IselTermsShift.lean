import FV.Backend.Proof.IselFamAluBShiftBase
import FV.Backend.Proof.IselFamAluBIconst

/-!
# `do_shift` (`lower.isle:1601`): contract over its four rules

* 1631 `do_shift_imm`: the amount is an `iconst` (looked through with `def_inst`): one
  immediate shift by the constant masked to the width (`imm_shift_from_imm64`);
* 1622 / 1623: `i32` / `i64`: one register shift (`LSLV`/`LSRV`/`ASRV` take the amount modulo
  the width);
* 1612 `do_shift_fits_in_16`: `and` the amount with `shift_mask` (`w - 1`), then a 32-bit
  register shift.

`do_shift_ok`: whatever rule fired, the result register holds the 32/64-bit shift of the
value operand by the CLIF amount modulo the width (`shiftF`), in every frame satisfying
`DFGCons` (the `iconst` case reads the amount's definition).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

/-- The shift a `do_shift` operation computes, at width `n`. -/
def shiftF (op : ALUOp) {n : Nat} (a : BitVec n) (s : Nat) : BitVec n :=
  match op with
  | .lsl => a <<< s
  | .lsr => a >>> s
  | .asr => a.sshiftRight s
  | _ => a

/-- The ALU shift operations and their `ALUOp` indices. -/
def ShiftOp (k : Nat) (op : ALUOp) : Prop :=
  (k = 18 ∧ op = .lsl) ∨ (k = 16 ∧ op = .lsr) ∨ (k = 17 ∧ op = .asr)

theorem ShiftOp.ofIdx {k : Nat} {op : ALUOp} (h : ShiftOp k op) : ALUOp.ofIdx? k = some op := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-! ## Extern helpers -/

section Extern
variable (st : LState)

theorem ctor_imm_shift_from_imm64 {w : Nat} (hw : 0 < w) (hw' : w ≤ 64) (c : Int) :
    externCtor ctx T.imm_shift_from_imm64 [.ty (.int w), .int c] st =
      .ok (.op (.immShift (Nat.land (u64 c) (w - 1))), st) := by
  have : externCtor ctx T.imm_shift_from_imm64 [.ty (.int w), .int c] st =
    if Nat.land (u64 c) ((CTy.int w).bits - 1) < 64 then
      .ok (.op (.immShift (Nat.land (u64 c) ((CTy.int w).bits - 1))), st) else .fail := rfl
  rw [this]
  have hlt : Nat.land (u64 c) (w - 1) < 64 := by
    have := Nat.and_le_right (n := u64 c) (m := w - 1)
    change u64 c &&& (w - 1) < 64
    omega
  simp only [CTy.bits, hlt, ↓reduceIte]

theorem ctor_shift_mask_i16 :
    externCtor ctx T.shift_mask [.ty (.int 16)] st = .ok (.op (.immLogic ⟨15, .size32⟩), st) := rfl

end Extern

/-! ## Rule 1631: the amount is an `iconst` -/

include hp in
/-- A `def_inst` look-through to an `iconst` matched: the amount's defining instruction has
`UnaryImm`/`Iconst` data. -/
theorem defInst_iconst_inv {st : LState} {y : Nat} {env env' : Interp.Env V} {rest : List Pattern}
    (h : matchPat p (sem ctx) st (.term 15 1 [(.term 18 209 [(.wildcard 14),
      (.term 152 2482 (.term 151 2341 [] :: rest))])]) (.value y) env = .ok (some env')) :
    ∃ j info fs, ctx.defInst? y = some j ∧ ctx.insts[j]? = some info ∧
      info.data = .data 152 35 (.data 151 57 [] :: fs) := by
  obtain ⟨fs0, hx, hm⟩ := matchPat_extract_inv hp.t1 term_1_kind rfl h
  rw [sem_extract, ext_def_inst] at hx
  cases hd : ctx.defInst? y with
  | none => rw [hd] at hx; cases hx
  | some j =>
  rw [hd] at hx
  cases hx
  obtain ⟨e1, hp1, -⟩ := matchArgs_cons_inv hm
  obtain ⟨fs1, hx1, hm1⟩ := matchPat_extract_inv hp.t209 term_209_kind rfl hp1
  rw [sem_extract] at hx1
  obtain ⟨info, hi, rfl⟩ := ext_inst_data_value_inv hx1
  obtain ⟨e2, -, hm2⟩ := matchArgs_cons_inv hm1
  obtain ⟨e3, hp3, -⟩ := matchArgs_cons_inv hm2
  obtain ⟨fs', hu, hm3⟩ := matchPat_enum_inv hp.t2482 term_2482_kind hp3
  have hd' := sem_unData_inv hu
  cases fs' with
  | nil => exact (matchArgs_cons_nil hm3).elim
  | cons w ws =>
    obtain ⟨e4, hp4, -⟩ := matchArgs_cons_inv hm3
    obtain ⟨fs'', hu', hm4⟩ := matchPat_enum_inv hp.t2341 term_2341_kind hp4
    have hw := sem_unData_inv hu'
    have := matchArgs_nil_inv hm4
    subst this
    exact ⟨j, info, ws, rfl, hi, by rw [hd', hw]⟩

/-- `CtxInv`: the looked-through definition is `iconst ty' imm`, with data `imm64OfIconst`. -/
theorem defInst_iconst_clif {f : Clif.Function} (hctx : CtxInv f ctx) {y j : Nat} {info : IInfo}
    {fs : List V} (hd : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info)
    (hdata : info.data = .data 152 35 (.data 151 57 [] :: fs)) :
    ∃ ty imm, info.clif = some (.iconst ty imm) ∧ fs = [.int (imm64OfIconst ty imm)] := by
  have hs := hctx.defClif y j info hd hi
  obtain ⟨cl, hcl⟩ := Option.isSome_iff_exists.mp hs
  have hdat := hctx.data j info cl hi hcl
  rw [hdata] at hdat
  obtain ⟨hf, ho⟩ := instData_inv_names hdat
  rw [fb_variantNames_UnaryImm] at hf
  rw [fb_variantNames_Iconst] at ho
  have hnm : instNames cl = ("UnaryImm", "Iconst") :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨ty, imm, rfl⟩ := fb_instNames_iconst hnm
  obtain ⟨-, hfs⟩ := fb_instData_iconst hdat
  exact ⟨ty, imm, hcl, hfs⟩

section
variable (st : LState) (tr : Array RuleId) (m : Nat)

/-- The `do_shift` argument list. -/
abbrev shiftArgs (k w : Nat) (a : Reg) (y : Nat) : List V :=
  [.data 59 k [], .ty (.int w), .reg a, .value y]

include hp in
theorem match_1631 {k w : Nat} (hw : 0 < w) (hw' : w ≤ 64) {a : Reg} {y j : Nat} {info : IInfo}
    (hd : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info) {c : Int}
    (hdata : info.data = .data 152 35 [.data 151 57 [], .int c]) :
    (matchRule p (sem ctx) cfg (m+10) rule_lower_1631 (shiftArgs k w a y)).run (st, tr) =
      .ok (some (env5 (.data 59 k []) (.ty (.int w)) (.reg a) (.int c)
        (.op (.immShift (Nat.land (u64 c) (w - 1))))), (st, tr)) := by
  have h1 := ext_def_inst_some ctx st hd
  have h2 := ext_inst_data_value ctx st hi
  rw [hdata] at h2
  have h3 := fun st => ctor_imm_shift_from_imm64 ctx st hw hw' c
  cases hp
  isel_eval [*, rule_lower_1631]

include hp in
theorem match_1622 {k : Nat} {a : Reg} {y : Nat} :
    (matchRule p (sem ctx) cfg (m+10) rule_lower_1622 (shiftArgs k 32 a y)).run (st, tr) =
      .ok (some (env3 (.data 59 k []) (.reg a) (.value y)), (st, tr)) := by
  have he := sem_eq_beq' ctx
  cases hp
  isel_eval [*, rule_lower_1622]

include hp in
theorem match_1622_none {k w : Nat} (hw : w ≠ 32) {a : Reg} {y : Nat} :
    (matchRule p (sem ctx) cfg (m+10) rule_lower_1622 (shiftArgs k w a y)).run (st, tr) =
      .ok (none, (st, tr)) := by
  have he := sem_eq_beq' ctx
  have hne : (V.ty (.int w) == V.ty (.int 32)) = false := by simp [hw]
  cases hp
  isel_eval [*, rule_lower_1622]

include hp in
theorem match_1623 {k : Nat} {a : Reg} {y : Nat} :
    (matchRule p (sem ctx) cfg (m+10) rule_lower_1623 (shiftArgs k 64 a y)).run (st, tr) =
      .ok (some (env3 (.data 59 k []) (.reg a) (.value y)), (st, tr)) := by
  have he := sem_eq_beq' ctx
  cases hp
  isel_eval [*, rule_lower_1623]

include hp in
theorem match_1623_none {k w : Nat} (hw : w ≠ 64) {a : Reg} {y : Nat} :
    (matchRule p (sem ctx) cfg (m+10) rule_lower_1623 (shiftArgs k w a y)).run (st, tr) =
      .ok (none, (st, tr)) := by
  have he := sem_eq_beq' ctx
  have hne : (V.ty (.int w) == V.ty (.int 64)) = false := by simp [hw]
  cases hp
  isel_eval [*, rule_lower_1623]

include hp in
theorem match_1612 {k w : Nat} (hw : w ≤ 16) {a : Reg} {y : Nat} :
    (matchRule p (sem ctx) cfg (m+10) rule_lower_1612 (shiftArgs k w a y)).run (st, tr) =
      .ok (some ((((((Array.replicate 6 none).setIfInBounds 0 (some (V.data 59 k []))).setIfInBounds 1
        (some (V.ty (CTy.int w)))).setIfInBounds 2 (some (V.reg a))).setIfInBounds 3
        (some (V.value y)))), (st, tr)) := by
  have h1 := ext_fits_in_16 ctx st w
  simp only [hw, ↓reduceIte] at h1
  cases hp
  isel_eval [*, rule_lower_1612]

include hp in
theorem match_1612_none {k w : Nat} (hw : ¬ w ≤ 16) {a : Reg} {y : Nat} :
    (matchRule p (sem ctx) cfg (m+10) rule_lower_1612 (shiftArgs k w a y)).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_fits_in_16 ctx st w
  simp only [hw, ↓reduceIte] at h1
  cases hp
  isel_eval [*, rule_lower_1612]

end

end Backend.Proof

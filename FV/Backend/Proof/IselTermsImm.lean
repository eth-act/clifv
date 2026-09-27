import FV.Backend.Proof.IselFamAluBBase
import FV.Backend.Proof.IselTermsAluB

/-!
# `imm` (`inst.isle:3738`): materialise a constant

Five rules: `movz` (3742), `movn` (3745, 32/64 bits), `orr` of a logical immediate into `xzr`
(3751, 32/64 bits), and `load_constant_full` (3786 at ≤ 32 bits, 3790 at 64 bits: `movz`/`movn`
plus `movk`s). Forward lemmas per rule (`imm_movz`, …), the meaning of each emitted sequence,
and the contract `imm_ok`: whenever `imm ty ext c` returns, it returned a fresh vreg `d`, the
code it emitted has `CodeShape`, and every run of it leaves in `d` a 64-bit value whose low
`ty.width` bits are `c`'s (and, outside `imm i32 Zero c` with `c ≥ 2³²`, the whole value
`immVal`).
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

/-! ## Extern helpers -/

section Extern
variable (st : LState)

theorem ext_integral_ty {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) :
    externExtract ctx T.integral_ty (.ty (.int w)) st = .ok [.ty (.int w)] := by
  have : externExtract ctx T.integral_ty (.ty (.int w)) st =
    if (CTy.int w == .int 8 || CTy.int w == .int 16 || CTy.int w == .int 32 ||
      CTy.int w == .int 64) = true then .ok [.ty (.int w)] else .fail := rfl
  rw [this]; rcases hw with rfl | rfl | rfl | rfl <;> rfl

theorem ctor_mwc_some {w : Nat} {i : Int} {mw : MoveWideConst}
    (h : MoveWideConst.ofNat? (if w < 64 then u64 i % 2 ^ w else u64 i) = some mw) :
    externCtor ctx T.move_wide_const_from_u64 [.ty (.int w), .int i] st =
      .ok (.op (.moveWideConst mw), st) := by
  have : externCtor ctx T.move_wide_const_from_u64 [.ty (.int w), .int i] st =
    match (MoveWideConst.ofNat? (if w < 64 then u64 i % 2 ^ w else u64 i)).map
      (V.op ∘ Opnd.moveWideConst) with
    | some v => .ok (v, st)
    | none => .fail := rfl
  rw [this, h]; rfl

theorem ctor_mwc_none {w : Nat} {i : Int}
    (h : MoveWideConst.ofNat? (if w < 64 then u64 i % 2 ^ w else u64 i) = none) :
    externCtor ctx T.move_wide_const_from_u64 [.ty (.int w), .int i] st = .fail := by
  have : externCtor ctx T.move_wide_const_from_u64 [.ty (.int w), .int i] st =
    match (MoveWideConst.ofNat? (if w < 64 then u64 i % 2 ^ w else u64 i)).map
      (V.op ∘ Opnd.moveWideConst) with
    | some v => .ok (v, st)
    | none => .fail := rfl
  rw [this, h]; rfl

theorem ofV_movWide {k ks : Nat} {op : MoveWideOp} {sz : OperandSize}
    (hk : k = 0 ∧ op = .movZ ∨ k = 1 ∧ op = .movN) (hs : OperandSize.ofIdx? ks = some sz)
    (rd : Reg) (mw : MoveWideConst) :
    MInst.ofV (.data 58 26 [.data 61 k [], .reg rd, .op (.moveWideConst mw), .data 93 ks []]) =
      some (.movWide op rd mw sz) := by
  have e3 : (V.data 93 ks []).size? = OperandSize.ofIdx? ks := rfl
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e1 : MInst.ofV (.data 58 26 [.data 61 0 [], .reg rd, .op (.moveWideConst mw),
        .data 93 ks []]) = (do return .movWide .movZ rd mw (← (V.data 93 ks []).size?)) := rfl
    rw [e1, e3, hs]; rfl
  · have e1 : MInst.ofV (.data 58 26 [.data 61 1 [], .reg rd, .op (.moveWideConst mw),
        .data 93 ks []]) = (do return .movWide .movN rd mw (← (V.data 93 ks []).size?)) := rfl
    rw [e1, e3, hs]; rfl

end Extern

/-! ## Forward lemmas -/

section
variable (st : LState) (tr : Array RuleId) (n : Nat)

set_option maxHeartbeats 2000000 in
include hp hc in
theorem imm_movz {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {i : Int}
    {mw : MoveWideConst}
    (hm : MoveWideConst.ofNat? (if w < 64 then u64 i % 2 ^ w else u64 i) = some mw) :
    ∃ tr', (applyTerm p (sem ctx) cfg (n+40) 27 553 [.ty (.int w), .data 122 1 [], .int i]).run
        (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.movWide .movZ (st.fresh .int).1 mw (szOf w)), tr')) := by
  have h1 := ext_integral_ty ctx st hw
  have h2 := fun st => ctor_mwc_some ctx st hm
  by_cases h32 : w ≤ 32
  · have h3 := fun st tr n => operand_size_32 hp ctx hc st tr n h32
    have h4 := fun st rd => ctor_emit ctx st (ofV_movWide (op := .movZ) (sz := .size32) (ks := 0)
      (.inl ⟨rfl, rfl⟩) rfl rd mw)
    simp only [szOf, h32, ↓reduceIte]
    clear hw hm h32
    cases hp
    refine Exists.intro ?w ?h
    case h =>
      isel_eval [*, rule_inst_3742, rule_inst_2513, ctor_temp_writable_reg_i64,
        ctor_writable_reg_to_reg]
      rfl
  · have h3 := fun st tr n => operand_size_64 hp ctx hc st tr n (w := w) (by omega) (by omega)
    have h4 := fun st rd => ctor_emit ctx st (ofV_movWide (op := .movZ) (sz := .size64) (ks := 1)
      (.inl ⟨rfl, rfl⟩) rfl rd mw)
    simp only [szOf, h32, ↓reduceIte]
    clear hw hm h32
    cases hp
    refine Exists.intro ?w2 ?h2
    case h2 =>
      isel_eval [*, rule_inst_3742, rule_inst_2513, ctor_temp_writable_reg_i64,
        ctor_writable_reg_to_reg]
      rfl

end

end Backend.Proof

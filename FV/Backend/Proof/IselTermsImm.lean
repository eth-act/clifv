import FV.Backend.Proof.IselLcf
import FV.Backend.Proof.IselTermsAluB

/-!
# `imm` (`inst.isle:3738`): materialise a constant

Five rules: `movz` (3742), `movn` (3745, 32/64 bits), `orr` of a logical immediate into `xzr`
(3751, 32/64 bits), and `load_constant_full` (3786 at ≤ 32 bits, 3790 at 64 bits: `movz`/`movn`
plus `movk`s). Forward lemmas per rule (`match_*`, `rhs_*`), the meaning of each emitted sequence,
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

theorem ctor_mwci {w : Nat} {i : Int} :
    externCtor ctx T.move_wide_const_from_inverted_u64 [.ty (.int w), .int i] st =
      match (MoveWideConst.ofNat? (if w < 64 then (2 ^ 64 - 1 - u64 i) % 2 ^ w
          else 2 ^ 64 - 1 - u64 i)).map (V.op ∘ Opnd.moveWideConst) with
      | some v => .ok (v, st)
      | none => .fail := rfl

theorem ctor_mwci_some {w : Nat} {i : Int} {mw : MoveWideConst}
    (h : MoveWideConst.ofNat? (if w < 64 then (2 ^ 64 - 1 - u64 i) % 2 ^ w
      else 2 ^ 64 - 1 - u64 i) = some mw) :
    externCtor ctx T.move_wide_const_from_inverted_u64 [.ty (.int w), .int i] st =
      .ok (.op (.moveWideConst mw), st) := by
  rw [ctor_mwci, h]; rfl

theorem ctor_mwci_none {w : Nat} {i : Int}
    (h : MoveWideConst.ofNat? (if w < 64 then (2 ^ 64 - 1 - u64 i) % 2 ^ w
      else 2 ^ 64 - 1 - u64 i) = none) :
    externCtor ctx T.move_wide_const_from_inverted_u64 [.ty (.int w), .int i] st = .fail := by
  rw [ctor_mwci, h]; rfl

theorem ofBits_szOf {w : Nat} (hw : w = 32 ∨ w = 64) : OperandSize.ofBits w = szOf w := by
  rcases hw with rfl | rfl <;> rfl

theorem ctor_imm_logic_u64 {w : Nat} (hw : w = 32 ∨ w = 64) {i : Int} :
    externCtor ctx T.imm_logic_from_u64 [.ty (.int w), .int i] st =
      match (ImmLogic.ofNat? (u64 i) (szOf w)).map (V.op ∘ Opnd.immLogic) with
      | some v => .ok (v, st)
      | none => .fail := by
  have : externCtor ctx T.imm_logic_from_u64 [.ty (.int w), .int i] st =
    if (CTy.int w == .int 32 || CTy.int w == .int 64) = true then
      match (ImmLogic.ofNat? (u64 i) (.ofBits w)).map (V.op ∘ Opnd.immLogic) with
      | some v => .ok (v, st)
      | none => .fail
    else .fail := rfl
  rw [this, ofBits_szOf hw]
  have hc : (CTy.int w == .int 32 || CTy.int w == .int 64) = true := by
    rcases hw with rfl | rfl <;> decide
  simp only [hc, ↓reduceIte]

theorem ctor_imm_logic_u64_narrow {w : Nat} (hw : w = 8 ∨ w = 16) {i : Int} :
    externCtor ctx T.imm_logic_from_u64 [.ty (.int w), .int i] st = .fail := by
  rcases hw with rfl | rfl <;> rfl

theorem ctor_imm_logic_some {w : Nat} (hw : w = 32 ∨ w = 64) {i : Int} {il : ImmLogic}
    (h : ImmLogic.ofNat? (u64 i) (szOf w) = some il) :
    externCtor ctx T.imm_logic_from_u64 [.ty (.int w), .int i] st = .ok (.op (.immLogic il), st) := by
  rw [ctor_imm_logic_u64 ctx st hw, h]; rfl

theorem ctor_imm_logic_none {w : Nat} (hw : w = 32 ∨ w = 64) {i : Int}
    (h : ImmLogic.ofNat? (u64 i) (szOf w) = none) :
    externCtor ctx T.imm_logic_from_u64 [.ty (.int w), .int i] st = .fail := by
  rw [ctor_imm_logic_u64 ctx st hw, h]; rfl

theorem ctor_imm_size {w : Nat} (hw : w = 32 ∨ w = 64) :
    externCtor ctx T.imm_size_from_type [.ty (.int w)] st = .ok (.int w, st) := by
  rcases hw with rfl | rfl <;> rfl

theorem ext_ty_32_or_64_32 :
    externExtract ctx T.ty_32_or_64 (.ty (.int 32)) st = .ok [.ty (.int 32)] := rfl
theorem ext_ty_32_or_64_64 :
    externExtract ctx T.ty_32_or_64 (.ty (.int 64)) st = .ok [.ty (.int 64)] := rfl
theorem ext_ty_32_or_64_8 : externExtract ctx T.ty_32_or_64 (.ty (.int 8)) st = .fail := rfl
theorem ext_ty_32_or_64_16 : externExtract ctx T.ty_32_or_64 (.ty (.int 16)) st = .fail := rfl

theorem ctor_zero_reg' : externCtor ctx T.zero_reg [] st = .ok (.reg .xzr, st) := rfl

theorem ctor_lcf (w e ks : Nat) {sz : OperandSize} (hs : OperandSize.ofIdx? ks = some sz) (i : Int) :
    externCtor ctx T.load_constant_full [.ty (.int w), .data 122 e [], .data 93 ks [], .int i] st =
      .ok (.reg (loadConstantFull w (e == 0) sz (u64 i) st).1,
        (loadConstantFull w (e == 0) sz (u64 i) st).2) := by
  have : externCtor ctx T.load_constant_full [.ty (.int w), .data 122 e [], .data 93 ks [], .int i]
      st = match (V.data 122 e []).enumOf? tyImmExtend, (V.data 93 ks []).size? with
    | some (e, _), some size =>
      let (r, st) := loadConstantFull (CTy.int w).bits (e == VIdx.ImmExtend.Sign) size (u64 i) st
      .ok (.reg r, st)
    | _, _ => .unmodeled "load_constant_full" := rfl
  rw [this]
  have e3 : (V.data 93 ks []).size? = OperandSize.ofIdx? ks := rfl
  rw [e3, hs]
  rfl

end Extern

/-! ## Forward lemmas, one rule at a time -/

/-- A four-variable rule environment as the matcher builds it. -/
abbrev env4 (a b c d : V) : Interp.Env V :=
  ((((Array.replicate 4 none).setIfInBounds 0 (some a)).setIfInBounds 1 (some b)).setIfInBounds 2
    (some c)).setIfInBounds 3 (some d)

/-- The `imm` argument list. -/
abbrev immArgs (w e : Nat) (i : Int) : List V := [.ty (.int w), .data 122 e [], .int i]

/-- `move_wide_const_from_u64`'s value. -/
abbrev mwcArg (w : Nat) (i : Int) : Nat := if w < 64 then u64 i % 2 ^ w else u64 i
/-- `move_wide_const_from_inverted_u64`'s value. -/
abbrev mwciArg (w : Nat) (i : Int) : Nat :=
  if w < 64 then (2 ^ 64 - 1 - u64 i) % 2 ^ w else 2 ^ 64 - 1 - u64 i

section
variable (st : LState) (tr : Array RuleId) (m : Nat)

theorem ext_ty_32_or_64_of {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) :
    externExtract ctx T.ty_32_or_64 (.ty (.int w)) st =
      if w = 32 ∨ w = 64 then .ok [.ty (.int w)] else .fail := by
  rcases hw with rfl | rfl | rfl | rfl <;> rfl

include hp in
theorem match_3742 {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {i : Int} {mw : MoveWideConst}
    (hm : MoveWideConst.ofNat? (mwcArg w i) = some mw) :
    (matchRule p (sem ctx) cfg (m+10) rule_inst_3742 (immArgs w 1 i)).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.int i) (.op (.moveWideConst mw))), (st, tr)) := by
  have h1 := ext_integral_ty ctx st hw
  have h2 := fun st => ctor_mwc_some ctx st hm
  clear hm hw
  cases hp
  isel_eval [*, rule_inst_3742]

include hp in
theorem match_3742_none {w e : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {i : Int}
    (he : e = 0 ∨ e = 1 ∧ MoveWideConst.ofNat? (mwcArg w i) = none) :
    (matchRule p (sem ctx) cfg (m+10) rule_inst_3742 (immArgs w e i)).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_integral_ty ctx st hw
  clear hw
  rcases he with rfl | ⟨rfl, hm⟩
  · cases hp
    isel_eval [*, rule_inst_3742]
  · have h2 := fun st => ctor_mwc_none ctx st hm
    clear hm
    cases hp
    isel_eval [*, rule_inst_3742]

include hp in
theorem match_3745 {w : Nat} (hw : w = 32 ∨ w = 64) {i : Int} {mw : MoveWideConst}
    (hm : MoveWideConst.ofNat? (mwciArg w i) = some mw) :
    (matchRule p (sem ctx) cfg (m+10) rule_inst_3745 (immArgs w 1 i)).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.int i) (.op (.moveWideConst mw))), (st, tr)) := by
  have h1 := ext_integral_ty ctx st (w := w) (by omega)
  have h2 := fun st => ctor_mwci_some ctx st hm
  have h3 := ext_ty_32_or_64_of ctx st (w := w) (by omega)
  simp only [hw, ↓reduceIte] at h3
  clear hm hw
  cases hp
  isel_eval [*, rule_inst_3745]

include hp in
theorem match_3745_none {w e : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {i : Int}
    (he : e = 0 ∨ (w = 8 ∨ w = 16) ∨ e = 1 ∧ MoveWideConst.ofNat? (mwciArg w i) = none) :
    (matchRule p (sem ctx) cfg (m+10) rule_inst_3745 (immArgs w e i)).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_integral_ty ctx st hw
  have h3 := ext_ty_32_or_64_of ctx st hw
  by_cases hn : w = 32 ∨ w = 64
  · simp only [hn, ↓reduceIte] at h3
    rcases he with rfl | hn' | ⟨rfl, hm⟩
    · clear hw hn; cases hp; isel_eval [*, rule_inst_3745]
    · omega
    · have h2 := fun st => ctor_mwci_none ctx st hm
      clear hm hw hn
      cases hp
      isel_eval [*, rule_inst_3745]
  · simp only [hn, ↓reduceIte] at h3
    clear hw hn he
    cases hp
    isel_eval [*, rule_inst_3745]

include hp in
theorem match_3751 {w : Nat} (hw : w = 32 ∨ w = 64) {i : Int} {il : ImmLogic}
    (hl : ImmLogic.ofNat? (u64 i) (szOf w) = some il) :
    (matchRule p (sem ctx) cfg (m+10) rule_inst_3751 (immArgs w 1 i)).run (st, tr) =
      .ok (some (env4 (.ty (.int w)) (.int i) (.op (.immLogic il)) (.int w)), (st, tr)) := by
  have h1 := ext_integral_ty ctx st (w := w) (by omega)
  have h2 := fun st => ctor_imm_logic_some ctx st hw hl
  have h3 := fun st => ctor_imm_size ctx st hw
  clear hl hw
  cases hp
  isel_eval [*, rule_inst_3751]

include hp in
theorem match_3751_none {w e : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {i : Int}
    (h01 : e = 0 ∨ e = 1) (he : e = 0 ∨ (w = 8 ∨ w = 16) ∨ e = 1 ∧ ImmLogic.ofNat? (u64 i) (szOf w) = none) :
    (matchRule p (sem ctx) cfg (m+10) rule_inst_3751 (immArgs w e i)).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_integral_ty ctx st hw
  rcases he with rfl | hn | ⟨rfl, hl⟩
  · clear hw; cases hp; isel_eval [*, rule_inst_3751]
  · have h2 := fun st => ctor_imm_logic_u64_narrow ctx st hn (i := i)
    clear hw hn
    rcases h01 with rfl | rfl <;> cases hp <;> isel_eval [*, rule_inst_3751]
  · by_cases hn : w = 32 ∨ w = 64
    · have h2 := fun st => ctor_imm_logic_none ctx st hn hl
      clear hw hn hl; cases hp; isel_eval [*, rule_inst_3751]
    · have h2 := fun st => ctor_imm_logic_u64_narrow ctx st (w := w) (by omega) (i := i)
      clear hw hn hl; cases hp; isel_eval [*, rule_inst_3751]

include hp in
theorem match_3786 {w e : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32) {i : Int} :
    (matchRule p (sem ctx) cfg (m+10) rule_inst_3786 (immArgs w e i)).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.data 122 e []) (.int i)), (st, tr)) := by
  have h1 := ext_integral_ty ctx st (w := w) (by omega)
  have h2 := ext_fits_in_32 ctx st w
  simp only [show w ≤ 32 by omega, ↓reduceIte] at h2
  clear hw
  cases hp
  isel_eval [*, rule_inst_3786]

include hp in
theorem match_3786_none {e : Nat} {i : Int} :
    (matchRule p (sem ctx) cfg (m+10) rule_inst_3786 (immArgs 64 e i)).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h2 := ext_fits_in_32 ctx st 64
  simp only [show ¬ (64 ≤ 32) by omega, ↓reduceIte] at h2
  cases hp
  isel_eval [*, rule_inst_3786]

include hp in
theorem match_3790 {e : Nat} {i : Int} :
    (matchRule p (sem ctx) cfg (m+10) rule_inst_3790 (immArgs 64 e i)).run (st, tr) =
      .ok (some (env2 (.data 122 e []) (.int i)), (st, tr)) := by
  have h1 := ext_integral_ty ctx st (w := 64) (by omega)
  have he := sem_eq_beq' ctx
  cases hp
  isel_eval [*, rule_inst_3790]

include hp in
theorem match_3790_none {w e : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32) {i : Int} :
    (matchRule p (sem ctx) cfg (m+10) rule_inst_3790 (immArgs w e i)).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_integral_ty ctx st (w := w) (by omega)
  have he := sem_eq_beq' ctx
  have hne : (V.ty (.int w) == V.ty (.int 64)) = false := by
    rcases hw with rfl | rfl | rfl <;> decide
  clear hw
  cases hp
  isel_eval [*, rule_inst_3790]

end

section
variable (st : LState) (tr : Array RuleId) (n : Nat)

theorem ofV_movWide' {k ks : Nat} {op : MoveWideOp} {sz : OperandSize}
    (hk : k = 0 ∧ op = .movZ ∨ k = 1 ∧ op = .movN) (hs : OperandSize.ofIdx? ks = some sz) (st : LState)
    (rd : Reg) (mw : MoveWideConst) :
    externCtor ctx T.emit [.data 58 26 [.data 61 k [], .reg rd, .op (.moveWideConst mw), .data 93 ks []]]
      st = .ok (.op .unit, st.emit (.movWide op rd mw sz)) := ctor_emit ctx st (ofV_movWide hk hs rd mw)

include hp hc in
theorem rhs_3742 {w : Nat} (hw : w ≤ 64) {i : Int} {mw : MoveWideConst} :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+30) rule_inst_3742.rhs
        (env3 (.ty (.int w)) (.int i) (.op (.moveWideConst mw)))).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.movWide .movZ (st.fresh .int).1 mw (szOf w)), tr')) := by
  by_cases h32 : w ≤ 32
  · have h3 := fun st tr n => operand_size_32 hp ctx hc st tr n h32
    have h4 := ofV_movWide' ctx (op := .movZ) (sz := .size32) (ks := 0) (.inl ⟨rfl, rfl⟩) rfl
    simp only [szOf, h32, ↓reduceIte]
    clear h32 hw
    cases hp
    refine Exists.intro ?rw0 ?rh0
    case rh0 =>
      isel_eval [*, rule_inst_3742, rule_inst_2513, ctor_temp_writable_reg_i64,
        ctor_writable_reg_to_reg]
      rfl
  · have h3 := fun st tr n => operand_size_64 hp ctx hc st tr n (w := w) (by omega) hw
    have h4 := ofV_movWide' ctx (op := .movZ) (sz := .size64) (ks := 1) (.inl ⟨rfl, rfl⟩) rfl
    simp only [szOf, h32, ↓reduceIte]
    clear h32 hw
    cases hp
    refine Exists.intro ?rw1 ?rh1
    case rh1 =>
      isel_eval [*, rule_inst_3742, rule_inst_2513, ctor_temp_writable_reg_i64,
        ctor_writable_reg_to_reg]
      rfl

include hp hc in
theorem rhs_3745 {w : Nat} (hw : w = 32 ∨ w = 64) {i : Int} {mw : MoveWideConst} :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+30) rule_inst_3745.rhs
        (env3 (.ty (.int w)) (.int i) (.op (.moveWideConst mw)))).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.movWide .movN (st.fresh .int).1 mw (szOf w)), tr')) := by
  rcases hw with rfl | rfl
  · have h3 := fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide)
    have h4 := ofV_movWide' ctx (op := .movN) (sz := .size32) (ks := 0) (.inr ⟨rfl, rfl⟩) rfl
    rw [show szOf 32 = .size32 from rfl]
    cases hp
    refine Exists.intro ?nw1 ?nh1
    case nh1 =>
      isel_eval [*, rule_inst_3745, rule_inst_2521, ctor_temp_writable_reg_i64,
        ctor_writable_reg_to_reg]
      rfl
  · have h3 := fun st tr n => operand_size_64 hp ctx hc st tr n (w := 64) (by decide) (by decide)
    have h4 := ofV_movWide' ctx (op := .movN) (sz := .size64) (ks := 1) (.inr ⟨rfl, rfl⟩) rfl
    rw [show szOf 64 = .size64 from rfl]
    cases hp
    refine Exists.intro ?nw2 ?nh2
    case nh2 =>
      isel_eval [*, rule_inst_3745, rule_inst_2521, ctor_temp_writable_reg_i64,
        ctor_writable_reg_to_reg]
      rfl

include hp hc in
theorem rhs_3751 {w : Nat} (hw : w = 32 ∨ w = 64) {i : Int} {il : ImmLogic} (x : V) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+30) rule_inst_3751.rhs
        (env4 (.ty (.int w)) (.int i) (.op (.immLogic il)) x)).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRImmLogic .orr (szOf w) (st.fresh .int).1 .xzr il), tr')) := by
  have e7 := ctor_zero_reg' ctx
  rcases hw with rfl | rfl
  · have h3 := fun st tr n a i => alu_rr_imm_logic_run hp ctx hc st tr n (k := 2) (op := .orr)
      (sz := .size32) (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide))
      rfl rfl a i
    rw [show szOf 32 = .size32 from rfl]
    cases hp
    refine Exists.intro ?ow1 ?oh1
    case oh1 =>
      isel_eval [*, rule_inst_3751, rule_inst_3416]
      rfl
  · have h3 := fun st tr n a i => alu_rr_imm_logic_run hp ctx hc st tr n (k := 2) (op := .orr)
      (sz := .size64) (fun st tr n => operand_size_64 hp ctx hc st tr n (w := 64) (by decide)
        (by decide)) rfl rfl a i
    rw [show szOf 64 = .size64 from rfl]
    cases hp
    refine Exists.intro ?ow2 ?oh2
    case oh2 =>
      isel_eval [*, rule_inst_3751, rule_inst_3416]
      rfl

include hp hc in
theorem rhs_3786 {w e : Nat} {i : Int} :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+30) rule_inst_3786.rhs
        (env3 (.ty (.int w)) (.data 122 e []) (.int i))).run (st, tr) =
      .ok (some (.reg (loadConstantFull w (e == 0) .size32 (u64 i) st).1),
        ((loadConstantFull w (e == 0) .size32 (u64 i) st).2, tr')) := by
  have h3 := fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide)
  have h4 := fun st => ctor_lcf ctx st w e 0 (sz := .size32) rfl i
  cases hp
  refine Exists.intro ?lw1 ?lh1
  case lh1 =>
    isel_eval [*, rule_inst_3786]
    rfl

include hp hc in
theorem rhs_3790 {e : Nat} {i : Int} :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+30) rule_inst_3790.rhs
        (env2 (.data 122 e []) (.int i))).run (st, tr) =
      .ok (some (.reg (loadConstantFull 64 (e == 0) .size64 (u64 i) st).1),
        ((loadConstantFull 64 (e == 0) .size64 (u64 i) st).2, tr')) := by
  have h3 := fun st tr n => operand_size_64 hp ctx hc st tr n (w := 64) (by decide) (by decide)
  have h4 := fun st => ctor_lcf ctx st 64 e 1 (sz := .size64) rfl i
  cases hp
  refine Exists.intro ?lw2 ?lh2
  case lh2 =>
    isel_eval [*, rule_inst_3790]
    rfl

end

/-! ## Meaning of the emitted code -/

theorem mwc_spec {v : Nat} {mw : MoveWideConst} (h : MoveWideConst.ofNat? v = some mw)
    (hv : v < 2 ^ 64) :
    mw.bits < 2 ^ 16 ∧ mw.shift < 4 ∧ mw.bits * 2 ^ (16 * mw.shift) = v ∧
      (v < 2 ^ 32 → mw.shift < 2) := by
  unfold MoveWideConst.ofNat? mask64 at h
  rw [Nat.mod_eq_of_lt hv] at h
  dsimp only at h
  split at h
  · rename_i h1; cases h; exact ⟨h1, Nat.zero_lt_succ _, by simp, fun _ => Nat.zero_lt_succ _⟩
  split at h
  · rename_i h1 h2; cases h; simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
    dsimp only; simp only [Nat.reduceMul, Nat.reducePow]; omega
  split at h
  · rename_i h1 h2 h3; cases h; simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h3
    dsimp only; simp only [Nat.reduceMul, Nat.reducePow]; omega
  split at h
  · rename_i h1 h2 h3 h4; cases h; simp only [beq_iff_eq] at h4
    dsimp only; simp only [Nat.reduceMul, Nat.reducePow]; omega
  · cases h

theorem movz_toNat {sz : OperandSize} {v : Nat} {mw : MoveWideConst}
    (h : MoveWideConst.ofNat? v = some mw) (hv : v < 2 ^ sz.bits) :
    (mw.bits < 2 ^ 16 ∧ 16 * mw.shift < sz.bits) ∧ (movWideVal .movZ sz.bits mw).toNat = v := by
  have h64 : v < 2 ^ 64 := Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (opSize_bits_le sz))
  obtain ⟨h1, h2, h3, h4⟩ := mwc_spec h h64
  simp only [movWideVal, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  cases sz <;> simp only [OperandSize.bits] at hv ⊢
  · have := h4 hv
    obtain ⟨b, sh⟩ := mw
    simp only at *
    obtain rfl | rfl : sh = 0 ∨ sh = 1 := by omega
    all_goals simp only [Nat.mul_zero, Nat.mul_one, Nat.pow_zero, Nat.reduceMul, Nat.reducePow] at *
    all_goals omega
  · obtain ⟨b, sh⟩ := mw
    simp only at *
    obtain rfl | rfl | rfl | rfl : sh = 0 ∨ sh = 1 ∨ sh = 2 ∨ sh = 3 := by omega
    all_goals simp only [Nat.mul_zero, Nat.mul_one, Nat.pow_zero, Nat.reduceMul, Nat.reducePow] at *
    all_goals omega

theorem movn_toNat {sz : OperandSize} {v : Nat} {mw : MoveWideConst}
    (h : MoveWideConst.ofNat? v = some mw) (hv : v < 2 ^ sz.bits) :
    (mw.bits < 2 ^ 16 ∧ 16 * mw.shift < sz.bits) ∧
      (movWideVal .movN sz.bits mw).toNat = 2 ^ sz.bits - 1 - v := by
  obtain ⟨hc, hz⟩ := movz_toNat h hv
  refine ⟨hc, ?_⟩
  simp only [movWideVal] at hz ⊢
  rw [BitVec.toNat_not, hz]

theorem vdd_orrImm (sz : OperandSize) (d : Nat) (il : ImmLogic) :
    vdefs (.aluRRImmLogic .orr sz (.vreg d .int) .xzr il) = [d] := rfl
theorem vdu_orrImm (sz : OperandSize) (d : Nat) (il : ImmLogic) :
    vuseNums (.aluRRImmLogic .orr sz (.vreg d .int) .xzr il) = [] := rfl

theorem ispec_orrImm_xzr {sz : OperandSize} {d v : Nat}
    (h : ImmLogic.ofNat? v sz = some ⟨v, sz⟩) (w : Arm.ArmState) :
    ispec (.aluRRImmLogic .orr sz (.vreg d .int) .xzr ⟨v, sz⟩) [] w =
      some ([resX sz (BitVec.ofNat _ v)], w, .next) := by
  show (if ImmLogic.ofNat? v sz = some ⟨v, sz⟩ ∧ ALUOp.orr ≠ .add ∧ ALUOp.orr ≠ .sub then _
    else none) = _
  simp only [h, ne_eq, reduceCtorEq, not_false_eq_true, and_self, ↓reduceIte, aluVal,
    Option.map_some, BitVec.zero_or]
  rfl

theorem immLogic_value {v : Nat} {sz : OperandSize} {il : ImmLogic}
    (h : ImmLogic.ofNat? v sz = some il) : il = ⟨v, sz⟩ := by
  cases sz <;> unfold ImmLogic.ofNat? at h <;> dsimp only at h <;> split at h <;>
    first | exact (Option.some.inj h).symm | cases h

/-- A one-instruction code, defining the fresh vreg `st.nextVreg` and reading nothing. -/
theorem codeShape_one {st : LState} {m : MInst} (hd : vdefs m = [st.nextVreg])
    (hu : vuseNums m = []) :
    CodeShape st ((st.fresh .int).2.emit m) [m] st.nextVreg st.nextVreg := by
  refine ⟨by simp [LState.emit, LState.fresh], by simp [LState.emit, LState.fresh], Nat.le_refl _,
    ?_, ?_⟩
  · intro mi hmi e he
    simp only [List.mem_singleton] at hmi; subst hmi
    rw [hd, List.mem_singleton] at he; subst he
    simp [LState.emit, LState.fresh]
  · intro mi hmi u hu'
    simp only [List.mem_singleton] at hmi; subst hmi
    rw [hu] at hu'; cases hu'

/-- The full 64-bit value `imm ty ext c` leaves (`load_constant_full`'s at the type's operand
size; the `movz`/`movn`/`orr` special cases agree with it except for `i32` constants `≥ 2³²`,
which the rules only pass for `ImmExtend.Sign`). -/
def immVal (w : Nat) (sg : Bool) (c : Nat) : Nat := lcfValue w sg (szOf w) c

theorem lcfValue32_mod {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32) (sg : Bool) {c : Nat}
    (hc : c < 2 ^ 64) : lcfValue w sg .size32 c % 2 ^ w = c % 2 ^ w := by
  unfold lcfValue mask64 u64 sextFrom
  rw [Nat.mod_eq_of_lt hc]
  rcases hw with rfl | rfl | rfl <;> cases sg <;> simp <;> omega

theorem lcfValue64 (sg : Bool) {c : Nat} (hc : c < 2 ^ 64) : lcfValue 64 sg .size64 c = c := by
  unfold lcfValue mask64
  cases sg <;> simp [Nat.mod_eq_of_lt hc]

/-- **What `imm ty ext c` produced**: a fresh vreg `d`, code with `CodeShape`, and on every run
a 64-bit value `X` in `d` whose low `w` bits are `c`'s, and which is `immVal` except for an
`i32` zero-extended constant `≥ 2³²`. -/
def ImmOut (F : BitVec 64 → Prop) (isem : Sem) (w e c : Nat) (st st' : LState) (v : V) : Prop :=
  ∃ ms d, v = .reg (.vreg d .int) ∧ CodeShape st st' ms d st.nextVreg ∧
    ∀ ρ, ∃ ρ' X, PRun F isem ms ρ ρ' ∧ lo64 (ρ' d) = BitVec.ofNat 64 X ∧ X % 2 ^ w = c % 2 ^ w ∧
      (w ≠ 32 ∨ e = 0 ∨ c < 2 ^ 32 → X = immVal w (e == 0) c)

section Contract
variable {F : BitVec 64 → Prop} {isem : Sem}

theorem immOut_one (hR : Refines F isem) {w e c : Nat} {st : LState} {m : MInst} {r : CV}
    (hd : vdefs m = [st.nextVreg]) (hu : vuseNums m = [])
    (hops : m.operands = .ok #[⟨st.nextVreg, .int, .def, .late, .reg⟩])
    (hs : ∀ w, ispec m [] w = some ([r], w, .next)) (X : Nat) (hX : lo64 r = BitVec.ofNat 64 X)
    (h1 : X % 2 ^ w = c % 2 ^ w) (h2 : w ≠ 32 ∨ e = 0 ∨ c < 2 ^ 32 → X = immVal w (e == 0) c) :
    ImmOut F isem w e c st ((st.fresh .int).2.emit m) (.reg (st.fresh .int).1) :=
  ⟨[m], st.nextVreg, rfl, codeShape_one hd hu, fun ρ =>
    ⟨_, X, prun_r0 hR hops hs (prun_nil _), by rw [upd_same]; exact hX, h1, h2⟩⟩

theorem imm_case_movz (hR : Refines F isem) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    {i : Int} {mw : MoveWideConst} (hmw : MoveWideConst.ofNat? (mwcArg w i) = some mw)
    (st : LState) :
    ImmOut F isem w 1 (u64 i) st
      ((st.fresh .int).2.emit (.movWide .movZ (st.fresh .int).1 mw (szOf w))) (.reg (st.fresh .int).1) := by
  have hc64 : u64 i < 2 ^ 64 := u64_lt' i
  have hvb : mwcArg w i < 2 ^ (szOf w).bits := by
    rcases hw with rfl | rfl | rfl | rfl <;> simp only [mwcArg, szOf, OperandSize.bits] <;>
      simp <;> omega
  have hb64 : 2 ^ (szOf w).bits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (opSize_bits_le _)
  obtain ⟨hcnd, hval⟩ := movz_toNat hmw hvb
  refine immOut_one hR rfl rfl rfl (fun w => ispec_movWide hcnd w) (mwcArg w i) ?_ ?_ ?_
  · apply BitVec.eq_of_toNat_eq
    rw [lo64_resX_toNat, hval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rcases hw with rfl | rfl | rfl | rfl <;> simp [mwcArg]
  · intro hcond
    rcases hw with rfl | rfl | rfl | rfl <;>
      simp [immVal, mwcArg, szOf, lcfValue, mask64, Nat.mod_eq_of_lt hc64] at hcond ⊢
    omega

theorem imm_case_movn (hR : Refines F isem) {w : Nat} (hw : w = 32 ∨ w = 64)
    {i : Int} {mw : MoveWideConst} (hmw : MoveWideConst.ofNat? (mwciArg w i) = some mw)
    (st : LState) :
    ImmOut F isem w 1 (u64 i) st
      ((st.fresh .int).2.emit (.movWide .movN (st.fresh .int).1 mw (szOf w))) (.reg (st.fresh .int).1) := by
  have hc64 : u64 i < 2 ^ 64 := u64_lt' i
  have hvb : mwciArg w i < 2 ^ (szOf w).bits := by
    rcases hw with rfl | rfl <;> simp only [mwciArg, szOf, OperandSize.bits] <;> simp <;> omega
  obtain ⟨hcnd, hval⟩ := movn_toNat hmw hvb
  refine immOut_one hR rfl rfl rfl (fun w => ispec_movWide hcnd w) (u64 i % 2 ^ w) ?_
    (Nat.mod_mod _ _) ?_
  · apply BitVec.eq_of_toNat_eq
    rw [lo64_resX_toNat, hval, BitVec.toNat_ofNat]
    rcases hw with rfl | rfl <;> simp only [mwciArg, szOf, OperandSize.bits] <;> simp <;> omega
  · intro hcond
    rcases hw with rfl | rfl <;>
      simp [immVal, szOf, lcfValue, mask64, Nat.mod_eq_of_lt hc64] at hcond ⊢ <;> omega

theorem imm_case_orr (hR : Refines F isem) {w : Nat} (hw : w = 32 ∨ w = 64)
    {i : Int} (hil : ImmLogic.ofNat? (u64 i) (szOf w) = some ⟨u64 i, szOf w⟩) (st : LState) :
    ImmOut F isem w 1 (u64 i) st
      ((st.fresh .int).2.emit (.aluRRImmLogic .orr (szOf w) (st.fresh .int).1 .xzr ⟨u64 i, szOf w⟩))
      (.reg (st.fresh .int).1) := by
  have hc64 : u64 i < 2 ^ 64 := u64_lt' i
  refine immOut_one hR rfl rfl rfl (fun w => ispec_orrImm_xzr hil w) (u64 i % 2 ^ w) ?_
    (Nat.mod_mod _ _) ?_
  · apply BitVec.eq_of_toNat_eq
    rw [lo64_resX_toNat]
    rcases hw with rfl | rfl <;> simp [szOf, OperandSize.bits, BitVec.toNat_ofNat, BitVec.zero_or] <;> omega
  · intro hcond
    rcases hw with rfl | rfl <;>
      simp [immVal, szOf, lcfValue, mask64, Nat.mod_eq_of_lt hc64] at hcond ⊢ <;> omega

theorem imm_case_lcf32 (hR : Refines F isem) {w e : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32) (i : Int)
    (st : LState) :
    ImmOut F isem w e (u64 i) st (loadConstantFull w (e == 0) .size32 (u64 i) st).2
      (.reg (loadConstantFull w (e == 0) .size32 (u64 i) st).1) := by
  obtain ⟨ms, d, hd, hsh, hrun⟩ := lcf_run (F := F) hR w (e == 0) .size32 (u64 i) st
  refine ⟨ms, d, by rw [hd], hsh, fun ρ => ?_⟩
  obtain ⟨ρ', hp', hv⟩ := hrun ρ
  refine ⟨ρ', _, hp', hv, lcfValue32_mod hw _ (u64_lt' i), fun _ => ?_⟩
  simp only [immVal, szOf, show w ≤ 32 by omega, ↓reduceIte]

theorem imm_case_lcf64 (hR : Refines F isem) {e : Nat} (i : Int) (st : LState) :
    ImmOut F isem 64 e (u64 i) st (loadConstantFull 64 (e == 0) .size64 (u64 i) st).2
      (.reg (loadConstantFull 64 (e == 0) .size64 (u64 i) st).1) := by
  obtain ⟨ms, d, hd, hsh, hrun⟩ := lcf_run (F := F) hR 64 (e == 0) .size64 (u64 i) st
  refine ⟨ms, d, by rw [hd], hsh, fun ρ => ?_⟩
  obtain ⟨ρ', hp', hv⟩ := hrun ρ
  exact ⟨ρ', _, hp', hv, by rw [lcfValue64 _ (u64_lt' i)], fun _ => rfl⟩

include hp hc in
/-- **Contract of `imm`** (all five rules), at `i8..i64`, both extensions. -/
theorem imm_ok (hR : Refines F isem) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {e : Nat}
    (he : e = 0 ∨ e = 1) {i : Int} {st : LState} {tr : Array RuleId} {n : Nat} {v : V}
    {s' : LState × Array RuleId}
    (h : (applyTerm p (sem ctx) cfg (n + 40) 27 553 (immArgs w e i)).run (st, tr) =
      .ok (some v, s')) :
    ImmOut F isem w e (u64 i) st s'.1 v := by
  obtain ⟨r, hr, m, env, s1, st2, tr2, hm, hmatch, heval, rfl⟩ :=
    applyTerm_internal_some (n := n + 39) hc hp.t553 term_553_kind rfl h
  rw [hp.r553] at hr hm
  simp only [R.imm, List.length_cons, List.length_nil] at hm
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  simp only [R.imm, List.mem_cons, List.mem_nil_iff, or_false] at hr
  have hwb : w ≤ 64 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · -- movz
    rcases he with rfl | rfl
    · rw [match_3742_none hp ctx st tr m' hw (.inl rfl)] at hmatch; cases hmatch
    cases hmw : MoveWideConst.ofNat? (mwcArg w i) with
    | none => rw [match_3742_none hp ctx st tr m' hw (.inr ⟨rfl, hmw⟩)] at hmatch; cases hmatch
    | some mw =>
      rw [match_3742 hp ctx st tr m' hw hmw] at hmatch
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
      obtain ⟨rfl, rfl⟩ := hmatch
      obtain ⟨tr', hr⟩ := rhs_3742 hp ctx hc st tr (n + 9) hwb (i := i) (mw := mw)
      rw [hr] at heval
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
      obtain ⟨rfl, rfl, rfl⟩ := heval
      exact imm_case_movz hR hw hmw st
  · -- movn
    rcases he with rfl | rfl
    · rw [match_3745_none hp ctx st tr m' hw (.inl rfl)] at hmatch; cases hmatch
    by_cases hn : w = 32 ∨ w = 64
    · cases hmw : MoveWideConst.ofNat? (mwciArg w i) with
      | none =>
        rw [match_3745_none hp ctx st tr m' hw (.inr (.inr ⟨rfl, hmw⟩))] at hmatch; cases hmatch
      | some mw =>
        rw [match_3745 hp ctx st tr m' hn hmw] at hmatch
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
        obtain ⟨rfl, rfl⟩ := hmatch
        obtain ⟨tr', hr⟩ := rhs_3745 hp ctx hc st tr (n + 9) hn (i := i) (mw := mw)
        rw [hr] at heval
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
        obtain ⟨rfl, rfl, rfl⟩ := heval
        exact imm_case_movn hR hn hmw st
    · rw [match_3745_none hp ctx st tr m' hw (.inr (.inl (by omega)))] at hmatch; cases hmatch
  · -- orr
    rcases he with rfl | rfl
    · rw [match_3751_none hp ctx st tr m' hw (.inl rfl) (.inl rfl)] at hmatch; cases hmatch
    by_cases hn : w = 32 ∨ w = 64
    · cases hil : ImmLogic.ofNat? (u64 i) (szOf w) with
      | none =>
        rw [match_3751_none hp ctx st tr m' hw (.inr rfl) (.inr (.inr ⟨rfl, hil⟩))] at hmatch
        cases hmatch
      | some il =>
        rw [match_3751 hp ctx st tr m' hn hil] at hmatch
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
        obtain ⟨rfl, rfl⟩ := hmatch
        obtain ⟨tr', hr⟩ := rhs_3751 hp ctx hc st tr (n + 9) hn (i := i) (il := il) (.int w)
        rw [hr] at heval
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
        obtain ⟨rfl, rfl, rfl⟩ := heval
        have hilv := immLogic_value hil
        subst hilv
        exact imm_case_orr hR hn hil st
    · rw [match_3751_none hp ctx st tr m' hw (.inr rfl) (.inr (.inl (by omega)))] at hmatch
      cases hmatch
  · -- load_constant_full at ≤ 32 bits
    by_cases h64 : w = 64
    · subst h64
      rw [match_3786_none hp ctx st tr m'] at hmatch; cases hmatch
    have hw' : w = 8 ∨ w = 16 ∨ w = 32 := by omega
    rw [match_3786 hp ctx st tr m' hw'] at hmatch
    simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
    obtain ⟨rfl, rfl⟩ := hmatch
    obtain ⟨tr', hr⟩ := rhs_3786 hp ctx hc st tr (n + 9) (w := w) (e := e) (i := i)
    rw [hr] at heval
    simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
    obtain ⟨rfl, rfl, rfl⟩ := heval
    exact imm_case_lcf32 hR hw' i st
  · -- load_constant_full at 64 bits
    by_cases h64 : w = 64
    · subst h64
      rw [match_3790 hp ctx st tr m'] at hmatch
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
      obtain ⟨rfl, rfl⟩ := hmatch
      obtain ⟨tr', hr⟩ := rhs_3790 hp ctx hc st tr (n + 9) (e := e) (i := i)
      rw [hr] at heval
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at heval
      obtain ⟨rfl, rfl, rfl⟩ := heval
      exact imm_case_lcf64 hR i st
    · rw [match_3790_none hp ctx st tr m' (w := w) (by omega)] at hmatch; cases hmatch

end Contract

end Backend.Proof

import FV.Backend.Proof.IselFamAluBBitrev

/-!
# Family B: `clz` and `ctz` root rules (`lower.isle:1951`, `1955`, `1961`, `1982`, `1986`, `1995`)

* `clz.i8`/`clz.i16`: `put_in_reg_zext32 x` (a `uxtb`/`uxth`), 32-bit `clz`, `sub #24`/`#16`;
* `clz.i32`/`i64`: one `clz` (rule `1961`; at i8/i16 the earlier rules `1951`/`1955` match);
* `ctz.i8`/`ctz.i16`: `rbit`, `orr #0x800000`/`#0x8000` (a sentinel bit just below the reversed
  byte/halfword, so a zero input counts 8/16), `clz`;
* `ctz.i32`/`i64`: `rbit`, `clz` (rule `1995`; at i8/i16 the rules `1982`/`1986` match).
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxRecDepth 20000 in
theorem variantNames_Clz : (variantNames 151)[107]? = some "Clz" := rfl
set_option maxRecDepth 20000 in
theorem variantNames_Ctz : (variantNames 151)[109]? = some "Ctz" := rfl

theorem ctor_u8_into_imm12_24 (st : LState) :
    externCtor ctx T.u8_into_imm12 [.int 24] st = .ok (.op (.imm12 ⟨24, false⟩), st) := rfl
theorem ctor_u8_into_imm12_16 (st : LState) :
    externCtor ctx T.u8_into_imm12 [.int 16] st = .ok (.op (.imm12 ⟨16, false⟩), st) := rfl
theorem ctor_imm_logic_800000 (st : LState) :
    externCtor ctx T.u64_into_imm_logic [.ty (.int 32), .int 8388608] st =
      .ok (.op (.immLogic ⟨8388608, .size32⟩), st) := rfl
theorem ctor_imm_logic_8000 (st : LState) :
    externCtor ctx T.u64_into_imm_logic [.ty (.int 32), .int 32768] st =
      .ok (.op (.immLogic ⟨32768, .size32⟩), st) := rfl

set_option maxRecDepth 20000 in
theorem lower_idx_1951 (hp : Data p) : (p.rulesOf TId.lower)[281]? = some rule_lower_1951 := by
  rw [show TId.lower = 686 from rfl, hp.r686]; rfl
set_option maxRecDepth 20000 in
theorem lower_idx_1955 (hp : Data p) : (p.rulesOf TId.lower)[282]? = some rule_lower_1955 := by
  rw [show TId.lower = 686 from rfl, hp.r686]; rfl
set_option maxRecDepth 20000 in
theorem lower_idx_1961 (hp : Data p) : (p.rulesOf TId.lower)[442]? = some rule_lower_1961 := by
  rw [show TId.lower = 686 from rfl, hp.r686]; rfl
set_option maxRecDepth 20000 in
theorem lower_idx_1982 (hp : Data p) : (p.rulesOf TId.lower)[284]? = some rule_lower_1982 := by
  rw [show TId.lower = 686 from rfl, hp.r686]; rfl
set_option maxRecDepth 20000 in
theorem lower_idx_1986 (hp : Data p) : (p.rulesOf TId.lower)[285]? = some rule_lower_1986 := by
  rw [show TId.lower = 686 from rfl, hp.r686]; rfl
set_option maxRecDepth 20000 in
theorem lower_idx_1995 (hp : Data p) : (p.rulesOf TId.lower)[443]? = some rule_lower_1995 := by
  rw [show TId.lower = 686 from rfl, hp.r686]; rfl

/-! ## Forward lemmas -/

section
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp in
theorem match_1951 {i x : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int 8))
    (hd : info.data = .data 152 29 [.data 151 107 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1951 [.inst i]).run (st, tr) =
      .ok (some (env1 (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  cases hp
  isel_eval [*, rule_lower_1951]

include hp in
theorem match_1951_ne {i x w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≠ 8)
    (hd : info.data = .data 152 29 [.data 151 107 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1951 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  have hne : (V.ty (.int w) == V.ty (.int 8)) = false := by simp [hw]
  cases hp
  isel_eval [*, rule_lower_1951]

include hp in
theorem match_1955 {i x : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int 16))
    (hd : info.data = .data 152 29 [.data 151 107 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1955 [.inst i]).run (st, tr) =
      .ok (some (env1 (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  cases hp
  isel_eval [*, rule_lower_1955]

include hp in
theorem match_1955_ne {i x w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≠ 16)
    (hd : info.data = .data 152 29 [.data 151 107 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1955 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  have hne : (V.ty (.int w) == V.ty (.int 16)) = false := by simp [hw]
  cases hp
  isel_eval [*, rule_lower_1955]

include hp in
theorem match_1961 {i x w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w))
    (hd : info.data = .data 152 29 [.data 151 107 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1961 [.inst i]).run (st, tr) =
      .ok (some (env2 (.ty (.int w)) (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  cases hp
  isel_eval [*, rule_lower_1961]

include hp in
theorem match_1982 {i x : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int 8))
    (hd : info.data = .data 152 29 [.data 151 109 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1982 [.inst i]).run (st, tr) =
      .ok (some (env1 (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  cases hp
  isel_eval [*, rule_lower_1982]

include hp in
theorem match_1982_ne {i x w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≠ 8)
    (hd : info.data = .data 152 29 [.data 151 109 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1982 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  have hne : (V.ty (.int w) == V.ty (.int 8)) = false := by simp [hw]
  cases hp
  isel_eval [*, rule_lower_1982]

include hp in
theorem match_1986 {i x : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int 16))
    (hd : info.data = .data 152 29 [.data 151 109 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1986 [.inst i]).run (st, tr) =
      .ok (some (env1 (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  cases hp
  isel_eval [*, rule_lower_1986]

include hp in
theorem match_1986_ne {i x w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≠ 16)
    (hd : info.data = .data 152 29 [.data 151 109 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1986 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq ctx
  have hne : (V.ty (.int w) == V.ty (.int 16)) = false := by simp [hw]
  cases hp
  isel_eval [*, rule_lower_1986]

include hp in
theorem match_1995 {i x w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w))
    (hd : info.data = .data 152 29 [.data 151 109 [], .value x]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1995 [.inst i]).run (st, tr) =
      .ok (some (env2 (.ty (.int w)) (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  cases hp
  isel_eval [*, rule_lower_1995]

include hp hc in
theorem rhs_1961 {x w : Nat} {rx : Reg} (hx : ctx.valueReg? x = some rx) (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_1961.rhs
        (env2 (.ty (.int w)) (.value x))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.bitRR .clz (szOf w) (st.fresh .int).1 rx), tr')) := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  by_cases h32 : w ≤ 32
  · have h3 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 1) (op := .clz)
      (sz := .size32) (fun st tr n => operand_size_32 hp ctx hc st tr n h32) rfl rfl a
    simp only [szOf, h32, ↓reduceIte]
    cases hp
    refine Exists.intro ?w ?h
    case h =>
      isel_eval [*, rule_lower_1961, rule_inst_3517, ctor_put_in_reg ctx _ hx]
      rfl
  · have h3 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 1) (op := .clz)
      (sz := .size64) (fun st tr n => operand_size_64 hp ctx hc st tr n (by omega) hw) rfl rfl a
    simp only [szOf, h32, ↓reduceIte]
    cases hp
    refine Exists.intro ?w2 ?h2
    case h2 =>
      isel_eval [*, rule_lower_1961, rule_inst_3517, ctor_put_in_reg ctx _ hx]
      rfl

set_option maxHeartbeats 1000000 in
include hp hc in
theorem rhs_1995 {x w : Nat} {rx : Reg} (hx : ctx.valueReg? x = some rx) (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_1995.rhs
        (env2 (.ty (.int w)) (.value x))).run (st, tr) =
      .ok (some (.regsVec [[.vreg (st.nextVreg + 1) .int]]),
        (((st.fresh .int).2.emit (.bitRR .rbit (szOf w) (st.fresh .int).1 rx)).fresh .int).2.emit
          (.bitRR .clz (szOf w) (.vreg (st.nextVreg + 1) .int) (st.fresh .int).1), tr') := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  by_cases h32 : w ≤ 32
  · have h3 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 1) (op := .clz)
      (sz := .size32) (fun st tr n => operand_size_32 hp ctx hc st tr n h32) rfl rfl a
    have h4 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 0) (op := .rbit)
      (sz := .size32) (fun st tr n => operand_size_32 hp ctx hc st tr n h32) rfl rfl a
    simp only [szOf, h32, ↓reduceIte]
    cases hp
    refine Exists.intro ?w ?h
    case h =>
      isel_eval [*, rule_lower_1995, rule_inst_3517, rule_inst_3512, ctor_put_in_reg ctx _ hx]
      rfl
  · have h3 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 1) (op := .clz)
      (sz := .size64) (fun st tr n => operand_size_64 hp ctx hc st tr n (by omega) hw) rfl rfl a
    have h4 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 0) (op := .rbit)
      (sz := .size64) (fun st tr n => operand_size_64 hp ctx hc st tr n (by omega) hw) rfl rfl a
    simp only [szOf, h32, ↓reduceIte]
    cases hp
    refine Exists.intro ?w2 ?h2
    case h2 =>
      isel_eval [*, rule_lower_1995, rule_inst_3517, rule_inst_3512, ctor_put_in_reg ctx _ hx]
      rfl

include hp hc in
theorem rhs_1982 {x : Nat} {rx : Reg} (hx : ctx.valueReg? x = some rx) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_1982.rhs (env1 (.value x))).run (st, tr) =
      .ok (some (.regsVec [[.vreg (st.nextVreg + 2) .int]]),
        (((((st.fresh .int).2.emit (.bitRR .rbit .size32 (st.fresh .int).1 rx)).fresh .int).2.emit
          (.aluRRImmLogic .orr .size32 (.vreg (st.nextVreg + 1) .int) (st.fresh .int).1
            ⟨8388608, .size32⟩)).fresh .int).2.emit
          (.bitRR .clz .size32 (.vreg (st.nextVreg + 2) .int) (.vreg (st.nextVreg + 1) .int)),
        tr') := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have h3 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 1) (op := .clz) (sz := .size32)
    (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide)) rfl rfl a
  have h4 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 0) (op := .rbit) (sz := .size32)
    (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide)) rfl rfl a
  have h5 := fun st tr n a i => alu_rr_imm_logic_run hp ctx hc st tr n (k := 2) (op := .orr)
    (sz := .size32) (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide))
    rfl rfl a i
  have h6 := ctor_imm_logic_800000 ctx
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_1982, rule_inst_3512, rule_inst_3517, rule_inst_3416,
      ctor_put_in_reg ctx _ hx]
    rfl

include hp hc in
theorem rhs_1986 {x : Nat} {rx : Reg} (hx : ctx.valueReg? x = some rx) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_1986.rhs (env1 (.value x))).run (st, tr) =
      .ok (some (.regsVec [[.vreg (st.nextVreg + 2) .int]]),
        (((((st.fresh .int).2.emit (.bitRR .rbit .size32 (st.fresh .int).1 rx)).fresh .int).2.emit
          (.aluRRImmLogic .orr .size32 (.vreg (st.nextVreg + 1) .int) (st.fresh .int).1
            ⟨32768, .size32⟩)).fresh .int).2.emit
          (.bitRR .clz .size32 (.vreg (st.nextVreg + 2) .int) (.vreg (st.nextVreg + 1) .int)),
        tr') := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have h3 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 1) (op := .clz) (sz := .size32)
    (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide)) rfl rfl a
  have h4 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 0) (op := .rbit) (sz := .size32)
    (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide)) rfl rfl a
  have h5 := fun st tr n a i => alu_rr_imm_logic_run hp ctx hc st tr n (k := 2) (op := .orr)
    (sz := .size32) (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide))
    rfl rfl a i
  have h6 := ctor_imm_logic_8000 ctx
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_1986, rule_inst_3512, rule_inst_3517, rule_inst_3416,
      ctor_put_in_reg ctx _ hx]
    rfl

include hp hc in
theorem rhs_1951_ext {x : Nat} {rx : Reg} {t : CTy} (hx : ctx.valueReg? x = some rx)
    (hT : ctx.valueType? x = some t) (h32 : t ≠ .int 32) (h64 : t ≠ .int 64) (hb : t.bits ≤ 32) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+80) rule_lower_1951.rhs (env1 (.value x))).run (st, tr) =
      .ok (some (.regsVec [[.vreg (st.nextVreg + 2) .int]]),
        (((((st.fresh .int).2.emit (.extend (st.fresh .int).1 rx false t.bits 32)).fresh .int).2.emit
          (.bitRR .clz .size32 (.vreg (st.nextVreg + 1) .int) (st.fresh .int).1)).fresh .int).2.emit
          (.aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 2) .int) (.vreg (st.nextVreg + 1) .int)
            ⟨24, false⟩),
        tr') := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have h3 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 1) (op := .clz) (sz := .size32)
    (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide)) rfl rfl a
  have h5 := fun st tr n a i => alu_rr_imm12_run hp ctx hc st tr n (k := 1) (op := .sub)
    (sz := .size32) (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide))
    rfl rfl a i
  have h6 := ctor_u8_into_imm12_24 ctx
  have h7 := fun st tr n => zext32_ext hp ctx hc st tr n hx hT h32 h64 hb
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_1951, rule_inst_3517, rule_inst_3142]
    rfl

set_option maxHeartbeats 1000000 in
include hp hc in
theorem rhs_1951_pass {x w : Nat} {rx : Reg} (hx : ctx.valueReg? x = some rx)
    (hT : ctx.valueType? x = some (.int w)) (hw : w = 32 ∨ w = 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+80) rule_lower_1951.rhs (env1 (.value x))).run (st, tr) =
      .ok (some (.regsVec [[.vreg (st.nextVreg + 1) .int]]),
        (((st.fresh .int).2.emit (.bitRR .clz .size32 (st.fresh .int).1 rx)).fresh .int).2.emit
          (.aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 1) .int) (st.fresh .int).1
            ⟨24, false⟩),
        tr') := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have h3 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 1) (op := .clz) (sz := .size32)
    (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide)) rfl rfl a
  have h5 := fun st tr n a i => alu_rr_imm12_run hp ctx hc st tr n (k := 1) (op := .sub)
    (sz := .size32) (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide))
    rfl rfl a i
  have h6 := ctor_u8_into_imm12_24 ctx
  rcases hw with rfl | rfl
  · have h7 := fun st tr n => zext32_pass32 hp ctx hc st tr n hx hT
    cases hp
    refine Exists.intro ?w1 ?h1
    case h1 =>
      isel_eval [*, rule_lower_1951, rule_inst_3517, rule_inst_3142]
      rfl
  · have h7 := fun st tr n => zext32_pass64 hp ctx hc st tr n hx hT
    cases hp
    refine Exists.intro ?w2 ?h2
    case h2 =>
      isel_eval [*, rule_lower_1951, rule_inst_3517, rule_inst_3142]
      rfl

include hp in
theorem rhs_1951_fail {x : Nat} (hT : ctx.valueType? x = none ∨ ∃ t, ctx.valueType? x = some t ∧
    t ≠ .int 32 ∧ t ≠ .int 64 ∧ ¬ t.bits ≤ 32) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+80) rule_lower_1951.rhs (env1 (.value x))).run (st, tr) ≠
      .ok (some v, s') := by
  rcases hT with hT | ⟨t, hT, h32, h64, hb⟩
  · have h7 := fun st tr n => zext32_none hp ctx (cfg := cfg) st tr n hT
    cases hp
    isel_eval [*, rule_lower_1951, rule_inst_3517, rule_inst_3142]
    exact fun h => by cases h
  · have h7 := fun st tr n => zext32_big hp ctx (cfg := cfg) st tr n hT h32 h64 hb
    cases hp
    isel_eval [*, rule_lower_1951, rule_inst_3517, rule_inst_3142]
    exact fun h => by cases h

include hp hc in
theorem rhs_1955_ext {x : Nat} {rx : Reg} {t : CTy} (hx : ctx.valueReg? x = some rx)
    (hT : ctx.valueType? x = some t) (h32 : t ≠ .int 32) (h64 : t ≠ .int 64) (hb : t.bits ≤ 32) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+80) rule_lower_1955.rhs (env1 (.value x))).run (st, tr) =
      .ok (some (.regsVec [[.vreg (st.nextVreg + 2) .int]]),
        (((((st.fresh .int).2.emit (.extend (st.fresh .int).1 rx false t.bits 32)).fresh .int).2.emit
          (.bitRR .clz .size32 (.vreg (st.nextVreg + 1) .int) (st.fresh .int).1)).fresh .int).2.emit
          (.aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 2) .int) (.vreg (st.nextVreg + 1) .int)
            ⟨16, false⟩),
        tr') := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have h3 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 1) (op := .clz) (sz := .size32)
    (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide)) rfl rfl a
  have h5 := fun st tr n a i => alu_rr_imm12_run hp ctx hc st tr n (k := 1) (op := .sub)
    (sz := .size32) (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide))
    rfl rfl a i
  have h6 := ctor_u8_into_imm12_16 ctx
  have h7 := fun st tr n => zext32_ext hp ctx hc st tr n hx hT h32 h64 hb
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_1955, rule_inst_3517, rule_inst_3142]
    rfl

set_option maxHeartbeats 1000000 in
include hp hc in
theorem rhs_1955_pass {x w : Nat} {rx : Reg} (hx : ctx.valueReg? x = some rx)
    (hT : ctx.valueType? x = some (.int w)) (hw : w = 32 ∨ w = 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+80) rule_lower_1955.rhs (env1 (.value x))).run (st, tr) =
      .ok (some (.regsVec [[.vreg (st.nextVreg + 1) .int]]),
        (((st.fresh .int).2.emit (.bitRR .clz .size32 (st.fresh .int).1 rx)).fresh .int).2.emit
          (.aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 1) .int) (st.fresh .int).1
            ⟨16, false⟩),
        tr') := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have h3 := fun st tr n a => bit_rr_run hp ctx hc st tr n (k := 1) (op := .clz) (sz := .size32)
    (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide)) rfl rfl a
  have h5 := fun st tr n a i => alu_rr_imm12_run hp ctx hc st tr n (k := 1) (op := .sub)
    (sz := .size32) (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide))
    rfl rfl a i
  have h6 := ctor_u8_into_imm12_16 ctx
  rcases hw with rfl | rfl
  · have h7 := fun st tr n => zext32_pass32 hp ctx hc st tr n hx hT
    cases hp
    refine Exists.intro ?w1 ?h1
    case h1 =>
      isel_eval [*, rule_lower_1955, rule_inst_3517, rule_inst_3142]
      rfl
  · have h7 := fun st tr n => zext32_pass64 hp ctx hc st tr n hx hT
    cases hp
    refine Exists.intro ?w2 ?h2
    case h2 =>
      isel_eval [*, rule_lower_1955, rule_inst_3517, rule_inst_3142]
      rfl

include hp in
theorem rhs_1955_fail {x : Nat} (hT : ctx.valueType? x = none ∨ ∃ t, ctx.valueType? x = some t ∧
    t ≠ .int 32 ∧ t ≠ .int 64 ∧ ¬ t.bits ≤ 32) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+80) rule_lower_1955.rhs (env1 (.value x))).run (st, tr) ≠
      .ok (some v, s') := by
  rcases hT with hT | ⟨t, hT, h32, h64, hb⟩
  · have h7 := fun st tr n => zext32_none hp ctx (cfg := cfg) st tr n hT
    cases hp
    isel_eval [*, rule_lower_1955, rule_inst_3517, rule_inst_3142]
    exact fun h => by cases h
  · have h7 := fun st tr n => zext32_big hp ctx (cfg := cfg) st tr n hT h32 h64 hb
    cases hp
    isel_eval [*, rule_lower_1955, rule_inst_3517, rule_inst_3142]
    exact fun h => by cases h

include hp in
theorem rhs_1961_none {x w : Nat} (hx : ctx.valueReg? x = none) (v : V)
    (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_1961.rhs (env2 (.ty (.int w)) (.value x))).run (st, tr) ≠
      .ok (some v, s') := by
  cases hp
  isel_eval [*, rule_lower_1961, rule_inst_3512, rule_inst_3517, rule_inst_3416,
    ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

include hp in
theorem rhs_1995_none {x w : Nat} (hx : ctx.valueReg? x = none) (v : V)
    (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_1995.rhs (env2 (.ty (.int w)) (.value x))).run (st, tr) ≠
      .ok (some v, s') := by
  cases hp
  isel_eval [*, rule_lower_1995, rule_inst_3512, rule_inst_3517, rule_inst_3416,
    ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

include hp in
theorem rhs_1982_none {x : Nat} (hx : ctx.valueReg? x = none) (v : V)
    (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_1982.rhs (env1 (.value x))).run (st, tr) ≠
      .ok (some v, s') := by
  cases hp
  isel_eval [*, rule_lower_1982, rule_inst_3512, rule_inst_3517, rule_inst_3416,
    ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

include hp in
theorem rhs_1986_none {x : Nat} (hx : ctx.valueReg? x = none) (v : V)
    (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_1986.rhs (env1 (.value x))).run (st, tr) ≠
      .ok (some v, s') := by
  cases hp
  isel_eval [*, rule_lower_1986, rule_inst_3512, rule_inst_3517, rule_inst_3416,
    ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

end

/-! ## The rule theorems -/

include hp in
/-- **`clz.i32`/`clz.i64`** (`lower.isle:1961`): one `clz`. At i8/i16 the earlier rules `1951`/`1955` match.** -/
theorem clz_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1961 :=
  unary_ruleOk hp (cop := .clz) rfl hp.t2391 term_2391_kind variantNames_Clz rfl
    (fun w x => env2 (.ty (.int w)) (.value x)) (fun w => w ≠ 8 ∧ w ≠ 16) (fun _ _ => True)
    (fun _ _ => 1) (fun w _ b x => [.bitRR .clz (szOf w) (.vreg b .int) (.vreg x .int)])
    (fun _ _ b => b)
    (fun ctx _ ii _ w _ st tr m _ _ hi hty _ hd hfirst h => by
      rw [match_1961 hp ctx st tr m hi hty hd] at h
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      refine ⟨h.1.symm, h.2.symm, ?_, ?_⟩
      · rintro rfl
        obtain ⟨pre, post, hL, hmem⟩ := earlier_of_idx (lower_idx_1961 hp) (lower_idx_1951 hp)
          (by decide)
        obtain ⟨m', hm', s', h'⟩ := hfirst pre post hL _ hmem
        obtain ⟨k, rfl⟩ : ∃ k, m' = k + 2 := ⟨m' - 2, by omega⟩
        rw [match_1951 hp ctx st tr k hi hty hd] at h'; cases h'
      · rintro rfl
        obtain ⟨pre, post, hL, hmem⟩ := earlier_of_idx (lower_idx_1961 hp) (lower_idx_1955 hp)
          (by decide)
        obtain ⟨m', hm', s', h'⟩ := hfirst pre post hL _ hmem
        obtain ⟨k, rfl⟩ : ∃ k, m' = k + 2 := ⟨m' - 2, by omega⟩
        rw [match_1955 hp ctx st tr k hi hty hd] at h'; cases h')
    (fun ctx _ _ _ st tr n hc hx hw _ _ => by
      obtain ⟨tr', h⟩ := rhs_1961 hp ctx hc st tr n hx hw
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_1961_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u hety _ hP _ _ _ hu => by
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_nil _), ?_⟩
      have hu' : (ρ x).setWidth ty.width = u := hu
      subst hu'
      revert hP
      wcases ty hety [Clif.Sem.unary, Clif.Sem.clz, Clif.Ty.width, ne_eq, not_true_eq_false,
        false_and, and_false, false_implies])

include hp in
/-- **`ctz.i32`/`ctz.i64`** (`lower.isle:1995`): `rbit`, `clz`. At i8/i16 the earlier rules `1982`/`1986` match.** -/
theorem ctz_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1995 :=
  unary_ruleOk hp (cop := .ctz) rfl hp.t2393 term_2393_kind variantNames_Ctz rfl
    (fun w x => env2 (.ty (.int w)) (.value x)) (fun w => w ≠ 8 ∧ w ≠ 16) (fun _ _ => True)
    (fun _ _ => 2) (fun w _ b x => [.bitRR .rbit (szOf w) (.vreg b .int) (.vreg x .int), .bitRR .clz (szOf w) (.vreg (b + 1) .int) (.vreg b .int)])
    (fun _ _ b => b + 1)
    (fun ctx _ ii _ w _ st tr m _ _ hi hty _ hd hfirst h => by
      rw [match_1995 hp ctx st tr m hi hty hd] at h
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      refine ⟨h.1.symm, h.2.symm, ?_, ?_⟩
      · rintro rfl
        obtain ⟨pre, post, hL, hmem⟩ := earlier_of_idx (lower_idx_1995 hp) (lower_idx_1982 hp)
          (by decide)
        obtain ⟨m', hm', s', h'⟩ := hfirst pre post hL _ hmem
        obtain ⟨k, rfl⟩ : ∃ k, m' = k + 2 := ⟨m' - 2, by omega⟩
        rw [match_1982 hp ctx st tr k hi hty hd] at h'; cases h'
      · rintro rfl
        obtain ⟨pre, post, hL, hmem⟩ := earlier_of_idx (lower_idx_1995 hp) (lower_idx_1986 hp)
          (by decide)
        obtain ⟨m', hm', s', h'⟩ := hfirst pre post hL _ hmem
        obtain ⟨k, rfl⟩ : ∃ k, m' = k + 2 := ⟨m' - 2, by omega⟩
        rw [match_1986 hp ctx st tr k hi hty hd] at h'; cases h')
    (fun ctx _ _ _ st tr n hc hx hw _ _ => by
      obtain ⟨tr', h⟩ := rhs_1995 hp ctx hc st tr n hx hw
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_1995_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u hety _ hP _ _ _ hu => by
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_rr hR rfl (fun _ => rfl) (prun_nil _)), ?_⟩
      have hu' : (ρ x).setWidth ty.width = u := hu
      subst hu'
      revert hP
      wcases ty hety [Clif.Sem.unary, Clif.Sem.ctz, BitVec.ctz, Clif.Ty.width, ne_eq, not_true_eq_false,
        false_and, and_false, false_implies])

include hp in
/-- **`ctz.i8`** (`lower.isle:1982`).** -/
theorem ctz_i8_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1982 :=
  unary_ruleOk hp (cop := .ctz) rfl hp.t2393 term_2393_kind variantNames_Ctz rfl
    (fun _ x => env1 (.value x)) (fun w => w = 8) (fun _ _ => True) (fun _ _ => 3)
    (fun _ _ b x => [.bitRR .rbit .size32 (.vreg b .int) (.vreg x .int),
      .aluRRImmLogic .orr .size32 (.vreg (b + 1) .int) (.vreg b .int) ⟨8388608, .size32⟩,
      .bitRR .clz .size32 (.vreg (b + 2) .int) (.vreg (b + 1) .int)])
    (fun _ _ b => b + 2)
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases hw : w = 8
      · subst hw
        rw [match_1982 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_1982_ne hp ctx st tr m hi hty hw hd] at h; cases h)
    (fun ctx _ _ _ st tr n hc hx _ _ _ => by
      obtain ⟨tr', h⟩ := rhs_1982 hp ctx hc st tr n hx
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_1982_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u _ _ hP _ _ _ hu => by
      obtain rfl := ty_eq_of_width (ty' := .i8) hP (by decide)
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_rr hR rfl (fun _ => rfl)
        (prun_rr hR rfl (fun _ => rfl) (prun_nil _))), ?_⟩
      have hu' : (ρ x).setWidth 8 = u := hu
      subst hu'
      wfix [Clif.Sem.unary, Clif.Sem.ctz, BitVec.ctz, aluVal])

include hp in
/-- **`ctz.i16`** (`lower.isle:1986`).** -/
theorem ctz_i16_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1986 :=
  unary_ruleOk hp (cop := .ctz) rfl hp.t2393 term_2393_kind variantNames_Ctz rfl
    (fun _ x => env1 (.value x)) (fun w => w = 16) (fun _ _ => True) (fun _ _ => 3)
    (fun _ _ b x => [.bitRR .rbit .size32 (.vreg b .int) (.vreg x .int),
      .aluRRImmLogic .orr .size32 (.vreg (b + 1) .int) (.vreg b .int) ⟨32768, .size32⟩,
      .bitRR .clz .size32 (.vreg (b + 2) .int) (.vreg (b + 1) .int)])
    (fun _ _ b => b + 2)
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases hw : w = 16
      · subst hw
        rw [match_1986 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_1986_ne hp ctx st tr m hi hty hw hd] at h; cases h)
    (fun ctx _ _ _ st tr n hc hx _ _ _ => by
      obtain ⟨tr', h⟩ := rhs_1986 hp ctx hc st tr n hx
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_1986_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u _ _ hP _ _ _ hu => by
      obtain rfl := ty_eq_of_width (ty' := .i16) hP (by decide)
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_rr hR rfl (fun _ => rfl)
        (prun_rr hR rfl (fun _ => rfl) (prun_nil _))), ?_⟩
      have hu' : (ρ x).setWidth 16 = u := hu
      subst hu'
      wfix [Clif.Sem.unary, Clif.Sem.ctz, BitVec.ctz, aluVal])

set_option maxHeartbeats 1000000 in
include hp in
/-- **`clz.i8`** (`lower.isle:1951`).** -/
theorem clz_i8_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1951 :=
  unary_ruleOk' hp (cop := .clz) rfl hp.t2391 term_2391_kind variantNames_Clz rfl
    (fun _ x => env1 (.value x)) (fun w => w = 8) F isem MR env cp hMR
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases hw : w = 8
      · subst hw
        rw [match_1951 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_1951_ne hp ctx st tr m hi hty hw hd] at h; cases h)
    (fun ctx cfg _ _ st tr n v s' _ hT => by
      have := rhs_1951_fail hp ctx (cfg := cfg) st tr (n + 120) (.inl hT) v s'
      rwa [show n + 120 + 80 = n + 200 by omega] at this)
    (fun ctx cfg x w st tr n v s' hc hx _ _ hP he => by
      subst hP
      cases hT : ctx.valueType? x with
      | none =>
        have := rhs_1951_fail hp ctx (cfg := cfg) st tr (n + 120) (.inl hT) v s'
        rw [show n + 120 + 80 = n + 200 by omega] at this
        exact absurd he this
      | some t =>
      by_cases h32 : t = .int 32
      · subst h32
        obtain ⟨tr', h⟩ := rhs_1951_pass hp ctx hc st tr (n + 120) hx hT (.inl rfl)
        rw [show n + 120 + 80 = n + 200 by omega, he] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[.bitRR .clz .size32 (.vreg st.nextVreg .int) (.vreg x .int), .aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 1) .int) (.vreg st.nextVreg .int) ⟨24, false⟩], _, rfl, ⟨by st_facts, by st_facts, by st_facts, by code_facts0, by code_facts0⟩,
          ?_⟩
        intro ty _ _ _ hT'
        rcases hT' with h | h <;> simp at h
      by_cases h64 : t = .int 64
      · subst h64
        obtain ⟨tr', h⟩ := rhs_1951_pass hp ctx hc st tr (n + 120) hx hT (.inr rfl)
        rw [show n + 120 + 80 = n + 200 by omega, he] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[.bitRR .clz .size32 (.vreg st.nextVreg .int) (.vreg x .int), .aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 1) .int) (.vreg st.nextVreg .int) ⟨24, false⟩], _, rfl, ⟨by st_facts, by st_facts, by st_facts, by code_facts0, by code_facts0⟩,
          ?_⟩
        intro ty _ _ _ hT'
        rcases hT' with h | h <;> simp at h
      by_cases hb : t.bits ≤ 32
      · obtain ⟨tr', h⟩ := rhs_1951_ext hp ctx hc st tr (n + 120) hx hT h32 h64 hb
        rw [show n + 120 + 80 = n + 200 by omega, he] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[.extend (.vreg st.nextVreg .int) (.vreg x .int) false t.bits 32, .bitRR .clz .size32 (.vreg (st.nextVreg + 1) .int) (.vreg st.nextVreg .int), .aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 2) .int) (.vreg (st.nextVreg + 1) .int) ⟨24, false⟩], _, rfl, ⟨by st_facts, by st_facts, by st_facts, by code_facts0, by code_facts0⟩,
          ?_⟩
        intro ty hty _ _ hT' ρ u hu
        have ht : t = .int 8 := by rcases hT' with h | h <;> simp_all
        subst ht
        obtain rfl := ty_eq_of_width (ty' := .i8) hty (by decide)
        refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_rr hR rfl (fun _ => rfl)
          (prun_rr hR rfl (fun _ => rfl) (prun_nil _))), ?_⟩
        have hu' : (ρ x).setWidth 8 = u := hu
        subst hu'
        wfix [Clif.Sem.unary, Clif.Sem.clz, CTy.bits, Imm12.value]
      · have := rhs_1951_fail hp ctx (cfg := cfg) st tr (n + 120) (.inr ⟨t, hT, h32, h64, hb⟩) v s'
        rw [show n + 120 + 80 = n + 200 by omega] at this
        exact absurd he this)

set_option maxHeartbeats 1000000 in
include hp in
/-- **`clz.i16`** (`lower.isle:1955`).** -/
theorem clz_i16_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1955 :=
  unary_ruleOk' hp (cop := .clz) rfl hp.t2391 term_2391_kind variantNames_Clz rfl
    (fun _ x => env1 (.value x)) (fun w => w = 16) F isem MR env cp hMR
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases hw : w = 16
      · subst hw
        rw [match_1955 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_1955_ne hp ctx st tr m hi hty hw hd] at h; cases h)
    (fun ctx cfg _ _ st tr n v s' _ hT => by
      have := rhs_1955_fail hp ctx (cfg := cfg) st tr (n + 120) (.inl hT) v s'
      rwa [show n + 120 + 80 = n + 200 by omega] at this)
    (fun ctx cfg x w st tr n v s' hc hx _ _ hP he => by
      subst hP
      cases hT : ctx.valueType? x with
      | none =>
        have := rhs_1955_fail hp ctx (cfg := cfg) st tr (n + 120) (.inl hT) v s'
        rw [show n + 120 + 80 = n + 200 by omega] at this
        exact absurd he this
      | some t =>
      by_cases h32 : t = .int 32
      · subst h32
        obtain ⟨tr', h⟩ := rhs_1955_pass hp ctx hc st tr (n + 120) hx hT (.inl rfl)
        rw [show n + 120 + 80 = n + 200 by omega, he] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[.bitRR .clz .size32 (.vreg st.nextVreg .int) (.vreg x .int), .aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 1) .int) (.vreg st.nextVreg .int) ⟨16, false⟩], _, rfl, ⟨by st_facts, by st_facts, by st_facts, by code_facts0, by code_facts0⟩,
          ?_⟩
        intro ty _ _ _ hT'
        rcases hT' with h | h <;> simp at h
      by_cases h64 : t = .int 64
      · subst h64
        obtain ⟨tr', h⟩ := rhs_1955_pass hp ctx hc st tr (n + 120) hx hT (.inr rfl)
        rw [show n + 120 + 80 = n + 200 by omega, he] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[.bitRR .clz .size32 (.vreg st.nextVreg .int) (.vreg x .int), .aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 1) .int) (.vreg st.nextVreg .int) ⟨16, false⟩], _, rfl, ⟨by st_facts, by st_facts, by st_facts, by code_facts0, by code_facts0⟩,
          ?_⟩
        intro ty _ _ _ hT'
        rcases hT' with h | h <;> simp at h
      by_cases hb : t.bits ≤ 32
      · obtain ⟨tr', h⟩ := rhs_1955_ext hp ctx hc st tr (n + 120) hx hT h32 h64 hb
        rw [show n + 120 + 80 = n + 200 by omega, he] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[.extend (.vreg st.nextVreg .int) (.vreg x .int) false t.bits 32, .bitRR .clz .size32 (.vreg (st.nextVreg + 1) .int) (.vreg st.nextVreg .int), .aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 2) .int) (.vreg (st.nextVreg + 1) .int) ⟨16, false⟩], _, rfl, ⟨by st_facts, by st_facts, by st_facts, by code_facts0, by code_facts0⟩,
          ?_⟩
        intro ty hty _ _ hT' ρ u hu
        have ht : t = .int 16 := by rcases hT' with h | h <;> simp_all
        subst ht
        obtain rfl := ty_eq_of_width (ty' := .i16) hty (by decide)
        refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_rr hR rfl (fun _ => rfl)
          (prun_rr hR rfl (fun _ => rfl) (prun_nil _))), ?_⟩
        have hu' : (ρ x).setWidth 16 = u := hu
        subst hu'
        wfix [Clif.Sem.unary, Clif.Sem.clz, CTy.bits, Imm12.value]
      · have := rhs_1955_fail hp ctx (cfg := cfg) st tr (n + 120) (.inr ⟨t, hT, h32, h64, hb⟩) v s'
        rw [show n + 120 + 80 = n + 200 by omega] at this
        exact absurd he this)

end Backend.Proof

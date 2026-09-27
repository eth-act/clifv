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

end Backend.Proof

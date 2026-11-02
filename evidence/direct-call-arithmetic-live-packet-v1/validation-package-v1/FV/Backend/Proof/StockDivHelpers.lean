import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.StockDivPure
import FV.Backend.Proof.IselCmpSdiv
import FV.Backend.Proof.IselTermsALUAMul
import FV.Backend.Proof.StockShiftHelper
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- Actual signed/unsigned division helpers emit the selected machine size and
preserve all Stock scheduling fields; source requests remain separate. -/
theorem stock_div_quotient_helper {p : Program} (hp : Data p) (ctx : Ctx)
    {cfg : Config} (hc : cfg.checkOverlap = false) {w : Nat} (width : w ≤ 64)
    (signed : Bool) (st : State) (tr : Array RuleId) (n : Nat) (rx ry : Reg) :
    ∃ trace,(applyTerm p (Stock.sem ctx) cfg (n+30) 27 (if signed then 493 else 492)
      [.ty (.int w),.reg rx,.reg ry]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := ((st.base.fresh .int).2.emit
          (.aluRRR (if signed then .sDiv else .uDiv) (szOf w) (st.base.fresh .int).1 rx ry))},trace) := by
  obtain ⟨ks,rid,size,sizeRun⟩ := operand_size_run hp ctx hc width
  cases signed
  · have alu := fun q trace fuel => alu_rrr_run hp ctx hc q trace fuel sizeRun
      (fun q rd rn rm => emit_aluRRR ctx q (k := VIdx.ALUOp.UDiv) rfl size rd rn rm) rx ry
    have legacy : (applyTerm p (Backend.sem ctx) cfg (n+30) 27 492
        [.ty (.int w),.reg rx,.reg ry]).run (st.base,tr) =
        .ok (some (.reg (st.base.fresh .int).1),(st.base.fresh .int).2.emit
          (.aluRRR .uDiv (szOf w) (st.base.fresh .int).1 rx ry),
          ((tr.push rid).push rule_inst_2545.id).push rule_inst_3389.id) := by
      cases hp
      isel_eval [*,rule_inst_3389]
    exact ⟨_,stock_div_pure_helper hp ctx (cfg := cfg) hc (by decide) legacy⟩
  · have alu := fun q trace fuel => alu_rrr_run hp ctx hc q trace fuel sizeRun
      (fun q rd rn rm => emit_aluRRR ctx q (k := VIdx.ALUOp.SDiv) rfl size rd rn rm) rx ry
    have legacy : (applyTerm p (Backend.sem ctx) cfg (n+30) 27 493
        [.ty (.int w),.reg rx,.reg ry]).run (st.base,tr) =
        .ok (some (.reg (st.base.fresh .int).1),(st.base.fresh .int).2.emit
          (.aluRRR .sDiv (szOf w) (st.base.fresh .int).1 rx ry),
          ((tr.push rid).push rule_inst_2545.id).push rule_inst_3394.id) := by
      cases hp
      isel_eval [*,rule_inst_3394]
    exact ⟨_,stock_div_pure_helper hp ctx (cfg := cfg) hc (by decide) legacy⟩

/-- The actual remainder multiply-subtract helper preserves the full Stock
frame while emitting the machine remainder reconstruction. -/
theorem stock_div_msub_helper {p : Program} (hp : Data p) (ctx : Ctx)
    {cfg : Config} (hc : cfg.checkOverlap = false) {w : Nat} (width : w ≤ 64)
    (st : State) (tr : Array RuleId) (n : Nat) (rx ry rz : Reg) :
    ∃ trace,(applyTerm p (Stock.sem ctx) cfg (n+30) 27 444
      [.ty (.int w),.reg rx,.reg ry,.reg rz]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := ((st.base.fresh .int).2.emit
          (.aluRRRR .mSub (szOf w) (st.base.fresh .int).1 rx ry rz))},trace) := by
  obtain ⟨ks,rid,size,sizeRun⟩ := operand_size_run hp ctx hc width
  exact ⟨_,stock_div_pure_helper hp ctx (cfg := cfg) hc (by decide)
    (msub_run hp ctx hc st.base tr n sizeRun size rx ry rz)⟩
def sizeIndex : OperandSize → Nat | .size32 => 0 | .size64 => 1
/-- The actual divisor-zero helper emits its runtime guard and returns the
same operand without allocating a register or changing scheduling fields. -/
theorem stock_div_zero_guard_helper {p : Program} (hp : Data p) (ctx : Ctx)
    {cfg : Config} (hc : cfg.checkOverlap = false) (sz : OperandSize)
    (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) cfg (n+40) 27 559
      [.reg r,.data 93 (sizeIndex sz) []]).run (st,tr) =
      .ok (some (.reg r),{st with base := st.base.emit (.trapIf (.zero r sz) .intDivz)},
        tr.push rule_inst_3838.id) := by
  have size : OperandSize.ofIdx? (sizeIndex sz) = some sz := by cases sz <;> rfl
  have emit := fun q => ctor_emit ctx q (ofV_trapIf_zero r size .intDivz)
  have cond : ∀ q,Backend.externCtor ctx T.cond_br_zero [.reg r,.data 93 (sizeIndex sz) []] q =
      .ok (.data tyCondBrKind VIdx.CondBrKind.Zero [.reg r,.data 93 (sizeIndex sz) []],q) := fun _ => rfl
  have code : ∀ q,Backend.externCtor ctx T.trap_code_division_by_zero [] q =
      .ok (.op (.trapCode .intDivz),q) := fun _ => rfl
  have legacy : (applyTerm p (Backend.sem ctx) cfg (n+40) 27 559
      [.reg r,.data 93 (sizeIndex sz) []]).run (st.base,tr) =
      .ok (some (.reg r),st.base.emit (.trapIf (.zero r sz) .intDivz),tr.push rule_inst_3838.id) := by
    cases hp
    isel_eval [*,rule_inst_3838]
  exact stock_div_pure_helper hp ctx hc (by decide) legacy
def overflowBase (b : LState) (w : Nat) (check divisor : Reg) : LState :=
  ((b.emit (.aluRRImm12 .addS (szOf w) .xzr divisor ⟨1,false⟩)).emit
    (.ccmpImm (szOf w) check 1 ⟨false,false,false,false⟩ .eq)).emit (.trapIf (.cond .vs) .intOvf)
/-- The real overflow helper emits all three flag/guard instructions, returns
the original dividend, and preserves the full Stock scheduling state. -/
theorem stock_div_overflow_guard_helper {p : Program} (hp : Data p) (ctx : Ctx)
    {cfg : Config} (hc : cfg.checkOverlap = false) {w : Nat}
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (st : State) (tr : Array RuleId) (n : Nat) (check dividend divisor : Reg) :
    ∃ trace,(applyTerm p (Stock.sem ctx) cfg (n+60) 27 561
      [.ty (.int w),.reg check,.reg dividend,.reg divisor]).run (st,tr) =
      .ok (some (.reg dividend),{st with base := overflowBase st.base w check divisor},trace) := by
  obtain ⟨ks,rid,size,sizeRun⟩ := operand_size_run hp ctx hc (show w ≤ 64 by omega)
  have addEmit := fun q => ctor_emit ctx q (ofV_addsImm ks size .xzr divisor ⟨1,false⟩)
  have cmpEmit := fun q => ctor_emit ctx q (ofV_ccmpImm1 (if w ≤ 32 then 0 else 1) (szIdx_ofIdx w) check)
  have trapEmit := fun q => ctor_emit ctx q ofV_trapIf_vs
  have codeOverflow : ∀ q,Backend.externCtor ctx T.trap_code_integer_overflow [] q =
      .ok (.op (.trapCode .intOvf),q) := fun _ => rfl
  have eq : ∀ a b,(Backend.sem ctx).eq a b = (a == b) := fun _ _ => rfl
  have sizeFrom : ∀ q trace fuel,(applyTerm p (Backend.sem ctx) cfg (fuel+10) 93 560 [.ty (.int w)]).run (q,trace) =
      .ok (some (.data 93 (if w ≤ 32 then 0 else 1) []),q,
        trace.push (if w ≤ 32 then rule_inst_3852.id else rule_inst_3853.id)) := by
    intro q trace fuel
    cases hp
    rcases width with rfl | rfl | rfl | rfl
    all_goals isel_eval [*,ext_fits_in_32,rule_inst_3852,rule_inst_3853]
  have legacy : ∃ trace,(applyTerm p (Backend.sem ctx) cfg (n+60) 27 561
      [.ty (.int w),.reg check,.reg dividend,.reg divisor]).run (st.base,tr) =
      .ok (some (.reg dividend),overflowBase st.base w check divisor,trace) := by
    cases hp
    refine Exists.intro ?trace ?proof
    case proof =>
      isel_eval [*,overflowBase,rule_inst_3861,ctor_writable_zero_reg,ctor_u8_into_uimm5_1,ctor_nzcv_0,ctor_cond_br_cond,ctor_u8_into_imm12_1]
      all_goals rfl
  obtain ⟨trace,legacy⟩ := legacy
  exact ⟨trace,stock_div_pure_helper hp ctx hc (by decide) legacy⟩
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem sem_mkData (ctx : Ctx) (t k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData t k vs = .data t k vs := rfl
private theorem sem_int (ctx : Ctx) (ty : Nat) (i : Int) :
    (Stock.sem ctx).int ty i = .int (normInt ty i) := rfl
/-- Actual signed-minimum check helpers shift8/16-bit operands into a32-bit
check register, and pass32/64-bit operands through; full scheduling is retained. -/
theorem stock_div_intmin_helper {p : Program} (hp : Data p) (ctx : Ctx)
    {cfg : Config} (hc : cfg.checkOverlap = false) {w : Nat}
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) :
    ∃ trace,(applyTerm p (Stock.sem ctx) cfg (n+60) 27 562 [.ty (.int w),.reg r]).run (st,tr) =
      .ok (some (.reg (if w ≤ 16 then (st.base.fresh .int).1 else r)),
        (if w ≤ 16 then {st with base := ((st.base.fresh .int).2.emit
          (.aluRRImmShift .lsl .size32 (st.base.fresh .int).1 r (32-w)))} else st),trace) := by
  have shift := fun q trace fuel => ScalarShift.stock_shift_imm_helper hp ctx hc
    (w := w) (k := 18) (op := .lsl) (show w ≤ 64 by omega) rfl q trace fuel r (32-w)
  have immediate : ∀ (q : State) (k : Nat),(k < 64) → Stock.externCtor ctx T.imm_shift_from_u8 [.int k] q =
      .ok (.op (.immShift k),q) := by
    intro q k bound
    rw [stock_ctor_baseOnly ctx T.imm_shift_from_u8 _ q (by decide),ctor_imm_shift_from_u8' ctx q.base k bound]
  have immediate24 : ∀ q,Stock.externCtor ctx T.imm_shift_from_u8 [.int 24] q =
      .ok (.op (.immShift 24),q) := fun q => immediate q 24 (by decide)
  have immediate16 : ∀ q,Stock.externCtor ctx T.imm_shift_from_u8 [.int 16] q =
      .ok (.op (.immShift 16),q) := fun q => immediate q 16 (by decide)
  have ne16 : (V.ty (.int 16) == V.ty (.int 8)) = false := rfl
  cases hp
  rcases width with rfl | rfl | rfl | rfl
  · refine ⟨(((tr.push rule_inst_1599.id).push rule_inst_1592.id).push rule_inst_2537.id).push rule_inst_3888.id,?_⟩
    isel_eval [*,rule_inst_3888,rule_inst_3892,rule_inst_1599,rule_inst_1600,
      sem_ctor,sem_extract,sem_eq,sem_prim,sem_mkData,sem_int,ext_fits_in_16',CTy.bits]
    all_goals rfl
  · refine ⟨(((tr.push rule_inst_1600.id).push rule_inst_1592.id).push rule_inst_2537.id).push rule_inst_3888.id,?_⟩
    isel_eval [*,rule_inst_3888,rule_inst_3892,rule_inst_1599,rule_inst_1600,
      sem_ctor,sem_extract,sem_eq,sem_prim,sem_mkData,sem_int,ext_fits_in_16',CTy.bits]
    all_goals rfl
  · refine ⟨tr.push rule_inst_3892.id,?_⟩
    isel_eval [*,rule_inst_3888,rule_inst_3892,sem_ctor,sem_extract,sem_eq,sem_prim,sem_mkData,ext_fits_in_16',CTy.bits]
  · refine ⟨tr.push rule_inst_3892.id,?_⟩
    isel_eval [*,rule_inst_3888,rule_inst_3892,sem_ctor,sem_extract,sem_eq,sem_prim,sem_mkData,ext_fits_in_16',CTy.bits]
end Backend.Stock.Proof.ScalarDiv

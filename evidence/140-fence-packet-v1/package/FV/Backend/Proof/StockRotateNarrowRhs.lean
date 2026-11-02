import FV.Backend.Proof.IselFamAluBRotTerms
import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.StockRotatePure
namespace Backend.Stock.Proof.ScalarRotate
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : LState) :
    (Backend.sem ctx).ctor t vs st = Backend.externCtor ctx t vs st := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Backend.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem sem_mkData (ctx : Ctx) (t k : Nat) (vs : List V) :
    (Backend.sem ctx).mkData t k vs = .data t k vs := rfl
private theorem sub_run {p : Program} (hp : Data p) (ctx : Ctx) (st : LState)
    (tr : Array RuleId) (n : Nat) (a b : Reg) :
    (applyTerm p (Backend.sem ctx) {} (n+30) 27 437 [.ty (.int 32),.reg a,.reg b]).run (st,tr) =
      .ok (some (.reg (st.fresh .int).1),
        ( (st.fresh .int).2.emit (.aluRRR .sub .size32 (st.fresh .int).1 a b)),
        ((tr.push rule_inst_1592.id).push rule_inst_2545.id).push rule_inst_3138.id) := by
  have inner := fun q trace fuel => alu_rrr_run hp ctx (cfg := {}) rfl (w := 32) q trace fuel
    (fun base rules gas => operand_size_32 hp ctx (cfg := {}) rfl base rules gas (by decide))
    (fun base rd rn rm => emit_aluRRR ctx base (k := 1) (op := .sub) rfl (sz := .size32) rfl rd rn rm) a b
  cases hp
  isel_eval [*,rule_inst_3138,sem_mkData]
  all_goals rfl
private theorem lsr_run {p : Program} (hp : Data p) (ctx : Ctx) (st : LState)
    (tr : Array RuleId) (n : Nat) (a b : Reg) :
    (applyTerm p (Backend.sem ctx) {} (n+30) 27 488 [.ty (.int 32),.reg a,.reg b]).run (st,tr) =
      .ok (some (.reg (st.fresh .int).1),
        ( (st.fresh .int).2.emit (.aluRRR .lsr .size32 (st.fresh .int).1 a b)),
        ((tr.push rule_inst_1592.id).push rule_inst_2545.id).push rule_inst_3371.id) := by
  have inner := fun q trace fuel => alu_rrr_run hp ctx (cfg := {}) rfl (w := 32) q trace fuel
    (fun base rules gas => operand_size_32 hp ctx (cfg := {}) rfl base rules gas (by decide))
    (fun base rd rn rm => emit_aluRRR ctx base (k := 16) (op := .lsr) rfl (sz := .size32) rfl rd rn rm) a b
  cases hp
  isel_eval [*,rule_inst_3371,sem_mkData]
  all_goals rfl
private theorem lsl_run {p : Program} (hp : Data p) (ctx : Ctx) (st : LState)
    (tr : Array RuleId) (n : Nat) (a b : Reg) :
    (applyTerm p (Backend.sem ctx) {} (n+30) 27 490 [.ty (.int 32),.reg a,.reg b]).run (st,tr) =
      .ok (some (.reg (st.fresh .int).1),
        ( (st.fresh .int).2.emit (.aluRRR .lsl .size32 (st.fresh .int).1 a b)),
        ((tr.push rule_inst_1592.id).push rule_inst_2545.id).push rule_inst_3380.id) := by
  have inner := fun q trace fuel => alu_rrr_run hp ctx (cfg := {}) rfl (w := 32) q trace fuel
    (fun base rules gas => operand_size_32 hp ctx (cfg := {}) rfl base rules gas (by decide))
    (fun base rd rn rm => emit_aluRRR ctx base (k := 18) (op := .lsl) rfl (sz := .size32) rfl rd rn rm) a b
  cases hp
  isel_eval [*,rule_inst_3380,sem_mkData]
  all_goals rfl
private theorem orr_run {p : Program} (hp : Data p) (ctx : Ctx) (st : LState)
    (tr : Array RuleId) (n : Nat) (a b : Reg) :
    (applyTerm p (Backend.sem ctx) {} (n+30) 27 497 [.ty (.int 32),.reg a,.reg b]).run (st,tr) =
      .ok (some (.reg (st.fresh .int).1),
        ( (st.fresh .int).2.emit (.aluRRR .orr .size32 (st.fresh .int).1 a b)),
        ((tr.push rule_inst_1592.id).push rule_inst_2545.id).push rule_inst_3412.id) := by
  have inner := fun q trace fuel => alu_rrr_run hp ctx (cfg := {}) rfl (w := 32) q trace fuel
    (fun base rules gas => operand_size_32 hp ctx (cfg := {}) rfl base rules gas (by decide))
    (fun base rd rn rm => emit_aluRRR ctx base (k := 2) (op := .orr) rfl (sz := .size32) rfl rd rn rm) a b
  cases hp
  isel_eval [*,rule_inst_3412,sem_mkData]
  all_goals rfl
private theorem lsrImm_run {p : Program} (hp : Data p) (ctx : Ctx) (st : LState)
    (tr : Array RuleId) (n : Nat) (a : Reg) (amount : Nat) :
    (applyTerm p (Backend.sem ctx) {} (n+30) 27 489 [.ty (.int 32),.reg a,.op (.immShift amount)]).run (st,tr) =
      .ok (some (.reg (st.fresh .int).1),
        ( (st.fresh .int).2.emit (.aluRRImmShift .lsr .size32 (st.fresh .int).1 a amount)),
        ((tr.push rule_inst_1592.id).push rule_inst_2537.id).push rule_inst_3375.id) := by
  have inner := fun q trace fuel => alu_rr_imm_shift_run hp ctx (cfg := {}) rfl (w := 32) q trace fuel
    (fun base rules gas => operand_size_32 hp ctx (cfg := {}) rfl base rules gas (by decide))
    (k := 16) (op := .lsr) rfl (sz := .size32) rfl a amount
  cases hp
  isel_eval [*,rule_inst_3375,sem_mkData]
  all_goals rfl
private theorem lslImm_run {p : Program} (hp : Data p) (ctx : Ctx) (st : LState)
    (tr : Array RuleId) (n : Nat) (a : Reg) (amount : Nat) :
    (applyTerm p (Backend.sem ctx) {} (n+30) 27 491 [.ty (.int 32),.reg a,.op (.immShift amount)]).run (st,tr) =
      .ok (some (.reg (st.fresh .int).1),
        ( (st.fresh .int).2.emit (.aluRRImmShift .lsl .size32 (st.fresh .int).1 a amount)),
        ((tr.push rule_inst_1592.id).push rule_inst_2537.id).push rule_inst_3384.id) := by
  have inner := fun q trace fuel => alu_rr_imm_shift_run hp ctx (cfg := {}) rfl (w := 32) q trace fuel
    (fun base rules gas => operand_size_32 hp ctx (cfg := {}) rfl base rules gas (by decide))
    (k := 18) (op := .lsl) rfl (sz := .size32) rfl a amount
  cases hp
  isel_eval [*,rule_inst_3384,sem_mkData]
  all_goals rfl
private theorem and_run {p : Program} (hp : Data p) (ctx : Ctx) (st : LState)
    (tr : Array RuleId) (n : Nat) (a : Reg) (imm : ImmLogic) :
    (applyTerm p (Backend.sem ctx) {} (n+30) 27 502 [.ty (.int 32),.reg a,.op (.immLogic imm)]).run (st,tr) =
      .ok (some (.reg (st.fresh .int).1),
        ( (st.fresh .int).2.emit (.aluRRImmLogic .and .size32 (st.fresh .int).1 a imm)),
        ((tr.push rule_inst_1592.id).push rule_inst_2529.id).push rule_inst_3431.id) := by
  have inner := fun q trace fuel => alu_rr_imm_logic_run_fb hp ctx (cfg := {}) rfl (w := 32) q trace fuel
    (fun base rules gas => operand_size_32 hp ctx (cfg := {}) rfl base rules gas (by decide))
    (k := 4) (op := .and) rfl (sz := .size32) rfl a imm
  cases hp
  isel_eval [*,rule_inst_3431,sem_mkData]
  all_goals rfl
private theorem subImm_run {p : Program} (hp : Data p) (ctx : Ctx) (st : LState)
    (tr : Array RuleId) (n : Nat) (a : Reg) (imm : Imm12) :
    (applyTerm p (Backend.sem ctx) {} (n+30) 27 438 [.ty (.int 32),.reg a,.op (.imm12 imm)]).run (st,tr) =
      .ok (some (.reg (st.fresh .int).1),
        ( (st.fresh .int).2.emit (.aluRRImm12 .sub .size32 (st.fresh .int).1 a imm)),
        ((tr.push rule_inst_1592.id).push rule_inst_2648.id).push rule_inst_3142.id) := by
  have inner := fun q trace fuel => alu_rr_imm12_run_fb hp ctx (cfg := {}) rfl (w := 32) q trace fuel
    (fun base rules gas => operand_size_32 hp ctx (cfg := {}) rfl base rules gas (by decide))
    (k := 1) (op := .sub) rfl (sz := .size32) rfl a imm
  cases hp
  isel_eval [*,rule_inst_3142,sem_mkData]
  all_goals rfl
private theorem zero_reg (ctx : Ctx) (st : LState) :
    Backend.externCtor ctx T.zero_reg [] st = .ok (.reg .xzr,st) := by
  all_goals rfl
private theorem ty_bits (ctx : Ctx) (st : LState) (w : Nat) :
    Backend.externCtor ctx T.ty_bits [.ty (.int w)] st = .ok (.int w,st) := by
  all_goals rfl
private theorem mask (ctx : Ctx) (st : LState) {w : Nat} (width : w = 8 ∨ w = 16) :
    Backend.externCtor ctx T.rotr_mask [.ty (.int w)] st = .ok (.op (.immLogic ⟨w-1,.size32⟩),st) := by
  rcases width with rfl | rfl <;> rfl
private theorem as_imm (ctx : Ctx) (st : LState) {w : Nat} (width : w = 8 ∨ w = 16) :
    Backend.externCtor ctx T.u8_into_imm12 [.int w] st = .ok (.op (.imm12 ⟨w,false⟩),st) := by
  rcases width with rfl | rfl <;> rfl
private theorem opposite (ctx : Ctx) (st : LState) {w amount : Nat}
    (width : w = 8 ∨ w = 16) (count : amount < w) :
    Backend.externCtor ctx T.rotr_opposite_amount [.ty (.int w),.op (.immShift amount)] st =
      .ok (.op (.immShift (w-amount)),st) := by
  have iw : IW w := by rcases width with rfl | rfl <;> simp [IW]
  have masked : Nat.land amount (w-1) = amount := by rw [land_mask_mod iw,Nat.mod_eq_of_lt count]
  have fits : w-amount < 64 := by rcases width with h | h <;> omega
  apply (ctor_rotr_opposite_iff ctx st w amount _ st).mpr
  exact ⟨by simpa only [masked] using fits,by rw [masked],rfl⟩
def rotateNarrowRegBase (w : Nat) (st : LState) (x a : Reg) : LState :=
  let s0 := (st.fresh .int).2.emit (.aluRRImmLogic .and .size32 (st.fresh .int).1 a ⟨w-1,.size32⟩)
  let s1 := (s0.fresh .int).2.emit (.aluRRImm12 .sub .size32 (s0.fresh .int).1 (.vreg st.nextVreg .int) ⟨w,false⟩)
  let s2 := (s1.fresh .int).2.emit (.aluRRR .sub .size32 (s1.fresh .int).1 .xzr (.vreg (st.nextVreg+1) .int))
  let s3 := (s2.fresh .int).2.emit (.aluRRR .lsr .size32 (s2.fresh .int).1 x (.vreg st.nextVreg .int))
  let s4 := (s3.fresh .int).2.emit (.aluRRR .lsl .size32 (s3.fresh .int).1 x (.vreg (st.nextVreg+2) .int))
  (s4.fresh .int).2.emit (.aluRRR .orr .size32 (s4.fresh .int).1 (.vreg (st.nextVreg+4) .int) (.vreg (st.nextVreg+3) .int))
def rotateNarrowImmBase (w : Nat) (st : LState) (x : Reg) (amount : Nat) : LState :=
  let s0 := (st.fresh .int).2.emit (.aluRRImmShift .lsr .size32 (st.fresh .int).1 x amount)
  let s1 := (s0.fresh .int).2.emit (.aluRRImmShift .lsl .size32 (s0.fresh .int).1 x (w-amount))
  (s1.fresh .int).2.emit (.aluRRR .orr .size32 (s1.fresh .int).1 (.vreg (st.nextVreg+1) .int) (.vreg st.nextVreg .int))
def rotateNarrowRegTrace (tr : Array RuleId) : Array RuleId :=
  (((((((((((((((((((tr).push rule_inst_1592.id).push rule_inst_2529.id).push rule_inst_3431.id).push rule_inst_1592.id).push rule_inst_2648.id).push rule_inst_3142.id).push rule_inst_1592.id).push rule_inst_2545.id).push rule_inst_3138.id).push rule_inst_1592.id).push rule_inst_2545.id).push rule_inst_3371.id).push rule_inst_1592.id).push rule_inst_2545.id).push rule_inst_3380.id).push rule_inst_1592.id).push rule_inst_2545.id).push rule_inst_3412.id).push rule_lower_1879.id
def rotateNarrowImmTrace (tr : Array RuleId) : Array RuleId :=
  ((((((((((tr).push rule_inst_1592.id).push rule_inst_2537.id).push rule_inst_3375.id).push rule_inst_1592.id).push rule_inst_2537.id).push rule_inst_3384.id).push rule_inst_1592.id).push rule_inst_2545.id).push rule_inst_3412.id).push rule_lower_1902.id
/-- Actual narrow register helper emits all six instructions and preserves
all Stock scheduling fields. -/
private theorem legacy_rotate_narrow_rr {p : Program} (hp : Data p) (ctx : Ctx)
    {w : Nat} (width : w = 8 ∨ w = 16) (st : LState) (tr : Array RuleId) (n : Nat) (x a : Reg) :
    (applyTerm p (Backend.sem ctx) {} (n+60) 27 710 [.ty (.int w),.reg x,.reg a]).run (st,tr) =
      .ok (some (.reg (.vreg (st.nextVreg+5) .int)),
        ( rotateNarrowRegBase w st x a),rotateNarrowRegTrace tr) := by
  have and := fun q trace fuel r imm => and_run hp ctx q trace fuel r imm
  have subImm := fun q trace fuel r imm => subImm_run hp ctx q trace fuel r imm
  have sub := fun q trace fuel r => sub_run hp ctx q trace fuel .xzr r
  have lsr := fun q trace fuel r amt => lsr_run hp ctx q trace fuel r amt
  have lsl := fun q trace fuel r amt => lsl_run hp ctx q trace fuel r amt
  have orr := fun q trace fuel l r => orr_run hp ctx q trace fuel l r
  have mask' := fun q => mask ctx q width
  have asImm := fun q => as_imm ctx q width
  have bits := fun q => ty_bits ctx q w
  have zero := fun q => zero_reg ctx q
  have term710 := hp.t710
  have term711 := hp.t711
  have term327 := hp.t327
  have term87 := hp.t87
  have term352 := hp.t352
  have rules := hp.r710
  rcases width with rfl | rfl
  all_goals
    isel_eval [*,rule_lower_1879,sem_ctor,sem_prim]
    simp only [rotateNarrowRegTrace]
    rfl
/-- Actual narrow immediate helper emits its two shifts and OR without
requesting the looked-through count, retaining the complete Stock state. -/
private theorem legacy_rotate_narrow_imm {p : Program} (hp : Data p) (ctx : Ctx)
    {w amount : Nat} (width : w = 8 ∨ w = 16) (count : amount < w)
    (st : LState) (tr : Array RuleId) (n : Nat) (x : Reg) :
    (applyTerm p (Backend.sem ctx) {} (n+60) 27 712 [.ty (.int w),.reg x,.op (.immShift amount)]).run (st,tr) =
      .ok (some (.reg (.vreg (st.nextVreg+2) .int)),
        ( rotateNarrowImmBase w st x amount),rotateNarrowImmTrace tr) := by
  have lsr := fun q trace fuel r amt => lsrImm_run hp ctx q trace fuel r amt
  have lsl := fun q trace fuel r amt => lslImm_run hp ctx q trace fuel r amt
  have orr := fun q trace fuel l r => orr_run hp ctx q trace fuel l r
  have opp := fun q => opposite ctx q width count
  have term712 := hp.t712
  have term713 := hp.t713
  have rules := hp.r712
  isel_eval [*,rule_lower_1902,sem_ctor,sem_prim]
  simp only [rotateNarrowImmTrace]
  rfl
/-- Actual narrow register helper emits all six instructions and preserves
all Stock scheduling fields. -/
theorem stock_rotate_narrow_rr_helper {p : Program} (hp : Data p) (ctx : Ctx)
    {w : Nat} (width : w = 8 ∨ w = 16) (st : State) (tr : Array RuleId) (n : Nat) (x a : Reg) :
    ∃ trace,(applyTerm p (Stock.sem ctx) {} (n+60) 27 710 [.ty (.int w),.reg x,.reg a]).run (st,tr) =
      .ok (some (.reg (.vreg (st.base.nextVreg+5) .int)),
        {st with base := rotateNarrowRegBase w st.base x a},trace) := by
  exact ⟨rotateNarrowRegTrace tr,stock_rotate_pure_helper hp ctx (cfg := {}) rfl (by decide)
    (legacy_rotate_narrow_rr hp ctx width st.base tr n x a)⟩
/-- Actual narrow immediate helper emits its two shifts and OR without
requesting the looked-through count, retaining the complete Stock state. -/
theorem stock_rotate_narrow_imm_helper {p : Program} (hp : Data p) (ctx : Ctx)
    {w amount : Nat} (width : w = 8 ∨ w = 16) (count : amount < w)
    (st : State) (tr : Array RuleId) (n : Nat) (x : Reg) :
    ∃ trace,(applyTerm p (Stock.sem ctx) {} (n+60) 27 712 [.ty (.int w),.reg x,.op (.immShift amount)]).run (st,tr) =
      .ok (some (.reg (.vreg (st.base.nextVreg+2) .int)),
        {st with base := rotateNarrowImmBase w st.base x amount},trace) := by
  exact ⟨rotateNarrowImmTrace tr,stock_rotate_pure_helper hp ctx (cfg := {}) rfl (by decide)
    (legacy_rotate_narrow_imm hp ctx width count st.base tr n x)⟩
theorem stock_rotate_narrow_imm_run {p : Program} (hp : Data p) (ctx : Ctx)
    {w amount : Nat} (width : w = 8 ∨ w = 16) (count : amount < w)
    (st : State) (tr : Array RuleId) (n : Nat) (x : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+60) 27 712 [.ty (.int w),.reg x,.op (.immShift amount)]).run (st,tr) =
      .ok (some (.reg (.vreg (st.base.nextVreg+2) .int)),
        {st with base := rotateNarrowImmBase w st.base x amount},rotateNarrowImmTrace tr) := by
  exact stock_rotate_pure_helper hp ctx (cfg := {}) rfl (by decide)
    (legacy_rotate_narrow_imm hp ctx width count st.base tr n x)
/-- Exact trace variant of the register helper; the existential variant is
retained for existing callers. -/
theorem stock_rotate_narrow_rr_run {p : Program} (hp : Data p) (ctx : Ctx)
    {w : Nat} (width : w = 8 ∨ w = 16) (st : State) (tr : Array RuleId) (n : Nat) (x a : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+60) 27 710 [.ty (.int w),.reg x,.reg a]).run (st,tr) =
      .ok (some (.reg (.vreg (st.base.nextVreg+5) .int)),
        {st with base := rotateNarrowRegBase w st.base x a},rotateNarrowRegTrace tr) := by
  exact stock_rotate_pure_helper hp ctx (cfg := {}) rfl (by decide)
    (legacy_rotate_narrow_rr hp ctx width st.base tr n x a)
end Backend.Stock.Proof.ScalarRotate

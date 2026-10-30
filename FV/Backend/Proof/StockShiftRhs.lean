import FV.Backend.Proof.StockAlu
import FV.Backend.Proof.IselTermsShift
import FV.Backend.Proof.StockLogicalForms
import FV.Backend.Proof.StockShiftHelper
namespace Backend.Stock.Proof.ScalarShift
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_prim_type (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem sem_mkData (ctx : Ctx) (t k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData t k vs = .data t k vs := rfl
section IntConstants
attribute [local semireducible] Isle.Aarch64.program
private theorem zero (ctx : Ctx) : (Stock.sem ctx).int 6 0 = .int 0 := rfl
end IntConstants
private theorem get_reg (ctx : Ctx) (st : State) (r : Reg) :
    Stock.externCtor ctx T.value_regs_get [.regs [r],.int 0] st = .ok (.reg r,st) := by
  rw [stock_ctor_baseOnly ctx T.value_regs_get _ st (by decide)]
  rfl
private theorem and_helper {p : Program} (hp : Data p) (ctx : Ctx) (st : State)
    (tr : Array RuleId) (n : Nat) (r : Reg) (imm : ImmLogic) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 502 [.ty (.int 32),.reg r,.op (.immLogic imm)]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRImmLogic .and .size32 (st.base.fresh .int).1 r imm)},
        ((tr.push rule_inst_1592.id).push rule_inst_2529.id).push rule_inst_3431.id) := by
  have inner := fun q trace fuel => LogicalForms.stock_logical_imm_helper hp ctx (cfg := {}) rfl
    (w := 32) (k := 4) (op := .and) (by decide) rfl q trace fuel r imm
  cases hp
  isel_eval [*,rule_inst_3431,sem_mkData]
  rfl

/-- Immediate-count helper RHSs emit one original shift template without
requesting or materializing the looked-through count value. -/
theorem stock_shift_imm_rhs {p : Program} (hp : Data p) (ctx : Ctx)
    {w k : Nat} {op : ALUOp} (width : w ≤ 64) (tag : ALUOp.ofIdx? k = some op)
    (st : State) (tr : Array RuleId) (n : Nat) (a : Reg) (c : Int) (amount : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+30) rule_lower_1631.rhs
      (env5 (.data 59 k []) (.ty (.int w)) (.reg a) (.int c) (.op (.immShift amount)))).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRImmShift op (szOf w) (st.base.fresh .int).1 a amount)},trace) := by
  have helper := fun q trace fuel => stock_shift_imm_helper hp ctx (cfg := {}) rfl width tag q trace fuel a amount
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    isel_eval [*,rule_lower_1631]
    rfl

/-- The matcher reserves both local slots before evaluating the masked RHS. -/
abbrev shiftMaskEnv (k w : Nat) (a : Reg) (y : Nat) : Isle.Interp.Env V :=
  ((((Array.replicate 6 none).setIfInBounds 0 (some (.data 59 k []))).setIfInBounds 1
    (some (.ty (.int w)))).setIfInBounds 2 (some (.reg a))).setIfInBounds 3 (some (.value y))

def shiftWidth (wide : Bool) : Nat := if wide then 64 else 32
def shiftRegisterRule (wide : Bool) : Rule := if wide then rule_lower_1623 else rule_lower_1622

/-- Both32/64-bit count helpers derive their marked demand from a guarded
mapped request and emit precisely one shift into the fresh result. -/
theorem stock_shift_rrr_rhs {p : Program} (hp : Data p) (ctx : Ctx) (wide : Bool)
    {k y : Nat} {op : ALUOp} {ry : Reg} (tag : ALUOp.ofIdx? k = some op)
    (mapped : ctx.valueReg? y = some ry) (st : State) (safe : DemandAllowed ctx st y)
    (tr : Array RuleId) (n : Nat) (a : Reg) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+40) (shiftRegisterRule wide).rhs
      (env3 (.data 59 k []) (.reg a) (.value y))).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st.mark y with base := (st.base.fresh .int).2.emit (.aluRRR op (szOf (shiftWidth wide)) (st.base.fresh .int).1 a ry)},trace) := by
  have request := stock_put_in_regs ctx st y ry mapped safe
  have get := fun q => get_reg ctx q ry
  have helper32 := fun q trace fuel => stock_alu_rrr_helper hp ctx (cfg := {}) rfl
    (w := 32) (by decide) tag q trace fuel a ry
  have helper64 := fun q trace fuel => stock_alu_rrr_helper hp ctx (cfg := {}) rfl
    (w := 64) (by decide) tag q trace fuel a ry
  cases hp
  cases wide
  · refine Exists.intro ?trace32 ?proof32
    case proof32 =>
      isel_eval [*,shiftRegisterRule,shiftWidth,rule_lower_1622,sem_ctor,sem_prim_type,zero]
      rfl
  · refine Exists.intro ?trace64 ?proof64
    case proof64 =>
      isel_eval [*,shiftRegisterRule,shiftWidth,rule_lower_1623,sem_ctor,sem_prim_type,zero]
      rfl

private theorem shift_mask_run (ctx : Ctx) (q : State) {w : Nat} (width : w = 8 ∨ w = 16) :
    Stock.externCtor ctx T.shift_mask [.ty (.int w)] q = .ok (.op (.immLogic ⟨w-1,.size32⟩),q) := by
  rw [stock_ctor_baseOnly ctx T.shift_mask _ q (by decide)]
  rcases width with rfl | rfl
  · rw [ctor_shift_mask_i8 ctx q.base]
  · rw [ctor_shift_mask_i16 ctx q.base]

private theorem masked_rhs_generic {p : Program} (hp : Data p) (semantics : Isle.Sem V State)
    {w k y : Nat} {op : ALUOp} {ry : Reg} (st : State) (tr : Array RuleId) (n : Nat) (a : Reg)
    (request : semantics.ctor T.put_in_regs [.value y] st = .ok (.regs [ry],st.mark y))
    (get : ∀ q,semantics.ctor T.value_regs_get [.regs [ry],.int 0] q = .ok (.reg ry,q))
    (mask : ∀ q,semantics.ctor T.shift_mask [.ty (.int w)] q = .ok (.op (.immLogic ⟨w-1,.size32⟩),q))
    (prim : semantics.prim 14 "I32" = some (.ty (.int 32)))
    (zero : semantics.int 6 0 = .int 0)
    (andRun : ∀ q trace fuel,
      (applyTerm p semantics {} (fuel+30) 27 502 [.ty (.int 32),.reg ry,.op (.immLogic ⟨w-1,.size32⟩)]).run (q,trace) =
        .ok (some (.reg (q.base.fresh .int).1),
          {q with base := (q.base.fresh .int).2.emit (.aluRRImmLogic .and .size32 (q.base.fresh .int).1 ry ⟨w-1,.size32⟩)},
          ((trace.push rule_inst_1592.id).push rule_inst_2529.id).push rule_inst_3431.id))
    (shiftRun : ∀ q trace fuel,
      (applyTerm p semantics {} (fuel+20) 27 362 [.data 59 k [],.ty (.int 32),.reg a,.reg (st.base.fresh .int).1]).run (q,trace) =
        .ok (some (.reg (q.base.fresh .int).1),
          {q with base := (q.base.fresh .int).2.emit (.aluRRR op (szOf 32) (q.base.fresh .int).1 a (st.base.fresh .int).1)},
          (trace.push rule_inst_1592.id).push rule_inst_2545.id)) :
    ∃ trace,(evalExpr p semantics {} (n+60) rule_lower_1612.rhs (shiftMaskEnv k w a y)).run (st,tr) =
      .ok (some (.reg (.vreg (st.base.nextVreg+1) .int)),
        {st.mark y with base := (((st.base.fresh .int).2.emit (.aluRRImmLogic .and .size32 (st.base.fresh .int).1 ry ⟨w-1,.size32⟩)).fresh .int).2.emit (.aluRRR op .size32 (.vreg (st.base.nextVreg+1) .int) a (st.base.fresh .int).1)},trace) := by
  have markedFresh : (st.mark y).base.fresh .int = st.base.fresh .int := rfl
  refine Exists.intro ?trace ?proof
  case proof =>
    isel_eval [hp.t183,hp.t185,hp.t704,request,get,mask,andRun,shiftRun,markedFresh,prim,zero,rule_lower_1612,shiftMaskEnv]
    simp only [State.mark,LState.fresh,LState.emit,szOf,Nat.le_refl,ite_true]
    rfl

/-- Narrow count helpers mark the original amount once, mask it in a fresh
scratch register and emit the shift, accounting for the entire Stock state. -/
theorem stock_shift_mask_rhs {p : Program} (hp : Data p) (ctx : Ctx)
    {w k y : Nat} {op : ALUOp} {ry : Reg} (width : w = 8 ∨ w = 16)
    (tag : ALUOp.ofIdx? k = some op) (mapped : ctx.valueReg? y = some ry)
    (st : State) (safe : DemandAllowed ctx st y) (tr : Array RuleId) (n : Nat) (a : Reg) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+60) rule_lower_1612.rhs
      (shiftMaskEnv k w a y)).run (st,tr) =
      .ok (some (.reg (.vreg (st.base.nextVreg+1) .int)),
        {st.mark y with base := (((st.base.fresh .int).2.emit (.aluRRImmLogic .and .size32 (st.base.fresh .int).1 ry ⟨w-1,.size32⟩)).fresh .int).2.emit (.aluRRR op .size32 (.vreg (st.base.nextVreg+1) .int) a (st.base.fresh .int).1)},trace) := by
  apply masked_rhs_generic hp (Stock.sem ctx) st tr n a
  · simpa only [sem_ctor] using stock_put_in_regs ctx st y ry mapped safe
  · intro q; simpa only [sem_ctor] using get_reg ctx q ry
  · intro q; simpa only [sem_ctor] using shift_mask_run ctx q width
  · rw [sem_prim_type]; rfl
  · exact zero ctx
  · intro q trace fuel; exact and_helper hp ctx q trace fuel ry ⟨w-1,.size32⟩
  · intro q trace fuel
    simpa only [Nat.le_refl,ite_true] using stock_alu_rrr_helper hp ctx (cfg := {}) rfl
      (w := 32) (by decide) tag q trace fuel a (st.base.fresh .int).1
end Backend.Stock.Proof.ScalarShift

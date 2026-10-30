import FV.Backend.Proof.StockRequestSuccess
import FV.Backend.Proof.StockLogicalForms
import FV.Backend.Proof.IselTermsALUAExtr

namespace Backend.Stock.Proof.LogicalExtr
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (t k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData t k vs = .data t k vs := rfl
private theorem extr_shift_32 (ctx : Ctx) (st : State) (amount : Nat) :
    Stock.externCtor ctx T.a64_extr_imm [.ty (.int 32),.op (.immShift amount)] st =
      .ok (.op (.shiftOpAndAmt ⟨.lsl,amount⟩),st) := by
  rw [stock_ctor_baseOnly ctx T.a64_extr_imm _ st (by decide)]
  rfl
private theorem extr_shift_64 (ctx : Ctx) (st : State) (amount : Nat) :
    Stock.externCtor ctx T.a64_extr_imm [.ty (.int 64),.op (.immShift amount)] st =
      .ok (.op (.shiftOpAndAmt ⟨.lsr,amount⟩),st) := by
  rw [stock_ctor_baseOnly ctx T.a64_extr_imm _ st (by decide)]
  rfl
private theorem immediate_shift (ctx : Ctx) (st : State) {amount : Int} (fits : amount < 64) :
    Stock.externCtor ctx T.imm_shift_from_u8 [.int amount] st =
      .ok (.op (.immShift amount.toNat),st) := by
  rw [stock_ctor_baseOnly ctx T.imm_shift_from_u8 _ st (by decide),
    ctor_imm_shift_from_u8 ctx st.base fits]
private theorem output_run {p : Program} (hp : Data p) (ctx : Ctx) (st : State)
    (tr : Array RuleId) (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+10) 25 172 [.reg r]).run (st,tr) =
      .ok (some (.regsVec [[r]]),st,tr.push rule_prelude_lower_105.id) := by
  have value : ∀ q,Stock.externCtor ctx T.value_reg [.reg r] q = .ok (.regs [r],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.value_reg _ q (by decide)]; rfl
  have output : ∀ q,Stock.externCtor ctx T.output [.regs [r]] q = .ok (.regsVec [[r]],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.output _ q (by decide)]; rfl
  cases hp
  isel_eval [*,rule_prelude_lower_105,sem_ctor]

def shiftFor (w amount : Nat) : ShiftOpAndAmt :=
  if w ≤ 32 then ⟨.lsl,amount⟩ else ⟨.lsr,amount⟩

/-- The real two-register EXTR helper preserves all Stock scheduling fields. -/
theorem helper_run {p : Program} (hp : Data p) (ctx : Ctx) {w : Nat}
    (width : w = 32 ∨ w = 64) (st : State) (tr : Array RuleId) (n : Nat)
    (rx ry : Reg) (amount : Nat) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 515
      [.ty (.int w),.reg rx,.reg ry,.op (.immShift amount)]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRRShift .extr (szOf w) (st.base.fresh .int).1 rx ry (shiftFor w amount))},
        ((tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2656.id).push
          rule_inst_3487.id) := by
  have small : w ≤ 64 := by rcases width with rfl | rfl <;> decide
  have inner := fun q trace fuel sh => LogicalForms.stock_logical_shift_helper hp ctx (cfg := {})
    rfl small (k := 15) (op := .extr) rfl q trace fuel rx ry sh
  have ctor32 := fun q => extr_shift_32 ctx q amount
  have ctor64 := fun q => extr_shift_64 ctx q amount
  cases hp
  rcases width with rfl | rfl
  all_goals simp only [shiftFor,szOf,Nat.reduceLeDiff,ite_true,ite_false] at *
  all_goals isel_eval [*,rule_inst_3487,sem_mkData,sem_ctor]
  all_goals rfl

def extrRule (mirrored : Bool) : Rule := if mirrored then rule_lower_1507 else rule_lower_1501

def extrEnv (mirrored : Bool) (w x : Nat) (X : Int) (y : Nat) (Y : Int) : Isle.Interp.Env V :=
  if mirrored then env5 (.ty (.int w)) (.value y) (.int Y) (.value x) (.int X)
  else env5 (.ty (.int w)) (.value x) (.int X) (.value y) (.int Y)

/-- Both original fused-OR RHSs request only the underlying source words,
retain complete Stock scheduling state, and emit the actual EXTR instruction. -/
theorem rhs_forward {p : Program} (hp : Data p) (ctx : Ctx) (mirrored : Bool)
    {w x y : Nat} {X Y : Int} {rx ry : Reg}
    (mappedX : ctx.valueReg? x = some rx) (mappedY : ctx.valueReg? y = some ry)
    (width : w = 32 ∨ w = 64) (fits : Y < 64)
    (st : State) (safeX : DemandAllowed ctx st x) (safeY : DemandAllowed ctx st y)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+60) (extrRule mirrored).rhs
      (extrEnv mirrored w x X y Y)).run (st,tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {(st.mark x).mark y with base := (st.base.fresh .int).2.emit (.aluRRRShift .extr (szOf w) (st.base.fresh .int).1 rx ry (shiftFor w Y.toNat))},trace) := by
  have requestX := stock_put_in_reg ctx st x rx mappedX safeX
  have requestY := stock_put_in_reg ctx (st.mark x) y ry mappedY safeY
  have shift := fun q => immediate_shift ctx q fits
  have helper := fun q trace fuel => helper_run hp ctx width q trace fuel rx ry Y.toNat
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  cases hp
  cases mirrored with
  | false =>
    refine Exists.intro ?trace0 ?proof0
    case proof0 =>
      simp only [extrRule,extrEnv,Bool.false_eq_true,ite_true,ite_false]
      isel_eval [*,rule_lower_1501,sem_ctor]
      rfl
  | true =>
    refine Exists.intro ?trace1 ?proof1
    case proof1 =>
      simp only [extrRule,extrEnv,Bool.false_eq_true,ite_true,ite_false]
      isel_eval [*,rule_lower_1507,sem_ctor]
      rfl

/-- Successful actual RHS execution supplies both guarded source requests;
no caller-provided register map or scheduling certificate is needed. -/
theorem rhs_requests {p : Program} (hp : Data p) (ctx : Ctx) (mirrored : Bool)
    {w x y n : Nat} {X Y : Int} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+60) (extrRule mirrored).rhs
      (extrEnv mirrored w x X y Y)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧
      (∃ rx,ctx.valueReg? x = some rx) ∧ ∃ ry,ctx.valueReg? y = some ry := by
  cases hp
  cases mirrored
  all_goals
    isel_inv [*,extrRule,extrEnv,rule_lower_1501,rule_lower_1507,sem_ctor,stock_put_in_reg_iff] at run
    all_goals simp only [stock_put_in_reg_iff,ExtResult.ok.injEq,Prod.mk.injEq] at *
    all_goals isel_destruct <;> subst_vars
  all_goals
    exact ⟨‹DemandAllowed ctx st x›,‹DemandAllowed ctx (st.mark x) y›,
      ⟨_,‹ctx.valueReg? x = some _›⟩,⟨_,‹ctx.valueReg? y = some _›⟩⟩

/-- Actual success determines the complete output and marking/emission state.
Root match guards will supply the width and immediate facts. -/
theorem rhs_observed {p : Program} (hp : Data p) (ctx : Ctx) (mirrored : Bool)
    {w x y n : Nat} {X Y : Int} (width : w = 32 ∨ w = 64) (fits : Y < 64)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+60) (extrRule mirrored).rhs
      (extrEnv mirrored w x X y Y)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧
      ∃ rx ry,ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
        out = .regsVec [[(st.base.fresh .int).1]] ∧
        next = {(st.mark x).mark y with base := (st.base.fresh .int).2.emit (.aluRRRShift .extr
          (szOf w) (st.base.fresh .int).1 rx ry (shiftFor w Y.toNat))} := by
  obtain ⟨safeX,safeY,⟨rx,mappedX⟩,ry,mappedY⟩ := rhs_requests hp ctx mirrored run
  obtain ⟨actualTrace,forward⟩ := rhs_forward hp ctx mirrored mappedX mappedY width fits st safeX safeY tr n
  rw [forward] at run
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
  obtain ⟨outEq,stateEq,_⟩ := run
  exact ⟨safeX,safeY,rx,ry,mappedX,mappedY,outEq.symm,stateEq.symm⟩

/-- Concrete mapped words inhabit both RHS routes and supported widths; the
source match/binding and complete-function witness remain separate obligations. -/
theorem rhs_witness (mirrored : Bool) (w : Nat) (width : w = 32 ∨ w = 64) :
    ∃ trace,(evalExpr program (Stock.sem sinkCtx) {} 60 (extrRule mirrored).rhs
      (extrEnv mirrored w 0 (w-1 : Nat) 1 1)).run (sinkState,#[]) =
      .ok (some (.regsVec [[(sinkState.base.fresh .int).1]]),
        {(sinkState.mark 0).mark 1 with base := (sinkState.base.fresh .int).2.emit (.aluRRRShift .extr (szOf w) (sinkState.base.fresh .int).1 (.vreg 192 .int)
            (.vreg 193 .int) (shiftFor w 1))},trace) := by
  have safe0 := stock_put_in_reg_witness.1
  have safe1 : DemandAllowed sinkCtx sinkState 1 := by
    intro i found
    change (none : Option Nat) = some i at found
    cases found
  exact rhs_forward data_program sinkCtx mirrored (w := w) (x := 0) (y := 1)
    (X := (w-1 : Nat)) (Y := 1) rfl rfl width (by decide) sinkState safe0 safe1 #[] 0

/-- Successful concrete runs inhabit the observation theorem for both mirrors
and source-compatible positive shifts summing to the supported width. -/
theorem rhs_observed_witness (mirrored : Bool) (w : Nat) (width : w = 32 ∨ w = 64) :
    DemandAllowed sinkCtx sinkState 0 ∧ DemandAllowed sinkCtx sinkState 1 ∧
      ∃ rx ry,sinkCtx.valueReg? 0 = some rx ∧ sinkCtx.valueReg? 1 = some ry ∧
        (.regsVec [[(sinkState.base.fresh .int).1]] : V) =
          .regsVec [[(sinkState.base.fresh .int).1]] ∧
        {(sinkState.mark 0).mark 1 with base := (sinkState.base.fresh .int).2.emit (.aluRRRShift .extr (szOf w) (sinkState.base.fresh .int).1 (.vreg 192 .int)
            (.vreg 193 .int) (shiftFor w 1))} =
        {(sinkState.mark 0).mark 1 with base := (sinkState.base.fresh .int).2.emit (.aluRRRShift .extr (szOf w) (sinkState.base.fresh .int).1 rx ry
            (shiftFor w (1 : Int).toNat))} := by
  obtain ⟨trace,run⟩ := rhs_witness mirrored w width
  exact rhs_observed data_program sinkCtx mirrored width (by decide) (n := 0) run

end Backend.Stock.Proof.LogicalExtr

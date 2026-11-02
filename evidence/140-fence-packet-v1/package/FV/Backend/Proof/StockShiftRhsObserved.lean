import FV.Backend.Proof.StockShiftRequests
import FV.Backend.Proof.StockShiftRhs
namespace Backend.Stock.Proof.ScalarShift
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_prim_type (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
section IntConstants
attribute [local semireducible] Isle.Aarch64.program
private theorem zero (ctx : Ctx) : (Stock.sem ctx).int 6 0 = .int 0 := rfl
end IntConstants

/-- A successful register-count RHS supplies the actual guarded count request,
mapping, output and complete Stock state internally. -/
theorem stock_shift_rrr_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx) (wide : Bool)
    {k y n : Nat} {op : ALUOp} (tag : ALUOp.ofIdx? k = some op)
    {st next : State} {tr trace : Array RuleId} {a : Reg} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+40) (shiftRegisterRule wide).rhs
      (env3 (.data 59 k []) (.reg a) (.value y))).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st y ∧ ∃ ry,ctx.valueReg? y = some ry ∧
      out = .reg (st.base.fresh .int).1 ∧
      next = {st.mark y with base := (st.base.fresh .int).2.emit (.aluRRR op (szOf (shiftWidth wide)) (st.base.fresh .int).1 a ry)} := by
  cases call : Stock.externCtor ctx T.put_in_regs [.value y] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) (shiftRegisterRule wide).rhs
        (env3 (.data 59 k []) (.reg a) (.value y))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases wide <;> isel_eval [*,shiftRegisterRule,rule_lower_1622,rule_lower_1623,sem_ctor,sem_prim_type,zero]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) (shiftRegisterRule wide).rhs
        (env3 (.data 59 k []) (.reg a) (.value y))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases wide <;> isel_eval [*,shiftRegisterRule,rule_lower_1622,rule_lower_1623,sem_ctor,sem_prim_type,zero]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | ok pair =>
    obtain ⟨value,middle⟩ := pair
    obtain ⟨safe,ry,mapped,rfl,rfl⟩ := (stock_shift_put_in_regs_iff ctx st y value middle).mp call
    obtain ⟨trace',expected⟩ := stock_shift_rrr_rhs hp ctx wide tag mapped st safe tr n a
    have same := Except.ok.inj (run.symm.trans expected)
    exact ⟨safe,ry,mapped,Option.some.inj (congrArg Prod.fst same),congrArg (fun q => q.2.1) same⟩

/-- A successful narrow-count RHS supplies its original guarded request and
complete two-instruction allocation/emission state, rather than a caller shape
certificate. -/
theorem stock_shift_mask_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {w k y n : Nat} {op : ALUOp} (width : w = 8 ∨ w = 16)
    (tag : ALUOp.ofIdx? k = some op) {st next : State} {tr trace : Array RuleId} {a : Reg} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+60) rule_lower_1612.rhs
      (shiftMaskEnv k w a y)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st y ∧ ∃ ry,ctx.valueReg? y = some ry ∧
      out = .reg (.vreg (st.base.nextVreg+1) .int) ∧
      next = {st.mark y with base := (((st.base.fresh .int).2.emit (.aluRRImmLogic .and .size32 (st.base.fresh .int).1 ry ⟨w-1,.size32⟩)).fresh .int).2.emit (.aluRRR op .size32 (.vreg (st.base.nextVreg+1) .int) a (st.base.fresh .int).1)} := by
  cases call : Stock.externCtor ctx T.put_in_regs [.value y] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+60) rule_lower_1612.rhs
        (shiftMaskEnv k w a y)).run (st,tr) ≠ .ok (some out,next,trace) := by
      isel_eval [hp.t183,hp.t185,call,rule_lower_1612,sem_ctor,sem_prim_type,zero,shiftMaskEnv]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+60) rule_lower_1612.rhs
        (shiftMaskEnv k w a y)).run (st,tr) ≠ .ok (some out,next,trace) := by
      isel_eval [hp.t183,hp.t185,call,rule_lower_1612,sem_ctor,sem_prim_type,zero,shiftMaskEnv]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | ok pair =>
    obtain ⟨value,middle⟩ := pair
    obtain ⟨safe,ry,mapped,rfl,rfl⟩ := (stock_shift_put_in_regs_iff ctx st y value middle).mp call
    obtain ⟨trace',expected⟩ := stock_shift_mask_rhs hp ctx width tag mapped st safe tr n a
    have same := Except.ok.inj (run.symm.trans expected)
    exact ⟨safe,ry,mapped,Option.some.inj (congrArg Prod.fst same),congrArg (fun q => q.2.1) same⟩
end Backend.Stock.Proof.ScalarShift

import FV.Backend.Proof.StockLogicalObserved

namespace Backend.Stock.Proof.LogicalNot
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.LogicalSemantics
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem match_rr (p : Program) (ctx : Ctx) (cfg : Config) (n : Nat) (args : List V) (st : State) (tr : Array RuleId) :
    (matchRule p (Stock.sem ctx) cfg (n+1) rule_inst_3939 args).run (st,tr) =
      (matchRule p (Stock.sem ctx) cfg (n+1) rule_inst_3916 args).run (st,tr) := rfl
private theorem match_imm (p : Program) (ctx : Ctx) (cfg : Config) (n : Nat) (args : List V) (st : State) (tr : Array RuleId) :
    (matchRule p (Stock.sem ctx) cfg (n+1) rule_inst_3941 args).run (st,tr) =
      (matchRule p (Stock.sem ctx) cfg (n+1) rule_inst_3920 args).run (st,tr) := rfl
private theorem match_shift (p : Program) (ctx : Ctx) (cfg : Config) (n : Nat) (args : List V) (st : State) (tr : Array RuleId) :
    (matchRule p (Stock.sem ctx) cfg (n+1) rule_inst_3944 args).run (st,tr) =
      (matchRule p (Stock.sem ctx) cfg (n+1) rule_inst_3928 args).run (st,tr) := rfl

/-- Actual register NOT-helper execution reuses the identical landed RHS. -/
theorem stock_not_rrr_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {k w x y n : Nat} {op : ALUOp} (tag : ALUOp.ofIdx? k = some op) (width : w ≤ 64)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n + 40) rule_inst_3939.rhs
      (env4 (.data 59 k []) (.ty (.int w)) (.value x) (.value y))).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧ ∃ rx ry,
      ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧ out = .reg (st.base.fresh .int).1 ∧
      next = {(st.mark x).mark y with
        base := (st.base.fresh .int).2.emit (.aluRRR op (szOf w) (st.base.fresh .int).1 rx ry)} := by
  rw [show rule_inst_3939.rhs = rule_inst_3916.rhs from rfl] at run
  exact stock_logical_rrr_rhs_observed hp ctx tag width run

/-- Actual immediate NOT-helper execution reuses the identical landed RHS. -/
theorem stock_not_imm_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {k w x y n : Nat} {kk : Int} {imm : ImmLogic} {op : ALUOp}
    (tag : ALUOp.ofIdx? k = some op) (width : w ≤ 64)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n + 40) rule_inst_3941.rhs
      (logicalImmEnv false k w x y kk imm)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,
      ctx.valueReg? x = some rx ∧ out = .reg (st.base.fresh .int).1 ∧
      next = {st.mark x with
        base := (st.base.fresh .int).2.emit (.aluRRImmLogic op (szOf w) (st.base.fresh .int).1 rx imm)} := by
  rw [show rule_inst_3941.rhs = rule_inst_3920.rhs from rfl] at run
  exact stock_logical_imm_rhs_observed hp ctx false tag width (x := x) (y := y) run

/-- Actual shifted NOT-helper execution reuses the identical landed RHS. -/
theorem stock_not_shift_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {k w x y z n : Nat} {kk : Int} {sh : ShiftOpAndAmt} {op : ALUOp}
    (tag : ALUOp.ofIdx? k = some op) (width : w ≤ 64)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n + 40) rule_inst_3944.rhs
      (logicalShiftEnv false k w x y z kk sh)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st z ∧ ∃ rx rz,
      ctx.valueReg? x = some rx ∧ ctx.valueReg? z = some rz ∧
      out = .reg (st.base.fresh .int).1 ∧ next = {(st.mark x).mark z with
        base := (st.base.fresh .int).2.emit (.aluRRRShift op (szOf w) (st.base.fresh .int).1 rx rz sh)} := by
  rw [show rule_inst_3944.rhs = rule_inst_3928.rhs from rfl] at run
  exact stock_logical_shift_rhs_observed hp ctx false tag width (x := x) (y := y) run


/-- Actual NOT matching reuses the identical proved source/value receipt. -/
theorem stock_not_imm_match_receipts {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
     {k x y m : Nat} {ty : Clif.Ty} (width : ty.width ≤ 64) {u : BitVec ty.width}
    (source : fr.getAs y ty = .ok u)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m + 10) rule_inst_3941
      [.data 59 k [],.ty (.int ty.width),.value x,.value y]).run (st,tr) = .ok (some env,middle)) :
    ∃ imm, env = logicalImmEnv false k ty.width x y (imm64OfIconst ty u) imm ∧ middle = (st,tr) ∧
      imm.value = u.toNat ∧ ImmLogic.ofNat? imm.value (szOf ty.width) = some imm := by
  rw [match_imm p ctx {} (m+9) _ st tr] at matched
  exact stock_logical_imm_match_receipts hp inv dfg false width source matched

/-- Actual NOT matching reuses the identical proved source/value receipt. -/
theorem stock_not_shift_match_receipts {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr)
     {k x y m : Nat} {ty : Clif.Ty} (width : ty.width ≤ 64) {v : BitVec ty.width}
    (source : fr.getAs y ty = .ok v)
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m + 10) rule_inst_3944
      [.data 59 k [],.ty (.int ty.width),.value x,.value y]).run (st,tr) = .ok (some env,middle)) :
    ∃ (z : Nat) (kk : Int) (sh : ShiftOpAndAmt) (u : BitVec ty.width),
      env = logicalShiftEnv false k ty.width x y z kk sh ∧ middle = (st,tr) ∧ fr.getAs z ty = .ok u ∧
      sh.op = .lsl ∧ sh.amt < ty.width ∧ v = u <<< sh.amt := by
  rw [match_shift p ctx {} (m+9) _ st tr] at matched
  exact stock_logical_shift_match_receipts hp inv dfg false width source matched

end Backend.Stock.Proof.LogicalNot

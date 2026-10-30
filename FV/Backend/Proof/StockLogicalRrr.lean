import FV.Backend.Proof.StockAlu
import FV.Backend.Proof.IselCtlTry

/-! Actual logical register RHS and its mapped machine value semantics. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem stock_sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl

/-- The actual logical register RHS marks its operands and emits the shared
ALU helper with mapped registers. The complete Stock state is accounted for. -/
theorem stock_rhs_3916 {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {k w x y : Nat} {op : ALUOp} {rx ry : Reg}
    (hk : ALUOp.ofIdx? k = some op) (hx : ctx.valueReg? x = some rx)
    (hy : ctx.valueReg? y = some ry) (width : w ≤ 64)
    (st : State) (safeX : DemandAllowed ctx st x) (safeY : DemandAllowed ctx st y)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace, (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_inst_3916.rhs
      (env4 (.data 59 k []) (.ty (.int w)) (.value x) (.value y))).run (st, tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {(st.mark x).mark y with base := (st.base.fresh .int).2.emit (.aluRRR op (szOf w) (st.base.fresh .int).1 rx ry)}, trace) := by
  have xPut := stock_put_in_reg ctx st x rx hx safeX
  have yPut := stock_put_in_reg ctx (st.mark x) y ry hy safeY
  have helper := fun q trace fuel => stock_alu_rrr_helper hp ctx hc width hk q trace fuel rx ry
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    isel_eval [*, rule_inst_3916, stock_sem_ctor]
    rfl

private def logicalState : State := {sinkState with
  base := ⟨195, Array.replicate 195 .int, #[], 0⟩
  demand := Array.replicate 101 0
  sunk := #[] }
private def logicalRegs (n : Nat) : CV := if n = 192 then 7 else if n = 193 then 5 else 0
private def logicalFrame (ctx : Ctx) (ty : Clif.Ty) : Clif.Frame := {
  func := ctx.func
  regs := fun x => if x = 7 then some (.ofInt ty 7) else if x = 31 then some (.ofInt ty 5) else none
  slots := [], body := [], term := .ret [100] }
private theorem logicalSafe (ctx : Ctx) (x : Nat) : DemandAllowed ctx logicalState x := by
  intro i _
  change (#[] : Array Bool)[i]! = false
  simp

/-- Real sparse-ID context construction inhabits the generic ALU helper and
actual logical RHS. AND/OR/XOR at32/64 bits compute the corresponding source
binary value, mark both operands and preserve their machine registers. -/
theorem stock_logical_rrr_witness (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64)
    (k : Nat) (op : ALUOp) (cop : Clif.BinaryOp) (tag : ALUOp.ofIdx? k = some op)
    (operation : (op, cop) = (.and, .band) ∨ (op, cop) = (.orr, .bor) ∨ (op, cop) = (.eor, .bxor)) :
    ∃ (ctx : Ctx) (next : State) (trace : Array RuleId) (ρ' : Nat → CV),
      ctx.valueReg? 7 = some (.vreg 192 .int) ∧ ctx.valueReg? 31 = some (.vreg 193 .int) ∧
      (applyTerm program (Stock.sem ctx) {} 20 27 362
        [.data 59 k [], .ty (.int ty.width), .reg (.vreg 192 .int), .reg (.vreg 193 .int)]).run
        (logicalState, #[]) = .ok (some (.reg (.vreg 195 .int)),
          {logicalState with base := (logicalState.base.fresh .int).2.emit (.aluRRR op (szOf ty.width) (.vreg 195 .int) (.vreg 192 .int) (.vreg 193 .int))},
          (#[(if ty.width ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)]).push rule_inst_2545.id) ∧
      (evalExpr program (Stock.sem ctx) {} 40 rule_inst_3916.rhs
        (env4 (.data 59 k []) (.ty (.int ty.width)) (.value 7) (.value 31))).run
          (logicalState, #[]) = .ok (some (.reg (.vreg 195 .int)), next, trace) ∧
      next.base.emitted = #[.aluRRR op (szOf ty.width) (.vreg 195 .int) (.vreg 192 .int) (.vreg 193 .int)] ∧
      next.demand[7]! = 1 ∧ next.demand[31]! = 1 ∧
      PRun (fun _ => True) ispec next.base.emitted.toList logicalRegs ρ' ∧
      VHolds ⟨ty, Clif.Sem.binary cop (BitVec.ofInt ty.width 7) (BitVec.ofInt ty.width 5)⟩ (ρ' 195) ∧
      ρ' 192 = 7 ∧ ρ' 193 = 5 := by
  obtain ⟨ctx, info, ignored, ignoredTrace, ignoredRegs, _, _, _, _, mx, my, _⟩ :=
    stock_alu_roots_witness false ty supported
  have width : ty.width ≤ 64 := by rcases supported with rfl | rfl <;> decide
  have helper := stock_alu_rrr_helper data_program ctx (cfg := {}) rfl width tag logicalState #[] 0
    (.vreg 192 .int) (.vreg 193 .int)
  obtain ⟨trace, rhs⟩ := stock_rhs_3916 data_program ctx (cfg := {}) rfl tag mx my width logicalState
    (logicalSafe ctx 7) (logicalSafe ctx 31) #[] 0
  have held : ValuesHeld (fun z => z = 7 ∨ z = 31) ctx (logicalFrame ctx ty)
      (fun n => logicalRegs (aliasNum #[] n)) := by
    intro z required val lookup
    rcases required with rfl | rfl
    · change some (Clif.Val.ofInt ty 7) = some val at lookup
      cases lookup
      refine ⟨192, mx, ?_⟩
      change VHolds (.ofInt ty 7) 7
      rcases supported with rfl | rfl <;> unfold VHolds <;> decide +kernel
    · change some (Clif.Val.ofInt ty 5) = some val at lookup
      cases lookup
      refine ⟨193, my, ?_⟩
      change VHolds (.ofInt ty 5) 5
      rcases supported with rfl | rfl <;> unfold VHolds <;> decide +kernel
  have sourceX : (logicalFrame ctx ty).getAs 7 ty = .ok (BitVec.ofInt ty.width 7) := by
    rcases supported with rfl | rfl <;> rfl
  have sourceY : (logicalFrame ctx ty).getAs 31 ty = .ok (BitVec.ofInt ty.width 5) := by
    rcases supported with rfl | rfl <;> rfl
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w', h, SameWorld.refl _ _⟩
  obtain ⟨ρ', execution, value, kept⟩ := stock_alu_rrr_resolved self (Or.inr (Or.inr operation)) width
    (aliases := #[]) (ρ := logicalRegs) (d := 195) (by decide) mx my held sourceX sourceY
  refine ⟨ctx, _, trace, ρ', mx, my, helper, rhs, rfl, rfl, rfl, ?_, value, ?_, ?_⟩
  · simpa [logicalState, LState.fresh, LState.emit, State.mark, MInst.mapRegs,
      Backend.lowerFunction.resolve, chaseF] using execution
  · exact (kept 192 (by decide)).trans rfl
  · exact (kept 193 (by decide)).trans rfl

end Backend.Stock.Proof

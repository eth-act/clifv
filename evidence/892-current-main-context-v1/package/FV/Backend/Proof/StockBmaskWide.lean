import FV.Backend.Proof.StockBmaskProjection
import FV.Backend.Proof.StockCmpBuilders
import FV.Backend.Proof.StockCmpWithFlags
import FV.Backend.Proof.StockDivPure

namespace Backend.Stock.Proof.ScalarMask
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_int (ctx : Ctx) (ty : Nat) (i : Int) :
    (Stock.sem ctx).int ty i = .int (normInt ty i) := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl

private theorem flags_register {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : State) (tr : Array RuleId) (n : Nat)
    {mi ci : V} {m1 m2 : MInst} (producer : MInst.ofV mi = some m1)
    (consumer : MInst.ofV ci = some m2) (r : Reg) :
    (applyTerm p (Stock.sem ctx) cfg (n+60) 27 255
      [.data 47 1 [mi],.data 49 3 [ci,.reg r]]).run (st,tr) =
      .ok (some (.reg r),{st with base := (st.base.emit m1).emit m2},
        (tr.push rule_prelude_lower_818.id).push rule_prelude_lower_984.id) := by
  have flags := fun q trace fuel =>
    ScalarCmp.stock_cmp_with_flags_reg hp ctx hc q trace fuel producer consumer r
  have get : ∀ q : State, Stock.externCtor ctx T.value_regs_get [.regs [r],.int 0] q =
      .ok (.reg r,q) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.value_regs_get _ q (by decide)]
    rfl
  cases hp
  isel_eval [*,rule_prelude_lower_984,sem_ctor,sem_int]

def bmaskWideTrace (sz : OperandSize) (tr : Array RuleId) : Array RuleId :=
  (((((tr.push (if sz = .size32 then rule_inst_1592.id else rule_inst_1593.id)).push
    rule_inst_2774.id).push rule_inst_3082.id).push rule_prelude_lower_818.id).push
      rule_prelude_lower_984.id).push rule_inst_5276.id

/-- Actual 32/64-bit `lower_bmask` execution allocates one result, emits CMP
and CSETM, and preserves every Stock scheduling field for any original output
width at most 64. -/
theorem stock_bmask_wide {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {wo : Nat} (output : wo ≤ 64)
    (sz : OperandSize) (r : Reg) (st : State) (tr : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (n+180) 22 658
      [.ty (.int wo),.ty (.int sz.bits),.regs [r]]).run (st,tr) =
      .ok (some (.regs [(st.base.fresh .int).1]),
        {st with base := ((st.base.fresh .int).2.emit
          (.aluRRImm12 .subS sz .xzr r ⟨0,false⟩)).emit (.csetm (st.base.fresh .int).1 .ne)},bmaskWideTrace sz tr) := by
  have not128 : wo ≠ 128 := by omega
  have immediate : ∀ q : State,Stock.externCtor ctx T.u8_into_imm12 [.int 0] q =
      .ok (.op (.imm12 ⟨0,false⟩),q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.u8_into_imm12 _ q (by decide)]; rfl
  have inputReg : ∀ q : State,Stock.externCtor ctx T.value_regs_get [.regs [r],.int 0] q =
      .ok (.reg r,q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.value_regs_get _ q (by decide)]; rfl
  have resultReg : ∀ (q : State) (rd : Reg),Stock.externCtor ctx T.value_reg [.reg rd] q =
      .ok (.regs [rd],q) := by
    intro q rd; rw [stock_ctor_baseOnly ctx T.value_reg _ q (by decide)]; rfl
  have cmp := fun q trace fuel => ScalarCmp.stock_cmp_imm_builder hp ctx hc q trace fuel
    (.data 93 (if sz = .size32 then 0 else 1) []) (.reg r) (.op (.imm12 ⟨0,false⟩))
  have set := fun q trace fuel => stock_csetm_helper hp ctx hc (.data 96 1 []) q trace fuel
  have decoded : MInst.ofV (.data 58 4 [.data 59 10 [],
      .data 93 (if sz = .size32 then 0 else 1) [],.reg .xzr,.reg r,.op (.imm12 ⟨0,false⟩)]) =
      some (.aluRRImm12 .subS sz .xzr r ⟨0,false⟩) := by cases sz <;> rfl
  have flags := fun q trace fuel => flags_register hp ctx hc q trace fuel decoded
    (show MInst.ofV (.data 58 34 [.reg (st.base.fresh .int).1,.data 96 1 []]) =
      some (.csetm (st.base.fresh .int).1 .ne) from rfl) (st.base.fresh .int).1
  cases sz
  · have size := fun (q : State) trace fuel => ScalarDiv.stock_div_pure_helper hp ctx hc
      (st := q) (t := 305) (by decide)
      (operand_size_32 hp ctx hc q.base trace fuel (w := 32) (by decide))
    simp only [ite_true] at cmp flags
    cases hp
    isel_eval [*,rule_inst_5276,rule_inst_5289,rule_inst_5298,rule_inst_5310,
      sem_ctor,sem_int,sem_mkData,stock_matchArgs,CTy.bits,OperandSize.bits,bmaskWideTrace,
      ext_fits_in_16',ext_fits_in_64',ext_ty_32_or_64',ext_ty_int_ref_scalar_64_extract,
      Backend.Proof.sem_eq,beq_iff_eq,V.ty.injEq,CTy.int.injEq,
      Bool.true_or,Bool.or_true,Bool.false_or,Bool.or_false,reduceCtorEq]
  · have size := fun (q : State) trace fuel => ScalarDiv.stock_div_pure_helper hp ctx hc
      (st := q) (t := 305) (by decide)
      (operand_size_64 hp ctx hc q.base trace fuel (w := 64) (by decide) (by decide))
    simp only [reduceCtorEq,ite_false] at cmp flags
    cases hp
    isel_eval [*,rule_inst_5276,rule_inst_5289,rule_inst_5298,rule_inst_5310,
      sem_ctor,sem_int,sem_mkData,stock_matchArgs,CTy.bits,OperandSize.bits,bmaskWideTrace,
      ext_fits_in_16',ext_fits_in_64',ext_ty_32_or_64',ext_ty_int_ref_scalar_64_extract,
      Backend.Proof.sem_eq,beq_iff_eq,V.ty.injEq,CTy.int.injEq,
      Bool.true_or,Bool.or_true,Bool.false_or,Bool.or_false,reduceCtorEq]

/-- An actual successful wide helper run determines its result and full state. -/
theorem stock_bmask_wide_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {wo : Nat} (output : wo ≤ 64)
    (sz : OperandSize) (r : Reg) {fuel : Nat} (enough : 179 ≤ fuel)
    {st next : State} {before trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg fuel 22 658
      [.ty (.int wo),.ty (.int sz.bits),.regs [r]] (st,before) out (next,trace)) :
    out = .regs [(st.base.fresh .int).1] ∧
      next = {st with base := ((st.base.fresh .int).2.emit
        (.aluRRImm12 .subS sz .xzr r ⟨0,false⟩)).emit (.csetm (st.base.fresh .int).1 .ne)} := by
  obtain ⟨n,equal⟩ : ∃ n,fuel+1=n+180 := ⟨fuel-179,by omega⟩
  have expected := stock_bmask_wide hp ctx hc output sz r st before n
  unfold ApplyInternal at run
  rw [equal] at run
  rw [run] at expected
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at expected
  exact ⟨expected.1,expected.2.1⟩

/-- All four original output widths and both wide input widths have real
executions and satisfy the observed contract. -/
theorem stock_bmask_wide_witness :
    ∀ wo ∈ ([8,16,32,64] : List Nat),∀ sz : OperandSize,
      ∃ (out : V) (next : State) (trace : Array RuleId),
        ApplyInternal program (Stock.sem sinkCtx) {} 999 22 658
          [.ty (.int wo),.ty (.int sz.bits),.regs [Reg.vreg 0 .int]]
          (sinkState,#[]) out (next,trace) ∧
        out = .regs [(sinkState.base.fresh .int).1] ∧
        next = {sinkState with base := ((sinkState.base.fresh .int).2.emit
          (.aluRRImm12 .subS sz .xzr (Reg.vreg 0 .int) ⟨0,false⟩)).emit (.csetm (sinkState.base.fresh .int).1 .ne)} := by
  intro wo member sz
  have width : wo ≤ 64 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at member; omega
  have run := stock_bmask_wide data_program sinkCtx (cfg := {}) rfl width sz
    (Reg.vreg 0 .int) sinkState #[] 820
  exact ⟨_,_,_,run,stock_bmask_wide_observed data_program sinkCtx rfl width sz _ (by decide) run⟩

end Backend.Stock.Proof.ScalarMask

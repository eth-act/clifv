module

public import FV.Backend.Proof.StockBmaskWide
public import FV.Backend.Proof.StockLogicalForms

@[expose] public section

namespace Backend.Stock.Proof.ScalarMask
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem sem_int (ctx : Ctx) (ty : Nat) (i : Int) :
    (Stock.sem ctx).int ty i = .int (normInt ty i) := rfl
private theorem sem_i32 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I32" = some (.ty (.int 32)) := rfl

private theorem and_immediate {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (r : Reg) (imm : ImmLogic)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (n+40) 27 502 [.ty (.int 32),.reg r,.op (.immLogic imm)]).run
      (st,tr) = .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRImmLogic .and .size32 (st.base.fresh .int).1 r imm)},
        ((tr.push rule_inst_1592.id).push rule_inst_2529.id).push rule_inst_3431.id) := by
  have helper := fun q trace fuel => LogicalForms.stock_logical_imm_helper hp ctx hc
    (w := 32) (k := 4) (op := .and) (by decide) rfl q trace fuel r imm
  cases hp
  isel_eval [*,rule_inst_3431,sem_mkData,szOf]

def bmaskMaskedBase (st : LState) (wi : Nat) (r : Reg) : LState :=
  (st.fresh .int).2.emit (.aluRRImmLogic .and .size32 (st.fresh .int).1 r ⟨2^wi-1,.size32⟩)

def bmaskNarrowBase (st : LState) (wi : Nat) (r : Reg) : LState :=
  (((bmaskMaskedBase st wi r).fresh .int).2.emit
    (.aluRRImm12 .subS .size32 .xzr (st.fresh .int).1 ⟨0,false⟩)).emit
      (.csetm ((bmaskMaskedBase st wi r).fresh .int).1 .ne)

def bmaskNarrowTrace (tr : Array RuleId) : Array RuleId :=
  (bmaskWideTrace .size32 (((tr.push rule_inst_1592.id).push rule_inst_2529.id).push
    rule_inst_3431.id)).push rule_inst_5310.id

/-- An 8/16-bit input is masked before the real recursive CMP/CSETM helper.
Input and output widths are independent, and the complete Stock scheduling
state is retained across both fresh allocations. -/
theorem stock_bmask_narrow {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {wo wi : Nat} (output : wo ≤ 64)
    (input : wi = 8 ∨ wi = 16) (r : Reg) (st : State) (tr : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (n+400) 22 658
      [.ty (.int wo),.ty (.int wi),.regs [r]]).run (st,tr) =
      .ok (some (.regs [((bmaskMaskedBase st.base wi r).fresh .int).1]),
        {st with base := bmaskNarrowBase st.base wi r},bmaskNarrowTrace tr) := by
  have not128 : wo ≠ 128 := by omega
  have inputReg : ∀ q : State,Stock.externCtor ctx T.value_regs_get [.regs [r],.int 0] q =
      .ok (.reg r,q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.value_regs_get _ q (by decide)]; rfl
  have resultReg : ∀ (q : State) (rd : Reg),Stock.externCtor ctx T.value_reg [.reg rd] q =
      .ok (.regs [rd],q) := by
    intro q rd; rw [stock_ctor_baseOnly ctx T.value_reg _ q (by decide)]; rfl
  have mask : ∀ q : State,Stock.externCtor ctx T.ty_mask [.ty (.int wi)] q =
      .ok (.int (2^wi-1),q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.ty_mask _ q (by decide)]; rfl
  have immediate : ∀ q : State,Stock.externCtor ctx T.imm_logic_from_u64
      [.ty (.int 32),.int (2^wi-1)] q = .ok (.op (.immLogic ⟨2^wi-1,.size32⟩),q) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.imm_logic_from_u64 _ q (by decide)]
    rcases input with rfl | rfl <;> rfl
  have logical := fun q trace fuel => and_immediate hp ctx hc r ⟨2^wi-1,.size32⟩ q trace fuel
  have lower := fun q trace fuel => stock_bmask_wide hp ctx hc output .size32
    (st.base.fresh .int).1 q trace fuel
  simp only [OperandSize.bits] at lower
  rcases input with rfl | rfl
  all_goals cases hp
  all_goals isel_eval [*,rule_inst_5276,rule_inst_5289,rule_inst_5298,rule_inst_5310,
    sem_ctor,sem_mkData,sem_int,sem_i32,stock_matchArgs,CTy.bits,OperandSize.bits,
    bmaskMaskedBase,bmaskNarrowBase,bmaskNarrowTrace,ext_fits_in_16',Backend.Proof.sem_eq,
    beq_iff_eq,V.ty.injEq,CTy.int.injEq]

/-- Successful narrow helper execution supplies its complete two-allocation
post-state, without assuming a caller-provided emission equation. -/
theorem stock_bmask_narrow_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {wo wi : Nat} (output : wo ≤ 64)
    (input : wi = 8 ∨ wi = 16) (r : Reg) {fuel : Nat} (enough : 399 ≤ fuel)
    {st next : State} {before trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg fuel 22 658
      [.ty (.int wo),.ty (.int wi),.regs [r]] (st,before) out (next,trace)) :
    out = .regs [((bmaskMaskedBase st.base wi r).fresh .int).1] ∧
      next = {st with base := bmaskNarrowBase st.base wi r} := by
  obtain ⟨n,equal⟩ : ∃ n,fuel+1=n+400 := ⟨fuel-399,by omega⟩
  have expected := stock_bmask_narrow hp ctx hc output input r st before n
  unfold ApplyInternal at run
  rw [equal] at run
  rw [run] at expected
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at expected
  exact ⟨expected.1,expected.2.1⟩

/-- Every combination of original output width and narrow input width has a
real helper execution satisfying the observed full-state contract. -/
theorem stock_bmask_narrow_witness :
    ∀ wo ∈ ([8,16,32,64] : List Nat),∀ wi ∈ ([8,16] : List Nat),
      ∃ (out : V) (next : State) (trace : Array RuleId),
        ApplyInternal program (Stock.sem sinkCtx) {} 999 22 658
          [.ty (.int wo),.ty (.int wi),.regs [Reg.vreg 0 .int]]
          (sinkState,#[]) out (next,trace) ∧
        out = .regs [((bmaskMaskedBase sinkState.base wi (.vreg 0 .int)).fresh .int).1] ∧
        next = {sinkState with base := bmaskNarrowBase sinkState.base wi (.vreg 0 .int)} := by
  intro wo outMember wi inMember
  have output : wo ≤ 64 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at outMember; omega
  have input : wi = 8 ∨ wi = 16 := by simpa using inMember
  have run := stock_bmask_narrow data_program sinkCtx (cfg := {}) rfl output input
    (.vreg 0 .int) sinkState #[] 600
  exact ⟨_,_,_,run,stock_bmask_narrow_observed data_program sinkCtx rfl output input _ (by decide) run⟩

end Backend.Stock.Proof.ScalarMask

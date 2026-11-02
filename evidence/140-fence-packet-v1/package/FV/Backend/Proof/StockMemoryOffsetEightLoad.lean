import FV.Backend.Proof.StockMemoryIntegerLoadSelection
import FV.Backend.Proof.StockMemoryOffsetEightAddress

namespace Backend.Stock.Memory.IntegerRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Proof.MemoryHelpers Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_i32 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I32" = some (.ty (.int 32)) := rfl

private theorem output_run {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) cfg (n+10) 25 172 [.reg r]).run (st,tr) =
      .ok (some (.regsVec [[r]]),st,tr.push rule_prelude_lower_105.id) := by
  have value : ∀ q,Stock.externCtor ctx T.value_reg [.reg r] q = .ok (.regs [r],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.value_reg _ q (by decide)]; rfl
  have output : ∀ q,Stock.externCtor ctx T.output [.regs [r]] q = .ok (.regsVec [[r]],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.output _ q (by decide)]; rfl
  cases hp
  isel_eval [*,rule_prelude_lower_105,sem_ctor]

private theorem sem_i8 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I8" = some (.ty (.int 8)) := rfl
private theorem sem_i16 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I16" = some (.ty (.int 16)) := rfl
private theorem sem_i64 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl

/-- Every unsigned integer load root uses the mapped parameter, records its demand,
allocates its exact fresh result and emits the selected offset8 load. -/
theorem stock_parameter_integer_load_eight_rhs {p : Program} (hp : Data p) (width : Width)
    (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false) {x nreg : Nat}
    (parameter : ctx.defInst? x = none) (mapped : ctx.valueReg? x = some (.vreg nreg .int))
    (flags : Clif.MemFlags) (st : State) (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) cfg (n+120) width.root.rhs
      (env3 (.value x) (.op (.memFlags flags)) (.int 8))).run (st,tr) =
        .ok (some (.regsVec [[(st.base.fresh .int).1]]),
          {(st.mark x) with base := (st.base.fresh .int).2.emit (.load width.loadOp (st.base.fresh .int).1 (.unsignedOffset (.vreg nreg .int) 8) flags)},trace) := by
  have address := fun q trace fuel =>
    stock_parameter_load_address_eight_width hp width ctx hc parameter mapped q trace fuel
  have load := fun q trace fuel => integer_load_forward width.helper hp ctx hc q trace fuel
    (.data 89 VIdx.AMode.UnsignedOffset [.reg (.vreg nreg .int),.op (.uimm12Scaled 8)])
    (.op (.memFlags flags))
    (.load width.loadOp (q.base.fresh .int).1 (.unsignedOffset (.vreg nreg .int) 8) flags)
    (by cases width <;> rfl)
  have output := fun q trace fuel r => output_run hp ctx hc q trace fuel r
  have offset (q : State) : Stock.externCtor ctx T.offset32_to_i32 [.int 8] q =
      .ok (.int 8,q) := by
    rw [stock_ctor_baseOnly ctx T.offset32_to_i32 _ q (by decide)]
    rfl
  refine ⟨(((tr.push rule_inst_4103.id).push rule_inst_4038.id).push
    width.helper.ruleId).push rule_prelude_lower_105.id,?_⟩
  cases width <;> simp only [Width.bits,Width.helper,Width.loadOp,Width.root,
    IntegerLoad.term,IntegerLoad.ruleId] at * <;> cases hp <;>
    isel_eval [*,rule_lower_2604,rule_lower_2607,rule_lower_2610,rule_lower_2613,
      sem_ctor,sem_i8,sem_i16,sem_i32,sem_i64,offset] <;> rfl

end Backend.Stock.Memory.IntegerRoots

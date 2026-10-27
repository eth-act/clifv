import FV.Backend.Proof.StockMemoryAddressSelection

namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
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

/-- Actual load root1043 uses the mapped parameter register, marks its demand,
allocates the fresh result and emits the selected unsigned-offset load. -/
theorem stock_parameter_load_rhs {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {x nreg : Nat}
    (parameter : ctx.defInst? x = none) (mapped : ctx.valueReg? x = some (.vreg nreg .int))
    (flags : Clif.MemFlags) (st : State) (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) cfg (n+120) rule_lower_2610.rhs
      (env3 (.value x) (.op (.memFlags flags)) (.int 0))).run (st,tr) =
        .ok (some (.regsVec [[(st.base.fresh .int).1]]),
          { (st.mark x) with base := (st.base.fresh .int).2.emit (.load .uload32 (st.base.fresh .int).1 (.unsignedOffset (.vreg nreg .int) 0) flags)},trace) := by
  have address := fun q trace fuel => stock_parameter_load_address hp ctx hc parameter mapped q trace fuel
  have load := fun q trace fuel => stock_uload32_helper hp ctx hc q trace fuel
    (.data 89 VIdx.AMode.UnsignedOffset [.reg (.vreg nreg .int),.op (.uimm12Scaled 0)])
    (.op (.memFlags flags))
    (.load .uload32 (q.base.fresh .int).1 (.unsignedOffset (.vreg nreg .int) 0) flags) rfl
  have output := fun q trace fuel r => output_run hp ctx hc q trace fuel r
  have offset (q : State) : Stock.externCtor ctx T.offset32_to_i32 [.int 0] q = .ok (.int 0,q) := by
    rw [stock_ctor_baseOnly ctx T.offset32_to_i32 _ q (by decide)]
    rfl
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    isel_eval [*,rule_lower_2610,sem_ctor,sem_i32,offset]
    rfl

end Backend.Stock.Memory

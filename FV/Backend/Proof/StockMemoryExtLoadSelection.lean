import FV.Backend.Proof.StockMemoryIntegerAddress

namespace Backend.Stock.Memory.ExtendedRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Proof.MemoryHelpers Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

inductive Kind where
  | unsigned8 | signed8 | unsigned16 | signed16 | unsigned32 | signed32

def Kind.width : Kind → IntegerRoots.Width
  | .unsigned8 | .signed8 => .w8
  | .unsigned16 | .signed16 => .w16
  | .unsigned32 | .signed32 => .w32

def Kind.helper : Kind → IntegerLoad
  | .unsigned8 => .unsigned8 | .signed8 => .signed8
  | .unsigned16 => .unsigned16 | .signed16 => .signed16
  | .unsigned32 => .unsigned32 | .signed32 => .signed32

def Kind.loadOp : Kind → LoadOp
  | .unsigned8 => .uload8 | .signed8 => .sload8
  | .unsigned16 => .uload16 | .signed16 => .sload16
  | .unsigned32 => .uload32 | .signed32 => .sload32

def Kind.sourceOp : Kind → Clif.LoadOp
  | .unsigned8 => .uload8 | .signed8 => .sload8
  | .unsigned16 => .uload16 | .signed16 => .sload16
  | .unsigned32 => .uload32 | .signed32 => .sload32

def Kind.sourceTag : Kind → Nat
  | .unsigned8 => 31 | .signed8 => 32
  | .unsigned16 => 34 | .signed16 => 35
  | .unsigned32 => 37 | .signed32 => 38

def Kind.root : Kind → Rule
  | .unsigned8 => rule_lower_2647 | .signed8 => rule_lower_2650
  | .unsigned16 => rule_lower_2653 | .signed16 => rule_lower_2656
  | .unsigned32 => rule_lower_2659 | .signed32 => rule_lower_2662

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

/-- Every extending integer load root records the pointer demand and emits its exact signed or unsigned load. -/
theorem stock_parameter_extending_load_rhs {p : Program} (hp : Data p) (kind : Kind)
    (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false) {x nreg : Nat}
    (parameter : ctx.defInst? x = none) (mapped : ctx.valueReg? x = some (.vreg nreg .int))
    (flags : Clif.MemFlags) (st : State) (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) cfg (n+120) kind.root.rhs
      (env3 (.value x) (.op (.memFlags flags)) (.int 0))).run (st,tr) =
        .ok (some (.regsVec [[(st.base.fresh .int).1]]),
          {(st.mark x) with base := (st.base.fresh .int).2.emit (.load kind.loadOp (st.base.fresh .int).1 (.unsignedOffset (.vreg nreg .int) 0) flags)},trace) := by
  have address := fun q trace fuel =>
    IntegerRoots.stock_parameter_load_address_width hp kind.width ctx hc parameter mapped q trace fuel
  have load := fun q trace fuel => integer_load_forward kind.helper hp ctx hc q trace fuel
    (.data 89 VIdx.AMode.UnsignedOffset [.reg (.vreg nreg .int),.op (.uimm12Scaled 0)])
    (.op (.memFlags flags))
    (.load kind.loadOp (q.base.fresh .int).1 (.unsignedOffset (.vreg nreg .int) 0) flags)
    (by cases kind <;> rfl)
  have output := fun q trace fuel r => output_run hp ctx hc q trace fuel r
  have offset (q : State) : Stock.externCtor ctx T.offset32_to_i32 [.int 0] q =
      .ok (.int 0,q) := by
    rw [stock_ctor_baseOnly ctx T.offset32_to_i32 _ q (by decide)]
    rfl
  refine ⟨(((tr.push rule_inst_4064.id).push rule_inst_4038.id).push
    kind.helper.ruleId).push rule_prelude_lower_105.id,?_⟩
  cases kind <;> simp only [Kind.width,IntegerRoots.Width.bits,Kind.helper,Kind.loadOp,Kind.root,
    IntegerLoad.term,IntegerLoad.tag,IntegerLoad.ruleId] at * <;> cases hp <;>
    isel_eval [*,rule_lower_2647,rule_lower_2650,rule_lower_2653,rule_lower_2656,rule_lower_2659,rule_lower_2662,
      sem_ctor,sem_i8,sem_i16,sem_i32,sem_i64,offset] <;> rfl

end Backend.Stock.Memory.ExtendedRoots

import FV.Backend.Proof.StockMemoryIntegerAddress
import FV.Backend.Proof.IselRulesALU

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Proof.MemoryHelpers Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

inductive Kind where
  | plain8 | plain16 | plain32 | plain64 | narrow8 | narrow16 | narrow32

def Kind.width : Kind → IntegerRoots.Width
  | .plain8 | .narrow8 => .w8
  | .plain16 | .narrow16 => .w16
  | .plain32 | .narrow32 => .w32
  | .plain64 => .w64

def Kind.helper : Kind → IntegerStore
  | .plain8 | .narrow8 => .bits8
  | .plain16 | .narrow16 => .bits16
  | .plain32 | .narrow32 => .bits32
  | .plain64 => .bits64

def Kind.storeOp : Kind → StoreOp
  | .plain8 | .narrow8 => .store8
  | .plain16 | .narrow16 => .store16
  | .plain32 | .narrow32 => .store32
  | .plain64 => .store64

def Kind.root : Kind → Rule
  | .plain8 => rule_lower_2705 | .plain16 => rule_lower_2709
  | .plain32 => rule_lower_2713 | .plain64 => rule_lower_2717
  | .narrow8 => rule_lower_2722 | .narrow16 => rule_lower_2726
  | .narrow32 => rule_lower_2730

def Kind.sourceOp : Kind → Clif.StoreOp
  | .narrow8 => .istore8 | .narrow16 => .istore16 | .narrow32 => .istore32
  | _ => .store

def Kind.sourceTy : Kind → Clif.Ty
  | .plain8 => .i8 | .plain16 => .i16 | .plain32 => .i32
  | _ => .i64

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_unData (ctx : Ctx) (ty t k : Nat) (vs : List V) :
    (Stock.sem ctx).unData ty (.data t k vs) = if t = ty then some (k,vs) else none :=
  Backend.Proof.sem_unData ctx ty t k vs
private theorem sem_i8 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I8" = some (.ty (.int 8)) := rfl
private theorem sem_i16 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I16" = some (.ty (.int 16)) := rfl
private theorem sem_i32 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I32" = some (.ty (.int 32)) := rfl
private theorem sem_i64 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl

/-- The enclosing side-effect term emits its decoded instruction and returns no values. -/
theorem stock_store_side_effect {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (kind : Kind) (value address : Reg)
    (flags : Clif.MemFlags) (st : State) (tr : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (n+20) 25 243
      [.data 46 0 [.data 58 kind.helper.tag
        [.reg value,.data 89 VIdx.AMode.UnsignedOffset [.reg address,.op (.uimm12Scaled 0)],
          .op (.memFlags flags)]]]).run (st,tr) =
      .ok (some (.regsVec []),
        {st with base := st.base.emit (.store kind.storeOp value (.unsignedOffset address 0) flags)},
        (tr.push rule_prelude_lower_522.id).push rule_prelude_lower_535.id) := by
  have emit (q : State) : Stock.externCtor ctx T.emit
      [.data 58 kind.helper.tag [.reg value,
        .data 89 VIdx.AMode.UnsignedOffset [.reg address,.op (.uimm12Scaled 0)],.op (.memFlags flags)]] q =
      .ok (.op .unit,{q with base := q.base.emit (.store kind.storeOp value (.unsignedOffset address 0) flags)}) := by
    rw [stock_ctor_baseOnly ctx T.emit _ q (by decide)]
    cases kind <;> rfl
  have output (q : State) : Stock.externCtor ctx T.output_none [] q = .ok (.regsVec [],q) := rfl
  cases kind <;> simp only [Kind.helper,IntegerStore.tag,Kind.storeOp] at * <;> cases hp <;>
    isel_eval [*,rule_prelude_lower_522,rule_prelude_lower_535,sem_ctor,sem_unData]

/-- The actual store RHS demands its parameter address and available value, then emits the store.
It retains the allocation frontier and every other scheduling field. -/
theorem stock_parameter_integer_store_rhs {p : Program} (hp : Data p) (kind : Kind)
    (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
    {pointer value pointerReg valueReg : Nat}
    (pointerParameter : ctx.defInst? pointer = none)
    (pointerMapped : ctx.valueReg? pointer = some (.vreg pointerReg .int))
    (valueMapped : ctx.valueReg? value = some (.vreg valueReg .int))
    (flags : Clif.MemFlags) (st : State) (tr : Array RuleId) (n : Nat)
    (valueSafe : DemandAllowed ctx st value) :
    ∃ trace,(evalExpr p (Stock.sem ctx) cfg (n+140) kind.root.rhs
      (env4 (.value value) (.value pointer) (.op (.memFlags flags)) (.int 0))).run (st,tr) =
      .ok (some (.regsVec []),
        {(st.mark pointer).mark value with
          base := st.base.emit (.store kind.storeOp (.vreg valueReg .int)
            (.unsignedOffset (.vreg pointerReg .int) 0) flags)},trace) := by
  have address := fun q trace fuel => IntegerRoots.stock_parameter_load_address_width hp kind.width ctx hc
    pointerParameter pointerMapped q trace fuel
  have payload := fun q trace fuel => integer_store_forward kind.helper hp ctx hc q trace fuel
    (.data 89 VIdx.AMode.UnsignedOffset [.reg (.vreg pointerReg .int),.op (.uimm12Scaled 0)])
    (.op (.memFlags flags)) (.reg (.vreg valueReg .int))
  have effect := fun q trace fuel => stock_store_side_effect hp ctx hc kind (.vreg valueReg .int)
    (.vreg pointerReg .int) flags q trace fuel
  have input : Stock.externCtor ctx T.put_in_reg [.value value] (st.mark pointer) =
      .ok (.reg (.vreg valueReg .int),(st.mark pointer).mark value) :=
    stock_put_in_reg ctx (st.mark pointer) value _ valueMapped valueSafe
  have offset (q : State) : Stock.externCtor ctx T.offset32_to_i32 [.int 0] q = .ok (.int 0,q) := by
    rw [stock_ctor_baseOnly ctx T.offset32_to_i32 _ q (by decide)]
    rfl
  refine ⟨((((tr.push rule_inst_4064.id).push rule_inst_4038.id).push kind.helper.ruleId).push
    rule_prelude_lower_522.id).push rule_prelude_lower_535.id,?_⟩
  cases kind <;> simp only [Kind.width,Kind.helper,Kind.storeOp,Kind.root,IntegerRoots.Width.bits,
    IntegerStore.term,IntegerStore.tag,IntegerStore.ruleId] at * <;> cases hp <;>
    isel_eval [*,rule_lower_2705,rule_lower_2709,rule_lower_2713,rule_lower_2717,
      rule_lower_2722,rule_lower_2726,rule_lower_2730,sem_ctor,sem_i8,sem_i16,sem_i32,sem_i64,offset,input] <;> rfl

end Backend.Stock.Memory.StoreRoots

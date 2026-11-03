import FV.Backend.Proof.StockMemoryStoreSelection
import FV.Backend.Proof.StockMemoryLoadedPointerAddress

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Proof.MemoryHelpers Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
attribute [local irreducible] Isle.Aarch64.program

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_unData (ctx : Ctx) (ty t k : Nat) (vs : List V) :
    (Stock.sem ctx).unData ty (.data t k vs) = if t = ty then some (k,vs) else none :=
  Backend.Proof.sem_unData ctx ty t k vs
private theorem sem_i8 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I8" = some (.ty (.int 8)) := rfl
private theorem sem_i16 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I16" = some (.ty (.int 16)) := rfl
private theorem sem_i32 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I32" = some (.ty (.int 32)) := rfl
private theorem sem_i64 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl

/-- The actual store RHS demands its loaded address and available value, then emits the store.
It retains the allocation frontier and every other scheduling field. -/
theorem stock_loaded_pointer_integer_store_rhs {p : Program} (hp : Data p) (kind : Kind)
    (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
    {pointer value pointerReg valueReg : Nat}
    {pointerInst sourcePointer : Nat} {pointerInfo : IInfo} {pointerFlags : Clif.MemFlags} {pointerOffset : Int}
    (pointerDefinition : ctx.defInst? pointer = some pointerInst)
    (pointerSource : ctx.insts[pointerInst]? = some pointerInfo)
    (pointerData : pointerInfo.data = .data 152 16
      [.data 151 29 [],.value sourcePointer,.op (.memFlags pointerFlags),.int pointerOffset])
    (pointerType : pointerInfo.resTys.head? = some (.int 64))
    (pointerMapped : ctx.valueReg? pointer = some (.vreg pointerReg .int))
    (valueMapped : ctx.valueReg? value = some (.vreg valueReg .int))
    (flags : Clif.MemFlags) (st : State) (tr : Array RuleId) (n : Nat)
    (pointerSafe : DemandAllowed ctx st pointer) (valueSafe : DemandAllowed ctx st value) :
    ∃ trace,(evalExpr p (Stock.sem ctx) cfg (n+140) kind.root.rhs
      (env4 (.value value) (.value pointer) (.op (.memFlags flags)) (.int 0))).run (st,tr) =
      .ok (some (.regsVec []),
        {(st.mark pointer).mark value with
          base := st.base.emit (.store kind.storeOp (.vreg valueReg .int)
            (.unsignedOffset (.vreg pointerReg .int) 0) flags)},trace) := by
  have address := fun trace fuel => IntegerRoots.stock_loaded_pointer_address_zero_width hp kind.width ctx hc
    pointerDefinition pointerSource pointerData pointerType pointerMapped st trace fuel pointerSafe
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

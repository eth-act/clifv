import FV.Backend.Proof.StockMemoryStoreSelection
import FV.Backend.Proof.StockDFG

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

def Kind.opcodeIndex : Kind → Nat
  | .plain8 | .plain16 | .plain32 | .plain64 => 30
  | .narrow8 => 33 | .narrow16 => 36 | .narrow32 => 39

private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty t k : Nat) (fs : List V) :
    (Stock.sem ctx).unData ty (.data t k fs) = if t = ty then some (k,fs) else none :=
  Backend.Proof.sem_unData ctx ty t k fs
private theorem sem_i8 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I8" = some (.ty (.int 8)) := rfl
private theorem sem_i16 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I16" = some (.ty (.int 16)) := rfl
private theorem sem_i32 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I32" = some (.ty (.int 32)) := rfl
private theorem sem_i64 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl

/-- Plain roots use the actual operand type. Narrow roots impose no operand-type equality. -/
theorem stock_match_integer_store {p : Program} (hp : Data p) (kind : Kind) (ctx : Ctx) {cfg : Config}
    {i value pointer : Nat} {info : IInfo} {flags : Clif.MemFlags}
    (source : ctx.insts[i]? = some info)
    (typed : kind.sourceOp = .store → ctx.valueType? value = some (.int kind.width.bits))
    (data : info.data = .data 152 22
      [.data 151 kind.opcodeIndex [],.values [value,pointer],.op (.memFlags flags),.int 0])
    (little : flags.endianness ≠ some .big) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) cfg (n+20) kind.root [.inst i]).run (st,tr) =
      .ok (some (env4 (.value value) (.value pointer) (.op (.memFlags flags)) (.int 0)),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data] at extraction
  have operands : Backend.externExtract ctx T.value_array_2 (.values [value,pointer]) st.base =
      .ok [.value value,.value pointer] := rfl
  have endian := (ext_little_or_native_endian_iff ctx st.base flags [.op (.memFlags flags)]).mpr ⟨little,rfl⟩
  have lookup : kind.sourceOp = .store →
      Backend.externExtract ctx T.value_type (.value value) st.base = .ok [.ty (.int kind.width.bits)] :=
    fun same => ext_value_type ctx st.base (typed same)
  cases kind <;>
    simp only [Kind.sourceOp,Kind.width,IntegerRoots.Width.bits,Kind.opcodeIndex,Kind.root,
      true_implies,reduceCtorEq,false_implies] at * <;> cases hp <;>
    isel_eval [*,rule_lower_2705,rule_lower_2709,rule_lower_2713,rule_lower_2717,
      rule_lower_2722,rule_lower_2726,rule_lower_2730,sem_extract,sem_unData,
      sem_i8,sem_i16,sem_i32,sem_i64,sem_eq]

section SourceData
attribute [local semireducible] Isle.Aarch64.program

/-- Accepted original metadata supplies the store opcode and endianness.
The instruction's declared type remains arbitrary. -/
theorem integer_store_source_data (kind : Kind) {ty : Clif.Ty}
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i value pointer : Nat} {info : IInfo} {flags : Clif.MemFlags}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.store kind.sourceOp ty flags value pointer 0)) :
    flags.endianness ≠ some .big ∧ info.data = .data 152 22
      [.data 151 kind.opcodeIndex [],.values [value,pointer],.op (.memFlags flags),.int 0] := by
  have data := inv.data i info _ source clif
  change (if (!eTy ty && !(ty.isFloat && kind.sourceOp == .store)) = true then
      Except.error s!"store.{ty.name}"
    else if (flags.endianness == some .big) = true then Except.error "big-endian store"
    else Except.ok (instDataV "Store" [opcodeV (storeOpcode kind.sourceOp),
      .values [value,pointer],.op (.memFlags flags),.int 0])) = Except.ok info.data at data
  by_cases invalid : (!eTy ty && !(ty.isFloat && kind.sourceOp == .store)) = true
  · rw [if_pos invalid] at data
    cases data
  · rw [if_neg invalid] at data
    have accepted : ¬ (flags.endianness == some .big) = true := by
      intro big
      rw [if_pos big] at data
      cases data
    have little : flags.endianness ≠ some .big := by
      intro big
      apply accepted
      simp [big]
    rw [if_neg accepted] at data
    refine ⟨little,(Except.ok.inj data).symm.trans ?_⟩
    cases kind <;> rfl

end SourceData
end Backend.Stock.Memory.StoreRoots

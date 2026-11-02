import FV.Backend.Proof.IselCmpCond
import FV.Backend.Proof.StockCmpBuilders
import FV.Backend.Proof.StockCmpWithFlags
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private def sizeIndex : OperandSize → Nat
  | .size32 => 0 | .size64 => 1
private theorem size_of_index (sz : OperandSize) : OperandSize.ofIdx? (sizeIndex sz) = some sz := by cases sz <;> rfl
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_int (ctx : Ctx) (ty : Nat) (i : Int) : (Stock.sem ctx).int ty i = .int (normInt ty i) := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem sem_unData (ctx : Ctx) (ty t k : Nat) (vs : List V) :
    (Stock.sem ctx).unData ty (.data t k vs) = if t = ty then some (k,vs) else none :=
  Backend.Proof.sem_unData ctx ty t k vs
/-- Actual Zero/NotZero condition-result paths allocate one fresh boolean,
emit the real zero comparison and cset, and preserve all scheduling fields. -/
theorem stock_cmp_condition_zero {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (nonzero : Bool) (sz : OperandSize)
    (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) :
    ∃ trace,(applyTerm p (Stock.sem ctx) cfg (n+120) 27 715
      [.data 123 (if nonzero then 1 else 0) [.reg r,.data 93 (sizeIndex sz) []]]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (((st.base.fresh .int).2.emit (.aluRRImm12 .subS sz .xzr r ⟨0,false⟩)).emit
          (.cset (st.base.fresh .int).1 (if nonzero then .ne else .eq)))},trace) := by
  have immediate : ∀ q : State,Stock.externCtor ctx T.u8_into_imm12 [.int 0] q =
      .ok (.op (.imm12 ⟨0,false⟩),q) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.u8_into_imm12 [.int 0] q (by decide)]
    rfl
  have getResult : ∀ q : State,Stock.externCtor ctx T.value_regs_get
      [.regs [(st.base.fresh .int).1],.int 0] q = .ok (.reg (st.base.fresh .int).1,q) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.value_regs_get _ q (by decide)]
    rfl
  have cmp := fun q trace fuel => stock_cmp_imm_builder hp ctx hc q trace fuel (.data 93 (sizeIndex sz) []) (.reg r) (.op (.imm12 ⟨0,false⟩))
  have setEq := fun q trace fuel => stock_cmp_cset_builder hp ctx hc q trace fuel (.data 96 0 [])
  have setNe := fun q trace fuel => stock_cmp_cset_builder hp ctx hc q trace fuel (.data 96 1 [])
  have decodeCompare : MInst.ofV (.data 58 4 [.data 59 10 [],.data 93 (sizeIndex sz) [],.reg .xzr,.reg r,.op (.imm12 ⟨0,false⟩)]) =
      some (.aluRRImm12 .subS sz .xzr r ⟨0,false⟩) := by
    rw [ofV_cmpImm,size_of_index]; rfl
  have flagsEq := fun q trace fuel => stock_cmp_with_flags_reg hp ctx hc q trace fuel
    decodeCompare (show MInst.ofV (.data 58 33 [.reg (st.base.fresh .int).1,.data 96 0 []]) = some (.cset (st.base.fresh .int).1 .eq) from by simp only [ofV_cset',V.cond?_data,cond_ofIdx_idx,cond_ofIdx_0,cond_ofIdx_1,Option.map_some]) (st.base.fresh .int).1
  have flagsNe := fun q trace fuel => stock_cmp_with_flags_reg hp ctx hc q trace fuel
    decodeCompare (show MInst.ofV (.data 58 33 [.reg (st.base.fresh .int).1,.data 96 1 []]) = some (.cset (st.base.fresh .int).1 .ne) from by simp only [ofV_cset',V.cond?_data,cond_ofIdx_idx,cond_ofIdx_0,cond_ofIdx_1,Option.map_some]) (st.base.fresh .int).1
  cases hp
  cases nonzero
  · refine ⟨(((tr.push rule_inst_2774.id).push rule_inst_3068.id).push rule_prelude_lower_818.id).push rule_lower_2222.id,?_⟩
    isel_eval [*,rule_lower_2222,rule_lower_2224,rule_lower_2226,sem_ctor,sem_int,sem_mkData,sem_unData,stock_matchArgs]
  · refine ⟨(((tr.push rule_inst_2774.id).push rule_inst_3068.id).push rule_prelude_lower_818.id).push rule_lower_2224.id,?_⟩
    isel_eval [*,rule_lower_2222,rule_lower_2224,rule_lower_2226,sem_ctor,sem_int,sem_mkData,sem_unData,stock_matchArgs]
/-- Actual explicit-flag condition-result execution emits the decoded
producer and one fresh cset, retaining the complete Stock scheduling state. -/
theorem stock_cmp_condition_flags {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : State) (tr : Array RuleId) (n : Nat)
    {mi : V} {m : MInst} (decoded : MInst.ofV mi = some m) (condition : Cond) :
    ∃ trace,(applyTerm p (Stock.sem ctx) cfg (n+120) 27 715
      [.data 123 2 [.data 47 1 [mi],.data 96 condition.idx []]]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (((st.base.fresh .int).2.emit m).emit
          (.cset (st.base.fresh .int).1 condition))},trace) := by
  have getResult : ∀ q : State,Stock.externCtor ctx T.value_regs_get
      [.regs [(st.base.fresh .int).1],.int 0] q = .ok (.reg (st.base.fresh .int).1,q) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.value_regs_get _ q (by decide)]
    rfl
  have set := fun q trace fuel => stock_cmp_cset_builder hp ctx hc q trace fuel (.data 96 condition.idx [])
  have decodeSet : MInst.ofV (.data 58 33 [.reg (st.base.fresh .int).1,.data 96 condition.idx []]) =
      some (.cset (st.base.fresh .int).1 condition) := by
    simp only [ofV_cset',V.cond?_data,cond_ofIdx_idx,cond_ofIdx_0,cond_ofIdx_1,Option.map_some]
  have flags := fun q trace fuel => stock_cmp_with_flags_reg hp ctx hc q trace fuel decoded decodeSet (st.base.fresh .int).1
  cases hp
  refine ⟨((tr.push rule_inst_3068.id).push rule_prelude_lower_818.id).push rule_lower_2226.id,?_⟩
  isel_eval [*,rule_lower_2222,rule_lower_2224,rule_lower_2226,sem_ctor,sem_int,sem_mkData,sem_unData,stock_matchArgs]
private theorem index_from_size {i : Nat} {sz : OperandSize} (decoded : OperandSize.ofIdx? i = some sz) : i = sizeIndex sz := by
  cases i with
  | zero => cases sz <;> simp_all [OperandSize.ofIdx?,sizeIndex]
  | succ i =>
    cases i with
    | zero => cases sz <;> simp_all [OperandSize.ofIdx?,sizeIndex]
    | succ i => simp [OperandSize.ofIdx?] at decoded
/-- Successful actual condition-result execution derives the flag/cset code,
full Stock state and fresh output internally from its established condition shape. -/
theorem stock_cmp_condition_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 119 ≤ fuel)
    {c : V} {P : Nat → Prop} (shape : CondShape c P)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg fuel 27 715 [c] (st,tr) out (next,trace)) :
    ∃ m condition,CondFlag cmpImm0 c m condition ∧ out = .reg (st.base.fresh .int).1 ∧
      next = {st with base := (((st.base.fresh .int).2.emit m).emit (.cset (st.base.fresh .int).1 condition))} := by
  obtain ⟨n,equal⟩ : ∃ n,fuel+1=n+120 := ⟨fuel-119,by omega⟩
  unfold ApplyInternal at run
  rw [equal] at run
  rcases shape with ⟨k,i,sz,rfl,decoded,_⟩ | ⟨k,i,sz,rfl,decoded,_⟩ | ⟨mi,m,condition,rfl,decoded,valid⟩
  · have index := index_from_size decoded
    subst i
    obtain ⟨expectedTrace,expected⟩ := stock_cmp_condition_zero hp ctx hc false sz st tr n (.vreg k .int)
    simp only [Bool.false_eq_true,ite_false] at expected
    rw [run] at expected
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at expected
    exact ⟨cmpImm0 sz k,.eq,Or.inl ⟨k,_,sz,rfl,decoded,rfl,rfl⟩,expected.1,expected.2.1⟩
  · have index := index_from_size decoded
    subst i
    obtain ⟨expectedTrace,expected⟩ := stock_cmp_condition_zero hp ctx hc true sz st tr n (.vreg k .int)
    simp only [ite_true] at expected
    rw [run] at expected
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at expected
    exact ⟨cmpImm0 sz k,.ne,Or.inr (Or.inl ⟨k,_,sz,rfl,decoded,rfl,rfl⟩),expected.1,expected.2.1⟩
  · obtain ⟨expectedTrace,expected⟩ := stock_cmp_condition_flags hp ctx hc st tr n decoded condition
    rw [run] at expected
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at expected
    exact ⟨m,condition,Or.inr (Or.inr ⟨mi,rfl,decoded⟩),expected.1,expected.2.1⟩
end Backend.Stock.Proof.ScalarCmp

import FV.Backend.Proof.StockMemoryOffsetEightLoad
import FV.Backend.Proof.StockMemoryOffsetEightStore
import FV.Backend.Proof.StockMemoryIntegerLoadWitness

namespace Backend.Stock.Memory.IntegerRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Original source contexts inhabit the offset8 load contract at every integer width. -/
theorem integer_load_eight_rhs_witness (width : Width) :
    ∃ (ctx : Ctx) (st : State) (trace : Array RuleId),
      ctx.defInst? 0 = none ∧ ctx.valueReg? 0 = some (.vreg 192 .int) ∧
      (evalExpr program (Stock.sem ctx) {} 120 width.root.rhs
        (env3 (.value 0) (.op (.memFlags {trapCode := none})) (.int 8))).run (st,#[]) =
        .ok (some (.regsVec [[(st.base.fresh .int).1]]),
          {(st.mark 0) with base := ((st.base.fresh .int).2.emit
            (.load width.loadOp (st.base.fresh .int).1
              (.unsignedOffset (.vreg 192 .int) 8) {trapCode := none}))},trace) := by
  obtain ⟨ctx,st,oldTrace,parameter,mapped,prior⟩ := integer_load_rhs_witness width
  obtain ⟨trace,actual⟩ := stock_parameter_integer_load_eight_rhs data_program width ctx (cfg := {}) rfl parameter mapped
    {trapCode := none} st #[] 0
  exact ⟨ctx,st,trace,parameter,mapped,actual⟩

end Backend.Stock.Memory.IntegerRoots

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def eightFixture (kind : Kind) : Clif.Function := {
  name := "stock_integer_store_offset_eight"
  sig := {
    params := [⟨.i64,.none,.normal⟩,⟨kind.sourceTy,.none,.normal⟩]
    returns := []
    callConv := some .systemV }
  blocks := [{
    id := 0
    params := [(0,.i64),(1,kind.sourceTy)]
    body := [⟨[],.store kind.sourceOp kind.sourceTy {trapCode := none} 1 0 8⟩]
    term := .ret [] }] }
private def eightBuilt (kind : Kind) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (eightFixture kind)).toOption.getD (sinkCtx,#[],sinkState)
private theorem eightFacts (kind : Kind) :
    Stock.buildCtx (eightFixture kind) = .ok (eightBuilt kind) ∧
    (eightBuilt kind).1.defInst? 0 = none ∧ (eightBuilt kind).1.defInst? 1 = none ∧
    (eightBuilt kind).1.valueReg? 0 = some (.vreg 192 .int) ∧
    (eightBuilt kind).1.valueReg? 1 = some (.vreg 193 .int) := by
  cases kind <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Source-built contexts inhabit the offset8 store RHS and its derived demand guard. -/
theorem integer_store_eight_rhs_witness (kind : Kind) :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st : State) (trace : Array RuleId),
      Stock.buildCtx f = .ok (ctx,ranges,st) ∧
      ctx.defInst? 0 = none ∧ ctx.defInst? 1 = none ∧
      ctx.valueReg? 0 = some (.vreg 192 .int) ∧ ctx.valueReg? 1 = some (.vreg 193 .int) ∧
      (evalExpr program (Stock.sem ctx) {} 140 kind.root.rhs
        (env4 (.value 1) (.value 0) (.op (.memFlags {trapCode := none})) (.int 8))).run (st,#[]) =
        .ok (some (.regsVec []),{(st.mark 0).mark 1 with base := (st.base.emit (.store kind.storeOp (.vreg 193 .int)
            (.unsignedOffset (.vreg 192 .int) 8) {trapCode := none}))},trace) ∧
      DemandAllowed ctx st 1 ∧
      (applyTerm program (Stock.sem ctx) {} 20 25 243
        [.data 46 0 [.data 58 kind.helper.tag [.reg (.vreg 193 .int),
          .data 89 VIdx.AMode.UnsignedOffset [.reg (.vreg 192 .int),.op (.uimm12Scaled 8)],
          .op (.memFlags {trapCode := none})]]]).run (st,#[]) =
        .ok (some (.regsVec []),{st with base := (st.base.emit
          (.store kind.storeOp (.vreg 193 .int) (.unsignedOffset (.vreg 192 .int) 8) {trapCode := none}))},
          (#[].push rule_prelude_lower_522.id).push rule_prelude_lower_535.id) := by
  obtain ⟨built,pointer,value,pointerMapped,valueMapped⟩ := eightFacts kind
  have safe : DemandAllowed (eightBuilt kind).1 (eightBuilt kind).2.2 1 := by
    intro i impossible
    rw [value] at impossible
    cases impossible
  obtain ⟨trace,actual⟩ := stock_parameter_integer_store_eight_rhs data_program kind (eightBuilt kind).1
    (cfg := {}) rfl pointer pointerMapped valueMapped {trapCode := none} (eightBuilt kind).2.2 #[] 0 safe
  have derived := stock_store_eight_rhs_result data_program kind (eightBuilt kind).1
    (cfg := {}) rfl pointer pointerMapped valueMapped {trapCode := none} (eightBuilt kind).2.2 #[] 0 actual
  exact ⟨eightFixture kind,(eightBuilt kind).1,(eightBuilt kind).2.1,(eightBuilt kind).2.2,trace,
    built,pointer,value,pointerMapped,valueMapped,actual,derived.1,
    stock_store_side_effect_eight data_program (eightBuilt kind).1 (cfg := {}) rfl kind
      (.vreg 193 .int) (.vreg 192 .int) {trapCode := none} (eightBuilt kind).2.2 #[] 0⟩

end Backend.Stock.Memory.StoreRoots

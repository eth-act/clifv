import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.StockDivPure
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem zero (ctx : Ctx) (st : State) :
    Stock.externCtor ctx T.writable_zero_reg [] st = .ok (.reg .xzr,st) := by
  rw [stock_ctor_baseOnly ctx T.writable_zero_reg _ st (by decide)]
  rfl
/-- Real32-bit masked flag-test construction preserves the complete Stock state. -/
theorem stock_cmp_test32_builder {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : State) (tr : Array RuleId) (n : Nat) (rx immediate : V) :
    (applyTerm p (Stock.sem ctx) cfg (n+40) 47 424 [.ty (.int 32),rx,immediate]).run (st,tr) =
      .ok (some (.data 47 1 [.data 58 5 [.data 59 5 [],.data 93 0 [],.reg .xzr,rx,immediate]]),
        st,(tr.push rule_inst_1592.id).push rule_inst_3044.id) := by
  have register := zero ctx st
  have size := fun (q : State) (trace : Array RuleId) (fuel : Nat) => ScalarDiv.stock_div_pure_helper hp ctx hc (st := q) (t := 305) (by decide)
    (operand_size_32 hp ctx hc q.base trace fuel (w := 32) (by decide))
  cases hp
  isel_eval [*,rule_inst_3044,sem_ctor,sem_mkData]
/-- A real sparse-register masked test inhabits the full-state builder contract. -/
theorem stock_cmp_test32_builder_witness :
    ∃ out trace,ApplyInternal program (Stock.sem sinkCtx) {} 999 47 424
      [.ty (.int 32),.reg (.vreg 7 .int),.op (.immLogic ⟨255,.size32⟩)]
      (sinkState,#[]) out (sinkState,trace) ∧
      MInst.ofV (.data 58 5 [.data 59 5 [],.data 93 0 [],.reg .xzr,.reg (.vreg 7 .int),
        .op (.immLogic ⟨255,.size32⟩)]) = some (.aluRRImmLogic .andS .size32 .xzr (.vreg 7 .int) ⟨255,.size32⟩) := by
  exact ⟨_,_,stock_cmp_test32_builder data_program sinkCtx (cfg := {}) rfl sinkState #[] 960 _ _,rfl⟩
end Backend.Stock.Proof.ScalarCmp

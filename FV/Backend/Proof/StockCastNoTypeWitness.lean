import FV.Backend.Proof.StockAluSelectedValues
import FV.Backend.Proof.StockCastBaseValues
namespace Backend.Stock.Proof.ScalarCast.Witness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def noTypeFunction (sg : Bool) : Clif.Function := {
  name := "stock_extend_missing_type"
  sig := {params := [],returns := [⟨.i16,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [],body := [⟨[100],.extend (extendOp sg) .i16 7⟩],term := .ret [100]}] }
private def noTypeBuilt (sg : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (noTypeFunction sg)).toOption.getD (sinkCtx,#[],sinkState)
/-- The missing-type match rejection is inhabited by an actual context build
with an undefined operand; it is not an accepted-program execution witness. -/
theorem stock_extend_match_no_type_witness (sg : Bool) :
    ∃ (ctx : Ctx) (ranges : Array (Nat × Nat)) (st : State) (info : IInfo),
      Stock.buildCtx (noTypeFunction sg) = .ok (ctx,ranges,st) ∧ ctx.insts[0]? = some info ∧
      info.resTys.head? = some (.int 16) ∧ info.data = .data 152 29 [.data 151 (extendOpcode sg) [],.value 7] ∧
      ctx.valueType? 7 = none ∧
      (matchRule program (Stock.sem ctx) {} 10 (extendRule sg) [.inst 0]).run (st,#[]) ≠
        .ok (some #[],st,#[]) := by
  let ctx := (noTypeBuilt sg).1
  let info := ctx.insts[0]!
  have built : Stock.buildCtx (noTypeFunction sg) = .ok (noTypeBuilt sg) := by cases sg <;> rfl
  have facts : ctx.insts[0]? = some info ∧
      info.resTys.head? = some (.int 16) ∧ info.data = .data 152 29 [.data 151 (extendOpcode sg) [],.value 7] ∧
      ctx.valueType? 7 = none := by
    refine ⟨?_,?_,?_,?_⟩
    · cases sg <;> rfl
    · cases sg <;> rfl
    · dsimp only [info,ctx]
      cases sg <;> decide +kernel
    · cases sg <;> rfl
  obtain ⟨source,type,data,typed⟩ := facts
  exact ⟨ctx,(noTypeBuilt sg).2.1,(noTypeBuilt sg).2.2,info,built,source,type,data,typed,
    stock_extend_match_no_type data_program ctx sg source type data typed (noTypeBuilt sg).2.2 (noTypeBuilt sg).2.2 #[] #[] 0 #[]⟩
end Backend.Stock.Proof.ScalarCast.Witness

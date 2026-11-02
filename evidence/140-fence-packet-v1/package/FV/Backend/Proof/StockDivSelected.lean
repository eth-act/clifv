import FV.Backend.Proof.StockDivDispatch
import FV.Backend.Proof.StockDivObservations
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
/-- Actual original unsigned source selection derives its canonical match,
guarded dividend preparation, real divisor execution and complete output/state
internally. It needs no chosen-root or helper execution certificate. -/
theorem stock_div_udiv_selected {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.div .udiv ty x y))
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules) :
    if ty.width = 64 then WideUdivReceipt program ctx 999949 x y st next #[] out
    else NarrowUdivReceipt program ctx 999949 x y ty.width st next #[] out := by
  obtain ⟨width,data,type⟩ := stock_div_source_data inv .udiv source clif
  have chosen := stock_selected_div_typed_roots inv .udiv source clif selected
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+2 := ⟨selected.matchFuel-2,by omega⟩
  by_cases wide : ty.width = 64
  · simp only [typedRoots,reduceCtorEq,ite_false,wide,ite_true,List.mem_singleton,baseWideRule] at chosen
    have matched := selected.matchedRun
    have type64 : info.resTys.head? = some (.int 64) := by simpa only [wide] using type
    rw [chosen,fuelEq] at matched
    change (matchRule program (Stock.sem ctx) {} (m+2) (baseWideRule .udiv) [.inst i]).run (st,#[]) =
      .ok (some selected.env,selected.matched,selected.matchTrace) at matched
    rw [stock_div_base_wide_match data_program ctx .udiv source type64 data st #[] m] at matched
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
    obtain ⟨envEq,stateEq,traceEq⟩ := matched
    have rhs := selected.rhsRun
    rw [chosen,← envEq,← stateEq,← traceEq] at rhs
    change (evalExpr program (Stock.sem ctx) {} (999949+50) rule_lower_1116.rhs
      (baseWideEnv .udiv x y)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
    simp only [wide,ite_true]
    exact stock_div_udiv_wide_observed data_program ctx (by decide) rhs
  · simp only [typedRoots,reduceCtorEq,ite_false,wide,List.mem_singleton,baseNarrowRule] at chosen
    have narrow : ty.width ≤ 32 := by omega
    have matched := selected.matchedRun
    rw [chosen,fuelEq] at matched
    change (matchRule program (Stock.sem ctx) {} (m+2) (baseNarrowRule .udiv) [.inst i]).run (st,#[]) =
      .ok (some selected.env,selected.matched,selected.matchTrace) at matched
    rw [stock_div_base_narrow_match data_program ctx .udiv source type narrow data st #[] m] at matched
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
    obtain ⟨envEq,stateEq,traceEq⟩ := matched
    have rhs := selected.rhsRun
    rw [chosen,← envEq,← stateEq,← traceEq] at rhs
    change (evalExpr program (Stock.sem ctx) {} (999949+50) rule_lower_1119.rhs
      (baseNarrowEnv .udiv ty.width x y)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
    simp only [wide,ite_false]
    exact stock_div_udiv_narrow_observed data_program ctx (by decide) (by omega) rhs
theorem stock_div_rem_selected {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (signed : Bool)
    {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.div (if signed then .srem else .urem) ty x y))
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules) :
    if ty.width = 64 then WideRemReceipt program ctx signed 999899 x y st next #[] out
    else NarrowRemReceipt program ctx signed 999899 x y ty.width st next #[] out := by
  obtain ⟨width,data,type⟩ := stock_div_source_data inv (if signed then .srem else .urem) source clif
  have chosen := stock_selected_div_typed_roots inv (if signed then .srem else .urem) source clif selected
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+2 := ⟨selected.matchFuel-2,by omega⟩
  have nonsigned : (if signed then .srem else .urem : Clif.DivOp) ≠ .sdiv := by cases signed <;> decide
  by_cases wide : ty.width = 64
  · simp only [typedRoots,nonsigned,ite_false,wide,ite_true,List.mem_singleton] at chosen
    have matched := selected.matchedRun
    have type64 : info.resTys.head? = some (.int 64) := by simpa only [wide] using type
    rw [chosen,fuelEq] at matched
    change (matchRule program (Stock.sem ctx) {} (m+2) (baseWideRule (if signed then .srem else .urem)) [.inst i]).run (st,#[]) =
      .ok (some selected.env,selected.matched,selected.matchTrace) at matched
    rw [stock_div_base_wide_match data_program ctx (if signed then .srem else .urem) source type64 data st #[] m] at matched
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
    obtain ⟨envEq,stateEq,traceEq⟩ := matched
    have rhs := selected.rhsRun
    rw [chosen,← envEq,← stateEq,← traceEq] at rhs
    change (evalExpr program (Stock.sem ctx) {} (999899+100) (baseWideRule (if signed then .srem else .urem)).rhs
      (baseWideEnv (if signed then .srem else .urem) x y)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
    simp only [wide,ite_true]
    exact stock_div_rem_wide_observed data_program ctx signed (by decide) rhs
  · simp only [typedRoots,nonsigned,ite_false,wide,List.mem_singleton] at chosen
    have narrow : ty.width ≤ 32 := by omega
    have matched := selected.matchedRun
    rw [chosen,fuelEq] at matched
    change (matchRule program (Stock.sem ctx) {} (m+2) (baseNarrowRule (if signed then .srem else .urem)) [.inst i]).run (st,#[]) =
      .ok (some selected.env,selected.matched,selected.matchTrace) at matched
    rw [stock_div_base_narrow_match data_program ctx (if signed then .srem else .urem) source type narrow data st #[] m] at matched
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
    obtain ⟨envEq,stateEq,traceEq⟩ := matched
    have rhs := selected.rhsRun
    rw [chosen,← envEq,← stateEq,← traceEq] at rhs
    change (evalExpr program (Stock.sem ctx) {} (999899+100) (baseNarrowRule (if signed then .srem else .urem)).rhs
      (baseNarrowEnv (if signed then .srem else .urem) ty.width x y)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
    simp only [wide,ite_false]
    exact stock_div_rem_narrow_observed data_program ctx signed (by decide) (by omega) rhs
end Backend.Stock.Proof.ScalarDiv

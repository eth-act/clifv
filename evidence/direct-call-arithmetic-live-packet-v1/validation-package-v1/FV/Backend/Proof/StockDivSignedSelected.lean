import FV.Backend.Proof.StockDivSignedObservations
import FV.Backend.Proof.StockDivSafeObservations
import FV.Backend.Proof.StockDivSafeMatchObserved
import FV.Backend.Proof.StockDivDispatch
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
def SignedSelectedReceipt (ctx : Ctx) (x y w : Nat) (st next : State) (out : V) : Prop :=
  (if w = 64 then GeneralSdivReceipt program ctx true 999899 x y 64 st next #[] out
    else GeneralSdivReceipt program ctx false 999899 x y w st next #[] out) ∨
  (∃ j constant i,ctx.defInst? y = some j ∧ ctx.insts[j]? = some constant ∧
    constant.data = .data 152 35 [.data 151 57 [],.int i] ∧
    (u64 i % 2^((CTy.int w).bytes*8) ≠ 0 ∧ u64 i % 2^((CTy.int w).bytes*8) ≠ 2^((CTy.int w).bytes*8)-1) ∧
    SafeSdivReceipt program ctx (w == 64) 999949 x w i (u64 i % 2^((CTy.int w).bytes*8)) st next #[] out)
/-- Actual original signed division selection derives its general guarded or
safe looked-through literal path, canonical environment, helper executions and
complete output/state internally, retaining the original source conditions. -/
theorem stock_div_sdiv_selected {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {id x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[id]? = some info) (clif : info.clif = some (.div .sdiv ty x y))
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx id st out next rules) : SignedSelectedReceipt ctx x y ty.width st next out := by
  obtain ⟨width,data,type⟩ := stock_div_source_data inv .sdiv source clif
  have chosen := stock_selected_div_typed_roots inv .sdiv source clif selected
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  unfold SignedSelectedReceipt
  by_cases wide : ty.width = 64
  · simp only [typedRoots,ite_true,wide,List.mem_cons,List.not_mem_nil,or_false] at chosen
    have type64 : info.resTys.head? = some (.int 64) := by simpa only [wide] using type
    rcases chosen with general | safe
    · left
      simp only [wide,ite_true]
      obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel=m+2 := ⟨selected.matchFuel-2,by omega⟩
      have matched := selected.matchedRun
      rw [general,fuelEq] at matched
      change (matchRule program (Stock.sem ctx) {} (m+2) (baseWideRule .sdiv) [.inst id]).run (st,#[]) =
        .ok (some selected.env,selected.matched,selected.matchTrace) at matched
      rw [stock_div_base_wide_match data_program ctx .sdiv source type64  data st #[] m] at matched
      simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
      obtain ⟨envEq,stateEq,traceEq⟩ := matched
      have rhs := selected.rhsRun
      rw [general,← envEq,← stateEq,← traceEq] at rhs
      change (evalExpr program (Stock.sem ctx) {} (999899+100) rule_lower_1145.rhs
        (baseWideEnv .sdiv x y)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
      exact stock_div_sdiv_wide_observed data_program ctx (by decide)  rhs
    · right
      obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel=m+10 := ⟨selected.matchFuel-10,by omega⟩
      have matched := selected.matchedRun
      rw [safe,fuelEq] at matched
      have observed := stock_div_safe_wide_match_observed data_program inv  source type64 data matched
      obtain ⟨j,constant,i,defined,found,literal,guard,envEq,stateEq⟩ := observed
      have states := Prod.mk.inj stateEq
      have rhs := selected.rhsRun
      rw [safe,envEq,states.1,states.2] at rhs
      change (evalExpr program (Stock.sem ctx) {} (999949+50) rule_lower_1163.rhs
        (safeWideEnv x i (u64 i % 2^((CTy.int 64).bytes*8)))).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
      have receipt := stock_div_sdiv_safe_wide_observed data_program ctx (by decide)  rhs
      simp only [wide]
      exact ⟨j,constant,i,defined,found,literal,guard,receipt⟩
  · simp only [typedRoots,ite_true,wide,ite_false,List.mem_cons,List.not_mem_nil,or_false] at chosen
    have narrow : ty.width ≤ 32 := by omega
    rcases chosen with general | safe
    · left
      simp only [wide,ite_false]
      obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel=m+2 := ⟨selected.matchFuel-2,by omega⟩
      have matched := selected.matchedRun
      rw [general,fuelEq] at matched
      change (matchRule program (Stock.sem ctx) {} (m+2) (baseNarrowRule .sdiv) [.inst id]).run (st,#[]) =
        .ok (some selected.env,selected.matched,selected.matchTrace) at matched
      rw [stock_div_base_narrow_match data_program ctx .sdiv source type narrow data st #[] m] at matched
      simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
      obtain ⟨envEq,stateEq,traceEq⟩ := matched
      have rhs := selected.rhsRun
      rw [general,← envEq,← stateEq,← traceEq] at rhs
      change (evalExpr program (Stock.sem ctx) {} (999899+100) rule_lower_1153.rhs
        (baseNarrowEnv .sdiv ty.width x y)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
      exact stock_div_sdiv_narrow_observed data_program ctx (by decide) (by omega) rhs
    · right
      obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel=m+10 := ⟨selected.matchFuel-10,by omega⟩
      have matched := selected.matchedRun
      rw [safe,fuelEq] at matched
      have observed := stock_div_safe_narrow_match_observed data_program inv narrow source type data matched
      obtain ⟨j,constant,i,defined,found,literal,guard,envEq,stateEq⟩ := observed
      have states := Prod.mk.inj stateEq
      have rhs := selected.rhsRun
      rw [safe,envEq,states.1,states.2] at rhs
      change (evalExpr program (Stock.sem ctx) {} (999949+50) rule_lower_1167.rhs
        (safeNarrowEnv ty.width x i (u64 i % 2^((CTy.int ty.width).bytes*8)))).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
      have receipt := stock_div_sdiv_safe_narrow_observed data_program ctx (by decide) (by omega) rhs
      have flag : (ty.width == 64) = false := beq_eq_false_iff_ne.mpr wide
      rw [flag]
      exact ⟨j,constant,i,defined,found,literal,guard,receipt⟩
end Backend.Stock.Proof.ScalarDiv

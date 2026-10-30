import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.StockSelectConditionOriginValues
namespace Backend.Stock.Proof.ScalarSelect.ConditionOriginWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def function : Clif.Function := {
  name := "stock_select_comparison_origin"
  sig := {params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64),(31,.i64)],body := [⟨[100],.icmp .ult .i64 7 31⟩,
    ⟨[101],.extend .uextend .i64 100⟩,⟨[102],.select .i64 101 7 31⟩],term := .ret [102]}] }
private def built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
private def frame : Clif.Frame := {
  func := function
  regs := fun x => if x = 7 then some ⟨.i64,7⟩ else if x = 31 then some ⟨.i64,9⟩ else
    if x = 100 then some ⟨.i8,1⟩ else if x = 101 then some ⟨.i64,1⟩ else none
  slots := [],body := [⟨[102],.select .i64 101 7 31⟩],term := .ret [102] }
private theorem scope : LowerScope function := lowerScope_of (by rfl)
private theorem build : Stock.buildCtx function = .ok built := rfl
private theorem dfg : DFGCons built.1 frame := by
  constructor
  · intro x j info cl value defined found source pure lookup
    by_cases seven : x = 7
    · subst x; change none = some j at defined; cases defined
    · by_cases thirtyone : x = 31
      · subst x; change none = some j at defined; cases defined
      · by_cases hundred : x = 100
        · subst x
          change some 0 = some j at defined
          cases defined
          cases found
          cases source
          simp only [frame,show (100:Nat) ≠ 7 by decide,show (100:Nat) ≠ 31 by decide,ite_false,ite_true,Option.some.injEq] at lookup
          subst value
          exact ⟨[⟨.i8,1⟩],fun _ => rfl,rfl⟩
        · by_cases hundredone : x = 101
          · subst x
            change some 1 = some j at defined
            cases defined
            cases found
            cases source
            simp only [frame,show (101:Nat) ≠ 7 by decide,show (101:Nat) ≠ 31 by decide,
              show (101:Nat) ≠ 100 by decide,ite_false,ite_true,Option.some.injEq] at lookup
            subst value
            exact ⟨[⟨.i64,1⟩],fun _ => rfl,rfl⟩
          · simp [frame,seven,thirtyone,hundred,hundredone] at lookup
  · intro x ty value typed lookup
    by_cases seven : x = 7
    · subst x; change some (.int 64) = some ty at typed; cases typed; cases lookup; rfl
    · by_cases thirtyone : x = 31
      · subst x; change some (.int 64) = some ty at typed; cases typed
        simp only [frame,show (31:Nat) ≠ 7 by decide,ite_false,ite_true,Option.some.injEq] at lookup
        subst value; rfl
      · by_cases hundred : x = 100
        · subst x; change some (.int 8) = some ty at typed; cases typed
          simp only [frame,show (100:Nat) ≠ 7 by decide,show (100:Nat) ≠ 31 by decide,ite_false,ite_true,Option.some.injEq] at lookup
          subst value; rfl
        · by_cases hundredone : x = 101
          · subst x; change some (.int 64) = some ty at typed; cases typed
            simp only [frame,show (101:Nat) ≠ 7 by decide,show (101:Nat) ≠ 31 by decide,
              show (101:Nat) ≠ 100 by decide,ite_false,ite_true,Option.some.injEq] at lookup
            subst value; rfl
          · simp [frame,seven,thirtyone,hundred,hundredone] at lookup
/-- Direct and zero-extended original comparisons inhabit DFG-derived truth
and original source operand reads, with no materialized machine condition premise. -/
theorem stock_select_comparison_origin_witness (extended : Bool) :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st : State) (fr : Clif.Frame)
      (c : Nat) (value : Clif.Val),LowerScope f ∧ Stock.buildCtx f = .ok (ctx,ranges,st) ∧
      MappedCtxInv f ctx ∧ DFGCons ctx fr ∧ SelectComparisonOrigin ctx c .ult .i64 7 31 ∧
      fr.regs c = some value ∧
      ∃ u v : BitVec 64,fr.getAs 7 .i64 = .ok u ∧ fr.getAs 31 .i64 = .ok v ∧
        Clif.Sem.truthy value.bits = Clif.Sem.intcc .ult u v := by
  let c := if extended then 101 else 100
  let value : Clif.Val := if extended then ⟨.i64,1⟩ else ⟨.i8,1⟩
  have origin : SelectComparisonOrigin built.1 c .ult .i64 7 31 := by
    cases extended
    · exact Or.inl rfl
    · exact Or.inr ⟨.i64,100,rfl,rfl⟩
  have read : frame.regs c = some value := by cases extended <;> rfl
  exact ⟨function,built.1,built.2.1,built.2.2,frame,c,value,scope,build,buildCtx_mappedInv scope build,dfg,
    origin,read,stock_select_comparison_origin_values dfg origin read⟩
end Backend.Stock.Proof.ScalarSelect.ConditionOriginWitness

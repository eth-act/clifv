import FV.Backend.Proof.IselCmpMinMax
import FV.Backend.Proof.StockMinMaxRegisterValues
import FV.Backend.Proof.StockMinMaxRegisterRuns
namespace Backend.Stock.Proof.ScalarSelect.MinMaxRegisterWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
open Backend.Stock.Proof.ScalarSelect.MinMaxRegisterFixture
private abbrev operation := minmaxOperation
private abbrev comparison := minmaxComparison
private abbrev function := minmaxFunction
private abbrev built := minmaxBuilt
private def frame (unsigned maximum : Bool) : Clif.Frame := {
  func := function unsigned maximum,regs := fun x => if x = 7 then some (.ofInt .i64 (-7)) else if x = 31 then some (.ofInt .i64 9) else none,
  slots := [],body := [⟨[100],.binary (operation unsigned maximum) .i64 7 31⟩],term := .ret [100] }
private def aliases : Array (Option Nat) := ((Array.replicate 195 none).setIfInBounds 192 (some 1)).setIfInBounds 193 (some 2)
private def registers (k : Nat) : CV := BitVec.ofNat 128 (2^100 + if k = 1 then (BitVec.ofInt 64 (-7)).toNat else 9)
private theorem build (unsigned maximum : Bool) : Stock.buildCtx (function unsigned maximum) = .ok (built unsigned maximum) :=
  by cases unsigned <;> cases maximum <;> rfl
private theorem scope (unsigned maximum : Bool) : LowerScope (function unsigned maximum) :=
  lowerScope_of (by cases unsigned <;> cases maximum <;> decide +kernel)
private theorem held (unsigned maximum : Bool) (st : State) : ValuesHeld (Demanded st) (built unsigned maximum).1 (frame unsigned maximum)
    (fun key => registers (aliasNum aliases key)) := by
  intro x needed value lookup
  by_cases seven : x = 7
  · subst x
    simp only [frame,ite_true,Option.some.injEq] at lookup
    subst value
    refine ⟨192,?_,?_⟩
    · cases unsigned <;> cases maximum <;> rfl
    · unfold VHolds
      decide +kernel
  · by_cases thirtyone : x = 31
    · subst x
      simp only [frame,show (31:Nat) ≠ 7 by decide,ite_false,ite_true,Option.some.injEq] at lookup
      subst value
      refine ⟨193,?_,?_⟩
      · cases unsigned <;> cases maximum <;> rfl
      · unfold VHolds
        decide +kernel
    · simp [frame,seven,thirtyone] at lookup
private theorem safe (unsigned maximum : Bool) (st : State) (x : Nat) (input : x = 7 ∨ x = 31) :
    DemandAllowed (built unsigned maximum).1 st x := by
  intro i h
  rcases input with rfl | rfl
  all_goals cases unsigned <;> cases maximum
  all_goals change none = some i at h
  all_goals cases h
/-- All four original64-bit min/max functions have complete Stock.lower runs,
and inhabit actual5128-emitter/659 source-value composition with negative input,
nonidentity aliases and dirty upper bits. The helper runs are not yet identified
with the retained records of those complete runs. -/
theorem stock_minmax_register_source_witness (unsigned maximum : Bool) :
    (∃ result,Stock.lower (function unsigned maximum) = .ok result) ∧
    ∃ condition middle emitTrace out next trace nx ny d,
      (evalExpr program (Stock.sem (built unsigned maximum).1) {} 1000 rule_inst_5128.rhs
        #[some (.data 145 (ccIdx (comparison unsigned maximum)) []),some (.value 7),some (.ty (.int 64)),some (.value 31)]).run
        ((built unsigned maximum).2.2,#[]) = .ok (some condition,middle,emitTrace) ∧
      ApplyInternal program (Stock.sem (built unsigned maximum).1) {} 999 22 659
        [.ty (.int 64),condition,.value 7,.value 31] (middle,emitTrace) out (next,trace) ∧
      out = .regs [.vreg d .int] ∧
      Frag (built unsigned maximum).2.2.base next.base
        [.aluRRR .subS .size64 .xzr (.vreg nx .int) (.vreg ny .int),
          .csel (.vreg d .int) (.vreg nx .int) (.vreg ny .int) (condOf (comparison unsigned maximum))] ∧
      ∀ world,Runs (fun _ => True) ispec
        ([MInst.aluRRR .subS .size64 .xzr (.vreg nx .int) (.vreg ny .int),
          .csel (.vreg d .int) (.vreg nx .int) (.vreg ny .int) (condOf (comparison unsigned maximum))].map
          (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) registers world
        (fun ρ' _ => VHolds ⟨.i64,Clif.Sem.binary (operation unsigned maximum) (BitVec.ofInt 64 (-7)) 9⟩ (ρ' d) ∧
          ∀ k,k ≠ d → ρ' k = registers k) := by
  have complete : ∃ result,Stock.lower (function unsigned maximum) = .ok result := by
    have success := stock_minmax_register_driver_success unsigned maximum
    cases actual : Stock.lower (function unsigned maximum) with
    | error e => rw [actual] at success; cases success
    | ok result => exact ⟨result,rfl⟩
  have mapX : (built unsigned maximum).1.valueReg? 7 = some (.vreg 192 .int) := by cases unsigned <;> cases maximum <;> rfl
  have mapY : (built unsigned maximum).1.valueReg? 31 = some (.vreg 193 .int) := by cases unsigned <;> cases maximum <;> rfl
  have emitter := stock_cmp_register_rhs data_program (built unsigned maximum).1 (cfg := {}) rfl
    (comparison unsigned maximum) .size64 (built unsigned maximum).2.2 #[] 900 7 31 (.vreg 192 .int) (.vreg 193 .int)
    mapX mapY (safe unsigned maximum _ _ (Or.inl rfl)) (safe unsigned maximum _ _ (Or.inr rfl))
  have decoded : MInst.ofV (.data 58 2 [.data 59 10 [],.data 93 1 [],.reg .xzr,.reg (.vreg 192 .int),.reg (.vreg 193 .int)]) =
      some (.aluRRR .subS .size64 .xzr (.vreg 192 .int) (.vreg 193 .int)) := rfl
  have consumer := stock_select_flags_run data_program (built unsigned maximum).1 (cfg := {}) rfl (w := 64) (by simp)
    (((built unsigned maximum).2.2.mark 7).mark 31)
    ((#[].push rule_inst_1593.id).push rule_inst_2767.id) 780 (condOf (comparison unsigned maximum)) decoded mapX mapY
    (safe unsigned maximum _ _ (Or.inl rfl)) (safe unsigned maximum _ _ (Or.inr rfl))
  have actual : ApplyInternal program (Stock.sem (built unsigned maximum).1) {} 999 22 659 _ _ _ _ := consumer
  have extent : ∀ z r,(built unsigned maximum).1.valueReg? z = some r → z < (built unsigned maximum).2.2.demand.size := by
    intro z r mapped
    have sizeEq : (built unsigned maximum).1.valReg.size = (built unsigned maximum).2.2.demand.size := by cases unsigned <;> cases maximum <;> rfl
    rw [← sizeEq]
    by_cases bound : z < (built unsigned maximum).1.valReg.size
    · exact bound
    · unfold Ctx.valueReg? at mapped
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt bound)] at mapped
      cases mapped
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨nx,ny,d,mappedX,mappedY,output,lower,upper,fragment,execution⟩ :=
    stock_select_register_emitter_source_values data_program (buildCtx_mappedInv (scope unsigned maximum) (build unsigned maximum))
      (comparison unsigned maximum) (ty := .i64) (u := BitVec.ofInt 64 (-7)) (v := 9) (by simp [Clif.Ty.width]) (fr := frame unsigned maximum)
      (by rfl) (by rfl) (by decide) emitter actual self (aliases := aliases) (ρ := registers)
      (by cases unsigned <;> cases maximum <;> decide +kernel) extent (held unsigned maximum _)
  have semantics : (if Clif.Sem.intcc (comparison unsigned maximum) (BitVec.ofInt 64 (-7)) 9
      then BitVec.ofInt 64 (-7) else 9) = Clif.Sem.binary (operation unsigned maximum) (BitVec.ofInt 64 (-7)) 9 := by
    cases unsigned <;> cases maximum
    · exact (minmax_sem 64 _ _).2.1
    · exact (minmax_sem 64 _ _).2.2.2
    · exact (minmax_sem 64 _ _).1
    · exact (minmax_sem 64 _ _).2.2.1
  refine ⟨complete,_,_,_,_,_,_,nx,ny,d,emitter,actual,output,fragment,?_⟩
  intro world
  apply (execution world).imp
  intro ρ' _ _ result
  refine ⟨?_,result.2⟩
  have value := result.1
  change (ρ' d).setWidth 64 = (if Clif.Sem.intcc (comparison unsigned maximum) (BitVec.ofInt 64 (-7)) 9
    then BitVec.ofInt 64 (-7) else 9) at value
  exact value.trans semantics
end Backend.Stock.Proof.ScalarSelect.MinMaxRegisterWitness

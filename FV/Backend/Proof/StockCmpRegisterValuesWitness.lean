module

public import FV.Backend.Proof.StockCmpRegisterValues

@[expose] public section

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def sourceTy : OperandSize → Clif.Ty | .size32 => .i32 | .size64 => .i64
private def function (sz : OperandSize) (cc : Clif.IntCC) : Clif.Function := {
  name := "stock_cmp_register_source_values"
  sig := {params := [⟨sourceTy sz,.none,.normal⟩,⟨sourceTy sz,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,sourceTy sz),(31,sourceTy sz)],body := [⟨[100],.icmp cc (sourceTy sz) 7 31⟩],term := .ret [100]}] }
private def built (sz : OperandSize) (cc : Clif.IntCC) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function sz cc)).toOption.getD (sinkCtx,#[],sinkState)
private def aliases : Array (Option Nat) :=
  ((Array.replicate 194 none).setIfInBounds 192 (some 1)).setIfInBounds 193 (some 3)
private def frame (sz : OperandSize) (cc : Clif.IntCC) : Clif.Frame := {
  func := function sz cc
  regs := fun z => if z = 7 then some ⟨sourceTy sz,BitVec.intMin (sourceTy sz).width⟩ else
    if z = 31 then some ⟨sourceTy sz,BitVec.allOnes (sourceTy sz).width⟩ else none
  slots := [],body := [⟨[100],.icmp cc (sourceTy sz) 7 31⟩],term := .ret [100] }
private def regs (sz : OperandSize) (key : Nat) : CV :=
  if key = 1 then BitVec.ofNat 128 (2^100+(BitVec.intMin (sourceTy sz).width).toNat)
  else if key = 3 then BitVec.ofNat 128 (2^100+(BitVec.allOnes (sourceTy sz).width).toNat) else 0
private theorem scope (sz : OperandSize) (cc : Clif.IntCC) : LowerScope (function sz cc) :=
  lowerScope_of (by cases sz <;> rfl)
private theorem built_run (sz : OperandSize) (cc : Clif.IntCC) : Stock.buildCtx (function sz cc) = .ok (built sz cc) := by
  cases sz <;> rfl
private theorem values (sz : OperandSize) (cc : Clif.IntCC) (st : State) :
    ValuesHeld (Demanded st) (built sz cc).1 (frame sz cc) (fun key => regs sz (aliasNum aliases key)) := by
  intro z needed value lookup
  by_cases first : z = 7
  · subst z
    simp only [frame,ite_true,Option.some.injEq] at lookup
    subst value
    refine ⟨192,?_,?_⟩
    · cases sz <;> rfl
    · unfold VHolds
      cases sz <;> decide +kernel
  · by_cases second : z = 31
    · subst z
      simp only [frame,first,ite_false,ite_true,Option.some.injEq] at lookup
      subst value
      refine ⟨193,?_,?_⟩
      · cases sz <;> rfl
      · unfold VHolds
        cases sz <;> decide +kernel
    · simp only [frame,first,second,ite_false] at lookup
      cases lookup
attribute [local irreducible] built
/-- Both original machine-sized source types and all ten conditions inhabit the
real guarded emitter/condition composition with dirty upper bits, nonidentity
final aliases, original getters and a complete outside-result machine frame. -/
theorem stock_cmp_register_condition_source_witness (sz : OperandSize) (cc : Clif.IntCC) :
    ∃ condition middle emitTrace out next trace nx ny d,
      (evalExpr program (Stock.sem (built sz cc).1) {} 1000 rule_inst_5128.rhs
        #[some (.data 145 (ccIdx cc) []),some (.value 7),some (.ty (.int sz.bits)),some (.value 31)]).run
        ((built sz cc).2.2,#[]) = .ok (some condition,middle,emitTrace) ∧
      ApplyInternal program (Stock.sem (built sz cc).1) {} 999 27 715 [condition]
        (middle,emitTrace) out (next,trace) ∧
      out = .reg (.vreg d .int) ∧
      Frag (built sz cc).2.2.base next.base [.aluRRR .subS sz .xzr (.vreg nx .int) (.vreg ny .int),.cset (.vreg d .int) (condOf cc)] ∧
      ∀ world,Runs (fun _ => True) ispec ([MInst.aluRRR .subS sz .xzr (.vreg nx .int) (.vreg ny .int),.cset (.vreg d .int) (condOf cc)].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) (regs sz) world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc (BitVec.intMin (sourceTy sz).width) (BitVec.allOnes (sourceTy sz).width))⟩ (ρ' d) ∧
          ∀ k,k ≠ d → ρ' k = regs sz k) := by
  have inv := buildCtx_mappedInv (scope sz cc) (built_run sz cc)
  have mapX : (built sz cc).1.valueReg? 7 = some (.vreg 192 .int) := by unfold built; cases sz <;> rfl
  have mapY : (built sz cc).1.valueReg? 31 = some (.vreg 193 .int) := by unfold built; cases sz <;> rfl
  have safeX : DemandAllowed (built sz cc).1 (built sz cc).2.2 7 := by
    intro i impossible
    have absent : (built sz cc).1.defInst? 7 = none := by unfold built; cases sz <;> rfl
    rw [absent] at impossible; cases impossible
  have safeY : DemandAllowed (built sz cc).1 ((built sz cc).2.2.mark 7) 31 := by
    intro i impossible
    have absent : (built sz cc).1.defInst? 31 = none := by unfold built; cases sz <;> rfl
    rw [absent] at impossible; cases impossible
  have emitter := stock_cmp_register_rhs data_program (built sz cc).1 (cfg := {}) rfl cc sz (built sz cc).2.2 #[] 900 7 31
    (.vreg 192 .int) (.vreg 193 .int) mapX mapY safeX safeY
  have decoded : MInst.ofV (.data 58 2 [.data 59 10 [],.data 93 (if sz = .size32 then 0 else 1) [],
      .reg .xzr,.reg (.vreg 192 .int),.reg (.vreg 193 .int)]) = some (.aluRRR .subS sz .xzr (.vreg 192 .int) (.vreg 193 .int)) := by cases sz <;> rfl
  obtain ⟨trace,actual⟩ := stock_cmp_condition_flags data_program (built sz cc).1 (cfg := {}) rfl
    (((built sz cc).2.2.mark 7).mark 31)
    (((#[] : Array RuleId).push (if sz = .size32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2767.id) 880 decoded (condOf cc)
  have conditionCall : ApplyInternal program (Stock.sem (built sz cc).1) {} 999 27 715 _ _ _ _ := actual
  have size : szOf (sourceTy sz).width = sz := by cases sz <;> rfl
  have width : (sourceTy sz).width = 32 ∨ (sourceTy sz).width = 64 := by cases sz <;> simp [sourceTy,Clif.Ty.width]
  have getX : (frame sz cc).getAs 7 (sourceTy sz) = .ok (BitVec.intMin (sourceTy sz).width) := by cases sz <;> rfl
  have getY : (frame sz cc).getAs 31 (sourceTy sz) = .ok (BitVec.allOnes (sourceTy sz).width) := by cases sz <;> rfl
  have sourceEmitter := emitter
  rw [show sz.bits = (szOf (sourceTy sz).width).bits from congrArg OperandSize.bits size.symm] at sourceEmitter
  obtain ⟨nx,ny,d,mappedX,mappedY,output,lower,upper,fragment,execution⟩ := stock_cmp_register_condition_source_values data_program inv cc width getX getY
    (by decide) sourceEmitter conditionCall (F := fun _ => True) (isem := ispec)
    (fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩) (aliases := aliases) (ρ := regs sz)
    (by
      have next : (built sz cc).2.2.base.nextVreg = 195 := by unfold built; cases sz <;> rfl
      rw [next]
      decide +kernel)
    (fun z r mapped => by
      have sizeEq : (built sz cc).1.valReg.size = (built sz cc).2.2.demand.size := by unfold built; cases sz <;> rfl
      rw [← sizeEq]
      by_cases bound : z < (built sz cc).1.valReg.size
      · exact bound
      · unfold Ctx.valueReg? at mapped
        rw [Array.getElem?_eq_none (Nat.le_of_not_lt bound)] at mapped
        cases mapped)
    (values sz cc _)
  rw [size] at fragment execution
  exact ⟨_,_,_,_,_,trace,nx,ny,d,emitter,conditionCall,output,fragment,execution⟩
end Backend.Stock.Proof.ScalarCmp

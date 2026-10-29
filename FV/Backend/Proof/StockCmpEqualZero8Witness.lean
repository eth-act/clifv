module

public import FV.Backend.Proof.StockCmpEqualZero8Values

@[expose] public section

namespace Backend.Stock.Proof.ScalarCmp.EqualZero8HelperWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def function : Clif.Function := {
  name := "stock_zero_original_parameter"
  sig := {params := [⟨.i8,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i8)],body := [],term := .ret [7]}] }
private def built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
private def word (zero : Bool) : BitVec 8 := if zero then 0 else 7
private def frame (zero : Bool) : Clif.Frame := {
  func := function,regs := fun x => if x = 7 then some ⟨.i8,word zero⟩ else none,
  slots := [],body := [],term := .ret [7] }
private def aliases : Array (Option Nat) := (Array.replicate 193 none).setIfInBounds 192 (some 1)
private def regs (zero : Bool) (_ : Nat) : CV := BitVec.ofNat 128 (2^100+(word zero).toNat)
private theorem scope : LowerScope function := lowerScope_of (by rfl)
private theorem build : Stock.buildCtx function = .ok built := rfl
private theorem held (zero : Bool) (st : State) :
    ValuesHeld (Demanded st) built.1 (frame zero) (fun key => regs zero (aliasNum aliases key)) := by
  intro x needed v lookup
  by_cases seven : x = 7
  · subst x
    simp only [frame,ite_true,Option.some.injEq] at lookup
    subst v
    refine ⟨192,rfl,?_⟩
    unfold VHolds
    cases zero <;> decide +kernel
  · simp [frame,seven] at lookup
attribute [local irreducible] built
/-- Both boolean outcomes inhabit actual4988 RHS/715 source-value execution on an
accepted original sparse-ID function with dirty bits and a nonidentity final alias. -/
theorem stock_cmp_equal_zero8_rhs_source_witness (zero : Bool) :
    ∃ condition middle emitTrace out next trace d,
      (evalExpr program (Stock.sem built.1) {} 1000 rule_inst_4988.rhs #[some (.value 7)]).run
        (built.2.2,#[]) = .ok (some condition,middle,emitTrace) ∧
      ApplyInternal program (Stock.sem built.1) {} 999 123 649 [condition]
        (middle,emitTrace) (.data 123 2 [.data 47 1 [.data 58 5 [.data 59 5 [],.data 93 0 [],.reg .xzr,
          .reg (.vreg 192 .int),.op (.immLogic ⟨255,.size32⟩)]],.data 96 0 []]) (middle,emitTrace.push rule_inst_4956.id) ∧
      ApplyInternal program (Stock.sem built.1) {} 999 27 715 [.data 123 2 [.data 47 1 [.data 58 5 [.data 59 5 [],.data 93 0 [],.reg .xzr,
          .reg (.vreg 192 .int),.op (.immLogic ⟨255,.size32⟩)]],.data 96 0 []]]
        (middle,emitTrace.push rule_inst_4956.id) out (next,trace) ∧ out = .reg (.vreg d .int) ∧
      ∀ world,Runs (fun _ => True) ispec ([MInst.aluRRImmLogic .andS .size32 .xzr (.vreg 192 .int) ⟨255,.size32⟩,.cset (.vreg d .int) .eq].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) (regs zero) world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 zero⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = regs zero k) := by
  have type : built.1.valueType? 7 = some (.int 8) := by unfold built; rfl
  have mapped192 : built.1.valueReg? 7 = some (.vreg 192 .int) := by unfold built; rfl
  have safe : DemandAllowed built.1 built.2.2 7 := by
    intro j impossible
    have parameter : built.1.defInst? 7 = none := by unfold built; rfl
    rw [parameter] at impossible; cases impossible
  have run := stock_cmp_nonzero8_rhs data_program built.1 (cfg := {}) rfl 7 (.vreg 192 .int)
    built.2.2 #[] 900 mapped192 safe
  let middle := built.2.2.mark 7
  let emitTrace : Array RuleId := (#[] : Array RuleId).push rule_inst_1592.id |>.push rule_inst_3044.id
  let condition : V := .data 123 2 [.data 47 1 [.data 58 5 [.data 59 5 [],.data 93 0 [],.reg .xzr,
    .reg (.vreg 192 .int),.op (.immLogic ⟨255,.size32⟩)]],.data 96 1 []]
  obtain ⟨trace,conditionRun⟩ := stock_cmp_condition_flags data_program built.1 (cfg := {}) rfl middle (emitTrace.push rule_inst_4956.id) 880
    (ofV_tst .xzr (.vreg 192 .int) ⟨255,.size32⟩) .eq
  have inversion : ApplyInternal program (Stock.sem built.1) {} 999 123 649 [condition]
      (middle,emitTrace) (.data 123 2 [.data 47 1 [.data 58 5 [.data 59 5 [],.data 93 0 [],.reg .xzr,
          .reg (.vreg 192 .int),.op (.immLogic ⟨255,.size32⟩)]],.data 96 0 []]) (middle,emitTrace.push rule_inst_4956.id) :=
    stock_cmp_flag_invert data_program built.1 (cfg := {}) rfl
      (.data 47 1 [.data 58 5 [.data 59 5 [],.data 93 0 [],.reg .xzr,.reg (.vreg 192 .int),
        .op (.immLogic ⟨255,.size32⟩)]]) .ne middle emitTrace 960
  have conditionCall := conditionRun
  change ApplyInternal program (Stock.sem built.1) {} 999 27 715 [.data 123 2 [.data 47 1 [.data 58 5 [.data 59 5 [],.data 93 0 [],.reg .xzr,
          .reg (.vreg 192 .int),.op (.immLogic ⟨255,.size32⟩)]],.data 96 0 []]]
    (middle,emitTrace.push rule_inst_4956.id) _ (_,trace) at conditionCall
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have extent : ∀ z r,built.1.valueReg? z = some r → z < built.2.2.demand.size := by
    intro z r mapped
    have sizeEq : built.1.valReg.size = built.2.2.demand.size := by unfold built; rfl
    rw [← sizeEq]
    by_cases bound : z < built.1.valReg.size
    · exact bound
    · unfold Ctx.valueReg? at mapped
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt bound)] at mapped
      cases mapped
  obtain ⟨key,d,mapping,output,lower,upper,fragment,execution⟩ := stock_cmp_equal_zero8_rhs_source_values data_program
    (buildCtx_mappedInv scope build) rfl type (by decide) (by decide) run inversion conditionCall self
    (aliases := aliases) (ρ := regs zero) (by unfold built; decide +kernel) extent (held zero _)
  have keyEq : key = 192 := (Reg.vreg.inj (Option.some.inj (mapping.symm.trans mapped192))).1
  subst key
  have truth : (word zero == 0) = zero := by cases zero <;> decide +kernel
  rw [truth] at execution
  exact ⟨condition,middle,emitTrace,_,_,trace,d,run,inversion,conditionCall,output,execution⟩
end Backend.Stock.Proof.ScalarCmp.EqualZero8HelperWitness

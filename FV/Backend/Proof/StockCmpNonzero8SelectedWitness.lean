import FV.Backend.Proof.StockCmpNonzero8SelectedValues
namespace Backend.Stock.Proof.ScalarCmp.Nonzero8SelectedWitness
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
section KernelFacts
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem emitter : ∃ out next trace,ApplyInternal program (Stock.sem built.1) {} 999 123 651 [.value 7]
    (built.2.2,#[]) out (next,trace) := by
  have actual : (((applyTerm program (Stock.sem built.1) {} 1000 123 651 [.value 7]).run
      (built.2.2,#[])).toOption.bind (fun result => result.1)).isSome = true := by decide +kernel
  cases run : (applyTerm program (Stock.sem built.1) {} 1000 123 651 [.value 7]).run (built.2.2,#[]) with
  | error e => simp only [run,Except.toOption,Option.bind_none,Option.isSome_none] at actual; cases actual
  | ok result =>
    obtain ⟨out,next,trace⟩ := result
    cases out with
    | none => simp only [run,Except.toOption,Option.bind_some,Option.isSome_none] at actual; cases actual
    | some out => exact ⟨out,next,trace,run⟩
end KernelFacts
attribute [local irreducible] built
/-- Both boolean outcomes inhabit actual651/715 source-value execution on an
accepted original sparse-ID function with dirty bits and a nonidentity final alias. -/
theorem stock_cmp_nonzero8_selected_source_witness (zero : Bool) :
    ∃ condition middle emitTrace out next trace d,
      ApplyInternal program (Stock.sem built.1) {} 999 123 651 [.value 7]
        (built.2.2,#[]) condition (middle,emitTrace) ∧
      ApplyInternal program (Stock.sem built.1) {} 999 27 715 [condition]
        (middle,emitTrace) out (next,trace) ∧ out = .reg (.vreg d .int) ∧
      ∀ world,Runs (fun _ => True) ispec ([MInst.aluRRImmLogic .andS .size32 .xzr (.vreg 192 .int) ⟨255,.size32⟩,.cset (.vreg d .int) .ne].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) (regs zero) world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (!zero)⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = regs zero k) := by
  obtain ⟨condition,middle,emitTrace,run⟩ := emitter
  have type : built.1.valueType? 7 = some (.int 8) := by unfold built; rfl
  have parameter : built.1.defInst? 7 = none := by unfold built; rfl
  have mapped192 : built.1.valueReg? 7 = some (.vreg 192 .int) := by unfold built; rfl
  obtain ⟨rhsTrace,rhs,traceEq⟩ := stock_cmp_parameter_nonzero8_selected data_program built.1 (by decide) type parameter run
  change (evalExpr program (Stock.sem built.1) {} (899+100) rule_inst_4988.rhs #[some (.value 7)]).run
    (built.2.2,#[]) = .ok (some condition,middle,rhsTrace) at rhs
  obtain ⟨safe,rx,mapped,producer,finish⟩ := stock_cmp_nonzero8_rhs_observed data_program built.1 rfl rhs
  have register : rx = .vreg 192 .int := Option.some.inj (mapped.symm.trans mapped192)
  subst rx
  obtain ⟨trace,conditionRun⟩ := stock_cmp_condition_flags data_program built.1 (cfg := {}) rfl middle emitTrace 880
    (ofV_tst .xzr (.vreg 192 .int) ⟨255,.size32⟩) .ne
  have conditionCall := conditionRun
  change ApplyInternal program (Stock.sem built.1) {} 999 27 715
    [.data 123 2 [.data 47 1 [.data 58 5 [.data 59 5 [],.data 93 0 [],.reg .xzr,
      .reg (.vreg 192 .int),.op (.immLogic ⟨255,.size32⟩)]],.data 96 1 []]]
    (middle,emitTrace) _ (_,trace) at conditionCall
  rw [← producer] at conditionCall
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
  obtain ⟨key,d,mapping,output,lower,upper,fragment,execution⟩ := stock_cmp_parameter_nonzero8_values data_program
    (buildCtx_mappedInv scope build) rfl type parameter (by decide) (by decide) run conditionCall self
    (aliases := aliases) (ρ := regs zero) (by unfold built; decide +kernel) extent (held zero _)
  have keyEq : key = 192 := (Reg.vreg.inj (Option.some.inj (mapping.symm.trans mapped192))).1
  subst key
  have truth : (word zero != 0) = !zero := by cases zero <;> decide +kernel
  rw [truth] at execution
  exact ⟨condition,middle,emitTrace,_,_,trace,d,run,conditionCall,output,execution⟩
end Backend.Stock.Proof.ScalarCmp.Nonzero8SelectedWitness

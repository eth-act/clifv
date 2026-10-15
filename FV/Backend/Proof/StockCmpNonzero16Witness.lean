import FV.Backend.Proof.StockCmpNonzero16Values
namespace Backend.Stock.Proof.ScalarCmp.Nonzero16HelperWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def function : Clif.Function := {
  name := "stock_nonzero16_original_parameter"
  sig := {params := [⟨.i16,.none,.normal⟩],returns := [⟨.i16,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i16)],body := [],term := .ret [7]}] }
private def built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
private def frame (word : BitVec 16) : Clif.Frame := {
  func := function,regs := fun x => if x = 7 then some ⟨.i16,word⟩ else none,
  slots := [],body := [],term := .ret [7] }
private def aliases : Array (Option Nat) := (Array.replicate 193 none).setIfInBounds 192 (some 1)
private def regs (word : BitVec 16) (_ : Nat) : CV := BitVec.ofNat 128 (2^100+word.toNat)
private theorem scope : LowerScope function := lowerScope_of (by rfl)
private theorem build : Stock.buildCtx function = .ok built := rfl
private theorem dfg (word : BitVec 16) : DFGCons built.1 (frame word) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases seven : x = 7
    · subst x
      have absent : built.1.defInst? 7 = none := by rfl
      rw [absent] at defined; cases defined
    · simp [frame,seven] at lookup
  · intro x t v typed lookup
    by_cases seven : x = 7
    · subst x
      simp only [frame,ite_true,Option.some.injEq] at lookup
      subst v
      change some (.int 16) = some t at typed
      cases typed
      rfl
    · simp [frame,seven] at lookup
private theorem held (word : BitVec 16) (st : State) :
    ValuesHeld (Demanded st) built.1 (frame word) (fun key => regs word (aliasNum aliases key)) := by
  intro x needed v lookup
  by_cases seven : x = 7
  · subst x
    simp only [frame,ite_true,Option.some.injEq] at lookup
    subst v
    refine ⟨192,rfl,?_⟩
    change (BitVec.ofNat 128 (2^100+word.toNat)).setWidth 16 = word
    rw [BitVec.setWidth_ofNat_of_le (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat,Nat.add_mod,show 2^100 % 2^16 = 0 from by decide +kernel,
      Nat.zero_add,Nat.mod_eq_of_lt word.isLt]
  · simp [frame,seven] at lookup
section KernelFacts
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem rhs : ∃ out next trace,
    (evalExpr program (Stock.sem built.1) {} 1000 rule_inst_4977.rhs
      #[some (.ty (.int 16)),some (.value 7)]).run (built.2.2,#[]) = .ok (some out,next,trace) := by
  have actual : (((evalExpr program (Stock.sem built.1) {} 1000 rule_inst_4977.rhs
      #[some (.ty (.int 16)),some (.value 7)]).run (built.2.2,#[])).toOption.bind (fun result => result.1)).isSome = true := by
    decide +kernel
  cases run : (evalExpr program (Stock.sem built.1) {} 1000 rule_inst_4977.rhs
      #[some (.ty (.int 16)),some (.value 7)]).run (built.2.2,#[]) with
  | error e => simp only [run,Except.toOption,Option.bind_none,Option.isSome_none] at actual; cases actual
  | ok result =>
    obtain ⟨out,next,trace⟩ := result
    cases out with
    | none => simp only [run,Except.toOption,Option.bind_some,Option.isSome_none] at actual; cases actual
    | some out => exact ⟨out,next,trace,rfl⟩
end KernelFacts
attribute [local irreducible] built
/-- Arbitrary original16-bit values inhabit real extension and condition
execution, with dirty upper bits, sparse source numbering and nonidentity aliases. -/
theorem stock_cmp_nonzero16_source_witness (word : BitVec 16) :
    ∃ condition middle emitTrace out next trace ms r d,
      LowerScope function ∧ DFGCons built.1 (frame word) ∧
      (evalExpr program (Stock.sem built.1) {} 1000 rule_inst_4977.rhs
        #[some (.ty (.int 16)),some (.value 7)]).run (built.2.2,#[]) = .ok (some condition,middle,emitTrace) ∧
      ApplyInternal program (Stock.sem built.1) {} 999 27 715 [condition] (middle,emitTrace) out (next,trace) ∧
      out = .reg (.vreg d .int) ∧ built.2.2.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag built.2.2.base next.base (ms ++ [cmpImm0 .size32 r,.cset (.vreg d .int) .ne]) ∧
      ∀ world,Runs (fun _ => True) ispec ((ms ++ [cmpImm0 .size32 r,.cset (.vreg d .int) .ne]).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) (regs word) world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (word != 0)⟩ (ρ' d) ∧
          ∀ k,k < built.2.2.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = regs word k) := by
  obtain ⟨condition,middle,emitTrace,run⟩ := rhs
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
  obtain ⟨value,producer,extended⟩ := stock_cmp_nonzero16_rhs_prefix_values data_program
    (buildCtx_mappedInv scope build) (dfg word) rfl (n := 780) run self
    (aliases := aliases) (ρ := regs word) (by unfold built; decide +kernel) extent (held word middle)
  obtain ⟨ms,r,ρ1,register,_⟩ := extended
  rw [register] at producer
  obtain ⟨trace,conditionRun⟩ := stock_cmp_condition_zero data_program built.1 (cfg := {}) rfl
    true .size32 middle emitTrace 880 (.vreg r .int)
  have conditionCall := conditionRun
  change ApplyInternal program (Stock.sem built.1) {} 999 27 715
    [.data 123 1 [.reg (.vreg r .int),.data 93 0 []]] (middle,emitTrace) _ (_,trace) at conditionCall
  rw [←producer] at conditionCall
  obtain ⟨code,input,d,output,lower,upper,fragment,execution⟩ := stock_cmp_nonzero16_rhs_source_values data_program
    (buildCtx_mappedInv scope build) (dfg word) rfl (n := 780) (by decide) run conditionCall self
    (aliases := aliases) (ρ := regs word) (by unfold built; decide +kernel) extent (held word _)
  exact ⟨condition,middle,emitTrace,_,_,trace,code,input,d,scope,dfg word,run,conditionCall,
    output,lower,upper,fragment,execution⟩
end Backend.Stock.Proof.ScalarCmp.Nonzero16HelperWitness

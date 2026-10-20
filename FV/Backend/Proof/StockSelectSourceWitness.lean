import FV.Backend.Proof.StockSelectSourceValues
namespace Backend.Stock.Proof.ScalarSelect.SourceWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private def function : Clif.Function := {
  name := "stock_select_original_values"
  sig := {params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64),(31,.i64)],body := [],term := .ret [7]}] }
private def built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
private def frame : Clif.Frame := {
  func := function,regs := fun x => if x = 7 then some ⟨.i64,7⟩ else if x = 31 then some ⟨.i64,9⟩ else none,
  slots := [],body := [],term := .ret [7] }
private def aliases : Array (Option Nat) := ((Array.replicate 194 none).setIfInBounds 192 (some 1)).setIfInBounds 193 (some 2)
private def registers (k : Nat) : CV := BitVec.ofNat 128 (2^100 + if k = 1 then 7 else 9)
private def producer : V := .data 58 2 [.data 59 10 [],.data 93 1 [],.reg .xzr,.reg (.vreg 192 .int),.reg (.vreg 192 .int)]
private def code : MInst := .aluRRR .subS .size64 .xzr (.vreg 192 .int) (.vreg 192 .int)
private def selected (chooseX : Bool) : Cond := if chooseX then .eq else .ne
private theorem scope : LowerScope function := lowerScope_of (by rfl)
private theorem build : Stock.buildCtx function = .ok built := rfl
private theorem held (st : State) : ValuesHeld (Demanded st) built.1 frame
    (fun key => registers (aliasNum aliases key)) := by
  intro x needed value lookup
  by_cases seven : x = 7
  · subst x
    simp only [frame,ite_true,Option.some.injEq] at lookup
    subst value
    refine ⟨192,rfl,?_⟩
    unfold VHolds
    decide +kernel
  · by_cases thirtyone : x = 31
    · subst x
      simp only [frame,show (31:Nat) ≠ 7 by decide,ite_false,ite_true,Option.some.injEq] at lookup
      subst value
      refine ⟨193,rfl,?_⟩
      unfold VHolds
      decide +kernel
    · simp [frame,seven,thirtyone] at lookup
private theorem safeX : DemandAllowed built.1 built.2.2 7 := by
  intro i h
  change none = some i at h
  cases h
private theorem safeY : DemandAllowed built.1 (built.2.2.mark 7) 31 := by
  intro i h
  change none = some i at h
  cases h
/-- The actual scalar RHS and660/659 calls inhabit the request inversion and
source-value consumer results. Distinct7/9 source values, sparse IDs, dirty high
bits, final aliases and both outcomes are preserved. This is a consumer witness;
complete retained minmax/select source-step witnesses remain separate work. -/
theorem stock_select_original_consumer_witness (chooseX : Bool) :
    (∃ out next trace,(evalExpr program (Stock.sem built.1) {} 1000 rule_inst_5364.rhs
      (selectEnv 64 7 31 producer (.data 96 (selected chooseX).idx []))).run (built.2.2,#[]) = .ok (some out,next,trace)) ∧
    (∃ out next trace,ApplyInternal program (Stock.sem built.1) {} 999 22 660
      [.ty (.int 64),.data 47 1 [producer],.data 96 (selected chooseX).idx [],.value 7,.value 31]
      (built.2.2,#[]) out (next,trace)) ∧
    ∃ out next trace nx ny d,ApplyInternal program (Stock.sem built.1) {} 999 22 659
      [.ty (.int 64),.data 123 2 [.data 47 1 [producer],.data 96 (selected chooseX).idx []],.value 7,.value 31]
      (built.2.2,#[]) out (next,trace) ∧
      built.1.valueReg? 7 = some (.vreg nx .int) ∧ built.1.valueReg? 31 = some (.vreg ny .int) ∧
      out = .regs [.vreg d .int] ∧ built.2.2.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag built.2.2.base next.base [code,.csel (.vreg d .int) (.vreg nx .int) (.vreg ny .int) (selected chooseX)] ∧
      ∀ world,Runs (fun _ => True) ispec
        ([code,.csel (.vreg d .int) (.vreg nx .int) (.vreg ny .int) (selected chooseX)].map
          (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) registers world
        (fun ρ' _ => VHolds ⟨.i64,if chooseX then 7 else 9⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = registers k) := by
  have decoded : MInst.ofV producer = some code := rfl
  have rhs := stock_select_rhs_run data_program built.1 (cfg := {}) rfl 64 built.2.2 #[] 880
    (selected chooseX) decoded (by rfl) (by rfl) safeX safeY
  have cond := stock_select_cond_run data_program built.1 (cfg := {}) rfl (w := 64) (by simp) built.2.2 #[] 840
    (selected chooseX) decoded (by rfl) (by rfl) safeX safeY
  have select := stock_select_flags_run data_program built.1 (cfg := {}) rfl (w := 64) (by simp) built.2.2 #[] 780
    (selected chooseX) decoded (by rfl) (by rfl) safeX safeY
  have actual : ApplyInternal program (Stock.sem built.1) {} 999 22 659
      [.ty (.int 64),.data 123 2 [.data 47 1 [producer],.data 96 (selected chooseX).idx []],.value 7,.value 31]
      (built.2.2,#[]) _ _ := select
  have extent : ∀ z r,built.1.valueReg? z = some r → z < built.2.2.demand.size := by
    intro z r mapped
    have sizeEq : built.1.valReg.size = built.2.2.demand.size := rfl
    rw [← sizeEq]
    by_cases bound : z < built.1.valReg.size
    · exact bound
    · unfold Ctx.valueReg? at mapped
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt bound)] at mapped
      cases mapped
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have flags := setsFlags_cmpRR .size64 192 192 (fun key => registers (aliasNum aliases key))
  obtain ⟨nx,ny,d,mapX,mapY,output,lower,upper,fragment,execution⟩ :=
    stock_select_flags_source_values data_program (buildCtx_mappedInv scope build) (ty := .i64) (by simp [Clif.Ty.width])
      (fr := frame) (by rfl) (by rfl) (by decide) decoded rfl actual self
      (aliases := aliases) (ρ := registers) (b := chooseX) (by decide +kernel) extent (held _) flags
      (by cases chooseX <;> decide +kernel)
  exact ⟨⟨_,_,_,rhs⟩,⟨_,_,_,cond⟩,_,_,_,nx,ny,d,actual,mapX,mapY,output,lower,upper,fragment,execution⟩
end Backend.Stock.Proof.ScalarSelect.SourceWitness

module

public import FV.Backend.Proof.StockSelectZeroSourceValues

@[expose] public section

namespace Backend.Stock.Proof.ScalarSelect.ZeroSourceWitness
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
/-- Both actual zero condition forms and sizes inhabit request inversion and
original source-value transfer with sparse source IDs, nonidentity aliases and dirty high bits. -/
theorem stock_select_zero_original_consumer_witness (nonzero : Bool) (size : OperandSize) :
    ∃ out next trace nx ny d,ApplyInternal program (Stock.sem built.1) {} 999 22 659
      [.ty (.int 64),.data 123 (if nonzero then 1 else 0)
        [.reg (.vreg 192 .int),.data 93 (if size = .size32 then 0 else 1) []],.value 7,.value 31]
      (built.2.2,#[]) out (next,trace) ∧
      built.1.valueReg? 7 = some (.vreg nx .int) ∧ built.1.valueReg? 31 = some (.vreg ny .int) ∧
      out = .regs [.vreg d .int] ∧ built.2.2.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag built.2.2.base next.base [cmpXzr size 192,
        .csel (.vreg d .int) (.vreg nx .int) (.vreg ny .int) (if nonzero then .ne else .eq)] ∧
      ∀ world,Runs (fun _ => True) ispec
        ([cmpXzr size 192,.csel (.vreg d .int) (.vreg nx .int) (.vreg ny .int) (if nonzero then .ne else .eq)].map
          (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) registers world
        (fun ρ' _ => VHolds ⟨.i64,if nonzero then 7 else 9⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = registers k) := by
  have select := stock_select_zero_run data_program built.1 (cfg := {}) rfl (w := 64) (by simp)
    built.2.2 #[] 780 nonzero size 192 (by rfl) (by rfl) safeX safeY
  have actual : ApplyInternal program (Stock.sem built.1) {} 999 22 659
      [.ty (.int 64),.data 123 (if nonzero then 1 else 0)
        [.reg (.vreg 192 .int),.data 93 (if size = .size32 then 0 else 1) []],.value 7,.value 31]
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
  obtain ⟨nx,ny,d,mapX,mapY,output,lower,upper,fragment,execution⟩ :=
    stock_select_zero_source_values data_program (buildCtx_mappedInv scope build) (ty := .i64) (by simp [Clif.Ty.width])
      (fr := frame) (by rfl) (by rfl) (by decide) nonzero size 192 actual self
      (aliases := aliases) (ρ := registers) (by decide +kernel) extent (held _)
  have truth : (if nonzero then opnd size (registers (aliasNum aliases 192)) != 0
      else opnd size (registers (aliasNum aliases 192)) == 0) = nonzero := by
    cases nonzero <;> cases size <;> decide +kernel
  simp only [truth] at execution
  exact ⟨_,_,_,nx,ny,d,actual,mapX,mapY,output,lower,upper,fragment,execution⟩
end Backend.Stock.Proof.ScalarSelect.ZeroSourceWitness

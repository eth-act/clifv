import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.LowerDecide
namespace Backend.Stock.Proof.ScalarSelect.ComparisonActualFixture
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program
private def function (ty : Clif.Ty) (cc : Clif.IntCC) : Clif.Function := {
  name := "stock_select_comparison_companion"
  sig := {params := [⟨ty,.none,.normal⟩,⟨ty,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,ty),(31,ty)],body := [⟨[100],.icmp cc ty 7 31⟩],term := .ret [100]}] }
private def built (ty : Clif.Ty) (cc : Clif.IntCC) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function ty cc)).toOption.getD (sinkCtx,#[],sinkState)
private def frame (ty : Clif.Ty) (cc : Clif.IntCC) (a b : BitVec ty.width) : Clif.Frame := {
  func := function ty cc,regs := fun x => if x = 7 then some ⟨ty,a⟩ else if x = 31 then some ⟨ty,b⟩ else none,
  slots := [],body := [⟨[100],.icmp cc ty 7 31⟩],term := .ret [100] }
private def aliases : Array (Option Nat) :=
  ((Array.replicate 194 none).setIfInBounds 192 (some 1)).setIfInBounds 193 (some 3)
private def dirty {w : Nat} (word : BitVec w) : CV := BitVec.ofNat 128 (2^100+word.toNat)
private def regs {w : Nat} (a b : BitVec w) (key : Nat) : CV :=
  if key = 1 then dirty a else if key = 3 then dirty b else 0
private theorem dirty_low {ty : Clif.Ty}
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) (word : BitVec ty.width) :
    (dirty word).setWidth ty.width = word := by
  have small : ty.width ≤ 128 := by omega
  unfold dirty
  rw [BitVec.setWidth_ofNat_of_le small]
  apply BitVec.eq_of_toNat_eq
  have upper : 2^100 % 2^ty.width = 0 := by rcases width with h | h | h | h <;> rw [h] <;> decide +kernel
  simp only [BitVec.toNat_ofNat,Nat.add_mod,upper,Nat.zero_add,Nat.mod_eq_of_lt word.isLt]
private theorem scope (ty : Clif.Ty) (cc : Clif.IntCC)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) (int : ty.isInt = true) :
    LowerScope (function ty cc) :=
  lowerScope_of (by cases ty <;> cases cc <;> first | rfl | (simp at int; done) | simp [Clif.Ty.width] at width)
private theorem build (ty : Clif.Ty) (cc : Clif.IntCC)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) (int : ty.isInt = true) :
    Stock.buildCtx (function ty cc) = .ok (built ty cc) := by
  cases ty <;> cases cc <;> first | rfl | (simp at int; done) | simp [Clif.Ty.width] at width
private theorem typeX (ty : Clif.Ty) (cc : Clif.IntCC) (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (int : ty.isInt = true) : (built ty cc).1.valueType? 7 = some (.int ty.width) := by
  cases ty <;> cases cc <;> first | rfl | (simp at int; done) | simp [Clif.Ty.width] at width
private theorem typeY (ty : Clif.Ty) (cc : Clif.IntCC) (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (int : ty.isInt = true) : (built ty cc).1.valueType? 31 = some (.int ty.width) := by
  cases ty <;> cases cc <;> first | rfl | (simp at int; done) | simp [Clif.Ty.width] at width
private theorem mappedX (ty : Clif.Ty) (cc : Clif.IntCC) (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (int : ty.isInt = true) : (built ty cc).1.valueReg? 7 = some (.vreg 192 .int) := by
  cases ty <;> cases cc <;> first | rfl | (simp at int; done) | simp [Clif.Ty.width] at width
private theorem mappedY (ty : Clif.Ty) (cc : Clif.IntCC) (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (int : ty.isInt = true) : (built ty cc).1.valueReg? 31 = some (.vreg 193 .int) := by
  cases ty <;> cases cc <;> first | rfl | (simp at int; done) | simp [Clif.Ty.width] at width
private theorem absentX (ty : Clif.Ty) (cc : Clif.IntCC) (int : ty.isInt = true) : (built ty cc).1.defInst? 7 = none := by
  cases ty <;> cases cc <;> first | rfl | (simp at int; done)
private theorem absentY (ty : Clif.Ty) (cc : Clif.IntCC) (int : ty.isInt = true) : (built ty cc).1.defInst? 31 = none := by
  cases ty <;> cases cc <;> first | rfl | (simp at int; done)
private theorem dfg (ty : Clif.Ty) (cc : Clif.IntCC) (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (int : ty.isInt = true) (a b : BitVec ty.width) : DFGCons (built ty cc).1 (frame ty cc a b) := by
  constructor
  · intro x j info cl value defined found source pure lookup
    by_cases seven : x = 7
    · subst x; rw [absentX ty cc int] at defined; cases defined
    · by_cases thirtyone : x = 31
      · subst x; rw [absentY ty cc int] at defined; cases defined
      · simp [frame,seven,thirtyone] at lookup
  · intro x cty value typed lookup
    by_cases seven : x = 7
    · subst x
      rw [typeX ty cc width int] at typed
      cases typed
      simp only [frame,ite_true,Option.some.injEq] at lookup
      subst value; cases ty <;> first | rfl | (simp at int; done)
    · by_cases thirtyone : x = 31
      · subst x
        rw [typeY ty cc width int] at typed
        cases typed
        simp only [frame,show (31:Nat) ≠ 7 by decide,ite_false,ite_true,Option.some.injEq] at lookup
        subst value; cases ty <;> first | rfl | (simp at int; done)
      · simp [frame,seven,thirtyone] at lookup
private theorem held (ty : Clif.Ty) (cc : Clif.IntCC)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) (int : ty.isInt = true)
    (a b : BitVec ty.width) (st : State) :
    ValuesHeld (Demanded st) (built ty cc).1 (frame ty cc a b) (fun key => regs a b (aliasNum aliases key)) := by
  intro x needed value lookup
  by_cases seven : x = 7
  · subst x
    simp only [frame,ite_true,Option.some.injEq] at lookup
    subst value
    refine ⟨192,mappedX ty cc width int,?_⟩
    change (dirty a).setWidth ty.width = a
    exact dirty_low width a
  · by_cases thirtyone : x = 31
    · subst x
      simp only [frame,show (31:Nat) ≠ 7 by decide,ite_false,ite_true,Option.some.injEq] at lookup
      subst value
      refine ⟨193,mappedY ty cc width int,?_⟩
      change (dirty b).setWidth ty.width = b
      exact dirty_low width b
    · simp [frame,seven,thirtyone] at lookup
private def Observed (ty : Clif.Ty) (cc : Clif.IntCC) : Prop :=
  (((applyTerm program (Stock.sem (built ty cc).1) {} 1001 123 652
      [.data 145 (ccIdx cc) [],.value 7,.value 31]).run ((built ty cc).2.2,#[])).toOption.bind
        (fun result => result.1)).isSome = true
section Kernel
attribute [local semireducible] Isle.Aarch64.program
private theorem observed (ty : Clif.Ty) (cc : Clif.IntCC)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) (int : ty.isInt = true) : Observed ty cc := by
  cases ty <;> cases cc
  all_goals first | (unfold Observed; decide +kernel) | (simp at int; done) | simp [Clif.Ty.width] at width
end Kernel
/-- Original sparse-ID scalar contexts inhabit the actual emitter and every
source-side value/separation/guard premise used by select composition.

Compatibility boundary (S11b, #140): the statement holds on the original integer domain only
(`f32` shares width 32 with `i32`); `int` is a trailing auto-parameter, discharged by `decide`
for every concrete integer type, so the original call shapes are unchanged. -/
theorem stock_select_comparison_actual_fixture (ty : Clif.Ty) (cc : Clif.IntCC)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) (a b : BitVec ty.width)
    (int : ty.isInt = true := by decide) :
    ∃ f ctx st middle raw trace fr aliases,∃ (ρ : Nat → CV),LowerScope f ∧ MappedCtxInv f ctx ∧ DFGCons ctx fr ∧
      fr.getAs 7 ty = .ok a ∧ fr.getAs 31 ty = .ok b ∧
      ctx.valueType? 7 = some (.int ty.width) ∧ ctx.valueType? 31 = some (.int ty.width) ∧
      ctx.valueReg? 7 = some (.vreg 192 .int) ∧ ctx.valueReg? 31 = some (.vreg 193 .int) ∧
      aliasNum aliases 192 = 1 ∧ aliasNum aliases 193 = 3 ∧ st.base.nextVreg = 195 ∧
      st.base.emitted = #[] ∧ aliases.size ≤ st.base.nextVreg ∧
      (∀ z r,ctx.valueReg? z = some r → z < st.demand.size) ∧
      (∀ state,ValuesHeld (Demanded state) ctx fr (fun key => ρ (aliasNum aliases key))) ∧
      (∀ state,DemandAllowed ctx state 7 ∧ DemandAllowed ctx state 31) ∧
      ApplyInternal program (Stock.sem ctx) {} 1000 123 652
        [.data 145 (ccIdx cc) [],.value 7,.value 31] (st,#[]) raw (middle,trace) := by
  let ctx := (built ty cc).1
  let st := (built ty cc).2.2
  have inv : MappedCtxInv (function ty cc) ctx := buildCtx_mappedInv (scope ty cc width int) (build ty cc width int)
  have success := observed ty cc width int
  obtain ⟨raw,middle,trace,run⟩ : ∃ raw middle trace,ApplyInternal program (Stock.sem ctx) {} 1000 123 652
      [.data 145 (ccIdx cc) [],.value 7,.value 31] (st,#[]) raw (middle,trace) := by
    unfold Observed at success
    cases actual : (applyTerm program (Stock.sem ctx) {} 1001 123 652
      [.data 145 (ccIdx cc) [],.value 7,.value 31]).run (st,#[]) with
    | error e => simp [ctx,st] at actual; rw [actual] at success; cases success
    | ok result =>
      obtain ⟨output,middle,trace⟩ := result
      cases output with
      | none => simp [ctx,st] at actual; rw [actual] at success; cases success
      | some raw => exact ⟨raw,middle,trace,actual⟩
  have bounded : aliases.size ≤ st.base.nextVreg := by
    cases ty <;> cases cc <;> first | (simp at int; done) | decide +kernel
  have extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size := by
    intro z r mapped
    have bound : ctx.valReg.size ≤ st.demand.size := by
      cases ty <;> cases cc <;> first | (simp at int; done) | decide +kernel
    have index : z < ctx.valReg.size := by
      by_cases inside : z < ctx.valReg.size
      · exact inside
      · have absent := Array.getElem?_eq_none (show ctx.valReg.size ≤ z by omega)
        have missing : ctx.valueReg? z = none := by simp [Ctx.valueReg?,absent]
        rw [missing] at mapped; cases mapped
    omega
  have getX : (frame ty cc a b).getAs 7 ty = .ok a := by simp [Clif.Frame.getAs,Clif.Frame.get,frame]
  have getY : (frame ty cc a b).getAs 31 ty = .ok b := by simp [Clif.Frame.getAs,Clif.Frame.get,frame]
  have base : st.base.nextVreg = 195 ∧ st.base.emitted = #[] := by
    cases ty <;> cases cc <;> first | exact ⟨rfl,rfl⟩ | (simp at int; done) | simp [Clif.Ty.width] at width
  have guards : ∀ state,DemandAllowed ctx state 7 ∧ DemandAllowed ctx state 31 := by
    intro state
    constructor
    · intro i impossible; rw [absentX ty cc int] at impossible; cases impossible
    · intro i impossible; rw [absentY ty cc int] at impossible; cases impossible
  exact ⟨function ty cc,ctx,st,middle,raw,trace,frame ty cc a b,aliases,regs a b,scope ty cc width int,inv,
    dfg ty cc width int a b,getX,getY,typeX ty cc width int,typeY ty cc width int,mappedX ty cc width int,
    mappedY ty cc width int,rfl,rfl,base.1,base.2,bounded,extent,held ty cc width int a b,guards,run⟩
end Backend.Stock.Proof.ScalarSelect.ComparisonActualFixture

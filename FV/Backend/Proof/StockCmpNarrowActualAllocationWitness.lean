import FV.Backend.Proof.StockAluSelectedValues
import FV.Backend.Proof.StockCmpNarrowActualAllocation
import FV.Backend.Proof.StockCmpNarrow8DriverRuns
import FV.Backend.Proof.StockCmpNarrow16DriverRuns
namespace Backend.Stock.Proof.ScalarCmp.NarrowActualAllocationWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
attribute [local irreducible] Isle.Aarch64.program
private def ty (half : Bool) : Clif.Ty := if half then .i16 else .i8
private def cc (signed : Bool) : Clif.IntCC := if signed then .slt else .ult
private def function (signed half : Bool) : Clif.Function :=
  if half then cmpNarrow16Function signed else cmpNarrow8Function signed
private def built (signed half : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function signed half)).toOption.getD (sinkCtx,#[],sinkState)
private def frame (signed half : Bool) (a b : BitVec (ty half).width) : Clif.Frame := {
  func := function signed half
  regs := fun x => if x = 7 then some ⟨ty half,a⟩ else if x = 31 then some ⟨ty half,b⟩ else none
  slots := [],body := [⟨[100],.icmp (cc signed) (ty half) 7 31⟩],term := .ret [100] }
private def dirty {n : Nat} (a : BitVec n) : CV := BitVec.ofNat 128 (2^100+a.toNat)
private theorem dirty_low (half : Bool) (a : BitVec (ty half).width) :
    (dirty a).setWidth (ty half).width = a := by
  have small : (ty half).width ≤ 128 := by cases half <;> decide
  unfold dirty
  rw [BitVec.setWidth_ofNat_of_le small]
  apply BitVec.eq_of_toNat_eq
  have upper : 2^100 % 2^(ty half).width = 0 := by cases half <;> decide +kernel
  simp only [BitVec.toNat_ofNat,Nat.add_mod,upper,Nat.zero_add,Nat.mod_eq_of_lt a.isLt]
private def regs (signed half : Bool) (a b : BitVec (ty half).width) (key : Nat) : CV :=
  if key = 192 then dirty a else if key = 193 then dirty b else 0
private def emittedState (signed half : Bool) : State :=
  let st := (built signed half).2.2
  {(st.mark 7).mark 31 with base := ((st.base.fresh .int).2.emit
    (.extend (st.base.fresh .int).1 (.vreg 192 .int) (signedCC (cc signed)) (if half then 16 else 8) 32))}
private def producer (signed half : Bool) : V :=
  let st := (built signed half).2.2
  .data 58 8 [.data 59 10 [],.data 93 0 [],.reg .xzr,.reg (st.base.fresh .int).1,
    .reg (.vreg 193 .int),.data 84 (if signedCC (cc signed) then (if half then 5 else 4) else (if half then 1 else 0)) []]
private def condition (signed half : Bool) : V :=
  .data 123 2 [.data 47 1 [producer signed half],.data 96 (condOf (cc signed)).idx []]
section Kernel
attribute [local semireducible] Isle.Aarch64.program
private theorem emitter_observed (signed half : Bool) :
    ((applyTerm program (Stock.sem (built signed half).1) {} 1001 123 652
      [.data 145 (ccIdx (cc signed)) [],.value 7,.value 31]).run ((built signed half).2.2,#[])).toOption.map
      (fun result => decide (result.1 = some (condition signed half)) &&
        decide (result.2.1 = emittedState signed half)) = some true := by
  cases signed <;> cases half <;> decide +kernel
end Kernel
/-- All premises of the universal narrow emitter theorem are inhabited by an
actual first-match emitter/condition pipeline in original built contexts, with
arbitrary source words and a successful complete Stock.lower of each function.
Retained-record composition remains a separate obligation. -/
theorem stock_cmp_narrow_actual_allocation_witness (signed half : Bool) (a b : BitVec (ty half).width) :
    ∃ result st middle next condition out emitTrace trace,
      Stock.lower (function signed half) = .ok result ∧ LowerScope (function signed half) ∧
      MappedCtxInv (function signed half) (built signed half).1 ∧
      DFGCons (built signed half).1 (frame signed half a b) ∧
      ApplyInternal program (Stock.sem (built signed half).1) {} 1000 123 652
        [.data 145 (ccIdx (cc signed)) [],.value 7,.value 31] (st,#[]) condition (middle,emitTrace) ∧
      ApplyInternal program (Stock.sem (built signed half).1) {} 999 27 715 [condition]
        (middle,#[]) out (next,trace) ∧
      st.base.nextVreg < next.base.nextVreg ∧
      CmpExecution (fun _ => True) ispec #[] (cc signed) (ty half) a b st next out (regs signed half a b) := by
  let ctx := (built signed half).1
  let st := (built signed half).2.2
  have scope : LowerScope (function signed half) := lowerScope_of (by cases signed <;> cases half <;> decide +kernel)
  have build : Stock.buildCtx (function signed half) = .ok (built signed half) := by
    cases signed <;> cases half <;> rfl
  have inv : MappedCtxInv (function signed half) ctx := buildCtx_mappedInv scope build
  have typeX : ctx.valueType? 7 = some (.int (if half then 16 else 8)) := by cases signed <;> cases half <;> rfl
  have mapX : ctx.valueReg? 7 = some (.vreg 192 .int) := by cases signed <;> cases half <;> rfl
  have mapY : ctx.valueReg? 31 = some (.vreg 193 .int) := by cases signed <;> cases half <;> rfl
  have absentX : ctx.defInst? 7 = none := by cases signed <;> cases half <;> rfl
  have safeX : DemandAllowed ctx st 7 := by intro i impossible; rw [absentX] at impossible; cases impossible
  have absentY : ctx.defInst? 31 = none := by cases signed <;> cases half <;> rfl
  have safeY : DemandAllowed ctx st 31 := by intro i impossible; rw [absentY] at impossible; cases impossible
  obtain ⟨emitTrace,emitter⟩ := stock_cmp_narrow_rhs data_program ctx (signedCC (cc signed)) half (cc signed)
    typeX mapX mapY st safeX safeY #[] 840
  let middle : State := {(st.mark 7).mark 31 with base := ((st.base.fresh .int).2.emit
    (.extend (st.base.fresh .int).1 (.vreg 192 .int) (signedCC (cc signed)) (if half then 16 else 8) 32))}
  let mi : V := .data 58 8 [.data 59 10 [],.data 93 0 [],.reg .xzr,.reg (st.base.fresh .int).1,
    .reg (.vreg 193 .int),.data 84 (if signedCC (cc signed) then (if half then 5 else 4) else (if half then 1 else 0)) []]
  let e := if signedCC (cc signed) then (if half then ExtendOp.sxth else .sxtb) else (if half then ExtendOp.uxth else .uxtb)
  have decoded : MInst.ofV mi = some (.aluRRRExtend .subS .size32 .xzr (st.base.fresh .int).1 (.vreg 193 .int) e) := by
    cases signed <;> cases half <;> rfl
  obtain ⟨trace,call⟩ := stock_cmp_condition_flags data_program ctx (cfg := {}) rfl middle #[] 880 decoded (condOf (cc signed))
  have enough : (119:Nat) ≤ 999 := by decide
  have extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size := by
    intro z r mapped
    have bound : ctx.valReg.size ≤ st.demand.size := by cases signed <;> cases half <;> decide +kernel
    have index : z < ctx.valReg.size := by
      by_cases inside : z < ctx.valReg.size
      · exact inside
      · have absent := Array.getElem?_eq_none (show ctx.valReg.size ≤ z by omega)
        unfold Ctx.valueReg? at mapped
        rw [absent] at mapped
        cases mapped
    omega
  have held : ∀ next,ValuesHeld (Demanded next) ctx (frame signed half a b)
      (fun key => regs signed half a b (aliasNum #[] key)) := by
    intro next z needed val lookup
    by_cases seven : z = 7
    · subst z
      change some ⟨ty half,a⟩ = some val at lookup
      cases lookup
      refine ⟨192,mapX,?_⟩
      change (regs signed half a b 192).setWidth (ty half).width = a
      exact dirty_low half a
    · by_cases thirtyone : z = 31
      · subst z
        change some ⟨ty half,b⟩ = some val at lookup
        cases lookup
        refine ⟨193,mapY,?_⟩
        change (regs signed half a b 193).setWidth (ty half).width = b
        exact dirty_low half b
      · simp [frame,seven,thirtyone] at lookup
  have separated : ∀ r,ctx.valueReg? 31 = some (.vreg r .int) → aliasNum #[] r ≠ st.base.nextVreg := by
    intro r mapped
    rw [mapY] at mapped
    cases mapped
    cases signed <;> cases half <;> decide +kernel
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have typeY : ctx.valueType? 31 = some (.int (if half then 16 else 8)) := by
    cases signed <;> cases half <;> rfl
  have dfg : DFGCons ctx (frame signed half a b) := by
    constructor
    · intro x j info inst val defined found original pure lookup
      by_cases seven : x = 7
      · subst x; rw [absentX] at defined; cases defined
      · by_cases thirtyone : x = 31
        · subst x; rw [absentY] at defined; cases defined
        · simp [frame,seven,thirtyone] at lookup
    · intro x t val typed lookup
      by_cases seven : x = 7
      · subst x; rw [typeX] at typed; cases typed; cases lookup
        cases half <;> rfl
      · by_cases thirtyone : x = 31
        · subst x; rw [typeY] at typed; cases typed; cases lookup
          cases half <;> rfl
        · simp [frame,seven,thirtyone] at lookup
  have observation := emitter_observed signed half
  change ((applyTerm program (Stock.sem ctx) {} 1001 123 652
    [.data 145 (ccIdx (cc signed)) [],.value 7,.value 31]).run (st,#[])).toOption.map
      (fun result => decide (result.1 = some (.data 123 2 [.data 47 1 [mi],.data 96 (condOf (cc signed)).idx []])) &&
        decide (result.2.1 = middle)) = some true at observation
  obtain ⟨actualTrace,actualCall⟩ : ∃ actualTrace,ApplyInternal program (Stock.sem ctx) {} 1000 123 652
      [.data 145 (ccIdx (cc signed)) [],.value 7,.value 31] (st,#[])
      (.data 123 2 [.data 47 1 [mi],.data 96 (condOf (cc signed)).idx []]) (middle,actualTrace) := by
    cases run : (applyTerm program (Stock.sem ctx) {} 1001 123 652
      [.data 145 (ccIdx (cc signed)) [],.value 7,.value 31]).run (st,#[]) with
    | error err => simp only [run,Except.toOption,Option.map_none] at observation; cases observation
    | ok result =>
      obtain ⟨value,state,actualTrace⟩ := result
      rw [run] at observation
      simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,decide_eq_true_eq] at observation
      obtain ⟨rfl,rfl⟩ := observation
      exact ⟨actualTrace,run⟩
  have driver : ∃ result,Stock.lower (function signed half) = .ok result := by
    have observed : (Stock.lower (function signed half)).toOption.isSome = true := by
      cases half
      · have observed := stock_cmp_narrow8_driver_observed signed
        cases run : Stock.lower (cmpNarrow8Function signed) with
        | error err => rw [run] at observed; simp only [Except.toOption,Option.map_none] at observed; cases observed
        | ok result => rw [show function signed false = cmpNarrow8Function signed from rfl,run]; rfl
      · have observed := stock_cmp_narrow16_driver_observed signed
        cases run : Stock.lower (cmpNarrow16Function signed) with
        | error err => rw [run] at observed; simp only [Except.toOption,Option.map_none] at observed; cases observed
        | ok result => rw [show function signed true = cmpNarrow16Function signed from rfl,run]; rfl
    cases run : Stock.lower (function signed half) with
    | error err => rw [run] at observed; simp only [Except.toOption,Option.isSome_none,Bool.false_eq_true] at observed; try cases observed
    | ok result => exact ⟨result,rfl⟩
  obtain ⟨result,driverRun⟩ := driver
  have grows := stock_cmp_narrow_actual_emitter_growth inv half (cc signed) rfl dfg
    (fr := frame signed half a b) (u := a) (v := b) (by cases half <;> rfl) (by cases half <;> rfl)
    typeX typeY (by decide) enough actualCall call self (aliases := #[]) (by simp) extent (held _)
  have execution := stock_cmp_narrow_actual_emitter_values inv half (cc signed) rfl dfg
    (fr := frame signed half a b) (u := a) (v := b) (by cases half <;> rfl) (by cases half <;> rfl)
    typeX typeY (by decide) enough actualCall call self (aliases := #[]) (by simp) extent (held _) separated
  exact ⟨result,st,middle,_,_,_,actualTrace,trace,driverRun,scope,inv,dfg,actualCall,call,grows,execution⟩
end Backend.Stock.Proof.ScalarCmp.NarrowActualAllocationWitness

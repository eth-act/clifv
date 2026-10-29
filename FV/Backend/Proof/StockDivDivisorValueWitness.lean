module

public import FV.Backend.Proof.StockDivDivisorValues

@[expose] public section

namespace Backend.Stock.Proof.ScalarDiv.DivisorValueWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def function (signed : Bool) (ty : Clif.Ty) (literal : Int) : Clif.Function := {
  name := "stock_div_request_original_context"
  sig := {params := [⟨ty,.none,.normal⟩],returns := [⟨ty,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,ty)],body := [⟨[31],.iconst ty (BitVec.ofInt ty.width literal)⟩,
    ⟨[100],.div (if signed then .sdiv else .udiv) ty 7 31⟩],term := .ret [100]}] }
private def built (signed : Bool) (ty : Clif.Ty) (literal : Int) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function signed ty literal)).toOption.getD (sinkCtx,#[],sinkState)
private def frame (signed : Bool) (ty : Clif.Ty) (literal : Int) : Clif.Frame := {
  func := function signed ty literal
  regs := fun x => if x = 31 then some (.ofInt ty literal) else if x = 7 then some (.ofInt ty 7) else none
  slots := [],body := [⟨[100],.div (if signed then .sdiv else .udiv) ty 7 31⟩],term := .ret [100] }
private def Supported (ty : Clif.Ty) := ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64
private theorem scope (signed : Bool) (ty : Clif.Ty) (literal : Int) (supported : Supported ty) (values : literal = 0 ∨ literal = 9) : LowerScope (function signed ty literal) :=
  lowerScope_of (by cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rcases values with rfl | rfl <;> decide +kernel)
private theorem built_run (signed : Bool) (ty : Clif.Ty) (literal : Int) (supported : Supported ty) :
    Stock.buildCtx (function signed ty literal) = .ok (built signed ty literal) := by
  cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
private theorem dfg (signed : Bool) (ty : Clif.Ty) (literal : Int) (supported : Supported ty) :
    DFGCons (built signed ty literal).1 (frame signed ty literal) := by
  constructor
  · intro x j info cl val defined found original pure lookup
    by_cases constant : x = 31
    · subst x
      cases signed <;> rcases supported with rfl | rfl | rfl | rfl
      all_goals
        change some 0 = some j at defined
        cases defined
        obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
        subst info
        cases original
        cases lookup
        exact ⟨[_],fun cm => rfl,rfl⟩
    · by_cases parameter : x = 7
      · subst x
        have absent : (built signed ty literal).1.defInst? 7 = none := by cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
        rw [absent] at defined; cases defined
      · simp [frame,constant,parameter] at lookup
  · intro x t val typed lookup
    by_cases present : x = 31 ∨ x = 7
    · rcases present with rfl | rfl <;> rcases supported with rfl | rfl | rfl | rfl
      all_goals change some (.int _) = some t at typed
      all_goals cases typed; cases lookup; rfl
    · simp only [not_or] at present
      simp [frame,present.1,present.2] at lookup
private def expectedRule (signed : Bool) (ty : Clif.Ty) (literal : Int) : RuleId :=
  if literal = 0 then
    if ty.width = 64 then rule_lower_1104.id else
      if signed then rule_lower_1107.id else rule_lower_1110.id
  else if signed then rule_lower_1101.id else rule_lower_1097.id
private def observed (signed : Bool) (ty : Clif.Ty) (literal : Int) : Option Bool :=
  ((applyTerm program (Stock.sem (built signed ty literal).1) {} 500 27 698
    [.value 31,.data 125 (if signed then 0 else 1) [],.ty (.int ty.width)]).run
      ((built signed ty literal).2.2,#[])).toOption.map (fun (v,_,trace) => v.isSome && decide (trace.toList.getLast? = some (expectedRule signed ty literal)))
section Runs
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed_run (signed : Bool) (ty : Clif.Ty) (literal : Int)
    (supported : Supported ty) (values : literal = 0 ∨ literal = 9) : observed signed ty literal = some true := by
  cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rcases values with rfl | rfl <;> decide +kernel
end Runs
private def aliases : Array (Option Nat) := #[some 1,none]
private theorem fixed (k : Nat) (nonzero : k ≠ 0) : aliasNum aliases k = k := by
  cases k with
  | zero => exact False.elim (nonzero rfl)
  | succ k =>
    cases k with
    | zero => exact chaseF_none rfl _
    | succ k =>
      apply chaseF_none
      rw [Array.getElem?_eq_none (by simp [aliases])]
      rfl
private theorem idem : ∀ k,aliasNum aliases (aliasNum aliases k) = aliasNum aliases k := by
  intro k
  by_cases zero : k = 0
  · subst k; decide +kernel
  · rw [fixed k zero]; exact fixed k zero
private def regs (ty : Clif.Ty) (literal : Int) (n : Nat) : CV :=
  if n = 193 then BitVec.ofNat 128 (2^100+(BitVec.ofInt ty.width literal).toNat)
  else if n = 192 then BitVec.ofNat 128 (2^100+7) else 0
private theorem extent (signed : Bool) (ty : Clif.Ty) (literal : Int) (supported : Supported ty)
    (x : Nat) (r : Reg) (mapped : (built signed ty literal).1.valueReg? x = some r) :
    x < (built signed ty literal).2.2.demand.size := by
  by_cases large : 101 ≤ x
  · have outside : (built signed ty literal).1.valReg.size ≤ x := by
      cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> change 101 ≤ x <;> exact large
    change ((built signed ty literal).1.valReg[x]?).join = some r at mapped
    rw [Array.getElem?_eq_none outside] at mapped; cases mapped
  · have size : (built signed ty literal).2.2.demand.size = 101 := by
      cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
    rw [size]; omega
private theorem held (signed : Bool) (ty : Clif.Ty) (literal : Int) (supported : Supported ty)
    (values : literal = 0 ∨ literal = 9) (needed : Nat → Prop) :
    ValuesHeld needed (built signed ty literal).1 (frame signed ty literal)
      (fun k => regs ty literal (aliasNum aliases k)) := by
  intro x required value lookup
  by_cases constant : x = 31
  · subst x
    change some (.ofInt ty literal) = some value at lookup
    cases lookup
    refine ⟨193,?_,?_⟩
    · cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
    · change VHolds (.ofInt ty literal) (regs ty literal (aliasNum aliases 193))
      rw [fixed 193 (by decide)]
      rcases supported with rfl | rfl | rfl | rfl <;> rcases values with rfl | rfl
      all_goals unfold VHolds; decide +kernel
  · by_cases parameter : x = 7
    · subst x
      change some (.ofInt ty 7) = some value at lookup
      cases lookup
      refine ⟨192,?_,?_⟩
      · cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
      · change VHolds (.ofInt ty 7) (regs ty literal (aliasNum aliases 192))
        rw [fixed 192 (by decide)]
        rcases supported with rfl | rfl | rfl | rfl <;> rcases values with rfl | rfl
        all_goals unfold VHolds; decide +kernel
    · simp [frame,constant,parameter] at lookup
/-- Sixteen real original-context divisor runs inhabit the complete aliased
machine contracts, including source zero traps and nonzero operands, with dirty
upper register bits. These are complete divisor-fragment witnesses, not complete
retained source-instruction/whole-driver simulation witnesses. -/
theorem stock_div_divisor_values_witness (signed : Bool) (ty : Clif.Ty) (literal : Int)
    (supported : Supported ty) (values : literal = 0 ∨ literal = 9)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem) :
    ∃ out next trace,
      MappedCtxInv (function signed ty literal) (built signed ty literal).1 ∧
      DFGCons (built signed ty literal).1 (frame signed ty literal) ∧
      (frame signed ty literal).getAs 31 ty = .ok (BitVec.ofInt ty.width literal) ∧
      (applyTerm program (Stock.sem (built signed ty literal).1) {} 500 27 698
        [.value 31,.data 125 (if signed then 0 else 1) [],.ty (.int ty.width)]).run
          ((built signed ty literal).2.2,#[]) = .ok (some out,next,trace) ∧
      trace.toList.getLast? = some (expectedRule signed ty literal) ∧
      DivisorValueOut F isem (built signed ty literal).1 31 (if signed then 0 else 1) ty
        (BitVec.ofInt ty.width literal) (built signed ty literal).2.2 next out aliases (regs ty literal) := by
  have actual := observed_run signed ty literal supported values
  unfold observed at actual
  cases run : (applyTerm program (Stock.sem (built signed ty literal).1) {} 500 27 698
      [.value 31,.data 125 (if signed then 0 else 1) [],.ty (.int ty.width)]).run ((built signed ty literal).2.2,#[]) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    obtain ⟨out,next,trace⟩ := result
    cases out with
    | none => simp only [run,Except.toOption,Option.map_some,Option.isSome_none] at actual; cases actual
    | some out =>
      have fired : trace.toList.getLast? = some (expectedRule signed ty literal) := by
        simpa only [run,Except.toOption,Option.map_some,Option.some.injEq,Option.isSome_some,Bool.true_and,decide_eq_true_eq] using actual
      have inv := buildCtx_mappedInv (scope signed ty literal supported values) (built_run signed ty literal supported)
      have get : (frame signed ty literal).getAs 31 ty = .ok (BitVec.ofInt ty.width literal) := by
        cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
      have width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := by
        rcases supported with rfl | rfl | rfl | rfl <;> simp [Clif.Ty.width]
      have extension : (if signed then 0 else 1 : Nat) = 0 ∨ (if signed then 0 else 1 : Nat) = 1 := by
        cases signed <;> simp
      have bounded : aliases.size ≤ (built signed ty literal).2.2.base.nextVreg := by
        cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rcases values with rfl | rfl <;> decide +kernel
      have result := stock_div_divisor_values data_program inv refines (dfg signed ty literal supported) get
        (n := 499) (by decide) width extension run bounded idem (extent signed ty literal supported)
        (held signed ty literal supported values (Demanded next))
      exact ⟨out,next,trace,inv,dfg signed ty literal supported,get,rfl,fired,result⟩
end Backend.Stock.Proof.ScalarDiv.DivisorValueWitness

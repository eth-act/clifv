import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.StockDivDividendValues
namespace Backend.Stock.Proof.ScalarDiv.DividendValueWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarShift
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private def function (ty : Clif.Ty) : Clif.Function := {
  name := "stock_extend_values",sig := {params := [⟨ty,.none,.normal⟩],returns := [⟨ty,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,ty)],body := [],term := .ret [7]}] }
private def built (ty : Clif.Ty) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function ty)).toOption.getD (sinkCtx,#[],sinkState)
private def frame (ty : Clif.Ty) : Clif.Frame := {
  func := function ty,regs := fun x => if x = 7 then some (.ofInt ty 165) else none,
  slots := [],body := [],term := .ret [7] }
private def regs (n : Nat) : CV := if n = 192 then BitVec.ofNat 128 (2^100+165) else 0
private theorem scope (ty : Clif.Ty) (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    LowerScope (function ty) := lowerScope_of (by rcases supported with rfl | rfl | rfl | rfl <;> decide +kernel)
private theorem build (ty : Clif.Ty) (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    Stock.buildCtx (function ty) = .ok (built ty) := by rcases supported with rfl | rfl | rfl | rfl <;> rfl
private theorem dfg (ty : Clif.Ty) (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    DFGCons (built ty).1 (frame ty) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases seven : x = 7
    · subst x
      have absent : (built ty).1.defInst? 7 = none := by rcases supported with rfl | rfl | rfl | rfl <;> rfl
      rw [absent] at defined; cases defined
    · simp [frame,seven] at lookup
  · intro x t v typed lookup
    by_cases seven : x = 7
    · subst x
      rcases supported with rfl | rfl | rfl | rfl
      all_goals
        change some (.int _) = some t at typed
        cases typed
        cases lookup
        rfl
    · simp [frame,seven] at lookup
private theorem extent (ty : Clif.Ty) (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64)
    (x : Nat) (r : Reg) (mapped : (built ty).1.valueReg? x = some r) : x < (built ty).2.2.demand.size := by
  by_cases large : 8 ≤ x
  · have outside : (built ty).1.valReg.size ≤ x := by rcases supported with rfl | rfl | rfl | rfl <;> change 8 ≤ x <;> exact large
    change ((built ty).1.valReg[x]?).join = some r at mapped
    rw [Array.getElem?_eq_none outside] at mapped; cases mapped
  · have size : (built ty).2.2.demand.size = 8 := by rcases supported with rfl | rfl | rfl | rfl <;> rfl
    rw [size]; omega
section Runs
attribute [local semireducible] Isle.Aarch64.program
private theorem observed (sg wide : Bool) (ty : Clif.Ty)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    ((applyTerm program (Stock.sem (built ty).1) {} 81 27 (extTerm sg wide) [.value 7]).run
      ((built ty).2.2,#[])).toOption.any (fun result => result.1.isSome) = true := by
  cases sg <;> cases wide <;> rcases supported with rfl | rfl | rfl | rfl <;> decide +kernel
end Runs

/-- All four actual extension helpers are inhabited at8/16/32/64 bits, covering
pass-through and emitted-extension selections with deliberately dirty upper bits. -/
theorem stock_div_dividend_values_witness (sg : Bool) (ty : Clif.Ty)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    ∃ (out : V) (next : State) (trace : Array RuleId),
      MappedCtxInv (function ty) (built ty).1 ∧ DFGCons (built ty).1 (frame ty) ∧
      (applyTerm program (Stock.sem (built ty).1) {} 81 27 (extTerm sg (ty.width == 64)) [.value 7]).run
        ((built ty).2.2,#[]) = .ok (some out,next,trace) ∧
      DividendValueOut (fun _ => True) ispec (built ty).1 7 sg ty (BitVec.ofNat ty.width 165)
        (built ty).2.2 next out #[] regs := by
  have actual := observed sg (ty.width == 64) ty supported
  cases run : (applyTerm program (Stock.sem (built ty).1) {} 81 27 (extTerm sg (ty.width == 64)) [.value 7]).run
      ((built ty).2.2,#[]) with
  | error err => simp [run,Except.toOption] at actual
  | ok result =>
    obtain ⟨value,next,trace⟩ := result
    cases value with
    | none => simp [run,Except.toOption] at actual
    | some out =>
      have inv := buildCtx_mappedInv (scope ty supported) (build ty supported)
      have source : (frame ty).getAs 7 ty = .ok (BitVec.ofNat ty.width 165) := by rcases supported with rfl | rfl | rfl | rfl <;> rfl
      have held : ValuesHeld (Demanded next) (built ty).1 (frame ty) (fun k => regs (aliasNum #[] k)) := by
        intro x needed val lookup
        by_cases seven : x = 7
        · subst x
          change some (.ofInt ty 165) = some val at lookup
          cases lookup
          refine ⟨192,?_,?_⟩
          · rcases supported with rfl | rfl | rfl | rfl <;> rfl
          · rcases supported with rfl | rfl | rfl | rfl <;> unfold VHolds <;> decide +kernel
        · simp [frame,seven] at lookup
      have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
      have value := stock_div_extended_dividend_values data_program inv self sg (ty.width == 64) (n := 80) (by decide)
        (dfg ty supported) source (by rcases supported with rfl | rfl | rfl | rfl <;> decide) (aliases := #[]) (ρ := regs) (by simp) (extent ty supported) held run
      exact ⟨out,next,trace,inv,dfg ty supported,rfl,value⟩
/-- The real unsigned64 register request also inhabits the original-source
operand contract and its empty, register-preserving fragment. -/
theorem stock_div_plain_dividend_values_witness :
    ∃ out next,MappedCtxInv (function .i64) (built .i64).1 ∧ DFGCons (built .i64).1 (frame .i64) ∧
      Stock.externCtor (built .i64).1 T.put_in_reg [.value 7] (built .i64).2.2 = .ok (out,next) ∧
      DividendValueOut (fun _ => True) ispec (built .i64).1 7 false .i64 (BitVec.ofNat 64 165)
        (built .i64).2.2 next out #[] regs := by
  have supported : Clif.Ty.i64 = .i8 ∨ Clif.Ty.i64 = .i16 ∨ Clif.Ty.i64 = .i32 ∨ Clif.Ty.i64 = .i64 := Or.inr (Or.inr (Or.inr rfl))
  have inv := buildCtx_mappedInv (scope .i64 supported) (build .i64 supported)
  have source : (frame .i64).getAs 7 .i64 = .ok (BitVec.ofNat 64 165) := rfl
  have run : Stock.externCtor (built .i64).1 T.put_in_reg [.value 7] (built .i64).2.2 =
      .ok (.reg (.vreg 192 .int),(built .i64).2.2.mark 7) := rfl
  have held : ValuesHeld (Demanded ((built .i64).2.2.mark 7)) (built .i64).1 (frame .i64)
      (fun k => regs (aliasNum #[] k)) := by
    intro x needed value lookup
    by_cases seven : x = 7
    · subst x
      change some (.ofInt .i64 165) = some value at lookup
      cases lookup
      exact ⟨192,rfl,by unfold VHolds; decide +kernel⟩
    · simp [frame,seven] at lookup
  have value := stock_div_plain_dividend_values inv (F := fun _ => True) (isem := ispec) source
    (aliases := #[]) (ρ := regs) (extent .i64 supported) held run
  exact ⟨_,_,inv,dfg .i64 supported,run,value⟩
end Backend.Stock.Proof.ScalarDiv.DividendValueWitness

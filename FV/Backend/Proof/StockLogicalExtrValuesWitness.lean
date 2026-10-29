module

public import FV.Backend.Proof.StockLogicalExtrValues

@[expose] public section

namespace Backend.Stock.Proof.LogicalExtr
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def inputFrame (ty : Clif.Ty) (a b : CV) : Clif.Frame := {
  func := default
  regs := fun z => if z = 0 then some ⟨ty,a.setWidth ty.width⟩
    else if z = 1 then some ⟨ty,b.setWidth ty.width⟩ else none
  slots := []
  body := []
  term := .ret [] }
private def inputRF (a b : CV) : Nat → CV :=
  fun n => if n = 192 then a else if n = 193 then b else 0
private def afterRhs (w : Nat) : State :=
  {(sinkState.mark 0).mark 1 with base := (sinkState.base.fresh .int).2.emit (.aluRRRShift .extr
    (szOf w) (sinkState.base.fresh .int).1 (.vreg 192 .int) (.vreg 193 .int) (shiftFor w 1))}

/-- Actual successful RHSs at both source-compatible shifts inhabit the whole
value bridge for arbitrary independent machine words, at both widths and mirrors. -/
theorem rhs_values_witness (mirrored : Bool) (ty : Clif.Ty)
    (supported : ty = .i32 ∨ ty = .i64) (a b : CV) :
    ∃ trace,
      (evalExpr program (Stock.sem sinkCtx) {} 60 (extrRule mirrored).rhs
        (extrEnv mirrored ty.width 0 (ty.width-1 : Nat) 1 1)).run (sinkState,#[]) =
        .ok (some (.regsVec [[(sinkState.base.fresh .int).1]]),afterRhs ty.width,trace) ∧
      ValueOut (fun _ => True) ispec ty (a.setWidth ty.width) (b.setWidth ty.width)
        (ty.width-1) 1 sinkState (afterRhs ty.width)
        (.regsVec [[(sinkState.base.fresh .int).1]]) #[] (inputRF a b) := by
  have width : ty.width = 32 ∨ ty.width = 64 := by
    rcases supported with rfl | rfl <;> simp [Clif.Ty.width]
  obtain ⟨trace,run⟩ := rhs_witness mirrored ty.width width
  refine ⟨trace,run,?_⟩
  have sourceX : (inputFrame ty a b).getAs 0 ty = .ok (a.setWidth ty.width) := by
    simp [Clif.Frame.getAs,Clif.Frame.get,inputFrame,Clif.Res.ofOption]
  have sourceY : (inputFrame ty a b).getAs 1 ty = .ok (b.setWidth ty.width) := by
    simp [Clif.Frame.getAs,Clif.Frame.get,inputFrame,Clif.Res.ofOption]
  have extent : ∀ z r,sinkCtx.valueReg? z = some r → z < sinkState.demand.size := by
    intro z r mapped
    change z < 2
    by_cases small : z < 2
    · exact small
    · have bound : 2 ≤ z := Nat.le_of_not_lt small
      change (#[some (.vreg 192 .int),some (.vreg 193 .int)][z]?).join = some r at mapped
      rw [Array.getElem?_eq_none bound] at mapped
      cases mapped
  have held : ValuesHeld (Demanded (afterRhs ty.width)) sinkCtx (inputFrame ty a b)
      (fun z => inputRF a b (aliasNum #[] z)) := by
    intro z needed val found
    by_cases h0 : z = 0
    · subst z
      simp only [inputFrame,ite_true] at found
      cases found
      exact ⟨192,rfl,by rfl⟩
    · by_cases h1 : z = 1
      · subst z
        simp only [inputFrame,h0,ite_false,ite_true] at found
        cases found
        exact ⟨193,rfl,by rfl⟩
      · simp only [inputFrame,h0,h1,ite_false] at found
        cases found
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have sum : ((ty.width-1 : Nat) : Int).toNat+(1 : Int).toNat = ty.width := by
    simp only [Int.toNat_natCast,show (1 : Int).toNat = 1 from rfl]
    rcases width with h | h <;> omega
  have count : (1 : Int).toNat < ty.width := by rcases width with h | h <;> omega
  simpa only [Int.toNat_natCast,show (1 : Int).toNat = 1 from rfl] using
    rhs_values data_program mirrored self width sum count sourceX sourceY
      (aliases := #[]) (ρ := inputRF a b) (by decide) extent held (n := 0) run
end Backend.Stock.Proof.LogicalExtr

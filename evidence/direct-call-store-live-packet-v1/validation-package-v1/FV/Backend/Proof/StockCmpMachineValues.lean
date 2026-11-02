import FV.Backend.Proof.StockCmpFlags
import FV.Backend.Proof.IselCmpCond
import FV.Backend.Proof.IselCmpRoot
import FV.Backend.Proof.IselCmpDiv
import FV.Backend.Proof.StockAliasSemantics
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Flag production followed by a boolean result uses the standard-only
condition inversion variant, leaving the legacy contract unchanged. -/
theorem stock_cmp_flags_cset {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {m : MInst} {ρ : Nat → CV} {ps : Arm.PState}
    {condition : Cond} {value : Bool} (flags : SetsFlags m ρ ps)
    (truth : condOn condition.bits ps = value) (valid : condition ≠ .al ∧ condition ≠ .nv)
    (d : Nat) (world : Arm.ArmState) :
    Runs F isem [m,.cset (.vreg d .int) condition] ρ world (fun ρ' _ =>
      ρ' = upd ρ d (ofX (if value then 1#64 else 0#64))) := by
  refine Runs.append (ms1 := [m]) (Runs.flags refines flags world) (fun ρ1 w1 ⟨same,produced⟩ => ?_)
  subst ρ1
  refine (Runs.cset refines d valid ρ w1).imp (fun ρ' _ _ actual => ?_)
  rw [actual,produced,stock_cmp_condition_invert _ valid,truth]
  cases value <;> rfl
/-- Established signed/unsigned source extensions yield the original comparison
predicate at the real machine operand width, including narrow source values. -/
theorem stock_cmp_original_flags {n : Nat} (width : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (cc : Clif.IntCC) {a b : BitVec n} {A B : CV}
    (inputA : DivOpnd (signedCC cc) a A) (inputB : DivOpnd (signedCC cc) b B) :
    condOn (condOf cc).bits (cmpFlags (opnd (szOf n) A) (opnd (szOf n) B)) = Clif.Sem.intcc cc a b := by
  unfold DivOpnd at inputA inputB
  rcases width with rfl | rfl | rfl | rfl
  · simp only [show (8:Nat) ≤ 32 by decide,ite_true] at inputA inputB
    have actual := stock_cmp_conditions (n := 32) (Or.inl rfl) cc (opnd .size32 A) (opnd .size32 B)
    rw [show opnd .size32 A = (lo64 A).setWidth 32 from rfl,
      show opnd .size32 B = (lo64 B).setWidth 32 from rfl,inputA,inputB] at actual
    change condOn (condOf cc).bits (cmpFlags ((lo64 A).setWidth 32) ((lo64 B).setWidth 32)) = _
    rw [inputA,inputB]
    cases signed : signedCC cc <;> simp only [signed,Bool.false_eq_true,ite_false,ite_true] at actual ⊢
    · exact actual.trans (stock_cmp_unsigned_extension (by decide) cc signed a b)
    · exact actual.trans (stock_cmp_signed_extension (by decide) cc signed a b)
  · simp only [show (16:Nat) ≤ 32 by decide,ite_true] at inputA inputB
    have actual := stock_cmp_conditions (n := 32) (Or.inl rfl) cc (opnd .size32 A) (opnd .size32 B)
    rw [show opnd .size32 A = (lo64 A).setWidth 32 from rfl,
      show opnd .size32 B = (lo64 B).setWidth 32 from rfl,inputA,inputB] at actual
    change condOn (condOf cc).bits (cmpFlags ((lo64 A).setWidth 32) ((lo64 B).setWidth 32)) = _
    rw [inputA,inputB]
    cases signed : signedCC cc <;> simp only [signed,Bool.false_eq_true,ite_false,ite_true] at actual ⊢
    · exact actual.trans (stock_cmp_unsigned_extension (by decide) cc signed a b)
    · exact actual.trans (stock_cmp_signed_extension (by decide) cc signed a b)
  · simp only [show (32:Nat) ≤ 32 by decide,ite_true] at inputA inputB
    have actual := stock_cmp_conditions (n := 32) (Or.inl rfl) cc (opnd .size32 A) (opnd .size32 B)
    rw [show opnd .size32 A = (lo64 A).setWidth 32 from rfl,
      show opnd .size32 B = (lo64 B).setWidth 32 from rfl,inputA,inputB] at actual
    change condOn (condOf cc).bits (cmpFlags ((lo64 A).setWidth 32) ((lo64 B).setWidth 32)) = _
    rw [inputA,inputB]
    cases signed : signedCC cc <;> simp only [signed,Bool.false_eq_true,ite_false,ite_true] at actual ⊢
    · exact actual.trans (stock_cmp_unsigned_extension (by decide) cc signed a b)
    · exact actual.trans (stock_cmp_signed_extension (by decide) cc signed a b)
  · simp only [show ¬(64:Nat) ≤ 32 by decide,ite_false] at inputA inputB
    have actual := stock_cmp_conditions (n := 64) (Or.inr rfl) cc (opnd .size64 A) (opnd .size64 B)
    rw [show opnd .size64 A = (lo64 A).setWidth 64 from rfl,
      show opnd .size64 B = (lo64 B).setWidth 64 from rfl,inputA,inputB] at actual
    change condOn (condOf cc).bits (cmpFlags ((lo64 A).setWidth 64) ((lo64 B).setWidth 64)) = _
    rw [inputA,inputB]
    exact actual
/-- The actual compare/cset pair executes through final aliases and holds the
original boolean source result, preserving every other machine register. -/
theorem stock_cmp_rr_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {n : Nat} (width : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (cc : Clif.IntCC) {a b : BitVec n} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    {x y d : Nat} (bounded : aliases.size ≤ d)
    (inputA : DivOpnd (signedCC cc) a (ρ (aliasNum aliases x)))
    (inputB : DivOpnd (signedCC cc) b (ρ (aliasNum aliases y))) (world : Arm.ArmState) :
    Runs F isem ([MInst.aluRRR .subS (szOf n) .xzr (.vreg x .int) (.vreg y .int),
      .cset (.vreg d .int) (condOf cc)].map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc a b)⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  have code : ([MInst.aluRRR .subS (szOf n) .xzr (.vreg x .int) (.vreg y .int),
      .cset (.vreg d .int) (condOf cc)].map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) =
      [.aluRRR .subS (szOf n) .xzr (.vreg (aliasNum aliases x) .int) (.vreg (aliasNum aliases y) .int),
        .cset (.vreg d .int) (condOf cc)] := by
    simp only [List.map_cons,List.map_nil,MInst.mapRegs,resolve_vreg]
    change [MInst.aluRRR .subS (szOf n) .xzr (.vreg (aliasNum aliases x) .int) (.vreg (aliasNum aliases y) .int),
      .cset (.vreg (aliasNum aliases d) .int) (condOf cc)] = _
    rw [fresh]
  rw [code]
  have flags := setsFlags_cmpRR (szOf n) (aliasNum aliases x) (aliasNum aliases y) ρ
  have original := stock_cmp_original_flags width cc inputA inputB
  exact (stock_cmp_flags_cset refines flags original (condOf_ne_al cc) d world).imp
    (fun ρ' _ _ same => by
      subst ρ'
      refine ⟨?_,fun k different => by simp [upd,different]⟩
      rw [upd_same]
      exact vholds_bool8 _)
end Backend.Stock.Proof.ScalarCmp

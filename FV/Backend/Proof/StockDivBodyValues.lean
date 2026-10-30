import FV.Backend.Proof.IselCmpDivRem
import FV.Backend.Proof.StockDivResolved
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem alias_fresh {aliases : Array (Option Nat)} {d : Nat} (bounded : aliases.size ≤ d) :
    aliasNum aliases d = d := by
  apply chaseF_none
  rw [Array.getElem?_eq_none bounded]
  rfl
/-- The real signed/unsigned quotient instruction implements successful original
source division from established original operands. Source errors are handled by
the preceding zero/overflow guards, rather than excluded from the full family. -/
theorem stock_div_quotient_source_values {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (signed : Bool) {ty : Clif.Ty} {u v q : BitVec ty.width}
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (source : Clif.Sem.div (if signed then .sdiv else .udiv) u v = .ok q)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {a b d : Nat} (bounded : aliases.size ≤ d)
    (inputX : DivOpnd signed u (ρ (aliasNum aliases a))) (inputY : DivOpnd signed v (ρ (aliasNum aliases b))) :
    ∃ ρ',PRun F isem
      [(MInst.aluRRR (if signed then .sDiv else .uDiv) (szOf ty.width) (.vreg d .int) (.vreg a .int) (.vreg b .int)).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧ VHolds ⟨ty,q⟩ (ρ' d) ∧
      ∀ k,k ≠ d → ρ' k = ρ k := by
  obtain ⟨ρ',execution,value,kept⟩ := stock_div_quotient_resolved refines signed (szOf ty.width) bounded
  refine ⟨ρ',execution,?_,kept⟩
  rw [value]
  cases signed
  · obtain ⟨_,rfl⟩ := udiv_ok source
    exact udiv_vholds (by omega) inputX inputY
  · obtain ⟨_,noOverflow,rfl⟩ := sdiv_ok source
    have guarded : u ≠ BitVec.intMin ty.width ∨ v ≠ -1#ty.width := by
      by_cases minimum : u = BitVec.intMin ty.width
      · right
        rw [BitVec.neg_one_eq_allOnes]
        exact fun minusOne => noOverflow ⟨minimum,minusOne⟩
      · exact Or.inl minimum
    exact sdiv_core (n := ty.width) (by omega) inputX inputY guarded
/-- The actual divide/multiply-subtract pair implements original signed or
unsigned remainder, retaining every register outside its two fresh results.
Operand noncapture is an internal allocation/availability obligation. -/
theorem stock_div_remainder_source_values {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (signed : Bool) {ty : Clif.Ty} {u v r : BitVec ty.width}
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (source : Clif.Sem.div (if signed then .srem else .urem) u v = .ok r)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {a b d : Nat} (bounded : aliases.size ≤ d)
    (outsideX : aliasNum aliases a ≠ d) (outsideY : aliasNum aliases b ≠ d)
    (inputX : DivOpnd signed u (ρ (aliasNum aliases a))) (inputY : DivOpnd signed v (ρ (aliasNum aliases b))) :
    ∃ ρ',PRun F isem
      ([MInst.aluRRR (if signed then .sDiv else .uDiv) (szOf ty.width) (.vreg d .int) (.vreg a .int) (.vreg b .int),
        MInst.aluRRRR .mSub (szOf ty.width) (.vreg (d+1) .int) (.vreg d .int) (.vreg b .int) (.vreg a .int)].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,r⟩ (ρ' (d+1)) ∧ ∀ k,k < d ∨ d+2 ≤ k → ρ' k = ρ k := by
  obtain ⟨ρ1,divide,quotient,kept1⟩ := stock_div_quotient_resolved refines signed (szOf ty.width) bounded
  obtain ⟨ρ2,multiply,remainder,kept2⟩ := stock_div_msub_resolved refines (szOf ty.width)
    (aliases := aliases) (ρ := ρ1) (a := d) (b := b) (c := a) (d := d+1) (by omega)
  have fresh : aliasNum aliases d = d := alias_fresh bounded
  rw [fresh,quotient,kept1 _ outsideX,kept1 _ outsideY] at remainder
  refine ⟨ρ2,prun_append divide multiply,?_,?_⟩
  · rw [remainder]
    cases signed
    · obtain ⟨_,rfl⟩ := urem_ok source
      exact urem_vholds (by omega) inputX inputY
    · obtain ⟨_,rfl⟩ := srem_ok source
      exact srem_core (n := ty.width) (by omega) inputX inputY
  · intro k outside
    rw [kept2 k (by omega),kept1 k (by omega)]
end Backend.Stock.Proof.ScalarDiv

import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.IselFamAluBPopcnt
import FV.Backend.Proof.StockPopcountMath
import FV.Backend.Proof.StockPopcountRhs
namespace Backend.Stock.Proof.ScalarPopcount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem fresh_reg {aliases : Array (Option Nat)} {d : Nat} (cls : RegClass)
    (bounded : aliases.size ≤ d) :
    Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d cls) = .vreg d cls := by
  rw [resolve_vreg]
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none; rw [Array.getElem?_eq_none bounded]; rfl
  change Reg.vreg (aliasNum aliases d) cls = _
  rw [fresh]
def popcountCode (w d x : Nat) : List MInst :=
  [.movToFpu (.vreg d .float) (.vreg x .int) (if w = 64 then .size64 else .size32),
   .vecMisc .cnt (.vreg (d+1) .float) (.vreg d .float) .size8x8] ++
  (if w = 8 then [.movFromVec (.vreg (d+2) .int) (.vreg (d+1) .float) 0 .size8]
   else [if w = 16 then .vecRRR .addp (.vreg (d+2) .float) (.vreg (d+1) .float) (.vreg (d+1) .float) .size8x8
         else .vecLanes .addv (.vreg (d+2) .float) (.vreg (d+1) .float) .size8x8,
         .movFromVec (.vreg (d+3) .int) (.vreg (d+2) .float) 0 .size8])
/-- Complete mixed-class popcount templates read original values through final
aliases and preserve registers below and above their entire fresh allocation. -/
private theorem resolved_core {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (w : Nat) (width : IW w)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {d x : Nat} (bounded : aliases.size ≤ d)
    :
    ∃ ρ',PRun F isem ((popcountCode w d x).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      (ρ' (popcountResult w d)).setWidth w = ((ρ (aliasNum aliases x)).setWidth w).cpop ∧
      ∀ z,z < d ∨ d+popcountAlloc w ≤ z → ρ' z = ρ z := by
  let raw := ρ (aliasNum aliases x)
  let m0 := if w = 64 then (lo64 raw).setWidth 128 else ((lo64 raw).setWidth 32).setWidth 128
  let s0 := upd ρ d m0
  let m1 := (cntBytes (lo64 (s0 d))).setWidth 128
  let s1 := upd s0 (d+1) m1
  let m2 := if w = 16 then (addpBytes (lo64 (s1 (d+1))) (lo64 (s1 (d+1)))).setWidth 128
    else (addvBytes (lo64 (s1 (d+1)))).setWidth 128
  let s2 := upd s1 (d+2) m2
  let result := ofX (((if w = 8 then s1 (d+1) else s2 (d+2)).extractLsb' 0 8).setWidth 64)
  let final := upd (if w = 8 then s1 else s2) (popcountResult w d) result
  refine ⟨final,?_,?_,?_⟩
  · simp only [popcountCode,List.map_append,List.map_cons,List.map_nil,MInst.mapRegs]
    rw [fresh_reg .float bounded,fresh_reg .float (by omega : aliases.size ≤ d+1),resolve_vreg]
    rcases width with rfl | rfl | rfl | rfl
    all_goals simp only [Nat.reduceEqDiff,ite_true,ite_false,List.append_cons,List.nil_append,List.append_nil]
    all_goals simp only [List.map_cons,List.map_nil,MInst.mapRegs]
    all_goals simp only [List.cons_append,List.nil_append,
      fresh_reg .float bounded,fresh_reg .float (by omega : aliases.size ≤ d+1),
      fresh_reg .float (by omega : aliases.size ≤ d+2),fresh_reg .int (by omega : aliases.size ≤ d+2),
      fresh_reg .int (by omega : aliases.size ≤ d+3)]
    all_goals first
      | (exact prun_rr_c refines rfl (fun _ => rfl)
          (prun_rr_c refines rfl (fun _ => rfl)
          (prun_rr_c refines rfl (fun _ => rfl) (prun_nil _))))
      | (exact prun_rr_c refines rfl (fun _ => rfl)
          (prun_rr_c refines rfl (fun _ => rfl)
          (prun_rrr_c refines rfl (fun _ => rfl)
          (prun_rr_c refines rfl (fun _ => rfl) (prun_nil _)))))
      | (exact prun_rr_c refines rfl (fun _ => rfl)
          (prun_rr_c refines rfl (fun _ => rfl)
          (prun_rr_c refines rfl (fun _ => rfl)
          (prun_rr_c refines rfl (fun _ => rfl) (prun_nil _)))))
  · change (final (popcountResult w d)).setWidth w = (raw.setWidth w).cpop
    dsimp only [final]
    rw [upd_same]
    dsimp only [result,s2,s1,s0,m2,m1,m0]
    simp only [upd_same]
    rcases width with rfl | rfl | rfl | rfl
    all_goals simp only [Nat.reduceEqDiff,ite_true,ite_false]
    · exact stock_popcnt8_fin raw
    · exact stock_popcnt16_fin raw
    · exact stock_popcnt32_fin raw
    · exact stock_popcnt64_fin raw
  · intro z outside
    rcases width with rfl | rfl | rfl | rfl
    all_goals simp only [popcountAlloc,Nat.reduceEqDiff,ite_true,ite_false] at outside
    all_goals simp (disch := omega) only [final,popcountResult,Nat.reduceEqDiff,ite_true,ite_false,s2,s1,s0,upd_ne_fb]
/-- Actual mixed-class templates compute the original scalar count through
final aliases, preserving both sides of the complete allocation. -/
theorem stock_popcount_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {ty : Clif.Ty} (width : IW ty.width)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {d x : Nat} (bounded : aliases.size ≤ d)
    {u : BitVec ty.width} (held : VHolds ⟨ty,u⟩ (ρ (aliasNum aliases x))) :
    ∃ ρ',PRun F isem ((popcountCode ty.width d x).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,u.cpop⟩ (ρ' (popcountResult ty.width d)) ∧
      ∀ z,z < d ∨ d+popcountAlloc ty.width ≤ z → ρ' z = ρ z := by
  obtain ⟨ρ',execution,value,kept⟩ := resolved_core refines ty.width width bounded
  exact ⟨ρ',execution,value.trans (congrArg BitVec.cpop held),kept⟩
/-- Dirty upper machine bits and empty final aliases inhabit the complete
machine-template contracts at every scalar width. Original driver/source
witnesses remain a separate requirement for retained composition. -/
theorem stock_popcount_machine_witness : ∀ ty ∈ ([.i8,.i16,.i32,.i64] : List Clif.Ty),
    let X : CV := BitVec.ofNat 128 (2^100+2^64+291)
    ∃ ρ',PRun (fun _ => True) ispec ((popcountCode ty.width 1 0).map
      (·.mapRegs (Backend.lowerFunction.resolve #[] 1))) (fun _ => X) ρ' ∧
      VHolds ⟨ty,(X.setWidth ty.width).cpop⟩ (ρ' (popcountResult ty.width 1)) ∧
      ∀ z,z < 1 ∨ 1+popcountAlloc ty.width ≤ z → ρ' z = X := by
  intro ty member
  have width : IW ty.width := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp [IW,Clif.Ty.width]
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ world' _ h => ⟨world',h,SameWorld.refl _ _⟩
  exact stock_popcount_resolved self width (aliases := #[]) (d := 1) (x := 0) (by decide) rfl
end Backend.Stock.Proof.ScalarPopcount

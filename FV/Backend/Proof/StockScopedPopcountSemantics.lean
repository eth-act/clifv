import FV.Backend.Proof.StockPopcountForms
import FV.Backend.Proof.StockCountSemantics
namespace Backend.Stock.Proof.Popcount
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

private theorem mapped_code {aliases : Array (Option Nat)} {d x : Nat}
    (bounded : aliases.size ≤ d) (w : Nat) :
    ((popcountCode w d x).map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) =
      popcountCode w d (aliasNum aliases x) := by
  have a : aliasNum aliases d = d := by
    apply chaseF_none; rw [Array.getElem?_eq_none bounded]; rfl
  have b : aliasNum aliases (d+1) = d+1 := by
    apply chaseF_none; rw [Array.getElem?_eq_none (by omega : aliases.size ≤ d+1)]; rfl
  have c : aliasNum aliases (d+2) = d+2 := by
    apply chaseF_none; rw [Array.getElem?_eq_none (by omega : aliases.size ≤ d+2)]; rfl
  have e : aliasNum aliases (d+3) = d+3 := by
    apply chaseF_none; rw [Array.getElem?_eq_none (by omega : aliases.size ≤ d+3)]; rfl
  simp only [aliasNum] at a b c e
  by_cases wide : w = 64
  all_goals
    by_cases byte : w = 8
    all_goals
      by_cases half : w = 16
      all_goals simp [popcountCode,wide,byte,half,ite_false,ite_true,List.map_append,
        List.map_cons,List.map_nil,MInst.mapRegs,resolve_vreg,a,b,c,e]
      all_goals rfl

/-- Actual resolved scalar/vector templates implement the source bit count and
write only their fresh allocation, even when old register high bits are arbitrary. -/
theorem resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {ty : Clif.Ty} (width : IW ty.width)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {d x : Nat}
    (bounded : aliases.size ≤ d) {u : BitVec ty.width}
    (held : VHolds ⟨ty,u⟩ (ρ (aliasNum aliases x))) :
    ∃ ρ',PRun F isem ((popcountCode ty.width d x).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .popcnt u⟩ (ρ' (popcountResult ty.width d)) ∧
      ∀ n,n < d ∨ d+popcountAlloc ty.width ≤ n → ρ' n = ρ n := by
  rw [mapped_code bounded]
  rcases width with h | h | h | h
  · let a : CV := ((lo64 (ρ (aliasNum aliases x))).setWidth 32).setWidth 128
    let first := upd ρ d a
    let b : CV := (cntBytes (lo64 (first d))).setWidth 128
    let second := upd first (d+1) b
    let result : CV := ofX (((second (d+1)).extractLsb' (8*0) 8).setWidth 64)
    refine ⟨upd second (d+2) result,?_,?_,?_⟩
    · simp only [popcountCode,h]
      exact prun_rr_c refines rfl (fun _ => rfl) (prun_rr_c refines rfl (fun _ => rfl) (prun_rr_c refines rfl (fun _ => rfl) (prun_nil _)))
    · have index : popcountResult ty.width d = d+2 := by simp [popcountResult,popcountAlloc,h]
      rw [index,upd_same]
      change result.setWidth ty.width = Clif.Sem.unary .popcnt u
      have computed : result.setWidth ty.width = ((ρ (aliasNum aliases x)).setWidth ty.width).cpop := by
        rw [h]
        dsimp only [result,second,second,b,first,a]
        simp only [upd_same]
        exact Backend.Proof.popcnt8_fin (ρ (aliasNum aliases x))
      exact computed.trans (congrArg (fun v => v.cpop) held)
    · intro n outside
      simp [popcountAlloc,h] at outside
      simp only [result,second,second,first,upd,
        show n ≠ d by omega,show n ≠ d+1 by omega,show n ≠ d+2 by omega,
        ite_false]
  · let a : CV := ((lo64 (ρ (aliasNum aliases x))).setWidth 32).setWidth 128
    let first := upd ρ d a
    let b : CV := (cntBytes (lo64 (first d))).setWidth 128
    let second := upd first (d+1) b
    let c : CV := (addpBytes (lo64 (second (d+1))) (lo64 (second (d+1)))).setWidth 128
    let third := upd second (d+2) c
    let result : CV := ofX (((third (d+2)).extractLsb' (8*0) 8).setWidth 64)
    refine ⟨upd third (d+3) result,?_,?_,?_⟩
    · simp only [popcountCode,h]
      exact prun_rr_c refines rfl (fun _ => rfl) (prun_rr_c refines rfl (fun _ => rfl) (prun_rrr_c refines rfl (fun _ => rfl) (prun_rr_c refines rfl (fun _ => rfl) (prun_nil _))))
    · have index : popcountResult ty.width d = d+3 := by simp [popcountResult,popcountAlloc,h]
      rw [index,upd_same]
      change result.setWidth ty.width = Clif.Sem.unary .popcnt u
      have computed : result.setWidth ty.width = ((ρ (aliasNum aliases x)).setWidth ty.width).cpop := by
        rw [h]
        dsimp only [result,third,third,c,second,b,first,a]
        simp only [upd_same]
        exact Backend.Proof.popcnt16_fin (ρ (aliasNum aliases x))
      exact computed.trans (congrArg (fun v => v.cpop) held)
    · intro n outside
      simp [popcountAlloc,h] at outside
      simp only [result,third,third,second,first,upd,
        show n ≠ d by omega,show n ≠ d+1 by omega,show n ≠ d+2 by omega,
        show n ≠ d+3 by omega,
        ite_false]
  · let a : CV := ((lo64 (ρ (aliasNum aliases x))).setWidth 32).setWidth 128
    let first := upd ρ d a
    let b : CV := (cntBytes (lo64 (first d))).setWidth 128
    let second := upd first (d+1) b
    let c : CV := (addvBytes (lo64 (second (d+1)))).setWidth 128
    let third := upd second (d+2) c
    let result : CV := ofX (((third (d+2)).extractLsb' (8*0) 8).setWidth 64)
    refine ⟨upd third (d+3) result,?_,?_,?_⟩
    · simp only [popcountCode,h]
      exact prun_rr_c refines rfl (fun _ => rfl) (prun_rr_c refines rfl (fun _ => rfl) (prun_rr_c refines rfl (fun _ => rfl) (prun_rr_c refines rfl (fun _ => rfl) (prun_nil _))))
    · have index : popcountResult ty.width d = d+3 := by simp [popcountResult,popcountAlloc,h]
      rw [index,upd_same]
      change result.setWidth ty.width = Clif.Sem.unary .popcnt u
      have computed : result.setWidth ty.width = ((ρ (aliasNum aliases x)).setWidth ty.width).cpop := by
        rw [h]
        dsimp only [result,third,third,c,second,b,first,a]
        simp only [upd_same]
        exact Backend.Proof.popcnt32_fin (ρ (aliasNum aliases x))
      exact computed.trans (congrArg (fun v => v.cpop) held)
    · intro n outside
      simp [popcountAlloc,h] at outside
      simp only [result,third,third,second,first,upd,
        show n ≠ d by omega,show n ≠ d+1 by omega,show n ≠ d+2 by omega,
        show n ≠ d+3 by omega,
        ite_false]
  · let a : CV := (lo64 (ρ (aliasNum aliases x))).setWidth 128
    let first := upd ρ d a
    let b : CV := (cntBytes (lo64 (first d))).setWidth 128
    let second := upd first (d+1) b
    let c : CV := (addvBytes (lo64 (second (d+1)))).setWidth 128
    let third := upd second (d+2) c
    let result : CV := ofX (((third (d+2)).extractLsb' (8*0) 8).setWidth 64)
    refine ⟨upd third (d+3) result,?_,?_,?_⟩
    · simp only [popcountCode,h]
      exact prun_rr_c refines rfl (fun _ => rfl) (prun_rr_c refines rfl (fun _ => rfl) (prun_rr_c refines rfl (fun _ => rfl) (prun_rr_c refines rfl (fun _ => rfl) (prun_nil _))))
    · have index : popcountResult ty.width d = d+3 := by simp [popcountResult,popcountAlloc,h]
      rw [index,upd_same]
      change result.setWidth ty.width = Clif.Sem.unary .popcnt u
      have computed : result.setWidth ty.width = ((ρ (aliasNum aliases x)).setWidth ty.width).cpop := by
        rw [h]
        dsimp only [result,third,third,c,second,b,first,a]
        simp only [upd_same]
        exact Backend.Proof.popcnt64_fin (ρ (aliasNum aliases x))
      exact computed.trans (congrArg (fun v => v.cpop) held)
    · intro n outside
      simp [popcountAlloc,h] at outside
      simp only [result,third,third,second,first,upd,
        show n ≠ d by omega,show n ≠ d+1 by omega,show n ≠ d+2 by omega,
        show n ≠ d+3 by omega,
        ite_false]
end Backend.Stock.Proof.Popcount

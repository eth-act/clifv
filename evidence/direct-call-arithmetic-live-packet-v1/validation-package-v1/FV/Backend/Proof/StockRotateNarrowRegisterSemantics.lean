import FV.Backend.Proof.StockRotateNarrowRoots
namespace Backend.Stock.Proof.ScalarRotate
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem fresh_reg {aliases : Array (Option Nat)} {d : Nat} (bounded : aliases.size ≤ d) :
    Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int) = .vreg d .int := by
  rw [resolve_vreg]
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none; rw [Array.getElem?_eq_none bounded]; rfl
  change Reg.vreg (aliasNum aliases d) .int = _
  rw [fresh]
def rotateNarrowHelperCode (w d x a : Nat) : List MInst :=
  [.aluRRImmLogic .and .size32 (.vreg d .int) (.vreg a .int) ⟨w-1,.size32⟩,
   .aluRRImm12 .sub .size32 (.vreg (d+1) .int) (.vreg d .int) ⟨w,false⟩,
   .aluRRR .sub .size32 (.vreg (d+2) .int) .xzr (.vreg (d+1) .int),
   .aluRRR .lsr .size32 (.vreg (d+3) .int) (.vreg x .int) (.vreg d .int),
   .aluRRR .lsl .size32 (.vreg (d+4) .int) (.vreg x .int) (.vreg (d+2) .int),
   .aluRRR .orr .size32 (.vreg (d+5) .int) (.vreg (d+4) .int) (.vreg (d+3) .int)]
private theorem helper_value {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {w : Nat} (width : w = 8 ∨ w = 16) {d x a : Nat}
    (protectedX : x < d ∨ d+6 ≤ x) (ρ : Nat → CV) :
    ∃ ρ',PRun F isem (rotateNarrowHelperCode w d x a) ρ ρ' ∧
      (∀ z,z < d ∨ d+6 ≤ z → ρ' z = ρ z) ∧
      ∀ u : BitVec w,opnd .size32 (ρ x) = u.setWidth 32 →
        (ρ' (d+5)).setWidth w = u.rotateRight ((ρ a).toNat % w) := by
  let st : LState := {nextVreg := d,classes := #[]}
  let next : LState := {nextVreg := d+6,classes := #[],emitted := (rotateNarrowHelperCode w d x a).toArray}
  have small : w < 4096 := by rcases width with h | h <;> omega
  have run := stock_small_rotate_run refines width (imm := ⟨w,false⟩) rfl small
    (xv := x) (a := a) (st := st) (st' := next) protectedX (by simp [st,next,rotateNarrowHelperCode]) rfl
  obtain ⟨ms,result,output,shape,values⟩ := run
  have resultEq : result = d+5 := Reg.vreg.inj (V.reg.inj output.symm) |>.1
  have codeEq : ms = rotateNarrowHelperCode w d x a := by
    have eq := congrArg Array.toList shape.emitted
    simpa [st,next] using eq.symm
  subst result; subst ms
  exact values ρ
def rotateNarrowRegisterCode (left : Bool) (w d x y : Nat) : List MInst :=
  let e := if left then d+1 else d
  (if left then [.aluRRR .sub .size32 (.vreg d .int) .xzr (.vreg y .int)] else []) ++
    [.extend (.vreg e .int) (.vreg x .int) false w 32] ++
    rotateNarrowHelperCode w (e+1) e (if left then d else y)
def rotateNarrowRegisterAlloc (left : Bool) : Nat := if left then 8 else 7
private theorem helper_resolve {aliases : Array (Option Nat)} {d x a : Nat} (w : Nat)
    (bound : aliases.size ≤ d) (sourceFresh : aliases.size ≤ x) :
    (rotateNarrowHelperCode w d x a).map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))) =
      rotateNarrowHelperCode w d x (aliasNum aliases a) := by
  simp only [rotateNarrowHelperCode,List.map_cons,List.map_nil,MInst.mapRegs]
  rw [fresh_reg bound,fresh_reg (by omega : aliases.size ≤ d+1),
    fresh_reg (by omega : aliases.size ≤ d+2),fresh_reg (by omega : aliases.size ≤ d+3),
    fresh_reg (by omega : aliases.size ≤ d+4),fresh_reg (by omega : aliases.size ≤ d+5),
    fresh_reg sourceFresh,resolve_vreg]
  rfl
/-- The complete narrow register templates execute original low-bit rotation
through final aliases and preserve both sides of their allocation interval.
Source protection is internal and follows availability in retained records. -/
theorem stock_rotate_narrow_register_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (left : Bool) {ty : Clif.Ty} (width : ty.width = 8 ∨ ty.width = 16)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {d x y : Nat} (bounded : aliases.size ≤ d)
    (protectedX : left = true → aliasNum aliases x ≠ d)
    (protectedY : left = false → aliasNum aliases y ≠ d)
    {u : BitVec ty.width} (heldX : VHolds ⟨ty,u⟩ (ρ (aliasNum aliases x)))
    {amount : Clif.Val} (heldY : VHolds amount (ρ (aliasNum aliases y))) :
    ∃ ρ',PRun F isem ((rotateNarrowRegisterCode left ty.width d x y).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,rotateWideBits left u amount.bits.toNat⟩ (ρ' (rotateNarrowRootResult left d)) ∧
      ∀ z,z < d ∨ d+rotateNarrowRegisterAlloc left ≤ z → ρ' z = ρ z := by
  have iw : IW ty.width := by rcases width with h | h <;> simp [IW,h]
  have small : ty.width < 32 := by rcases width with h | h <;> omega
  have input : (lo64 (ρ (aliasNum aliases x))).setWidth ty.width = u := by
    change (opnd .size64 (ρ (aliasNum aliases x))).setWidth ty.width = u
    rw [opnd_setWidth (by change ty.width ≤ 64; omega) (by decide)]
    exact heldX
  have count := amt_of_holds iw heldY
  cases left
  · let r0 := resX .size32 (u.setWidth 32)
    let q0 := upd ρ d r0
    obtain ⟨ρ',helper,kept,result⟩ := helper_value refines width (d := d+1) (x := d)
      (a := aliasNum aliases y) (.inl (by omega)) q0
    refine ⟨ρ',?_,?_,?_⟩
    · simp only [rotateNarrowRegisterCode,Bool.false_eq_true,ite_false,List.nil_append,List.map_append]
      rw [helper_resolve ty.width (by omega) bounded]
      simp only [List.map_cons,List.map_nil,MInst.mapRegs]
      rw [fresh_reg bounded,resolve_vreg]
      exact prun_append (prun_rr refines rfl
        (fun _ => ispec_extend (width.elim (fun h => .inl h) (fun h => .inr (.inl h))) (.inl rfl) small)
        (by
          change PRun F isem [] (upd ρ d (resX .size32 (((lo64 (ρ (aliasNum aliases x))).setWidth ty.width).setWidth 32))) q0
          rw [input]; exact prun_nil q0)) helper
    · change (ρ' (d+6)).setWidth ty.width = _
      have value := result u (by simp only [q0,upd_same,r0]; exact opnd_resX .size32 (u.setWidth 32))
      change (ρ' (d+1+5)).setWidth ty.width = _
      rw [show q0 (aliasNum aliases y) = ρ (aliasNum aliases y) from upd_ne_fb (protectedY rfl)] at value
      simpa only [rotateWideBits,Bool.false_eq_true,ite_false,count] using value
    · intro z outside
      have after : z < d+1 ∨ d+1+6 ≤ z := by simp only [rotateNarrowRegisterAlloc,Bool.false_eq_true,ite_false] at outside; omega
      rw [kept z after]
      exact upd_ne_fb (by simp only [rotateNarrowRegisterAlloc,Bool.false_eq_true,ite_false] at outside; omega)
  · let r0 := resX .size32 (0-opnd .size32 (ρ (aliasNum aliases y)))
    let q0 := upd ρ d r0
    let r1 := resX .size32 (u.setWidth 32)
    let q1 := upd q0 (d+1) r1
    obtain ⟨ρ',helper,kept,result⟩ := helper_value refines width (d := d+2) (x := d+1)
      (a := d) (.inl (by omega)) q1
    refine ⟨ρ',?_,?_,?_⟩
    · simp only [rotateNarrowRegisterCode,ite_true,List.map_append]
      rw [helper_resolve ty.width (by omega) (by omega)]
      simp only [List.map_cons,List.map_nil,MInst.mapRegs]
      rw [fresh_reg bounded,resolve_vreg,fresh_reg (by omega : aliases.size ≤ d+1),resolve_vreg]
      have fixed : aliasNum aliases d = d := by
        apply chaseF_none; rw [Array.getElem?_eq_none bounded]; rfl
      rw [fixed]
      have source : (lo64 (q0 (aliasNum aliases x))).setWidth ty.width = u := by
        rw [show q0 (aliasNum aliases x) = ρ (aliasNum aliases x) from upd_ne_fb (protectedX rfl)]
        exact input
      have negRun : PRun F isem [.aluRRR .sub .size32 (.vreg d .int) .xzr (.vreg (aliasNum aliases y) .int)] ρ q0 :=
        prun_rr refines rfl (fun _ => ispec_sub_xzr_fb) (prun_nil q0)
      have extRun : PRun F isem [.extend (.vreg (d+1) .int) (.vreg (aliasNum aliases x) .int) false ty.width 32] q0 q1 :=
        prun_rr refines rfl
          (fun _ => ispec_extend (width.elim (fun h => .inl h) (fun h => .inr (.inl h))) (.inl rfl) small)
          (by
            change PRun F isem [] (upd q0 (d+1) (resX .size32 (((lo64 (q0 (aliasNum aliases x))).setWidth ty.width).setWidth 32))) q1
            rw [source]; exact prun_nil q1)
      exact prun_append (prun_append negRun extRun) helper
    · change (ρ' (d+7)).setWidth ty.width = _
      have value := result u (by simp only [q1,upd_same,r1]; exact opnd_resX .size32 (u.setWidth 32))
      have neg := neg_mod (N := 32) (w := ty.width) (.inl ⟨rfl,width.elim (fun h => .inl h) (fun h => .inr (.inl h))⟩)
        (opnd .size32 (ρ (aliasNum aliases y)))
      have negCount : (q1 d).toNat % ty.width = (ty.width-amount.bits.toNat%ty.width)%ty.width := by
        simp only [q1,upd_ne_fb (by omega : d ≠ d+1),q0,upd_same,r0]
        rw [← opnd_mod iw .size32 (resX .size32 _),opnd_resX]
        have negEq : (0-opnd .size32 (ρ (aliasNum aliases y))).toNat % ty.width =
            (ty.width-(opnd .size32 (ρ (aliasNum aliases y))).toNat%ty.width)%ty.width := neg
        rw [negEq,opnd_mod iw .size32 (ρ (aliasNum aliases y)),← count]
      rw [negCount] at value
      have positive : 0 < ty.width := by rcases width with h | h <;> omega
      exact value.trans (rotr_neg positive u (amount.bits.toNat % ty.width) _ (by simp only [Nat.mod_mod]))
    · intro z outside
      have after : z < d+2 ∨ d+2+6 ≤ z := by simp only [rotateNarrowRegisterAlloc,ite_true] at outside; omega
      rw [kept z after]
      simp only [q1,q0,upd,show z ≠ d+1 by simp only [rotateNarrowRegisterAlloc,ite_true] at outside; omega,
        show z ≠ d by simp only [rotateNarrowRegisterAlloc,ite_true] at outside; omega,ite_false]
end Backend.Stock.Proof.ScalarRotate

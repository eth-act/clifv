import FV.Backend.Proof.IselCmpSelect
import FV.Backend.Proof.StockCmpMachineValues
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem append_fall_inv {V W : Type} (sem : ISem V W) {leading suffix : List MInst}
    {ρ final : Nat → V} {w endWorld : W}
    (run : seqRun sem (leading++suffix) ρ w = some (.fall final endWorld)) :
    ∃ middle world,seqRun sem leading ρ w = some (.fall middle world) ∧
      seqRun sem suffix middle world = some (.fall final endWorld) := by
  induction leading generalizing ρ w with
  | nil => exact ⟨ρ,w,rfl,run⟩
  | cons i ms ih =>
    simp only [List.cons_append,seqRun] at run
    split at run
    · cases run
    · rename_i ops operands
      split at run
      · cases run
      · rename_i outs nextWorld ctl step
        split at run
        · rename_i length
          split at run
          · cases rest : seqRun sem (ms++suffix) (vdefUpd ops outs ρ) nextWorld with
            | none => rw [rest] at run; cases run
            | some result =>
              rw [rest] at run
              cases result with
              | fall after afterWorld =>
                cases run
                obtain ⟨middle,world,left,right⟩ := ih rest
                refine ⟨middle,world,?_,right⟩
                simp only [seqRun,operands,step,length,ite_true,left,Option.map_some]
                rfl
              | stop k j used before beforeWorld values stoppedWorld control => cases run
          · cases run
        · cases run
private theorem nf_symm {F : BitVec 64 → Prop} {a b : Arm.ArmState}
    (h : SameWorldNF F a b) : SameWorldNF F b a :=
  ⟨fun f hf hfl => (h.1 f hf hfl).symm,fun x hx => (h.2.1 x hx).symm,h.2.2.symm⟩
/-- The original Zero/NotZero consumer uses cmpXzr while its boolean companion
uses cmpImm0. Their common computed flags justify replacing both the zero
producer and the final boolean consumer after the same executed prefix. -/
theorem stock_select_replace_zero_cset {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {leading : List MInst} {ρ : Nat → CV} {world : Arm.ArmState}
    (nonzero : Bool) (size : OperandSize) (key : Nat) {d x y : Nat}
    {ty : Clif.Ty} (width : ty.width ≤ 64) {u v : BitVec ty.width} {b : Bool} {P : Nat → Prop}
    (separateX : x ≠ d) (separateY : y ≠ d) (outside : ∀ k,P k → k ≠ d)
    (run : Runs F isem (leading++[cmpImm0 size key,.cset (.vreg d .int) (if nonzero then .ne else .eq)])
      ρ world (fun final _ => VHolds ⟨.i8,Clif.Sem.bool8 b⟩ (final d) ∧ VHolds ⟨ty,u⟩ (final x) ∧
        VHolds ⟨ty,v⟩ (final y) ∧ ∀ k,P k → final k = ρ k)) :
    Runs F isem (leading++[cmpXzr size key,
      .csel (.vreg d .int) (.vreg x .int) (.vreg y .int) (if nonzero then .ne else .eq)]) ρ world
      (fun final _ => VHolds ⟨ty,if b then u else v⟩ (final d) ∧ ∀ k,P k → final k = ρ k) := by
  obtain ⟨final,endWorld,full,fullNF,boolean,inputX,inputY,frame⟩ := run
  obtain ⟨middle,middleWorld,prefixRun,tailRun⟩ := append_fall_inv isem full
  let value : Bool := if nonzero then opnd size (middle key) != 0 else opnd size (middle key) == 0
  have truth : condOn (if nonzero then Cond.ne else Cond.eq).bits
      (cmpFlags (opnd size (middle key)) 0) = value := by
    cases nonzero
    · exact ScalarCmp.stock_cmp_zero_flag _ _
    · exact ScalarCmp.stock_cmp_conditions (n := size.bits) (by cases size <;> simp [OperandSize.bits]) .ne _ _
  have valid : (if nonzero then Cond.ne else Cond.eq) ≠ .al ∧ (if nonzero then Cond.ne else Cond.eq) ≠ .nv := by
    cases nonzero <;> decide
  obtain ⟨expected,expectedWorld,expectedRun,tailNF,updated⟩ := ScalarCmp.stock_cmp_flags_cset refines
    (setsFlags_cmp_imm0 size key middle) truth valid d middleWorld
  have both := SeqEnd.fall.inj (Option.some.inj (tailRun.symm.trans expectedRun))
  have output : final = upd middle d (ofX (if value then 1#64 else 0#64)) := both.1.trans updated
  have suffixNF : SameWorldNF F endWorld middleWorld := by rw [both.2]; exact tailNF
  have middleNF := (nf_symm suffixNF).trans fullNF
  rw [output,upd_same] at boolean
  have equal : value = b := by
    cases hv : value <;> cases b
    all_goals simp [hv,VHolds,ofX,Clif.Sem.bool8,Clif.Ty.width] at boolean ⊢
  have originalX : VHolds ⟨ty,u⟩ (middle x) := by
    rw [output] at inputX
    simpa only [upd,separateX,ite_false] using inputX
  have originalY : VHolds ⟨ty,v⟩ (middle y) := by
    rw [output] at inputY
    simpa only [upd,separateY,ite_false] using inputY
  have oldFrame : ∀ k,P k → middle k = ρ k := by
    intro k hk
    have kept := frame k hk
    rw [output] at kept
    simpa only [upd,outside k hk,ite_false] using kept
  have prefixValue : Runs F isem leading ρ world (fun regs flags => regs = middle ∧ flags = middleWorld) :=
    ⟨middle,middleWorld,prefixRun,middleNF,rfl,rfl⟩
  refine Runs.append prefixValue ?_
  intro regs flags pair
  obtain ⟨sameRegs,sameFlags⟩ := pair
  subst regs
  subst flags
  apply (runs_flags_csel refines (setsFlags_cmpXzr size key middle) (truth.trans equal) d x y middleWorld).imp
  intro selected _ _ result
  subst selected
  constructor
  · rw [upd_same]
    cases b
    · change (ofX (lo64 (middle y))).setWidth ty.width = v
      exact (setWidth_ofX_lo64 width _).trans originalY
    · change (ofX (lo64 (middle x))).setWidth ty.width = u
      exact (setWidth_ofX_lo64 width _).trans originalX
  · intro k hk
    simpa only [upd,outside k hk,ite_false] using oldFrame k hk
end Backend.Stock.Proof.ScalarSelect

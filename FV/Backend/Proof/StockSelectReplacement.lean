import FV.Backend.Proof.StockCmpFlags
import FV.Backend.Proof.IselCmpSelect
import FV.Backend.Proof.PrepareCheck
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
private theorem condition_read (c : BitVec 4) (w : Arm.ArmState) :
    Arm.ConditionHolds c w = condOn c (Arm.read_pstate w) := by
  simp only [Arm.ConditionHolds,condOn,Arm.read_pstate,Arm.read_flag,Arm.r]
  rfl
private theorem condition_invert (c : Cond) (valid : c ≠ .al ∧ c ≠ .nv) (w : Arm.ArmState) :
    Arm.ConditionHolds c.invert.bits w = !Arm.ConditionHolds c.bits w := by
  rw [condition_read,condition_read,ScalarCmp.stock_cmp_condition_invert c valid]
/-- Replace the final boolean consumer with the actual csel, reusing the same
executed leading under arbitrary refining semantics. Prefix operands and frame
facts must come from the established comparison run; no instruction is inserted
into the selected code and no source classification is assumed here. -/
theorem stock_select_replace_cset {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {leading : List MInst} {ρ : Nat → CV} {world : Arm.ArmState}
    {d x y : Nat} {condition : Cond} (valid : condition ≠ .al ∧ condition ≠ .nv)
    {ty : Clif.Ty} (width : ty.width ≤ 64) {u v : BitVec ty.width} {b : Bool} {P : Nat → Prop}
    (separateX : x ≠ d) (separateY : y ≠ d) (outside : ∀ k,P k → k ≠ d)
    (run : Runs F isem (leading++[.cset (.vreg d .int) condition]) ρ world (fun final _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 b⟩ (final d) ∧ VHolds ⟨ty,u⟩ (final x) ∧
      VHolds ⟨ty,v⟩ (final y) ∧ ∀ k,P k → final k = ρ k)) :
    Runs F isem (leading++[.csel (.vreg d .int) (.vreg x .int) (.vreg y .int) condition]) ρ world
      (fun final _ => VHolds ⟨ty,if b then u else v⟩ (final d) ∧ ∀ k,P k → final k = ρ k) := by
  obtain ⟨final,endWorld,full,fullNF,boolean,inputX,inputY,frame⟩ := run
  obtain ⟨middle,middleWorld,prefixRun,tailRun⟩ := append_fall_inv isem full
  obtain ⟨expected,expectedWorld,expectedRun,tailNF,updated⟩ := Runs.cset refines d valid middle middleWorld
  have both := SeqEnd.fall.inj (Option.some.inj (tailRun.symm.trans expectedRun))
  have output : final = upd middle d (ofX (if Arm.ConditionHolds condition.invert.bits middleWorld then 0#64 else 1#64)) :=
    both.1.trans updated
  have suffixNF : SameWorldNF F endWorld middleWorld := by rw [both.2]; exact tailNF
  have middleNF := (nf_symm suffixNF).trans fullNF
  rw [output,upd_same,condition_invert condition valid] at boolean
  have truth : Arm.ConditionHolds condition.bits middleWorld = b := by
    cases actual : Arm.ConditionHolds condition.bits middleWorld <;> cases b
    all_goals simp [actual,VHolds,ofX,Clif.Sem.bool8,Clif.Ty.width] at boolean ⊢
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
  intro regs flags equal
  obtain ⟨sameRegs,sameFlags⟩ := equal
  subst regs
  subst flags
  apply (Runs.csel refines d x y condition middle middleWorld).imp
  intro selected _ _ value
  subst selected
  constructor
  · rw [upd_same,truth]
    cases b
    · change (ofX (lo64 (middle y))).setWidth ty.width = v
      exact (setWidth_ofX_lo64 width _).trans originalY
    · change (ofX (lo64 (middle x))).setWidth ty.width = u
      exact (setWidth_ofX_lo64 width _).trans originalX
  · intro k hk
    simpa only [upd,outside k hk,ite_false] using oldFrame k hk
/-- A successful existing comparison run under the instruction specification
establishes condition validity internally, including exclusion of AL/NV. -/
theorem stock_select_cset_condition_valid {leading : List MInst} {ρ : Nat → CV}
    {world : Arm.ArmState} {d : Nat} {condition : Cond}
    (run : ∃ final endWorld,seqRun ispec (leading++[.cset (.vreg d .int) condition]) ρ world =
      some (.fall final endWorld)) : condition ≠ .al ∧ condition ≠ .nv := by
  obtain ⟨final,endWorld,full⟩ := run
  obtain ⟨middle,middleWorld,_,tail⟩ := append_fall_inv ispec full
  constructor
  · intro equal
    rw [equal] at tail
    have failed : seqRun ispec [.cset (.vreg d .int) .al] middle middleWorld = none := rfl
    rw [failed] at tail
    cases tail
  · intro equal
    rw [equal] at tail
    have failed : seqRun ispec [.cset (.vreg d .int) .nv] middle middleWorld = none := rfl
    rw [failed] at tail
    cases tail
/-- The semantic comparison specification supplies condition validity, rather
than adding a caller condition-code certificate to the consumer replacement. -/
theorem stock_select_replace_cset_from_spec {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {leading : List MInst} {ρ : Nat → CV} {world : Arm.ArmState}
    {d x y : Nat} {condition : Cond} {ty : Clif.Ty} (width : ty.width ≤ 64)
    {u v : BitVec ty.width} {b : Bool} {P : Nat → Prop}
    (separateX : x ≠ d) (separateY : y ≠ d) (outside : ∀ k,P k → k ≠ d)
    (specification : ∃ final endWorld,seqRun ispec (leading++[.cset (.vreg d .int) condition]) ρ world =
      some (.fall final endWorld))
    (run : Runs F isem (leading++[.cset (.vreg d .int) condition]) ρ world (fun final _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 b⟩ (final d) ∧ VHolds ⟨ty,u⟩ (final x) ∧
      VHolds ⟨ty,v⟩ (final y) ∧ ∀ k,P k → final k = ρ k)) :
    Runs F isem (leading++[.csel (.vreg d .int) (.vreg x .int) (.vreg y .int) condition]) ρ world
      (fun final _ => VHolds ⟨ty,if b then u else v⟩ (final d) ∧ ∀ k,P k → final k = ρ k) :=
  stock_select_replace_cset refines (stock_select_cset_condition_valid specification) width separateX separateY outside run
end Backend.Stock.Proof.ScalarSelect

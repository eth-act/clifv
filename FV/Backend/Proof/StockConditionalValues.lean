import FV.Backend.Proof.StockCmpMachineValues
import FV.Backend.Proof.StockBranchHelperProjection
import FV.Backend.Proof.StockSequence
import FV.Backend.Proof.IselCtlBrif
namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Sequence
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
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
/-- Reuse a proved original condition's boolean companion to execute the real
branch. The ghost cset is removed, not inserted into the compiled program; only
the actual leading instructions and conditional terminator execute. -/
theorem branch_of_boolean_companion {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {leading : List MInst} {ρ : Nat → CV} {world : Arm.ArmState}
    {d : Nat} {condition : Cond} (valid : condition ≠ .al ∧ condition ≠ .nv)
    {b : Bool} {P : Nat → Prop} (outside : ∀ k,P k → k ≠ d)
    (run : Runs F isem (leading++[.cset (.vreg d .int) condition]) ρ world (fun final _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 b⟩ (final d) ∧ ∀ k,P k → final k = ρ k))
    (yes no : Label) :
    ∃ regs prefixWorld branchWorld,
      seqRun isem (leading++[.condBr yes no (.cond condition)]) ρ world =
        some (.stop leading.length (.condBr yes no (.cond condition)) #[] regs prefixWorld
          [] branchWorld (.goto (if b then 0 else 1))) ∧
      SameWorldNF F branchWorld world ∧ ∀ k,P k → regs k = ρ k := by
  obtain ⟨final,endWorld,full,fullNF,boolean,frame⟩ := run
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
  have oldFrame : ∀ k,P k → middle k = ρ k := by
    intro k hk
    have kept := frame k hk
    rw [output] at kept
    simpa only [upd,outside k hk,ite_false] using kept
  have spec : ispec (.condBr yes no (.cond condition)) [] middleWorld =
      some ([],middleWorld,.goto (if b then 0 else 1)) := by
    simp only [ispec,condBrHolds,truth]
  obtain ⟨branchWorld,branchRun,branchNF⟩ := seqRun_one_stop refines
    (operands_condBr_cond yes no condition) (ρ := middle) (by simp) spec (by simp)
  refine ⟨middle,middleWorld,branchWorld,?_,(SameWorld.nf branchNF).trans middleNF,oldFrame⟩
  simpa only [Nat.add_zero,Nat.zero_add] using seqRun_append_fall_stop isem prefixRun branchRun

/-- A real cset execution and arbitrary original flags inhabit the semantic
replacement, with both branch outcomes and all unaffected registers covered. -/
theorem branch_companion_witness {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (ρ : Nat → CV) (world : Arm.ArmState) :
    ∃ regs prefixWorld branchWorld,
      seqRun isem [.condBr 2 1 (.cond .eq)] ρ world =
        some (.stop 0 (.condBr 2 1 (.cond .eq)) #[] regs prefixWorld [] branchWorld
          (.goto (if Arm.ConditionHolds Cond.eq.bits world then 0 else 1))) ∧
      SameWorldNF F branchWorld world ∧ ∀ k,k ≠ 0 → regs k = ρ k := by
  have companion : Runs F isem [.cset (.vreg 0 .int) .eq] ρ world (fun final _ =>
      VHolds ⟨.i8,Clif.Sem.bool8 (Arm.ConditionHolds Cond.eq.bits world)⟩ (final 0) ∧
      ∀ k,k ≠ 0 → final k = ρ k) := by
    apply (Runs.cset refines 0 (by decide : Cond.eq ≠ .al ∧ Cond.eq ≠ .nv) ρ world).imp
    intro final endWorld _ updated
    rw [updated]
    constructor
    · rw [upd_same,condition_invert .eq (by decide)]
      cases h : Arm.ConditionHolds Cond.eq.bits world <;> rfl
    · intro k different
      simp only [upd,different,ite_false]
  exact branch_of_boolean_companion refines (leading := []) (by decide)
    (P := fun k => k ≠ 0) (fun _ h => h) companion 2 1

/-- A decoded zero/nonzero branch reuses the proved boolean companion while
removing both ghost comparison and cset. The real branch reads the value at the
same prefix boundary, including a real narrow-width extension when present. -/
theorem zero_branch_of_boolean_companion {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {leading : List MInst} {ρ : Nat → CV} {world : Arm.ArmState}
    (nonzero : Bool) (size : OperandSize) (key : Nat) {d : Nat} {b : Bool} {P : Nat → Prop}
    (outside : ∀ k,P k → k ≠ d)
    (run : Runs F isem (leading++[cmpImm0 size key,.cset (.vreg d .int) (if nonzero then .ne else .eq)])
      ρ world (fun final _ => VHolds ⟨.i8,Clif.Sem.bool8 b⟩ (final d) ∧ ∀ k,P k → final k = ρ k))
    (yes no : Label) :
    ∃ regs prefixWorld branchWorld,
      seqRun isem (leading++[.condBr yes no (if nonzero then .notZero (.vreg key .int) size else .zero (.vreg key .int) size)]) ρ world =
        some (.stop leading.length (.condBr yes no (if nonzero then .notZero (.vreg key .int) size else .zero (.vreg key .int) size))
          #[⟨key,.int,.use,.early,.reg⟩] regs prefixWorld [] branchWorld (.goto (if b then 0 else 1))) ∧
      SameWorldNF F branchWorld world ∧ ∀ k,P k → regs k = ρ k := by
  obtain ⟨final,endWorld,full,fullNF,boolean,frame⟩ := run
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
  have oldFrame : ∀ k,P k → middle k = ρ k := by
    intro k hk
    have kept := frame k hk
    rw [output] at kept
    simpa only [upd,outside k hk,ite_false] using kept
  let kind : CondBrKind := if nonzero then .notZero (.vreg key .int) size else .zero (.vreg key .int) size
  have operands : (MInst.condBr yes no kind).operands = .ok #[⟨key,.int,.use,.early,.reg⟩] := by cases nonzero <;> rfl
  have branchTruth : condBrHolds kind [middle key] middleWorld = value := by
    cases nonzero
    · exact condBrHolds_zero _ _ _ _
    · exact condBrHolds_notZero _ _ _ _
  have spec : ispec (.condBr yes no kind) (vuses #[⟨key,.int,.use,.early,.reg⟩] middle) middleWorld =
      some ([],middleWorld,.goto (if b then 0 else 1)) := by
    change some ([],middleWorld,Ctl.goto (if condBrHolds kind [middle key] middleWorld then 0 else 1)) = _
    rw [branchTruth,equal]
  obtain ⟨branchWorld,branchRun,branchNF⟩ := seqRun_one_stop refines operands (ρ := middle)
    (by simp) spec (by simp [Operand.isDef])
  refine ⟨middle,middleWorld,branchWorld,?_,(SameWorld.nf branchNF).trans middleNF,oldFrame⟩
  simpa only [Nat.zero_add] using seqRun_append_fall_stop isem prefixRun branchRun

/-- Arbitrary input words, both operand sizes and both zero polarities inhabit
real compare/cset-to-direct-branch replacement. -/
theorem zero_branch_companion_witness {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (ρ : Nat → CV) (world : Arm.ArmState)
    (nonzero : Bool) (size : OperandSize) :
    ∃ regs prefixWorld branchWorld,
      seqRun isem [.condBr 2 1 (if nonzero then .notZero (.vreg 1 .int) size else .zero (.vreg 1 .int) size)] ρ world =
        some (.stop 0 (.condBr 2 1 (if nonzero then .notZero (.vreg 1 .int) size else .zero (.vreg 1 .int) size))
          #[⟨1,.int,.use,.early,.reg⟩] regs prefixWorld [] branchWorld
          (.goto (if (if nonzero then opnd size (ρ 1) != 0 else opnd size (ρ 1) == 0) then 0 else 1))) ∧
      SameWorldNF F branchWorld world ∧ ∀ k,k ≠ 0 → regs k = ρ k := by
  let value : Bool := if nonzero then opnd size (ρ 1) != 0 else opnd size (ρ 1) == 0
  have truth : condOn (if nonzero then Cond.ne else Cond.eq).bits (cmpFlags (opnd size (ρ 1)) 0) = value := by
    cases nonzero
    · exact ScalarCmp.stock_cmp_zero_flag _ _
    · exact ScalarCmp.stock_cmp_conditions (n := size.bits) (by cases size <;> simp [OperandSize.bits]) .ne _ _
  have valid : (if nonzero then Cond.ne else Cond.eq) ≠ .al ∧ (if nonzero then Cond.ne else Cond.eq) ≠ .nv := by cases nonzero <;> decide
  obtain ⟨final,endWorld,run,nf,updated⟩ := ScalarCmp.stock_cmp_flags_cset refines
    (setsFlags_cmp_imm0 size 1 ρ) truth valid 0 world
  have companion : Runs F isem [cmpImm0 size 1,.cset (.vreg 0 .int) (if nonzero then .ne else .eq)]
      ρ world (fun result _ => VHolds ⟨.i8,Clif.Sem.bool8 value⟩ (result 0) ∧ ∀ k,k ≠ 0 → result k = ρ k) := by
    refine ⟨final,endWorld,run,nf,?_⟩
    rw [updated]
    constructor
    · rw [upd_same]
      cases value <;> rfl
    · intro k different
      simp only [upd,different,ite_false]
  exact zero_branch_of_boolean_companion refines (leading := []) nonzero size 1
    (P := fun k => k ≠ 0) (fun _ h => h) companion 2 1

/-- The actual conditional descriptor has the existing decoded branch form and
preserves the compiler base state. Its source condition semantics can therefore
reuse the established zero/nonzero/flag producers rather than a second selector. -/
theorem descriptor_shape {ctx : Ctx} {cfg : Config}
    (overlap : cfg.checkOverlap = false) {fuel : Nat} (enough : 100 ≤ fuel)
    {condition descriptor : V} {P : Nat → Prop} (shape : CondShape condition P)
    {a b : Label} {before after : State} {trace final : Array RuleId}
    (run : ApplyInternal program (Stock.sem ctx) cfg fuel 46 722
      [condition,.label a,.label b] (before,trace) descriptor (after,final)) :
    after.base = before.base ∧ descriptor = brCondV condition a b := by
  have projected := BranchHelpers.stock_br_cond_result_projects ctx cfg overlap (fuel+1)
    [condition,.label a,.label b] before trace
  have legacy : ApplyInternal program (Backend.sem ctx) cfg fuel 46 722
      [condition,.label a,.label b] (before.base,trace) descriptor (after.base,final) := by
    unfold ApplyInternal at run ⊢
    rw [run] at projected
    exact projected.symm
  exact br_cond_result_ok data_program overlap enough shape legacy

end Backend.Stock.Proof.ConditionalValues




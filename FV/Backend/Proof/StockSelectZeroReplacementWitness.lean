module

public import FV.Backend.Proof.StockSelectZeroReplacementResolved

@[expose] public section

namespace Backend.Stock.Proof.ScalarSelect.ZeroReplacementWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private def aliases : Array (Option Nat) := #[some 1,none,some 3,none,some 5,none]
private def registers (test : Bool) (key : Nat) : CV :=
  BitVec.ofNat 128 (2^100 + if key = 1 then (if test then 1 else 0) else if key = 3 then 7 else 9)
private def chosen (nonzero test : Bool) : Bool := if nonzero then test else !test
private def leading : MInst := .aluRRR .subS .size64 .xzr (.vreg 2 .int) (.vreg 2 .int)
private theorem boolean_run (ty : Clif.Ty)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (nonzero test : Bool) (size : OperandSize) (world : Arm.ArmState) :
    Runs (fun _ => True) ispec
      (([leading]++[cmpImm0 size 0,.cset (.vreg 6 .int) (if nonzero then .ne else .eq)]).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) (registers test) world
      (fun final _ => VHolds ⟨.i8,Clif.Sem.bool8 (chosen nonzero test)⟩ (final 6) ∧
        VHolds ⟨ty,BitVec.ofNat ty.width 7⟩ (final (aliasNum aliases 2)) ∧
        VHolds ⟨ty,BitVec.ofNat ty.width 9⟩ (final (aliasNum aliases 4)) ∧
        ∀ key,key ≠ 6 → final key = registers test key) := by
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  change Runs (fun _ => True) ispec
    ([MInst.aluRRR .subS .size64 .xzr (.vreg 3 .int) (.vreg 3 .int)]++
      [cmpImm0 size 1,.cset (.vreg 6 .int) (if nonzero then .ne else .eq)]) (registers test) world _
  have leadingRun := Runs.flags self (setsFlags_cmpRR .size64 3 3 (registers test)) world
  refine Runs.append leadingRun ?_
  intro middle flags preserved
  obtain ⟨same,_⟩ := preserved
  subst middle
  have truth : condOn (if nonzero then Cond.ne else Cond.eq).bits
      (cmpFlags (opnd size (registers test 1)) 0) = chosen nonzero test := by
    cases nonzero <;> cases test <;> cases size <;> decide +kernel
  have valid : (if nonzero then Cond.ne else Cond.eq) ≠ .al ∧
      (if nonzero then Cond.ne else Cond.eq) ≠ .nv := by cases nonzero <;> decide
  apply (ScalarCmp.stock_cmp_flags_cset self (setsFlags_cmp_imm0 size 1 (registers test)) truth valid 6 flags).imp
  intro final _ _ same
  subst final
  refine ⟨?_,?_,?_,?_⟩
  · rw [upd_same]
    cases nonzero <;> cases test <;> unfold VHolds <;> decide +kernel
  · change (registers test 3).setWidth ty.width = BitVec.ofNat ty.width 7
    rcases width with h | h | h | h <;> rw [h] <;> cases test <;> decide +kernel
  · change (registers test 5).setWidth ty.width = BitVec.ofNat ty.width 9
    rcases width with h | h | h | h <;> rw [h] <;> cases test <;> decide +kernel
  · intro key different
    simp only [upd,different,ite_false]
/-- Both zero condition forms, both sizes, both truth outcomes and every scalar
result width inhabit producer/consumer replacement after a nonempty prefix.
Real final aliases are nonidentity and input upper bits are dirty. -/
theorem stock_select_zero_replacement_alias_witness (ty : Clif.Ty)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (nonzero test : Bool) (size : OperandSize) (world : Arm.ArmState) :
    Runs (fun _ => True) ispec
      (([leading]++[cmpXzr size 0,.csel (.vreg 6 .int) (.vreg 2 .int) (.vreg 4 .int)
        (if nonzero then .ne else .eq)]).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) (registers test) world
      (fun final _ => VHolds ⟨ty,if chosen nonzero test then BitVec.ofNat ty.width 7 else BitVec.ofNat ty.width 9⟩ (final 6) ∧
        ∀ key,key ≠ 6 → final key = registers test key) := by
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  exact stock_select_replace_zero_cset_resolved self nonzero size 0 (by omega)
    (by decide) (by decide +kernel) (by decide +kernel) (fun _ h => h) (boolean_run ty width nonzero test size world)
end Backend.Stock.Proof.ScalarSelect.ZeroReplacementWitness

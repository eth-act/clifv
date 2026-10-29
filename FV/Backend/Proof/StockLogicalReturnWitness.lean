module

public import FV.Backend.Proof.StockLogicalReturnRefines
public import FV.Backend.Proof.StockLogicalRecordWitness
public import FV.Backend.Proof.MemRefines
public import FV.Backend.Proof.RefinesCSem
public import FV.E2E.RegLevelDriverSem

@[expose] public section

namespace Backend.Stock.Proof.LogicalBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64
open Backend.Stock.Proof.LogicalSelected Backend.Stock.Proof.LogicalSemantics
set_option autoImplicit false
set_option Elab.async false

private theorem rrDominated : Dominated (formFunction .registers) := by
  constructor
  · decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [formFunction,formX,formY] at block
      subst b
      constructor
      · intro j stm statement y member
        cases j <;> simp at statement
        subst stm
        change y ∈ [7, 31] at member
        change y ∈ (([7, 31] ++ (availIn (formFunction .registers) ctx).getD 0 [] ++ []).filter (fun x => decide (x ∉ [100])))
        simp only [List.mem_filter, decide_eq_true_eq, List.append_nil]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp
      · intro y member
        change y ∈ [100] at member
        have equal := List.mem_singleton.mp member
        subst y
        change 100 ∈ (([7, 31] ++ (availIn (formFunction .registers) ctx).getD 0 [] ++ [100]).filter
          (fun x => decide (x ∉ ([] : List Nat))))
        simp
    | succ bi => simp [formFunction,formX,formY] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bounds := (inFix_fixOk (f := (formFunction .registers)) (ctx := ctx) (gn := id)).cand tl x available
    have length : (formFunction .registers).blocks.length = 1 := rfl
    omega

/-- A real nonempty logical source body and arbitrary ABI argument values execute from
instruction zero to the actual return, without initial-value or row premises. -/
theorem actual_logical_entry_return_witness (u v : BitVec 64) (X : ExtSem)
    (base : Arm.ArmState) :
    ∃ (f : Clif.Function) (result : Result) (b : Clif.Block) (fr : Clif.Frame)
      (world : Arm.ArmState) (ρ : Nat → CV),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧ f.blocks = [b] ∧ b.body ≠ [] ∧
      Clif.enterFunc f [⟨.i64,u⟩,⟨.i64,v⟩] Clif.Mem.empty = .ok (fr,Clif.Mem.empty) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨fr,[],Clif.Mem.empty⟩ =
        .returned [⟨.i64,u ||| v⟩] Clif.Mem.empty ∧
      ArgsAtEntry (fun _ => False) f.sig [⟨.i64,u⟩,⟨.i64,v⟩] world ∧
      RunOkABI f result.code (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True) fr.slots
        ⟨0,0,ρ,world⟩ (.returned [⟨.i64,u ||| v⟩] Clif.Mem.empty) := by
  obtain ⟨input⟩ := stock_lower_logical_record_inputs_witness .registers
  have run := input.run
  have scope := formScope .registers
  have dominated := rrDominated
  let f := formFunction .registers
  let b := f.blocks[0]!
  let fr : Clif.Frame := {
    func := f
    regs := (Clif.Regs.empty.set 7 ⟨.i64,u⟩).set 31 ⟨.i64,v⟩
    slots := []
    body := b.body
    term := b.term }
  let world := Arm.write_base_gpr 0 u (Arm.write_base_gpr 1 v base)
  have family : ∀ stm ∈ b.body, Family stm.inst := by
    intro stm member
    change stm ∈ [⟨[100],.binary .bor .i64 7 31⟩] at member
    have equal := List.mem_singleton.mp member
    subst stm
    exact Or.inr (Or.inr ⟨.bor,.i64,7,31,rfl⟩)
  have entered : Clif.enterFunc f [⟨.i64,u⟩,⟨.i64,v⟩] Clif.Mem.empty =
      .ok (fr,Clif.Mem.empty) := rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨fr,[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,u ||| v⟩] Clif.Mem.empty := rfl
  have arg0 : VHolds ⟨.i64,u⟩ (regVal world (.x 0)) := by
    simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
      Arm.read_store,Arm.write_store,rnum]
    change (u.setWidth 128).setWidth 64 = u
    rw [BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_eq]
  have arg1 : VHolds ⟨.i64,v⟩ (regVal world (.x 1)) := by
    simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
      Arm.read_store,Arm.write_store,rnum]
    change (v.setWidth 128).setWidth 64 = v
    rw [BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_eq]
  have arguments : ArgsAtEntry (fun _ => False) f.sig [⟨.i64,u⟩,⟨.i64,v⟩] world := by
    intro loc value member
    change (loc,value) ∈ [(.reg (.x 0),⟨.i64,u⟩),(.reg (.x 1),⟨.i64,v⟩)] at member
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact arg0
    · have equal := List.mem_singleton.mp member
      cases equal; exact arg1
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by
    intro _ _ _ _ _ _
    trivial
  have memSem : MemRefines (fun _ => False) 0 (fun _ => none) (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  obtain ⟨ρ,semantics⟩ := actual_logical_entry_return_refines run scope dominated (abi := rfl)
    (b := b) rfl family (xs := [100]) rfl entered returned
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    memSem stable trivial arguments
  exact ⟨f,_,b,fr,world,ρ,run,scope,dominated,rfl,by decide,entered,returned,arguments,semantics⟩

end Backend.Stock.Proof.LogicalBody

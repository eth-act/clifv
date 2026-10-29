module

public import FV.Backend.Proof.StockArithmeticEntryRefines
public import FV.Backend.Proof.StockScalarAddScanWitness
public import FV.Backend.Proof.StockScalarAddSource
public import FV.Backend.Proof.MemRefines
public import FV.Backend.Proof.RefinesCSem
public import FV.E2E.RegLevelDriverSem

@[expose] public section

namespace Backend.Stock.Proof.ArithmeticBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- A real nonempty source body and arbitrary ABI argument values execute from
instruction zero to the actual return, without initial-value or row premises. -/
theorem actual_arithmetic_entry_return_witness (u v : BitVec 64) (X : ExtSem)
    (base : Arm.ArmState) :
    ∃ (f : Clif.Function) (result : Result) (b : Clif.Block) (fr : Clif.Frame)
      (world : Arm.ArmState) (ρ : Nat → CV),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧ f.blocks = [b] ∧ b.body ≠ [] ∧
      Clif.enterFunc f [⟨.i64,u⟩,⟨.i64,v⟩] Clif.Mem.empty = .ok (fr,Clif.Mem.empty) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨fr,[],Clif.Mem.empty⟩ =
        .returned [⟨.i64,u+v⟩] Clif.Mem.empty ∧
      ArgsAtEntry (fun _ => False) f.sig [⟨.i64,u⟩,⟨.i64,v⟩] world ∧
      RunOkABI f result.code (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True) fr.slots
        ⟨0,0,ρ,world⟩ (.returned [⟨.i64,u+v⟩] Clif.Mem.empty) := by
  obtain ⟨run,scope,dominated,events,records,scanned,oldFamilies,source,execution⟩ :=
    ScalarAddScanWitness.actual_scan_body_witness
  let f := ScalarAdd.source "scalar_add_scan" .systemVI64 []
  let b := f.blocks[0]!
  let fr := ScalarAdd.Source.frame "scalar_add_scan" .systemVI64 [] u v
  let world := Arm.write_base_gpr 0 u (Arm.write_base_gpr 1 v base)
  have family : ∀ stm ∈ b.body, ∃ subtract : Bool, ∃ ty x y,
      stm.inst = .binary (if subtract then .isub else .iadd) ty x y := by
    intro stm member
    change stm ∈ [⟨[2],.binary .iadd .i64 0 1⟩] at member
    have equal := List.mem_singleton.mp member
    subst stm
    exact ⟨false,.i64,0,1,rfl⟩
  have entered : Clif.enterFunc f [⟨.i64,u⟩,⟨.i64,v⟩] Clif.Mem.empty =
      .ok (fr,Clif.Mem.empty) := rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨fr,[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,u+v⟩] Clif.Mem.empty := rfl
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
  obtain ⟨ρ,semantics⟩ := actual_arithmetic_entry_return_refines run scope dominated (abi := rfl)
    (b := b) rfl family (xs := [2]) rfl entered returned
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    memSem stable trivial arguments
  exact ⟨f,_,b,fr,world,ρ,run,scope,dominated,rfl,by decide,entered,returned,arguments,semantics⟩

end Backend.Stock.Proof.ArithmeticBody

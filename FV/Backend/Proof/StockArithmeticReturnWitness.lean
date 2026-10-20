import FV.Backend.Proof.StockArithmeticReturnRefines
import FV.Backend.Proof.StockScalarAddScanWitness
namespace Backend.Stock.Proof.ArithmeticBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Real reference entry, nonempty arithmetic, dirty machine inputs and the
actual VCode return inhabit the complete body/return simulation boundary. -/
theorem actual_arithmetic_return_witness :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (b : Clif.Block)
      (args : List Clif.Val) (fr : Clif.Frame) (cm : Clif.Mem)
      (label k : Nat) (registers : Nat → CV),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧ sigAbiOk f.sig = true ∧
      event ∈ result.blockScans.toList ∧ f.blocks = [b] ∧ b.body ≠ [] ∧
      Clif.enterFunc f args Clif.Mem.empty = .ok (fr,cm) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨fr,[],cm⟩ = .returned [⟨.i64,12⟩] Clif.Mem.empty ∧
      ∀ w, GuardedScanRel f result event.ctx event.block (fun _ memory _ => memory = Clif.Mem.empty)
        event.output.state (0,fr,cm) registers w ∧
        RunOkABI f result.code ispec (fun _ memory _ => memory = Clif.Mem.empty) fr.slots
          ⟨label,k,registers,w⟩ (.returned [⟨.i64,12⟩] Clif.Mem.empty) := by
  obtain ⟨run,scope,dominated,events,records,scanned,oldFamilies,source,execution⟩ :=
    ScalarAddScanWitness.actual_scan_body_witness
  obtain ⟨oldBlock,oldTerm,oldBody,oldSplit,oldFamily,behaviour⟩ :=
    ScalarAddScanWitness.actual_body_split_witness
  let b := (ScalarAdd.source "scalar_add_scan" .systemVI64 []).blocks[0]!
  have family : ∀ stm ∈ b.body, ∃ subtract : Bool, ∃ ty x y,
      stm.inst = .binary (if subtract then .isub else .iadd) ty x y := by
    intro stm member
    change stm ∈ [⟨[2],.binary .iadd .i64 0 1⟩] at member
    have eq := List.mem_singleton.mp member
    subst stm
    exact ⟨false,.i64,0,1,rfl⟩
  let args : List Clif.Val := [⟨.i64,7⟩,⟨.i64,5⟩]
  let fr := ScalarAdd.Source.frame "scalar_add_scan" .systemVI64 [] 7 5
  have entered : Clif.enterFunc (ScalarAdd.source "scalar_add_scan" .systemVI64 []) args Clif.Mem.empty =
      .ok (fr,Clif.Mem.empty) := rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨fr,[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,12⟩] Clif.Mem.empty := rfl
  have abi : sigAbiOk (ScalarAdd.source "scalar_add_scan" .systemVI64 []).sig = true := rfl
  have self : Refines (fun _ => True) ispec :=
    fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have stable : MRStable (fun _ => True) (fun _ cm _ => cm = Clif.Mem.empty) := by
    intro _ _ _ _ _ h
    exact h
  obtain ⟨label,k,semantics⟩ := actual_arithmetic_entered_return_refines
    run scope dominated abi (b := b) rfl family (xs := [2]) rfl events entered returned self stable
  exact ⟨_,_,_,b,args,fr,Clif.Mem.empty,label,k,_,run,scope,dominated,abi,events,rfl,
    by decide,entered,returned,by
      intro w
      have pre := (behaviour w).1
      exact ⟨pre,semantics _ w pre⟩⟩

end Backend.Stock.Proof.ArithmeticBody

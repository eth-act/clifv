import FV.Backend.Proof.StockMemoryReturnRefines
import FV.Backend.Proof.StockMemoryLoadWitness
import FV.E2E.RegLevelDriverSem
import FV.Backend.Proof.RefinesCSem

namespace Backend.Stock.Memory.EntryFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def function : Clif.Function := {
  name := "ordinary_entry_return"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(0,.i64)],term := .ret [0]}] }
private def frame : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 0 ⟨.i64,4096⟩,slots := [],body := [],term := .ret [0] }
private def world : Arm.ArmState := Arm.write_base_gpr 0#5 4096 LoadFixture.world
private theorem scope : LowerScope function := lowerScope_of rfl
private theorem dominated : Dominated function := by
  constructor
  · change ([0] : List Nat).Nodup; decide
  · intro ctx ranges st build bi b found
    have bound : bi < 1 := by have h := lt_of_getElem? found; simpa [function] using h
    have zero : bi = 0 := by omega
    subst bi
    simp [function] at found
    subst b
    constructor
    · intro j stm present; simp at present
    · intro x member
      have zero : x = 0 := by simpa [abiTerm,Driver.termArgs,sretRet,sigRets,function] using member
      subst x
      simp [availOf,function,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have length : function.blocks.length = 1 := rfl
    omega
private theorem memory : LoadFixture.relation.holds function frame.slots LoadFixture.heap world := by
  refine ⟨⟨?_,LoadFixture.memory_world.1.valid,rfl⟩,?_,E2E.outRel_zero _ _ _⟩
  · intro a b valid byte
    exact LoadFixture.memory_world.1.bytes a b valid byte
  · intro id b present; cases present
private theorem arguments : ArgsAtEntry LoadFixture.relation.F function.sig [⟨.i64,4096⟩] world := by
  intro loc value member
  change (loc,value) ∈ [(.reg (.x 0),⟨.i64,4096⟩)] at member
  cases List.mem_singleton.mp member
  simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum]
  rfl
private theorem lowered : (Stock.lower function).isOk = true := by decide +kernel

/-- The additive ordinary entry wrapper has inhabited original ABI/source/world
premises and starts the actual Stock machine at instruction zero. Memory remains
the live nonempty heap; the load-body return witness is separate. -/
theorem ordinary_entry_return_witness (X : ExtSem) :
    ∃ (result : Result) (ρ : Nat → CV),Stock.lower function = .ok result ∧
      RunOkABI function result.code (csem LoadFixture.relation.F ⟨0,0⟩ X)
        (LoadFixture.relation.holds function) frame.slots ⟨0,0,ρ,world⟩
        (.returned [⟨.i64,4096⟩] LoadFixture.heap) := by
  have success := lowered
  cases run : Stock.lower function with
  | error err => rw [run] at success; cases success
  | ok result =>
    have entered : SourceEntry function [⟨.i64,4096⟩] frame :=
      SourceEntry.of_enterFunc (show Clif.enterFunc function [⟨.i64,4096⟩] LoadFixture.heap = .ok (frame,LoadFixture.heap) from rfl)
    obtain ⟨ρ,returned⟩ := OrdinaryBody.actual_ordinary_entry_return_refines_frame run scope dominated rfl rfl
      (by intro stm member; cases member) rfl entered
      (show Clif.runLoop Clif.Env.empty {funcs := []} 1 ⟨frame,[],LoadFixture.heap⟩ =
        .returned [⟨.i64,4096⟩] LoadFixture.heap from rfl)
      (refines_csem LoadFixture.relation.F ⟨0,0⟩ X) (driverSem_csem LoadFixture.relation.F ⟨0,0⟩ X)
      (memRefines_csem LoadFixture.relation.F ⟨0,0⟩ X (syms := fun _ => none) rfl (fun _ _ h => by cases h))
      (E2E.mrStable_holds LoadFixture.relation function)
      (by
        intro event events
        obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope events
        have bound : event.block < 1 := by have h := lt_of_getElem? split.block; simpa [function] using h
        have zero : event.block = 0 := by omega
        have same : b = function.blocks[0]! := Option.some.inj (split.block.symm.trans (by rw [zero]; rfl))
        subst b
        refine ⟨term,body,split,?_⟩
        have normal : ∀ record ∈ body.records,
            ScanFallRefines (IndexedSourceInst Clif.Env.empty {funcs := []} function event.ctx event.block)
              (csem LoadFixture.relation.F ⟨0,0⟩ X) result.final.alias
              (GuardedScanRel function result event.ctx event.block (LoadFixture.relation.holds function)) record := by
          intro record member
          obtain ⟨j,stm,statement,current⟩ := split.positions record member
          change ([] : List Clif.Stmt)[j]? = some stm at statement
          simp at statement
        intro s s' source ρ w held
        apply split.scanned.fall_refines normal s s'
        · simpa [sourceBodyIndices,function] using source
        · simpa only [split.state] using held)
      memory arguments
    exact ⟨result,ρ,rfl,returned⟩

end Backend.Stock.Memory.EntryFixture

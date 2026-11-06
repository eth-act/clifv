import FV.Backend.Proof.StockMemorySinkExtBody
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.RefinesCSem
import FV.Backend.Proof.MemRefines
import FV.Backend.Proof.StockSourceEntry
import FV.E2E.Main
import FV.E2E.RegLevelDriverSem

/-! Non-vacuity of the sinking body on Cranelift's `%load_uextend_i8_i32`
(`load-extends.clif`, default trapping load): a live heap byte 165 at address 4096,
the actual original-scope Stock code, and the original source run returning
`uextend.i32 (load.i8 v0)`. The value lemma, the extension record facts, the body
simulation and the return contract are all instantiated. -/
namespace Backend.Stock.Memory.SinkExtend
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64 E2E
open Backend.Stock.Memory.ExtendedRoots (Kind)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.lower

private def block : Clif.Block :=
  { id := 0, params := [(0,.i64)],
    body := [⟨[1],.load .load .i8 {} 0 0⟩,⟨[2],.extend .uextend .i32 1⟩],
    term := .ret [2] }

private def function : Clif.Function :=
  { name := "load_uextend_i8_i32",
    sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨.i32,.none,.normal⟩] },
    blocks := [block] }

private def lowers : Bool :=
  match Stock.lower function with
  | .ok result => result.blockScans.size == 1
  | .error _ => false

section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.lower
private theorem lowers_true : lowers = true := by decide +kernel
private theorem scope_true : lowerScopeB function = true := by decide +kernel
end Kernel

private theorem dominated : Dominated function := by
  constructor
  · change ([0,1,2] : List Nat).Nodup; decide
  · intro ctx ranges st build bi b found
    have bound : bi < 1 := by have h := lt_of_getElem? found; simpa [function] using h
    have zero : bi = 0 := by omega
    subst bi
    simp [function] at found
    subst b
    constructor
    · intro j stm present
      cases j with
      | zero =>
        simp [block] at present
        subst stm
        intro x member
        have zero : x = 0 := by simpa [Driver.instArgs] using member
        subst x
        simp [availOf,function,block,defsBefore,defsFrom]
      | succ j =>
        cases j with
        | zero =>
          simp [block] at present
          subst stm
          intro x member
          have one : x = 1 := by simpa [Driver.instArgs] using member
          subst x
          simp [availOf,function,block,defsBefore,defsFrom]
        | succ j => simp [block] at present
    · intro x member
      have two : x = 2 := by
        simpa [abiTerm,Driver.termArgs,sretRet,sigRets,function,block] using member
      subst x
      simp [availOf,function,block,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have length : function.blocks.length = 1 := rfl
    omega

private theorem shape : Shape .unsigned8 function block 0 1 2 .i32 {} :=
  ⟨rfl,rfl,rfl,rfl,by simp [block],by simp [function,sigRets]⟩

private theorem actual : ∃ (result : Result) (event : BlockScanEvent),
    Stock.lower function = .ok result ∧ event ∈ result.blockScans.toList := by
  have lowered := lowers_true
  unfold lowers at lowered
  cases run : Stock.lower function with
  | error e => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    have size : result.blockScans.size = 1 := by simpa using lowered
    exact ⟨result,result.blockScans[0],rfl,Array.mem_toList_iff.mpr (Array.getElem_mem (by omega))⟩

private def initial : Clif.Frame :=
  { func := function, regs := Clif.Regs.empty.set 0 ⟨.i64,4096⟩, slots := [],
    body := block.body, term := block.term }
private def loaded : Clif.Frame :=
  { initial with regs := initial.regs.set 1 ⟨.i8,165⟩, body := [⟨[2],.extend .uextend .i32 1⟩] }
private def heap : Clif.Mem := {allocs := [⟨4096,8,false⟩],bytes := fun _ => some 165}
private def baseWorld : Arm.ArmState := {Arm.ArmState.default with mem := fun _ => 165}
private def world : Arm.ArmState := Arm.write_base_gpr 0#5 4096 baseWorld
private def relation : E2E.Rel := ⟨fun _ => False,fun _ => none,0,0⟩
private def noExternal : ExtSem := ⟨fun _ _ _ => none,fun _ _ => 0,0,fun _ _ => Arm.PState.zero⟩

/-- The two source steps and the single extending source load agree on the live byte. -/
theorem extend_load_eval_witness :
    Clif.evalInst initial heap (.load .load .i8 {} 0 0) = .ok ([⟨.i8,165⟩],heap) ∧
    loaded.get 1 = .ok ⟨.i8,165⟩ ∧
    Clif.evalInst loaded heap (.extend .uextend .i32 1) = .ok ([⟨.i32,165⟩],heap) ∧
    Clif.evalInst initial heap (.load .uload8 .i32 {} 0 0) = .ok ([⟨.i32,165⟩],heap) := by
  have first : Clif.evalInst initial heap (.load .load .i8 {} 0 0) = .ok ([⟨.i8,165⟩],heap) := by rfl
  have second : loaded.get 1 = .ok ⟨.i8,165⟩ := by rfl
  have third : Clif.evalInst loaded heap (.extend .uextend .i32 1) = .ok ([⟨.i32,165⟩],heap) := by rfl
  exact ⟨first,second,third,(extend_load_eval .unsigned8 first second third).2⟩

private theorem memory_base : relation.holds function initial.slots heap baseWorld := by
  refine ⟨⟨?_,?_,rfl⟩,?_,outRel_zero _ _ _⟩
  · intro a b valid byte
    have equal : (165 : BitVec 8) = b := Option.some.inj byte
    subst b
    rfl
  · intro a n valid
    have bound : 4096 ≤ a ∧ a+n ≤ 4104 := by
      simpa [heap,Clif.Mem.valid,Clif.Alloc.contains] using valid
    exact ⟨by omega,fun _ _ h => h⟩
  · intro id b present
    cases present

private theorem memory : relation.holds function initial.slots heap world := by
  refine ⟨⟨?_,memory_base.1.valid,rfl⟩,?_,E2E.outRel_zero _ _ _⟩
  · intro a b valid byte; exact memory_base.1.bytes a b valid byte
  · intro id b present; cases present

private theorem arguments : ArgsAtEntry relation.F function.sig [⟨.i64,4096⟩] world := by
  intro loc value member
  change (loc,value) ∈ [(.reg (.x 0),⟨.i64,4096⟩)] at member
  cases List.mem_singleton.mp member
  simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,
    Arm.write_store,rnum]
  rfl

/-- The extension record facts and the body simulation apply to the actual run. -/
theorem sink_extend_body_witness (X : ExtSem) :
    ∃ (result : Result) (event : BlockScanEvent),Stock.lower function = .ok result ∧
      event ∈ result.blockScans.toList ∧
      (∃ (term extend load : ScanRecord) (scanned : BlockScan) (nreg a : Nat),
        SourceBodySplit function event block term scanned ∧
        scanned.code = extend.output.emitted ∧
        extend.output.emitted = #[.load .uload8 (.vreg extend.input.base.nextVreg .int)
          (.unsignedOffset (.vreg nreg .int) 0) {}] ∧
        event.ctx.valueReg? 0 = some (.vreg nreg .int) ∧ event.ctx.valueReg? 2 = some (.vreg a .int) ∧
        Demanded extend.output.state 0 ∧ ¬ Demanded extend.output.state 1 ∧ load.inst = 0) ∧
      ∃ (term : ScanRecord) (body : BlockScan),SourceBodySplit function event block term body ∧
        ∀ s s',SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} function event.ctx event.block)
          ((List.range block.body.length).map (blockStart function event.block + ·)) s s' →
        ∀ ρ w,GuardedScanRel function result event.ctx event.block (fun sl cm w => relation.holds function sl cm w)
            event.output.state s ρ w → ∃ ρ' w',
          seqRun (csem relation.F ⟨0,0⟩ X) (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w =
            some (.fall ρ' w') ∧
          GuardedScanRel function result event.ctx event.block (fun sl cm w => relation.holds function sl cm w)
            term.output.state s' ρ' w' := by
  obtain ⟨result,event,run,events⟩ := actual
  obtain ⟨term,extend,load,scanned,_,nreg,a,split,_,_,loadInst,_,_,_,_,_,_,mapped,zMapped,_,codeEq,
    emittedEq,_,demanded,quiet⟩ :=
    stock_lower_sink_extend_body_facts .unsigned8 run (lowerScope_of scope_true) dominated shape events
  exact ⟨result,event,run,events,⟨term,extend,load,scanned,nreg,a,split,codeEq,emittedEq,mapped,zMapped,
    demanded,quiet,loadInst⟩,
    stock_sink_extend_return_body .unsigned8 run (lowerScope_of scope_true) dominated shape
      (E2E.mrStable_holds relation function)
      (memRefines_csem relation.F ⟨0,0⟩ X rfl (fun _ _ h => by cases h))
      (E2E.memRelOk_holds relation function) events⟩

/-- The return contract on the actual run: the original source returns the zero-extended
live byte, and the actual Stock code refines it from a real ABI entry world. -/
theorem sink_extend_returns_witness :
    ∃ (result : Result) (ρ : Nat → CV),Stock.lower function = .ok result ∧
      Clif.enterFunc function [⟨.i64,4096⟩] heap = .ok (initial,heap) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 3 ⟨initial,[],heap⟩ = .returned [⟨.i32,165⟩] heap ∧
      RunOkABI function result.code (csem relation.F ⟨0,0⟩ noExternal)
        (fun sl cm w => relation.holds function sl cm w) initial.slots ⟨0,0,ρ,world⟩
        (.returned [⟨.i32,165⟩] heap) := by
  obtain ⟨result,_,run,_⟩ := actual
  have entered : Clif.enterFunc function [⟨.i64,4096⟩] heap = .ok (initial,heap) := by rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 3 ⟨initial,[],heap⟩ =
      .returned [⟨.i32,165⟩] heap := by rfl
  obtain ⟨ρ,finished⟩ := stock_sink_extend_returns .unsigned8 run (lowerScope_of scope_true) dominated
    rfl shape (SourceEntry.of_enterFunc entered) returned
    (refines_csem (F := relation.F) (ctx := ⟨0,0⟩) noExternal)
    (driverSem_csem relation.F ⟨0,0⟩ noExternal)
    (memRefines_csem relation.F ⟨0,0⟩ noExternal rfl (fun _ _ h => by cases h))
    (E2E.mrStable_holds relation function) (E2E.memRelOk_holds relation function) memory arguments
  exact ⟨result,ρ,run,entered,returned,finished⟩

end Backend.Stock.Memory.SinkExtend

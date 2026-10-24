import FV.Backend.Proof.StockBmaskSourceValues
import FV.Backend.Proof.StockBmaskRecordWitness

namespace Backend.Stock.Proof.ScalarMask
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def inputValue : Clif.Val := .ofInt .i64 (-7)
private def outputValue : Clif.Val := ⟨.i8,Clif.Sem.bmask inputValue.bits⟩
private def frame : Clif.Frame := {
  func := bmaskWitnessFunction
  regs := fun x => if x = 7 then some inputValue else none
  slots := [],body := [⟨[100],.bmask .i8 7⟩],term := .ret [100] }
private def registers (aliases : Array (Option Nat)) (n : Nat) : CV :=
  if n = aliasNum aliases 192 then inputValue.bits.setWidth 128 else 0

private theorem dominated : Dominated bmaskWitnessFunction := by
  constructor
  · change ([7,100] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [bmaskWitnessFunction] at block
      subst b
      constructor
      · intro j stm statement y member
        cases j <;> simp at statement
        subst stm
        change y ∈ [7] at member
        have same := List.mem_singleton.mp member
        subst y
        simp [availOf,bmaskWitnessFunction,defsBefore,defsFrom]
      · intro y member
        have same : y = 100 := List.mem_singleton.mp member
        subst y
        simp [availOf,bmaskWitnessFunction,defsBefore,defsFrom]
    | succ bi => simp [bmaskWitnessFunction] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := bmaskWitnessFunction) (ctx := ctx) (gn := id)).cand tl x available
    have length : bmaskWitnessFunction.blocks.length = 1 := rfl
    omega

private theorem frame_available (ctx : Ctx) :
    (restrict frame (availOf bmaskWitnessFunction (availIn bmaskWitnessFunction ctx) 0 0)).regs = frame.regs := by
  funext x
  by_cases present : x = 7
  · subst x
    apply restrict_regs_of_mem
    simp [availOf,bmaskWitnessFunction,defsBefore,defsFrom]
  · simp [restrict,frame,present]

/-- A successful complete driver run and a real original source step inhabit
guarded value transfer, including the actual bound result and machine run.
The source consumes an i64 parameter and returns an i8 mask. -/
theorem stock_lower_bmask_source_values_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step)
      (d : Nat) (ρ' : Nat → CV) (world : Arm.ArmState) (fr' : Clif.Frame),
      Stock.lower bmaskWitnessFunction = .ok result ∧ LowerScope bmaskWitnessFunction ∧ Dominated bmaskWitnessFunction ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst (frame,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      seqRun ispec (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        (registers result.final.alias) Arm.ArmState.default = some (.fall ρ' world) ∧
      VHolds outputValue (ρ' d) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf bmaskWitnessFunction (availIn bmaskWitnessFunction result.ctx) 0 1)
        event.ctx fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨result,event,record,info,step,wi,nx,next,run,events,records,source,clif,results,mapped,
    typed,mapX,undefined,current,recorded,emitted,_,_,_,_,_⟩ := stock_lower_bmask_record_witness
  have scope : LowerScope bmaskWitnessFunction := lowerScope_of (by decide +kernel)
  have dfg : DFGCons event.ctx (restrict frame (availOf bmaskWitnessFunction
      (availIn bmaskWitnessFunction result.ctx) 0 0)) := by
    constructor
    · intro x j info inst value defined found original pure lookup
      rw [frame_available] at lookup
      by_cases present : x = 7
      · subst x; rw [undefined] at defined; cases defined
      · simp [frame,present] at lookup
    · intro x t value type lookup
      rw [frame_available] at lookup
      by_cases present : x = 7
      · subst x
        rw [typed] at type
        cases type
        simp only [frame,ite_true] at lookup
        cases lookup
        rfl
      · simp [frame,present] at lookup
  have held : ValuesHeld (fun y => Demanded record.output.state y ∧
      y ∈ availOf bmaskWitnessFunction (availIn bmaskWitnessFunction result.ctx) 0 0)
      event.ctx frame (fun k => registers result.final.alias (aliasNum result.final.alias k)) := by
    intro x needed value lookup
    by_cases present : x = 7
    · subst x
      simp only [frame,ite_true] at lookup
      cases lookup
      exact ⟨192,mapX,by simp [VHolds,registers,inputValue,Clif.Val.ofInt,Clif.Ty.width,BitVec.setWidth_setWidth_of_le]⟩
    · simp [frame,present] at lookup
  let post : Clif.Frame := {withValue frame 100 outputValue with body := []}
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
      (frame,Clif.Mem.empty) (post,Clif.Mem.empty) := by
    refine ⟨info,.bmask .i8 7,[outputValue],(withValue frame 100 outputValue).regs,[],source,clif,?_,?_,?_,rfl⟩
    · rw [results]; rfl
    · rfl
    · rw [results]; rfl
  have refines : Refines (fun _ => True) ispec := by
    intro inst args world outs next ctl executed
    exact ⟨next,executed,SameWorld.refl _ _⟩
  have block : bmaskWitnessFunction.blocks[0]? = some bmaskWitnessFunction.blocks[0]! := rfl
  have statement : bmaskWitnessFunction.blocks[0]!.body[0]? = some (Clif.Stmt.mk [100] (.bmask .i8 7)) := rfl
  have located : record.inst = blockStart bmaskWitnessFunction 0 + 0 := current
  obtain ⟨value,d,lookup,_,output,bounds,execution⟩ := stock_lower_bmask_available_source run scope dominated events records
    block statement located source clif results rfl mapped recorded emitted refines dfg held sourceStep
  change some inputValue = some value at lookup
  cases lookup
  obtain ⟨ρ',world,executed,_,valueHeld,_,postHeld⟩ := execution Arm.ArmState.default
  exact ⟨result,event,record,step,d,ρ',world,post,run,scope,dominated,events,records,recorded,emitted,
    output,bounds,sourceStep,executed,valueHeld,postHeld⟩

end Backend.Stock.Proof.ScalarMask

module

public import FV.Backend.Proof.MemRefines
public import FV.Backend.Proof.StockEntrySeed
public import FV.Backend.Proof.StockEntryArgs
public import FV.Backend.Proof.StockEntryPrelude
public import FV.E2E.RegLevelDriverSem
public import FV.Backend.Proof.StockArithmeticReturnRefines
public import FV.Backend.Lowering.StockScalarAdd
public import FV.Backend.Proof.LowerDecide

@[expose] public section

namespace Backend.Stock.Proof.EntrySeedWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private def function : Clif.Function :=
  let base := D0.source "entry_unused" .systemVI64 []
  {base with
    sig := {base.sig with params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]}
    blocks := [{id := 0,params := [(0,.i64),(1,.i64)],body := [],term := .ret [0]}]}

private theorem finite :
    ((Backend.buildCtx function).toOption.map
      (fun s => decide (s.1.valDef = #[none,none]))).getD false = true ∧
    lowerScopeB function = true := by decide +kernel

private theorem domain : Dominated function ∧ LowerScope function := by
  have stored : ∀ {ctx ranges st0}, Backend.buildCtx function = .ok (ctx,ranges,st0) →
      ctx.valDef = #[none,none] := by
    intro ctx ranges st0 build
    have h := finite.1
    rw [build] at h
    exact of_decide_eq_true h
  refine ⟨?_,lowerScope_of finite.2⟩
  constructor
  · change ([0,1] : List Nat).Nodup
    decide
  · intro ctx ranges st0 build bi b block
    cases bi with
    | zero =>
      have same : b = function.blocks[0]! := by simpa [function,D0.source] using block.symm
      subst b
      constructor
      · intro j stm statement
        simp [function] at statement
      · intro y member
        have same : y = 0 := by simpa [function,D0.source,abiTerm,sretRet,sigRets,Backend.Proof.Driver.termArgs] using member
        subst y
        simp [availOf,function,D0.source,defsBefore,defsFrom]
    | succ bi => simp [function] at block
  · intro ctx ranges st0 build tl x available notLocal y member
    cases tl with
    | zero =>
      have absent : Ctx.defInst? ctx x = none := by
        have values := stored build
        cases x with
        | zero => simp [Ctx.defInst?,values]
        | succ x =>
          cases x with
          | zero => simp [Ctx.defInst?,values]
          | succ x => simp [Ctx.defInst?,values]
      simp [defArgs,absent] at member
    | succ tl => simp [parsOf,function,D0.source]

theorem success : (Stock.lower function).isOk = true := by native_decide
private theorem some_result : (Stock.lower function).toOption.isSome := by
  have h := success
  cases actual : Stock.lower function with
  | error e => rw [actual] at h; cases h
  | ok r => rfl
private def result : Result := (Stock.lower function).toOption.get some_result
private theorem run : Stock.lower function = .ok result := by
  cases actual : Stock.lower function with
  | error e => have h := success; rw [actual] at h; cases h
  | ok r => unfold result; simp only [actual,Except.toOption,Option.get_some]
theorem event_bound : 0 < result.blockScans.size := by native_decide
private def event : BlockScanEvent := result.blockScans[0]'event_bound
private theorem events : event ∈ result.blockScans.toList := Array.getElem_mem_toList event_bound

/-- The actual entry copy omits parameter1, while its source/register mapping
remains present. Native facts describe this fixed trace only. -/
theorem unused_parameter_trace :
    result.initial.uses[1]! = .unused ∧
    event.ctx.valueReg? 0 = some (.vreg 192 .int) ∧
    event.ctx.valueReg? 1 = some (.vreg 193 .int) ∧
    result.code.blocks[0]!.insts =
      #[.args [(.vreg 192 .int,.x 0)],.rets [(.vreg 192 .int,.x 0)]] := by native_decide

private def frame (u v : BitVec 64) : Clif.Frame := {
  func := function,regs := (Clif.Regs.empty.set 0 ⟨.i64,u⟩).set 1 ⟨.i64,v⟩,
  slots := [],body := [],term := .ret [0] }

/-- All parameter values, including the omitted one, inhabit the seeded and
resolved source relations; actual reference entry/return reaches the real VCode
return. The machine argument-prelude composition is a separate next obligation. -/
theorem unused_parameter_seed_witness (u v : BitVec 64) :
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    result.initial.uses[1]! = .unused ∧
    Clif.enterFunc function [⟨.i64,u⟩,⟨.i64,v⟩] Clif.Mem.empty = .ok (frame u v,Clif.Mem.empty) ∧
    VHolds ⟨.i64,v⟩ (entrySeed event.ctx (frame u v) 193) ∧
    ValuesHeld (fun _ => True) event.ctx (frame u v)
      (fun key => entrySeed event.ctx (frame u v) (aliasNum result.final.alias key)) ∧
    DFGCons event.ctx (restrict (frame u v) [0,1]) ∧
    ∃ label k, ∀ w, RunOkABI function result.code ispec
      (fun _ memory _ => memory = Clif.Mem.empty) []
      ⟨label,k,entrySeed event.ctx (frame u v),w⟩ (.returned [⟨.i64,u⟩] Clif.Mem.empty) := by
  have entered : Clif.enterFunc function [⟨.i64,u⟩,⟨.i64,v⟩] Clif.Mem.empty =
      .ok (frame u v,Clif.Mem.empty) := rfl
  have held := entrySeed_entered_values run domain.2 domain.1 events entered
  have unused := held.read (x := 1) trivial rfl unused_parameter_trace.2.2.1
  have resolved := entrySeed_entered_resolved_values run domain.2 domain.1 events entered
  have dfg := stock_lower_entered_restrict_dfg run domain.1 events entered [0,1]
  have self : Refines (fun _ => True) ispec :=
    fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have stable : MRStable (fun _ => True) (fun _ memory _ => memory = Clif.Mem.empty) := by
    intro _ _ _ _ _ h
    exact h
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 1 ⟨frame u v,[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,u⟩] Clif.Mem.empty := rfl
  obtain ⟨label,k,semantics⟩ := ArithmeticBody.actual_arithmetic_entered_return_refines
    run domain.2 domain.1 (abi := rfl) (b := function.blocks[0]!) rfl
    (by intro stm member; cases member) (xs := [0]) rfl events entered returned self stable
  refine ⟨run,domain.2,domain.1,unused_parameter_trace.1,entered,unused,resolved,dfg,label,k,?_⟩
  intro w
  exact semantics _ w (stock_lower_entered_seed_guarded run domain.2 domain.1 events entered
    event.output.state w rfl)

/-- A real ABI world and the actual argument-copy instruction preserve the
unused parameter for arbitrary source values. No source-value premise is assumed. -/
theorem unused_parameter_csem_args_witness (u v : BitVec 64) (X : ExtSem) (base : Arm.ArmState) :
    ∃ w ρ', ArgsAtEntry (fun _ => False) function.sig [⟨.i64,u⟩,⟨.i64,v⟩] w ∧
      seqRun (csem (fun _ => False) ⟨0,0⟩ X) [.args [(.vreg 192 .int,.x 0)]]
        (entrySeed event.ctx (frame u v)) w = some (.fall ρ' w) ∧
      ValuesHeld (fun _ => True) event.ctx (frame u v) ρ' ∧ VHolds ⟨.i64,v⟩ (ρ' 193) := by
  let world := Arm.write_base_gpr 0#5 u (Arm.write_base_gpr 1#5 v base)
  have arg0 : VHolds ⟨.i64,u⟩ (regVal world (.x 0)) := by
    simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum]
    change (u.setWidth 128).setWidth 64 = u
    rw [BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_eq]
  have arg1 : VHolds ⟨.i64,v⟩ (regVal world (.x 1)) := by
    simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum]
    change (v.setWidth 128).setWidth 64 = v
    rw [BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_eq]
  have arguments : ArgsAtEntry (fun _ => False) function.sig [⟨.i64,u⟩,⟨.i64,v⟩] world := by
    intro loc val member
    change (loc,val) ∈ [(.reg (.x 0),⟨.i64,u⟩),(.reg (.x 1),⟨.i64,v⟩)] at member
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact arg0
    · have equal := List.mem_singleton.mp member
      cases equal
      exact arg1
  have entered : Clif.enterFunc function [⟨.i64,u⟩,⟨.i64,v⟩] Clif.Mem.empty =
      .ok (frame u v,Clif.Mem.empty) := rfl
  have held := entrySeed_entered_values run domain.2 domain.1 events entered
  have inv := (stock_lower_record_context run domain.2 events).1
  have physical : ∀ x val key pin, (frame u v).regs x = some val →
      event.ctx.valueReg? x = some (.vreg key .int) →
      (key,pin) ∈ [(192,Reg.x 0)] → VHolds val (regVal world pin) := by
    intro x val key pin found mapped member
    have equal : (key,pin) = (192,Reg.x 0) := List.mem_singleton.mp member
    cases equal
    have same : x = 0 := inv.injective x 0 192 mapped unused_parameter_trace.2.1
    subst x
    change some ⟨.i64,u⟩ = some val at found
    cases found
    exact arg0
  obtain ⟨ρ',execution,values⟩ := entry_args_preserve_values
    (driverSem_csem (fun _ => False) ⟨0,0⟩ X) [(192,Reg.x 0)] (by decide) held physical
  refine ⟨world,ρ',arguments,execution,values,?_⟩
  exact values.read (x := 1) trivial rfl unused_parameter_trace.2.2.1

/-- The actual whole-driver prelude also covers arbitrary register arguments
when the second source parameter is unused; no row certificates are supplied. -/
theorem unused_whole_entry_prelude_witness (u v : BitVec 64) (X : ExtSem) (baseWorld : Arm.ArmState) :
    ∃ (w : Arm.ArmState) (actual : BlockScanEvent) (block : VBlock) (prelude body : Array MInst)
      (ρ' : Nat → CV) (w' : Arm.ArmState),
      ArgsAtEntry (fun _ => False) function.sig [⟨.i64,u⟩,⟨.i64,v⟩] w ∧
      actual ∈ result.blockScans.toList ∧ actual.block = 0 ∧
      result.code.blocks[0]? = some block ∧ block.insts = prelude ++ body ∧
      seqRun (csem (fun _ => False) ⟨0,0⟩ X) prelude.toList
        (entrySeed actual.ctx (frame u v)) w = some (.fall ρ' w') ∧
      ValuesHeld (fun _ => True) actual.ctx (frame u v) ρ' ∧ SameWorld (fun _ => False) w' w := by
  obtain ⟨w,_,arguments,_,_,_⟩ := unused_parameter_csem_args_witness u v X baseWorld
  have entered : Clif.enterFunc function [⟨.i64,u⟩,⟨.i64,v⟩] Clif.Mem.empty =
      .ok (frame u v,Clif.Mem.empty) := rfl
  have memSem : MemRefines (fun _ => False) 0 (fun _ => none) (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by
    intro _ _ _ _ _ _
    trivial
  obtain ⟨actual,block,prelude,body,ρ',w',events,zero,placed,code,execution,_,values,same,_⟩ :=
    stock_lower_entry_prelude_refines run domain.2 domain.1 entered
      (driverSem_csem (fun _ => False) ⟨0,0⟩ X) memSem stable trivial arguments
  exact ⟨w,actual,block,prelude,body,ρ',w',arguments,events,zero,placed,code,execution,values,same⟩

end Backend.Stock.Proof.EntrySeedWitness

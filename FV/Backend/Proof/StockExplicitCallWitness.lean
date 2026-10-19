import FV.Backend.Proof.StockExplicitCallExecution
import FV.Backend.Proof.StockCallResultBindingWitness
import FV.E2E.NonVacuity
import FV.Backend.Proof.RefinesCSem
namespace Backend.Stock.Proof.ExplicitCallWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open ExplicitCallSemDraft ExplicitCallFramesDraft ExplicitCallPhysicalDraft ExplicitCallExecutionDraft CallStaticFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower

def values (implicit : Bool) : List Clif.Val := if implicit then [] else [⟨.i64,7⟩,⟨.i64,9⟩]
def outputs (implicit : Bool) : List CV := if implicit then [123] else [7,9]
def model (implicit : Bool) : ExtSem :=
  ⟨fun _ _ w => some (outputs implicit,w),fun _ _ => 0,0,fun _ w => Arm.read_pstate w⟩
def sourceEnv (indirect implicit : Bool) : Clif.Env := {
  extern := fun _ => some (fun _ cm => .returned (values implicit) cm)
  sigOf := fun _ => some (signature indirect implicit) }
def machineUses (implicit : Bool) : List (Nat × Reg) :=
  if implicit then [(192,.x 8)] else [(192,.x 0),(193,.x 1),(194,.x 2),(195,.x 3),(196,.x 4),(197,.x 5),(198,.x 6),(199,.x 7)]
def sourceArgs (indirect implicit : Bool) : List Clif.Val :=
  List.replicate (count indirect implicit) ⟨.i64,0⟩
private theorem held (implicit : Bool) : PrefixHold (values implicit) (outputs implicit) := by
  cases implicit with
  | false =>
    constructor
    · decide
    · intro j v x hv hx
      rcases j with _ | (_ | j)
      all_goals simp [values,outputs] at hv hx
      all_goals cases hv; cases hx; rfl
  | true => exact ⟨by decide,by intro j v x hv; simp [values] at hv⟩
private theorem xcalls (indirect implicit : Bool) (ext : Clif.ExtFunc)
    (sig : ext.sig = signature indirect implicit) :
    XCallsOk (sourceEnv indirect implicit) [ext] (fun _ _ _ => True) (model implicit) := by
  intro e member g sl cm w d uses args vals rvals cm' found target arguments memory returned length
  simp only [List.mem_singleton] at member
  subst e
  simp only [sourceEnv,Option.some.injEq] at found
  subst g
  cases returned
  exact ⟨outputs implicit,w,rfl,(by rw [sig]; cases indirect <;> cases implicit <;> rfl),held implicit,trivial⟩
private theorem xind (indirect implicit : Bool) :
    XCallsIndOk (sourceEnv indirect implicit) [signature indirect implicit] (fun _ _ _ => True) (model implicit) := by
  intro sig member name g sl cm w u args vals rvals cm' found signature address count arguments memory returned length typed
  simp only [List.mem_singleton] at member
  subst sig
  simp only [sourceEnv,Option.some.injEq] at found
  subst g
  cases returned
  exact ⟨outputs implicit,w,rfl,(by cases indirect <;> cases implicit <;> rfl),held implicit,trivial⟩
private theorem all_zero (n : Nat) : AllHold (List.replicate n (⟨.i64,0⟩ : Clif.Val)) (List.replicate n (0 : CV)) := by
  constructor
  · simp
  · intro j v x hv hx
    have av := (List.mem_replicate.mp (List.mem_of_getElem? hv)).2
    have ax := (List.mem_replicate.mp (List.mem_of_getElem? hx)).2
    subst v; subst x; rfl
private theorem args_at (implicit : Bool) :
    ArgsAt (signature false implicit) (sourceArgs false implicit)
      ((machineUses implicit).map (fun _ => (0 : CV))) Arm.ArmState.default := by
  constructor
  · cases implicit <;> rfl
  constructor
  · cases implicit
    · change AllHold (List.replicate 8 (⟨.i64,0⟩ : Clif.Val)) (List.replicate 8 (0 : CV))
      exact all_zero 8
    · change AllHold (List.replicate 1 (⟨.i64,0⟩ : Clif.Val)) (List.replicate 1 (0 : CV))
      exact all_zero 1
  · intro off v member
    cases implicit
    · change (ArgLoc.stack off,v) ∈ [(.reg (.x 0),⟨.i64,0⟩),(.reg (.x 1),⟨.i64,0⟩),
        (.reg (.x 2),⟨.i64,0⟩),(.reg (.x 3),⟨.i64,0⟩),(.reg (.x 4),⟨.i64,0⟩),
        (.reg (.x 5),⟨.i64,0⟩),(.reg (.x 6),⟨.i64,0⟩),(.reg (.x 7),⟨.i64,0⟩),(.stack 0,⟨.i64,0⟩)] at member
      have only : off = 0 ∧ v = ⟨.i64,0⟩ := by simpa using member
      rcases only with ⟨rfl,rfl⟩
      rfl
    · change (ArgLoc.stack off,v) ∈ [(.reg (.x 8),⟨.i64,0⟩)] at member
      simp at member
private theorem mapped_args (ctx : Ctx) (xs : List Nat)
    (each : ∀ x ∈ xs,ctx.valueReg? x = some (.vreg (192+x) .int)) :
    xs.mapM ctx.valueReg? = some (xs.map (fun x => Reg.vreg (192+x) .int)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons,each x (List.mem_cons_self ..),List.map_cons]
    rw [ih (fun y hy => each y (List.mem_cons_of_mem _ hy))]
    rfl

/-- Complete original ordinary and sret pipelines expose the SAME actual
retained direct call, whose explicit-result semantics now executes successfully.
Original external contracts, inhabited ABI arguments, real call membership,
returned values/world, result holding and original pipeline stages are included. -/
theorem stock_complete_explicit_direct_call_witness (implicit : Bool) :
    ∃ (out : Output) (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (step : Step) (call : CallInfo)
      (fr : Clif.Frame) (outs : List CV) (world : Arm.ArmState),
      LowerScope (function false implicit) ∧ Dominated (function false implicit) ∧
      ArityOk (function false implicit) ∧ AbiSigsOk (function false implicit) ∧
      Stock.lower (function false implicit) = .ok out.result ∧
      prepareAt out.result.code out.result.edgeArgs = .ok out.prepared ∧
      out.rf = spillAllocAt out.prepared.code out.prepared.edges ∧
      checkAllocAt out.prepared.code out.prepared.edges out.rf = .ok () ∧
      lowerRFunc out.prepared.code out.rf = .ok out.af ∧ Facts false implicit out ∧
      event ∈ out.result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.call 0 (arguments false implicit)) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      MInst.call call ∈ record.output.emitted.toList ∧
      call = ⟨.sym calleeName,retPairs (machineUses implicit),
        callDefs (outDefs record.input.base.nextVreg (signature false implicit).returns.length)⟩ ∧
      XCallsOk (sourceEnv false implicit) [{name := calleeName,sig := signature false implicit,colocated := true}]
        (fun _ _ _ => True) (model implicit) ∧
      ArgsAt (signature false implicit) (sourceArgs false implicit)
        ((machineUses implicit).map (fun _ => (0 : CV))) Arm.ArmState.default ∧
      seqRun (explicitCallSem (csem (fun _ => False) ⟨0,0⟩ (model implicit))) [MInst.call call] (fun _ => 0)
        Arm.ArmState.default = some (.fall
          (writeV (fun _ => 0) ((callDefOps (outDefs record.input.base.nextVreg (signature false implicit).returns.length)).zip outs)) world) ∧
      outs.length = (if implicit then 0 else 2) ∧ AllHold (values implicit) outs ∧
      ResultsHeld record.input.base.nextVreg fr (outRegs' record.input.base.nextVreg (signature false implicit).returns.length)
        (values implicit) (writeV (fun _ => 0)
          ((callDefOps (outDefs record.input.base.nextVreg (signature false implicit).returns.length)).zip outs)) := by
  obtain ⟨out,event,record,info,step,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,actual,placed⟩ :=
    CallEmissionWitnessDraft.stock_complete_direct_call_emission_witness implicit
  obtain ⟨ns,locs,bytes,stack,call,copies,mapping,byteRun,locations,shape,code,member,raw,static,resolved⟩ := actual
  have each : ∀ x ∈ arguments false implicit,event.ctx.valueReg? x = some (.vreg (192+x) .int) := by
    intro x hx
    rw [(stock_lower_record_context lowered scope events).2.1]
    exact beq_iff_eq.mp (List.all_eq_true.mp facts.2.2.1 x hx)
  have expected := mapped_args event.ctx (arguments false implicit) each
  have equal := Option.some.inj (mapping.symm.trans expected)
  have nsEq : ns = numbers false implicit := by
    have projected := congrArg (List.map (fun r => match r with | .vreg n _ => n | _ => 0)) equal
    simpa [numbers,List.map_map,Function.comp_def] using projected
  have used : regPairsOf ((locs.zip ns).zip bytes) = machineUses implicit := by
    rw [nsEq]
    have knownBytes : sigParamBytes (signature false implicit) = .ok (List.replicate (count false implicit) 8) := by cases implicit <;> rfl
    have sameBytes := Except.ok.inj (byteRun.symm.trans knownBytes)
    subst bytes
    cases implicit
    · have known : sigArgLocs (signature false false) = .ok ([.reg (.x 0),.reg (.x 1),.reg (.x 2),.reg (.x 3),.reg (.x 4),.reg (.x 5),.reg (.x 6),.reg (.x 7),.stack 0],16) := rfl
      cases Except.ok.inj (locations.symm.trans known)
      rfl
    · have known : sigArgLocs (signature false true) = .ok ([.reg (.x 8)],0) := rfl
      cases Except.ok.inj (locations.symm.trans known)
      rfl
  rw [used] at shape
  let fr : Clif.Frame := ⟨function false implicit,fun _ => none,[],[],.ret []⟩
  let ext : Clif.ExtFunc := {name := calleeName,sig := signature false implicit,colocated := true}
  have external := xcalls false implicit ext rfl
  obtain ⟨outs,world,execution,length,held,results,related⟩ := stock_explicit_direct_call_execution
    (F := fun _ => False) (ctx := ⟨0,0⟩) (base := record.input.base.nextVreg) (ρ := fun _ => 0)
    (ext := ext) (L := machineUses implicit) (vals := sourceArgs false implicit) (rvals := values implicit)
    (sl := []) (cm := Clif.Mem.empty) (cm' := Clif.Mem.empty) external (by simp) fr rfl (args_at implicit) trivial rfl (by cases implicit <;> rfl)
  have execute : seqRun (explicitCallSem (csem (fun _ => False) ⟨0,0⟩ (model implicit))) [.call call] (fun _ => 0)
      Arm.ArmState.default = some (.fall (writeV (fun _ => 0)
        ((callDefOps (outDefs record.input.base.nextVreg (signature false implicit).returns.length)).zip outs)) world) := by
    rw [shape]; exact execution
  have count : outs.length = (if implicit then 0 else 2) := by rw [length]; cases implicit <;> rfl
  exact ⟨out,event,record,info,step,call,fr,outs,world,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,member,shape,external,args_at implicit,execute,count,held,results⟩

private def zeroCalls (info : CallInfo) : Prop := ∃ L,info = ⟨.sym calleeName,retPairs L,[]⟩
private theorem sret_callee : CalleeOk (fun _ => True) 32 (model true)
    (E2E.witnessHooks 0 0 (fun _ _ => 0) 0) zeroCalls := by
  apply E2E.calleeOk_of_keepsBut
    (fun _ => E2E.witnessCall_keepsBut 0 0)
    (fun _ s valid aligned => E2E.witnessCall_pc 0 0 s valid aligned)
    (by intro d uses w outs w' actual; simp only [model,Option.some.injEq,Prod.mk.injEq] at actual; exact actual.2.symm)
  intro info site c wh ops regs s w outs w' operands checked actual p member
  obtain ⟨L,rfl⟩ := site
  have canonical := operands_call_sym calleeName L []
  simp only [callDefs,List.map_nil] at canonical
  rw [canonical] at operands
  cases operands
  simp only [defRegs,callDefOps,List.map_nil,List.append_nil,Array.toList_zip,List.toList_toArray] at member
  have filtered := (List.of_mem_zip member).1
  have pair := List.mem_filter.mp filtered
  have op := (List.of_mem_zip pair.1).1
  have impossible : p.1.1 ∈ (retOps L).filter Operand.isDef := List.mem_filter.mpr ⟨op,pair.2⟩
  rw [filter_isDef_retOps'] at impossible
  cases impossible

/-- A complete actual sret pipeline jointly inhabits the ORIGINAL external and
physical callee contracts with one ignored ABI result and zero recorded defs.
The same callee proves ordinary and guarded adapter physical correctness. -/
theorem stock_complete_explicit_sret_physical_witness :
    ∃ (out : Output) (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (step : Step) (call : CallInfo),
      LowerScope (function false true) ∧ Dominated (function false true) ∧ ArityOk (function false true) ∧
      AbiSigsOk (function false true) ∧ Stock.lower (function false true) = .ok out.result ∧
      prepareAt out.result.code out.result.edgeArgs = .ok out.prepared ∧
      out.rf = spillAllocAt out.prepared.code out.prepared.edges ∧
      checkAllocAt out.prepared.code out.prepared.edges out.rf = .ok () ∧
      lowerRFunc out.prepared.code out.rf = .ok out.af ∧ Facts false true out ∧
      event ∈ out.result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.call 0 (arguments false true)) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      MInst.call call ∈ record.output.emitted.toList ∧ call.defs = [] ∧
      XCallsOk (sourceEnv false true) [{name := calleeName,sig := signature false true,colocated := true}]
        (fun _ _ _ => True) (model true) ∧
      CalleeOk (fun _ => True) 32 (model true) (E2E.witnessHooks 0 0 (fun _ _ => 0) 0) zeroCalls ∧
      (∀ ctx,CallSoundCtl (fun _ => True) 32 (callExec (E2E.witnessHooks 0 0 (fun _ _ => 0) 0))
        (explicitCallSem (csem (fun _ => True) ctx (model true))) (.call call) .next) ∧
      ∀ G s0 Pc gv ctx,CallSoundCtlG (fun _ => True) 32 G s0 Pc (callExec (E2E.witnessHooks 0 0 (fun _ _ => 0) 0))
        (explicitCallSem (csemV gv (fun _ => True) ctx (model true))) (.call call) .next := by
  obtain ⟨out,event,record,info,step,call,fr,outs,world,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,member,shape,external,args,executed,count,held,results⟩ :=
    stock_complete_explicit_direct_call_witness true
  have site : zeroCalls call := by rw [shape]; exact ⟨machineUses true,rfl⟩
  have defs : call.defs = [] := by rw [shape]; rfl
  exact ⟨out,event,record,info,step,call,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,member,defs,external,sret_callee,
    fun ctx => stock_explicit_call_physical sret_callee ctx call site,
    fun G s0 Pc gv ctx => stock_explicit_call_guarded_physical (sret_callee.g G s0 Pc gv) ctx call site⟩

/-- Successful legacy two-result calls keep their full output/world, while
scalar refinement, driver invariants and non-call semantics remain inhabited. -/
theorem stock_explicit_call_legacy_structure_witness :
    ∃ (call : CallInfo) (world : Arm.ArmState),call.defs.length = 2 ∧
      csem (fun _ => False) ⟨0,0⟩ (model false) (.call call) [] world = some ([7,9],world,.next) ∧
      explicitCallSem (csem (fun _ => False) ⟨0,0⟩ (model false)) (.call call) [] world = some ([7,9],world,.next) ∧
      Refines (fun _ => False) (explicitCallSem (csem (fun _ => False) ⟨0,0⟩ (model false))) ∧
      DriverSem (explicitCallSem (csem (fun _ => False) ⟨0,0⟩ (model false))) ∧
      explicitCallSem (csem (fun _ => False) ⟨0,0⟩ (model false)) (.jump 0) = csem (fun _ => False) ⟨0,0⟩ (model false) (.jump 0) := by
  let call : CallInfo := ⟨.sym calleeName,[],callDefs (outDefs 200 2)⟩
  have old : csem (fun _ => False) ⟨0,0⟩ (model false) (.call call) [] Arm.ArmState.default = some ([7,9],Arm.ArmState.default,.next) := rfl
  exact ⟨call,Arm.ArmState.default,rfl,old,stock_explicit_call_sem_compatible old rfl,
    stock_explicit_call_sem_refines (refines_csem _ _ _),stock_explicit_call_sem_driver (driverSem_csem _ _ _),
    stock_explicit_call_sem_other _ _ (by intro i h; cases h)⟩

def indirectUses (implicit : Bool) : List (Nat × Reg) :=
  if implicit then [(192,.x 8)] else [(192,.x 0),(193,.x 1)]
private theorem indirect_args (implicit : Bool) :
    AllHold (sourceArgs true implicit) ((indirectUses implicit).map (fun _ => (0 : CV))) := by
  cases implicit
  · exact all_zero 2
  · exact all_zero 1
/-- Complete original ordinary and sret pipelines expose the SAME actual
retained indirect call, whose explicit-result semantics now executes successfully.
Original external contracts, inhabited ABI arguments, real call membership,
returned values/world, result holding and original pipeline stages are included. -/
theorem stock_complete_explicit_indirect_call_witness (implicit : Bool) :
    ∃ (out : Output) (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (step : Step) (call : CallInfo) (target : Nat)
      (fr : Clif.Frame) (outs : List CV) (world : Arm.ArmState),
      LowerScope (function true implicit) ∧ Dominated (function true implicit) ∧
      ArityOk (function true implicit) ∧ AbiSigsOk (function true implicit) ∧
      Stock.lower (function true implicit) = .ok out.result ∧
      prepareAt out.result.code out.result.edgeArgs = .ok out.prepared ∧
      out.rf = spillAllocAt out.prepared.code out.prepared.edges ∧
      checkAllocAt out.prepared.code out.prepared.edges out.rf = .ok () ∧
      lowerRFunc out.prepared.code out.rf = .ok out.af ∧ Facts true implicit out ∧
      event ∈ out.result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.callIndirect 0 80 (arguments true implicit)) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      MInst.call call ∈ record.output.emitted.toList ∧
      call = ⟨.reg (.vreg target .int),retPairs (indirectUses implicit),
        callDefs (outDefs record.input.base.nextVreg (signature true implicit).returns.length)⟩ ∧
      XCallsIndOk (sourceEnv true implicit) [signature true implicit]
        (fun _ _ _ => True) (model implicit) ∧
      AllHold (sourceArgs true implicit)
        ((indirectUses implicit).map (fun _ => (0 : CV))) ∧
      seqRun (explicitCallSem (csem (fun _ => False) ⟨0,0⟩ (model implicit))) [MInst.call call] (fun _ => 0)
        Arm.ArmState.default = some (.fall
          (writeV (fun _ => 0) ((callDefOps (outDefs record.input.base.nextVreg (signature true implicit).returns.length)).zip outs)) world) ∧
      outs.length = (if implicit then 0 else 2) ∧ AllHold (values implicit) outs ∧
      ResultsHeld record.input.base.nextVreg fr (outRegs' record.input.base.nextVreg (signature true implicit).returns.length)
        (values implicit) (writeV (fun _ => 0)
          ((callDefOps (outDefs record.input.base.nextVreg (signature true implicit).returns.length)).zip outs)) := by
  obtain ⟨out,event,record,info,step,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,origin,actual,placed⟩ :=
    IndirectCallEmissionWitnessDraft.stock_complete_indirect_call_emission_witness implicit
  obtain ⟨target,ns,locs,bytes,stack,call,copies,targetMap,mapping,byteRun,locations,shape,code,member,raw,static,resolved⟩ := actual
  have each : ∀ x ∈ arguments true implicit,event.ctx.valueReg? x = some (.vreg (192+x) .int) := by
    intro x hx
    rw [(stock_lower_record_context lowered scope events).2.1]
    exact beq_iff_eq.mp (List.all_eq_true.mp facts.2.2.1 x hx)
  have expected := mapped_args event.ctx (arguments true implicit) each
  have equal := Option.some.inj (mapping.symm.trans expected)
  have nsEq : ns = numbers true implicit := by
    have projected := congrArg (List.map (fun r => match r with | .vreg n _ => n | _ => 0)) equal
    simpa [numbers,List.map_map,Function.comp_def] using projected
  have used : regPairsOf ((locs.zip ns).zip bytes) = indirectUses implicit := by
    rw [nsEq]
    have knownBytes : sigParamBytes (signature true implicit) = .ok (List.replicate (count true implicit) 8) := by cases implicit <;> rfl
    have sameBytes := Except.ok.inj (byteRun.symm.trans knownBytes)
    subst bytes
    cases implicit
    · have known : sigArgLocs (signature true false) = .ok ([.reg (.x 0),.reg (.x 1)],0) := rfl
      cases Except.ok.inj (locations.symm.trans known)
      rfl
    · have known : sigArgLocs (signature true true) = .ok ([.reg (.x 8)],0) := rfl
      cases Except.ok.inj (locations.symm.trans known)
      rfl
  rw [used] at shape
  let fr : Clif.Frame := ⟨function true implicit,fun _ => none,[],[],.ret []⟩
  have external := xind true implicit
  obtain ⟨outs,world,execution,length,held,results,related⟩ := stock_explicit_indirect_call_execution
    (F := fun _ => False) (ctx := ⟨0,0⟩) (base := record.input.base.nextVreg) (ρ := fun _ => 0)
    (sig := signature true implicit) (target := target) (name := calleeName) (L := indirectUses implicit) (vals := sourceArgs true implicit) (rvals := values implicit)
    (sl := []) (cm := Clif.Mem.empty) (cm' := Clif.Mem.empty) external (by simp) fr rfl
      (by intro sig hs; change some (signature true implicit) = some sig at hs; cases hs; cases implicit <;> decide +kernel)
      rfl (by cases implicit <;> decide) (indirect_args implicit) trivial rfl (by cases implicit <;> rfl) (by cases implicit <;> rfl)
  have execute : seqRun (explicitCallSem (csem (fun _ => False) ⟨0,0⟩ (model implicit))) [.call call] (fun _ => 0)
      Arm.ArmState.default = some (.fall (writeV (fun _ => 0)
        ((callDefOps (outDefs record.input.base.nextVreg (signature true implicit).returns.length)).zip outs)) world) := by
    rw [shape]; exact execution
  have count : outs.length = (if implicit then 0 else 2) := by rw [length]; cases implicit <;> rfl
  exact ⟨out,event,record,info,step,call,target,fr,outs,world,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,member,shape,external,indirect_args implicit,execute,count,held,results⟩
end Backend.Stock.Proof.ExplicitCallWitnessDraft

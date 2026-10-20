import FV.Backend.Proof.StockCallResolvedSource
import FV.Backend.Proof.StockExplicitCallWitness
import FV.Backend.Proof.MemRefines
namespace Backend.Stock.Proof.CallRecordSourceWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open CallStaticFixture ExplicitCallWitnessDraft ExplicitCallSemDraft CallStoreSemDraft CallRecordSourceDraft CallRecordFootprintDraft CallResolvedSourceDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower
private theorem set_exists (xs : List Nat) (vs : List Clif.Val) (length : xs.length = vs.length) (r : Clif.Regs) :
    ∃ next,r.setMany xs vs = some next := by
  induction xs generalizing vs r with
  | nil => cases vs <;> simp_all [Clif.Regs.setMany]
  | cons x xs ih =>
    cases vs with
    | nil => simp at length
    | cons v vs => exact ih vs (by simpa using length) (r.set x v)
private theorem stack_ok (implicit : Bool) : CallsStack (function false implicit) 16 := by
  intro b block stm statement fn args ext inst declared
  simp only [function,List.mem_singleton] at block
  subst b
  change stm ∈ [callStatement false implicit] at statement
  have same := List.mem_singleton.mp statement
  subst stm
  change Clif.Inst.call 0 (arguments false implicit) = .call fn args at inst
  cases inst
  change some {name := calleeName,sig := signature false implicit,colocated := true} = some ext at declared
  cases declared
  cases implicit <;> constructor <;> decide +kernel
private theorem outgoing_ok : OutArgsOk (fun _ => False) 16 (fun _ _ _ => True) := by
  intro sl cm w related
  exact ⟨by decide,by intro k bound bad; exact bad,by intro k n y inside; trivial⟩

/-- Complete original ordinary nine-argument/two-result AND implicit-sret
pipelines inhabit actual source evaluation and result binding, every original
memory/external/outgoing contract, the complete real emitted record and its
final alias-resolved execution. All new results and other demanded/available
source values hold after that SAME record; cached lowering stages are reused. -/
theorem stock_complete_direct_call_source_record_witness (implicit : Bool) :
    ∃ (out : Output) (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (step : Step)
      (bi j : Nat) (b : Clif.Block) (stm : Clif.Stmt) (fr fr' : Clif.Frame) (next : Nat → CV) (world : Arm.ArmState),
      LowerScope (function false implicit) ∧ Dominated (function false implicit) ∧
      ArityOk (function false implicit) ∧ AbiSigsOk (function false implicit) ∧
      Stock.lower (function false implicit) = .ok out.result ∧
      prepareAt out.result.code out.result.edgeArgs = .ok out.prepared ∧
      out.rf = spillAllocAt out.prepared.code out.prepared.edges ∧
      checkAllocAt out.prepared.code out.prepared.edges out.rf = .ok () ∧
      lowerRFunc out.prepared.code out.rf = .ok out.af ∧ Facts false implicit out ∧
      event ∈ out.result.blockScans.toList ∧ record ∈ event.output.records ∧
      (function false implicit).blocks[bi]? = some b ∧ b.body[j]? = some stm ∧
      record.inst = blockStart (function false implicit) bi+j ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.call 0 (arguments false implicit)) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      info.results.length = (if implicit then 0 else 2) ∧
      SourceInstResult (sourceEnv false implicit) {funcs := []} event.ctx record.inst
        (fr,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      MRStable (fun _ => False) (fun _ _ _ => True) ∧
      MemRefinesR (fun _ => True) (fun _ => False) 0 (fun _ => none)
        (csem (fun _ => False) ⟨0,0⟩ (model implicit)) ∧
      OutArgsOk (fun _ => False) 16 (fun _ _ _ => True) ∧ CallsStack (function false implicit) 16 ∧
      XCallsOk (sourceEnv false implicit) ((function false implicit).externs.map (·.2)) (fun _ _ _ => True) (model implicit) ∧
      ValuesHeld (fun x => Demanded record.output.state x ∧
        x ∈ availOf (function false implicit) (availIn (function false implicit) out.result.ctx) bi j)
        event.ctx fr (fun key => (0 : CV)) ∧
      seqRun (explicitCallSem (csem (fun _ => False) ⟨0,0⟩ (model implicit)))
        (record.output.emitted.toList.map (·.mapRegs (Backend.lowerFunction.resolve out.result.final.alias (out.result.final.alias.size+1))))
        (fun _ => 0) Arm.ArmState.default = some (.fall next world) ∧
      ValuesHeld (fun x => Demanded record.input x ∧
        x ∈ availOf (function false implicit) (availIn (function false implicit) out.result.ctx) bi (j+1))
        out.result.ctx fr' (fun key => next (aliasNum out.result.final.alias key)) ∧
      ValuesHeld (fun x => x ∈ info.results) out.result.ctx fr' (fun key => next (aliasNum out.result.final.alias key)) := by
  obtain ⟨out,event,record,info,step,call,callFrame,outs,callWorld,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,member,shape,external,argumentsAt,callRun,callCount,returned,results⟩ :=
    stock_complete_explicit_direct_call_witness implicit
  obtain ⟨b,j,stm,block,statement,current,inst⟩ := SourceRecordStatementDraft.stock_lower_source_record_statement
    lowered scope events records slot clif
  let fr : Clif.Frame := {
    func := function false implicit
    regs := fun x => if x ∈ arguments false implicit then some ⟨.i64,0⟩ else none
    slots := []
    body := [⟨info.results,.call 0 (arguments false implicit)⟩]
    term := .ret (if implicit then [] else [40,41]) }
  have size := (CallResultBindingDraft.stock_lower_call_result_binding lowered scope dominated.ssa abi events records slot clif
    (show (function false implicit).extern? 0 = some {name := calleeName,sig := signature false implicit,colocated := true} from rfl) recorded emitted).1
  have count : info.results.length = (values implicit).length := by rw [size]; cases implicit <;> rfl
  obtain ⟨regs,set⟩ := set_exists info.results (values implicit) count fr.regs
  let fr' : Clif.Frame := {fr with regs,body := []}
  have evaluated : instOutcome (sourceEnv false implicit) {funcs := []} fr Clif.Mem.empty
      (.call 0 (arguments false implicit)) = .ok (values implicit,Clif.Mem.empty) := by
    cases implicit <;> rfl
  have source : SourceInstResult (sourceEnv false implicit) {funcs := []} event.ctx record.inst (fr,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨info,.call 0 (arguments false implicit),values implicit,regs,[],slot,clif,rfl,evaluated,set,rfl⟩
  have held : ValuesHeld (fun _ => True) event.ctx fr (fun _ => (0 : CV)) := by
    intro x required v lookup
    by_cases present : x ∈ arguments false implicit
    · have mapped : event.ctx.valueReg? x = some (.vreg (192+x) .int) := by
        rw [(stock_lower_record_context lowered scope events).2.1]
        exact beq_iff_eq.mp (List.all_eq_true.mp facts.2.2.1 x present)
      have same : v = ⟨.i64,0⟩ := by simpa only [fr,if_pos present,Option.some.injEq] using lookup.symm
      subst v
      exact ⟨192+x,mapped,rfl⟩
    · simp only [fr,if_neg present] at lookup
      cases lookup
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro sl cm w w' same related; trivial
  have memory : MemRefinesR (fun _ => True) (fun _ => False) 0 (fun _ => none) (csem (fun _ => False) ⟨0,0⟩ (model implicit)) :=
    memRefinesR_of (memRefines_csem _ _ _ rfl (by intro n b found; cases found))
  have external : XCallsOk (sourceEnv false implicit) ((function false implicit).externs.map (·.2)) (fun _ _ _ => True) (model implicit) := external
  obtain ⟨next,world,executed,relatedAfter,guarded,allResults⟩ := stock_lower_direct_call_guarded_source_run
    (Rd := fun _ => True) (asm := ⟨0,0⟩) (X := model implicit) (ρ := fun _ => 0)
    lowered scope dominated abi stable memory outgoing_ok (stack_ok implicit) external events records block statement current slot clif
    (show (function false implicit).extern? 0 = some {name := calleeName,sig := signature false implicit,colocated := true} from rfl)
    rfl recorded emitted (show fr.func = function false implicit from rfl) (held.mono (fun _ _ => trivial)) trivial source
  have explicitCount : info.results.length = (if implicit then 0 else 2) := by rw [size]; cases implicit <;> rfl
  exact ⟨out,event,record,info,step,event.block,j,b,stm,fr,fr',next,world,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,block,statement,current,slot,clif,recorded,emitted,explicitCount,source,stable,memory,outgoing_ok,stack_ok implicit,external,
    held.mono (fun _ _ => trivial),executed,guarded,allResults⟩
end Backend.Stock.Proof.CallRecordSourceWitnessDraft

import FV.Backend.Proof.StockIndirectResolvedSource
import FV.Backend.Proof.StockIndirectCallEmissionWitness
import FV.Backend.Proof.StockExplicitCallWitness
namespace Backend.Stock.Proof.IndirectSourceWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open CallStaticFixture ExplicitCallSemDraft ExplicitCallWitnessDraft IndirectRecordCodeDraft IndirectResolvedSourceDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower

def symbols (name : String) : Option Nat := if name = calleeName then some 4096 else none
def memory : Clif.Mem := {Clif.Mem.empty with symbols}
def relation : MemRelT := fun _ cm _ => cm.symbols = symbols
def indirectModel (implicit : Bool) : ExtSem := {model implicit with sym := fun _ _ => 4096}
def indirectEnv (implicit : Bool) : Clif.Env := {sourceEnv true implicit with names := [calleeName]}
private theorem prefix_held (implicit : Bool) : PrefixHold (values implicit) (outputs implicit) := by
  cases implicit with
  | false =>
    constructor
    · decide
    · intro j v x hv hx
      rcases j with _ | (_ | j)
      all_goals simp [values,outputs] at hv hx
      all_goals cases hv; cases hx; rfl
  | true => exact ⟨by decide,by intro j v x hv; simp [values] at hv⟩
private theorem external (implicit : Bool) :
    XCallsIndOk (indirectEnv implicit) (indSigs (function true implicit)) relation (indirectModel implicit) := by
  have signatures : indSigs (function true implicit) = [signature true implicit] := by cases implicit <;> rfl
  rw [signatures]
  intro sig member name g sl cm w u args vals rvals cm' found matching address count arguments related returned length typed
  simp only [List.mem_singleton] at member
  subst sig
  simp only [indirectEnv,sourceEnv,Option.some.injEq] at found
  subst g
  cases returned
  exact ⟨outputs implicit,w,rfl,(by cases implicit <;> rfl),prefix_held implicit,related⟩
private theorem symbol_addresses (implicit : Bool) :
    ∀ name b,symbols name = some b → (indirectModel implicit).sym name 0 = BitVec.ofNat 64 b := by
  intro name b found
  by_cases known : name = calleeName
  · simp only [symbols,if_pos known,Option.some.injEq] at found
    subst b
    rfl
  · simp only [symbols,if_neg known] at found
    cases found
private theorem set_exists (xs : List Nat) (vs : List Clif.Val) (length : xs.length = vs.length) (r : Clif.Regs) :
    ∃ next,r.setMany xs vs = some next := by
  induction xs generalizing vs r with
  | nil => cases vs <;> simp_all [Clif.Regs.setMany]
  | cons x xs ih =>
    cases vs with
    | nil => simp at length
    | cons v vs => exact ih vs (by simpa using length) (r.set x v)

/-- Complete ORIGINAL indirect ordinary/two-result and implicit-sret/zero-result
pipelines inhabit actual source calls at address4096, the corresponding original
symbol/external contracts, real retained code and final alias-resolved execution.
Every returned result and every other demanded/available value hold afterwards;
source argument values and the original constant callee value are all4096. -/
theorem stock_complete_indirect_call_source_record_witness (implicit : Bool) :
    ∃ (out : Output) (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (step : Step)
      (bi j : Nat) (b : Clif.Block) (stm : Clif.Stmt) (fr fr' : Clif.Frame) (next : Nat → CV) (world : Arm.ArmState),
      LowerScope (function true implicit) ∧ Dominated (function true implicit) ∧
      ArityOk (function true implicit) ∧ AbiSigsOk (function true implicit) ∧
      Stock.lower (function true implicit) = .ok out.result ∧
      prepareAt out.result.code out.result.edgeArgs = .ok out.prepared ∧
      out.rf = spillAllocAt out.prepared.code out.prepared.edges ∧
      checkAllocAt out.prepared.code out.prepared.edges out.rf = .ok () ∧
      lowerRFunc out.prepared.code out.rf = .ok out.af ∧ Facts true implicit out ∧
      event ∈ out.result.blockScans.toList ∧ record ∈ event.output.records ∧
      (function true implicit).blocks[bi]? = some b ∧ b.body[j]? = some stm ∧
      record.inst = blockStart (function true implicit) bi+j ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.callIndirect 0 80 (arguments true implicit)) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      info.results.length = (if implicit then 0 else 2) ∧ fr.regs 80 = some ⟨.i64,4096⟩ ∧ memory.symbols calleeName = some 4096 ∧
      SourceInstResult (indirectEnv implicit) {funcs := []} event.ctx record.inst (fr,memory) (fr',memory) ∧
      (∀ name b,symbols name = some b → (indirectModel implicit).sym name 0 = BitVec.ofNat 64 b) ∧
      (∀ sl cm w,relation sl cm w → cm.symbols = symbols) ∧
      XCallsIndOk (indirectEnv implicit) (indSigs (function true implicit)) relation (indirectModel implicit) ∧
      ValuesHeld (fun x => Demanded record.output.state x ∧
        x ∈ availOf (function true implicit) (availIn (function true implicit) out.result.ctx) bi j)
        event.ctx fr (fun _ => (4096 : CV)) ∧
      seqRun (explicitCallSem (csem (fun _ => False) ⟨0,0⟩ (indirectModel implicit)))
        (record.output.emitted.toList.map (·.mapRegs (Backend.lowerFunction.resolve out.result.final.alias (out.result.final.alias.size+1))))
        (fun _ => 4096) Arm.ArmState.default = some (.fall next world) ∧ relation fr'.slots memory world ∧
      ValuesHeld (fun x => Demanded record.input x ∧
        x ∈ availOf (function true implicit) (availIn (function true implicit) out.result.ctx) bi (j+1))
        out.result.ctx fr' (fun key => next (aliasNum out.result.final.alias key)) ∧
      ValuesHeld (fun x => x ∈ info.results) out.result.ctx fr' (fun key => next (aliasNum out.result.final.alias key)) := by
  obtain ⟨out,event,record,info,step,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,slot,clif,recorded,emitted,origin,actual,placed⟩ :=
    IndirectCallEmissionWitnessDraft.stock_complete_indirect_call_emission_witness implicit
  obtain ⟨b,j,stm,block,statement,current,inst⟩ := SourceRecordStatementDraft.stock_lower_source_record_statement
    lowered scope events records slot clif
  obtain ⟨sig,declared,params8,abiSig,target,ns,locs,bytes,stack,targetMap,mapping,byteRun,locations,code⟩ :=
    stock_lower_indirect_call_record_code lowered scope dominated.ssa abi events records slot clif recorded emitted
  have expected : (function true implicit).sigDecls.lookup 0 = some (signature true implicit) := rfl
  have same := Option.some.inj (declared.symm.trans expected)
  subst sig
  let fr : Clif.Frame := {
    func := function true implicit
    regs := fun x => if x = 80 ∨ x ∈ arguments true implicit then some ⟨.i64,4096⟩ else none
    slots := []
    body := [⟨info.results,.callIndirect 0 80 (arguments true implicit)⟩]
    term := .ret (if implicit then [] else [40,41]) }
  obtain ⟨sig,declared,resultCount,vectors,bindings⟩ := CallResultBindingDraft.stock_lower_indirect_call_result_binding
    lowered scope dominated.ssa abi events records slot clif recorded emitted
  have same := Option.some.inj (declared.symm.trans expected)
  subst sig
  have count : info.results.length = (values implicit).length := by rw [resultCount]; cases implicit <;> rfl
  obtain ⟨regs,set⟩ := set_exists info.results (values implicit) count fr.regs
  let fr' : Clif.Frame := {fr with regs,body := []}
  have evaluated : instOutcome (indirectEnv implicit) {funcs := []} fr memory
      (.callIndirect 0 80 (arguments true implicit)) = .ok (values implicit,memory) := by
    cases implicit <;> rfl
  have source : SourceInstResult (indirectEnv implicit) {funcs := []} event.ctx record.inst (fr,memory) (fr',memory) :=
    ⟨info,.callIndirect 0 80 (arguments true implicit),values implicit,regs,[],slot,clif,rfl,evaluated,set,rfl⟩
  have held : ValuesHeld (fun _ => True) event.ctx fr (fun _ => (4096 : CV)) := by
    intro x required v lookup
    by_cases present : x = 80 ∨ x ∈ arguments true implicit
    · have same : v = ⟨.i64,4096⟩ := by simpa only [fr,if_pos present,Option.some.injEq] using lookup.symm
      subst v
      rcases present with rfl | member
      · exact ⟨target,targetMap,rfl⟩
      · have mapped : event.ctx.valueReg? x = some (.vreg (192+x) .int) := by
          rw [(stock_lower_record_context lowered scope events).2.1]
          exact beq_iff_eq.mp (List.all_eq_true.mp facts.2.2.1 x member)
        exact ⟨192+x,mapped,rfl⟩
    · simp only [fr,if_neg present] at lookup
      cases lookup
  obtain ⟨next,world,executed,related,guarded,allResults⟩ := stock_lower_indirect_call_guarded_source_run
    (F := fun _ => False) (asm := ⟨0,0⟩) (X := indirectModel implicit) (ρ := fun _ => 4096)
    lowered scope dominated abi (symbol_addresses implicit) (fun _ _ _ h => h) (external implicit)
    events records block statement current slot clif recorded emitted (show fr.func = function true implicit from rfl)
    (held.mono (fun _ _ => trivial)) (show relation fr.slots memory Arm.ArmState.default from rfl) source
  have explicitCount : info.results.length = (if implicit then 0 else 2) := by rw [resultCount]; cases implicit <;> rfl
  exact ⟨out,event,record,info,step,event.block,j,b,stm,fr,fr',next,world,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,events,records,block,statement,current,slot,clif,recorded,emitted,explicitCount,(by simp [fr]),(by simp [memory,symbols]),source,
    symbol_addresses implicit,(fun _ _ _ h => h),external implicit,held.mono (fun _ _ => trivial),executed,related,guarded,allResults⟩
end Backend.Stock.Proof.IndirectSourceWitnessDraft

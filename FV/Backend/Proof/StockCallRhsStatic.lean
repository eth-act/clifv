import FV.Backend.Proof.StockCallRootMatch
namespace Backend.Stock.Proof.CallRhsStaticDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64
open CallRhsCallsDraft CallAbiStaticDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem abi_identity {ctx : Ctx} {sig : Clif.Signature} {st next : State} {v : V}
    (run : Stock.externCtor ctx T.abi_sig [.op (.sig sig)] st = .ok (v,next)) :
    v = .op (.sig sig) ∧ next = st := by
  rw [stock_ctor_baseOnly _ _ _ _ (by decide)] at run
  change ExtResult.ok (.op (.sig sig),st) = .ok (v,next) at run
  cases run
  exact ⟨rfl,rfl⟩

private theorem none_identity {ctx : Ctx} {st next : State} {v : V}
    (run : Stock.externCtor ctx T.try_call_none [] st = .ok (v,next)) :
    v = .op .tryCallNone ∧ next = st := by
  change ExtResult.ok (.op .tryCallNone,st) = .ok (v,next) at run
  cases run
  exact ⟨rfl,rfl⟩

private theorem numbers : ∀ rs : List Reg,(∀ r ∈ rs,∃ n,r = .vreg n .int) →
    ∃ ns : List Nat,rs = ns.map (fun n => Reg.vreg n .int)
  | [],_ => ⟨[],rfl⟩
  | r :: rs,virtual => by
    obtain ⟨n,rfl⟩ := virtual r (List.mem_cons_self ..)
    obtain ⟨ns,rfl⟩ := numbers rs (fun r member => virtual r (List.mem_cons_of_mem _ member))
    exact ⟨n :: ns,rfl⟩

/-- Helpers extracted from the real direct-call RHS produce statically valid
ABI call info at its actual internal call execution. Virtual source arguments
come from the original mapped context, and the ABI condition is unchanged.
No separately replayed helper protocol or call-shape certificate is supplied. -/
theorem stock_direct_call_rhs_info_static {p : Program} {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {args : List Nat} {sig : Clif.Signature}
    (abi : sigAbiOk sig = true) {name : String} {before next : State}
    {tr trace : Array RuleId} {out : V}
    (calls : DirectRootCalls p ctx args sig name false before next tr trace out) :
    ∃ (call : CallInfo) (atCall afterCall : State) (callTrace : Array RuleId) (machine : V) (fuel : Nat),
      SpillInstOk (.call call) ∧ 30 ≤ fuel ∧
      ApplyInternal p (Stock.sem ctx) {} fuel 46 638 [.op (.callInfo call)]
        (atCall,tr) machine (afterCall,callTrace) := by
  obtain ⟨outs,afterOut,abiValue,afterAbi,requested,afterRequest,uses,afterArgs,defs,afterDefs,noTry,afterNone,
    info,afterInfo,machine,afterMachine,machineTrace,unit,afterEmit,emitTrace,callFuel,emitFuel,
    output,abiRun,request,arguments,returns,noneRun,formed,callBound,emitBound,machineCall,emission,outputRun,traceEq⟩ := calls
  obtain ⟨rfl,rfl⟩ := abi_identity abiRun
  obtain ⟨safe,rs,mapping,rfl,requestState⟩ := (stock_put_in_regs_vec_iff _ _ _ _ _).mp request
  have virtual : ∀ r ∈ rs,∃ n,r = .vreg n .int := by
    intro r member
    obtain ⟨x,present,lookup⟩ := Backend.Proof.Flow.mapM_mem mapping r member
    exact mapped.valueReg x r lookup
  obtain ⟨ns,rfl⟩ := numbers rs virtual
  obtain ⟨rfl,rfl⟩ := none_identity noneRun
  obtain ⟨locs,bytes,stack,call,byteRun,locations,useValue,defValue,infoValue,shape,valid,static,
    stores,pins,outgoing⟩ := stock_call_helpers_static abi false name 0 output arguments returns formed
  rw [infoValue] at machineCall
  exact ⟨call,afterInfo,afterMachine,machineTrace,machine,callFuel,static,callBound,machineCall⟩
end Backend.Stock.Proof.CallRhsStaticDraft

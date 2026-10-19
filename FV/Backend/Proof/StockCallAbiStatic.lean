import FV.Backend.Proof.StockCallOutputStatic
namespace Backend.Stock.Proof.CallAbiStaticDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.CallOutputStaticDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

def infoTerm (indirect : Bool) : Term := if indirect then T.gen_call_ind_info else T.gen_call_info
def infoArgs (indirect : Bool) (sig : Clif.Signature) (name : String) (target : Nat) (uses defs : V) : List V :=
  if indirect then [.op (.sig sig),.reg (.vreg target .int),uses,defs,.op .tryCallNone]
  else [.op (.sig sig),.op (.extName name),uses,defs,.op .tryCallNone,.bool false]
private theorem delegated {ctx : Ctx} {term : Term} {args : List V} {st next : State} {out : V}
    (ordinary : term.id ∉ revisedCtors)
    (run : Stock.externCtor ctx term args st = .ok (out,next)) :
    ∃ base,Backend.externCtor ctx term args st.base = .ok (out,base) ∧ next = {st with base} := by
  rw [stock_ctor_baseOnly _ _ _ _ ordinary] at run
  cases call : Backend.externCtor ctx term args st.base with
  | fail => rw [call] at run; cases run
  | unmodeled e => rw [call] at run; cases run
  | ok pair =>
    rcases pair with ⟨value,base⟩
    rw [call] at run
    cases run
    exact ⟨base,rfl,rfl⟩

/-- Actual Stock helper executions derive direct/indirect call static validity
and fresh distinct ABI definitions, with arbitrary stack-passed arguments.
The signature ABI premise is the original input condition; no caller call-shape
or post-helper certificate is supplied. Helpers may run at their actual states. -/
theorem stock_call_helpers_static {ctx : Ctx} {sig : Clif.Signature} (abi : sigAbiOk sig = true)
    {before afterOut argBefore argAfter pinBefore pinAfter infoBefore infoAfter : State}
    {outs uses defs info : V} {args : List Nat} (indirect : Bool) (name : String) (target : Nat)
    (output : Stock.externCtor ctx T.gen_call_output [.op (.sig sig)] before = .ok (outs,afterOut))
    (arguments : Stock.externCtor ctx T.gen_call_args
      [.op (.sig sig),.regsVec ((args.map fun n => Reg.vreg n .int).map fun r => [r])] argBefore = .ok (uses,argAfter))
    (returns : Stock.externCtor ctx T.gen_call_rets [.op (.sig sig),outs] pinBefore = .ok (defs,pinAfter))
    (formed : Stock.externCtor ctx (infoTerm indirect) (infoArgs indirect sig name target uses defs) infoBefore = .ok (info,infoAfter)) :
    ∃ (locs : List ArgLoc) (bytes : List Nat) (stack : Nat) (call : CallInfo),
      sigParamBytes sig = .ok bytes ∧ sigArgLocs sig = .ok (locs,stack) ∧
      uses = .op (.callArgs (retPairs (regPairsOf ((locs.zip args).zip bytes)))) ∧
      defs = .op (.callRets (callDefs (outDefs before.base.nextVreg sig.returns.length))) ∧
      info = .op (.callInfo call) ∧
      call = ⟨if indirect then .reg (.vreg target .int) else .sym name,
        retPairs (regPairsOf ((locs.zip args).zip bytes)),callDefs (outDefs before.base.nextVreg sig.returns.length)⟩ ∧
      CallOk before.base.nextVreg (regPairsOf ((locs.zip args).zip bytes)) (outDefs before.base.nextVreg sig.returns.length) ∧
      SpillInstOk (.call call) ∧
      argAfter = {argBefore with base.emitted := argBefore.base.emitted ++
        ((stackEnts ((locs.zip args).zip bytes)).map argStore).toArray} ∧
      pinAfter = pinBefore ∧ infoAfter = {infoBefore with base.outgoing := max infoBefore.base.outgoing stack} := by
  rw [stock_gen_call_output_exact] at output
  cases output
  obtain ⟨argBase,argRun,argState⟩ := delegated (by decide) arguments
  obtain ⟨bytes,byteRun⟩ := ctor_gen_call_args_bytes argRun
  obtain ⟨locs,stack,locRun⟩ := ctor_gen_call_args_locs argRun
  obtain ⟨useValue,stores⟩ := (ctor_gen_call_args_gen _ _ args byteRun locRun _ _).mp argRun
  have argFull : argAfter = {argBefore with base.emitted := argBefore.base.emitted ++
      ((stackEnts ((locs.zip args).zip bytes)).map argStore).toArray} := by
    rw [argState,stores]
  obtain ⟨retBase,retRun,retState⟩ := delegated (by decide) returns
  obtain ⟨ps,rs,pins,unpacked,defValue,unchanged⟩ := (ctor_gen_call_rets_iff _ _ _ _ _).mp retRun
  rw [outRegs_length] at pins
  rw [outRegs_single] at unpacked
  cases unpacked
  obtain ⟨bound,pinShape⟩ := retRegs_eq pins
  rw [pinShape,callDefs_outDefs] at defValue
  have pinFull : pinAfter = pinBefore := by rw [retState,unchanged]
  have classed := callOk_of (N := before.base.nextVreg) (b := before.base.nextVreg)
    (Nat.le_refl _) bound abi locRun args bytes
  have final : info = .op (.callInfo ⟨if indirect then .reg (.vreg target .int) else .sym name,
        retPairs (regPairsOf ((locs.zip args).zip bytes)),callDefs (outDefs before.base.nextVreg sig.returns.length)⟩) ∧
      infoAfter = {infoBefore with base.outgoing := max infoBefore.base.outgoing stack} := by
    rw [useValue,defValue] at formed
    cases indirect with
    | false =>
      obtain ⟨base,legacy,state⟩ := delegated (by decide) formed
      obtain ⟨value,area⟩ := (ctor_gen_call_info_gen _ _ _ _ _ _ _ locRun _ _).mp legacy
      exact ⟨value,by rw [state,area]⟩
    | true =>
      obtain ⟨base,legacy,state⟩ := delegated (by decide) formed
      obtain ⟨value,area⟩ := (ctor_gen_call_ind_info_gen _ _ _ _ _ _ locRun _ _).mp legacy
      exact ⟨value,by rw [state,area]⟩
  refine ⟨locs,bytes,stack,_,byteRun,locRun,useValue,defValue,final.1,rfl,classed,?_,argFull,pinFull,final.2⟩
  cases indirect with
  | false => exact spillInstOk_callSym name classed
  | true => exact spillInstOk_callReg target classed
end Backend.Stock.Proof.CallAbiStaticDraft

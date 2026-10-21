import FV.Backend.Proof.StockCallRootSelection
namespace Backend.Stock.Proof.CallRhsCallsDraft
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl

def directEnv (args : List Nat) (sig : Clif.Signature) (name : String) (patch : Bool) : Isle.Interp.Env V :=
  #[some (.values args),some (.op (.sig sig)),some (.op (.extName name)),some (.bool patch),none,none,none,none,none,none]

def DirectRootCalls (p : Program) (ctx : Ctx) (args : List Nat) (sig : Clif.Signature)
    (name : String) (patch : Bool) (before next : State) (tr trace : Array RuleId) (out : V) : Prop :=
  ∃ outs afterOut abi afterAbi requested afterRequest uses afterArgs defs afterDefs noTry afterNone
      info afterInfo machine afterMachine machineTrace unit afterEmit emitTrace callFuel emitFuel,
    Stock.externCtor ctx T.gen_call_output [.op (.sig sig)] before = .ok (outs,afterOut) ∧
    Stock.externCtor ctx T.abi_sig [.op (.sig sig)] afterOut = .ok (abi,afterAbi) ∧
    Stock.externCtor ctx T.put_in_regs_vec [.values args] afterAbi = .ok (requested,afterRequest) ∧
    Stock.externCtor ctx T.gen_call_args [abi,requested] afterRequest = .ok (uses,afterArgs) ∧
    Stock.externCtor ctx T.gen_call_rets [abi,outs] afterArgs = .ok (defs,afterDefs) ∧
    Stock.externCtor ctx T.try_call_none [] afterDefs = .ok (noTry,afterNone) ∧
    Stock.externCtor ctx T.gen_call_info [abi,.op (.extName name),uses,defs,noTry,.bool patch] afterNone = .ok (info,afterInfo) ∧
    30 ≤ callFuel ∧ 30 ≤ emitFuel ∧
    ApplyInternal p (Stock.sem ctx) {} callFuel 46 638 [info] (afterInfo,tr) machine (afterMachine,machineTrace) ∧
    ApplyInternal p (Stock.sem ctx) {} emitFuel 13 242 [machine] (afterMachine,machineTrace) unit (afterEmit,emitTrace) ∧
    Stock.externCtor ctx T.output_vec [outs] afterEmit = .ok (out,next) ∧ trace = emitTrace

/-- The actual direct-call RHS yields every helper at its real intermediate
Stock state and both real internal call/emit executions. This binds helpers to
the selected expression rather than a separately replayed protocol. -/
theorem stock_direct_call_rhs_calls {p : Program} (hp : Data p) (ctx : Ctx)
    (args : List Nat) (sig : Clif.Signature) (name : String) (patch : Bool)
    {before next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} 999999 rule_lower_2508.rhs (directEnv args sig name patch)).run
      (before,tr) = .ok (some out,next,trace)) : DirectRootCalls p ctx args sig name patch before next tr trace out := by
  have hc : ({} : Config).checkOverlap = false := rfl
  cases hp
  isel_inv [*,rule_lower_2508,directEnv,sem_ctor] at run
  isel_destruct
  simp [Array.getElem?_setIfInBounds,Array.size_setIfInBounds] at *
  isel_destruct
  subst_vars
  rename_i afterOutput afterOut afterAbi afterArgs afterDefs requested unit afterEmission abi afterInfo
    outs afterRequest machine afterMachine uses info defs noTry afterNone emissionCall noneCall machineCall
    trivial1 trivial2 trivial3 trivial4 trivial5 trivial6 outputCall outputCtor retsCtor argsCtor abiCtor requestCtor infoCtor
  exact ⟨outs,afterOut,abi,afterAbi,requested,afterRequest,uses,afterArgs,defs,afterDefs,noTry,afterNone,
    info,afterInfo,machine,afterMachine.1,afterMachine.2,unit,afterEmission.1,afterEmission.2,999988,999990,
    outputCtor,abiCtor,requestCtor,argsCtor,retsCtor,noneCall,infoCtor,by decide,by decide,machineCall,
    emissionCall,outputCall,rfl⟩

end Backend.Stock.Proof.CallRhsCallsDraft

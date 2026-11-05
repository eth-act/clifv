import FV.E2E.StockCallStoreFunction
import FV.E2E.StockCallStoreNoTrap

namespace Backend.Stock.CallStore
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false

/-- Returned executions use both existing contracts. Callee-trap propagation is a separate obligation. -/
structure ReturnStoreDomain (f : Clif.Function) (vc : VCode) : Prop where
  scope : LowerScope f
  dominated : Dominated f
  abi : sigAbiOk f.sig = true
  lower : ∃ result,Stock.lower f = .ok result ∧ result.code = vc
  returns : ∀ {env : Clif.Env} {cp : Clif.Program},InSubset cp f →
    ∀ {args : List Clif.Val} {fr : Clif.Frame} {cm outMem : Clif.Mem},SourceEntry f args fr →
    ∀ {fuel : Nat} {vals : List Clif.Val},
      Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem →
    ∀ {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {MR : MemRelT},
      XCallsOk env (f.externs.map (·.2)) MR X → MRStable F MR →
    ∀ {sb : Nat} {syms : String → Option Nat},MemRefines F sb syms (csem F ctx X) →
      MemRelOk F sb syms f MR →
    ∀ {w : Arm.ArmState},MR fr.slots cm w → ArgsAtEntry F f.sig args w →
      ∃ ρ,RunOkABI f vc (csem F ctx X) MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals outMem)
  notrap_under_original_condition : ∀ {env : Clif.Env} {cp : Clif.Program},InSubset cp f →
    ∀ {args : List Clif.Val} {fr : Clif.Frame} {cm : Clif.Mem},SourceEntry f args fr →
      TrapsExplicit env cp ⟨fr,[],cm⟩ → ∀ fuel code,Clif.runLoop env cp fuel ⟨fr,[],cm⟩ ≠ .trapped code

/-- Artifact checks establish the returned-execution contract without a source-memory admission guard. -/
theorem check_return_store_domain {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ReturnStoreDomain f vc := by
  obtain ⟨result,lowered,equal,scope,dominated,abi,⟨layout⟩,_⟩ := check_sound checked
  refine ⟨scope,dominated,abi,⟨result,lowered,equal⟩,?_,?_⟩
  · intro env cp subset args fr cm outMem entered fuel vals returned F ctx X MR calls stable sb syms
      memorySem memoryOk w memory arguments
    rw [← equal]
    exact layout.return_function lowered scope dominated subset entered returned calls stable memorySem memoryOk memory arguments
  · intro env cp subset args fr cm entered explicit fuel code
    obtain ⟨blocks,parameters,body,term,params,returns,calleeParams,calleeReturns,integer,lookup,pins,
      pointerCalled,argumentCalled,pointerArgument,flags,parameterBytes⟩ := layout.source_fields
    obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := entered
    have first : f.entry? = some layout.data.block := by
      simp only [Clif.Function.entry?,blocks,List.head?_cons]
    cases Option.some.inj (found.symm.trans first)
    have func : fr.func = f := congrArg Clif.Frame.func frame
    have sourceBody : fr.body = [⟨[layout.data.called],.call layout.data.fn [layout.data.argument]⟩,
        ⟨[],.store .store .i64 layout.data.flags layout.data.called layout.data.pointer 8⟩] :=
      (congrArg Clif.Frame.body frame).trans body
    have sourceTerm : fr.term = .ret [layout.data.called] := (congrArg Clif.Frame.term frame).trans term
    apply no_trap_under_original_condition sourceBody sourceTerm (by rw [flags]; decide)
      (by rw [func]; exact lookup) ?_ calleeReturns explicit fuel code
    exact subset.externCalls layout.data.block (by simp [blocks])
      ⟨[layout.data.called],.call layout.data.fn [layout.data.argument]⟩ (by simp [body])
      layout.data.fn [layout.data.argument] rfl layout.data.ext lookup

end Backend.Stock.CallStore

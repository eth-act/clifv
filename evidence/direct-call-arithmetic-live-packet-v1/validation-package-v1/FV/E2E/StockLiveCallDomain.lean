import FV.E2E.StockLiveCallFunction
import FV.E2E.StockResultCallDomain

namespace Backend.Stock.LiveCall
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The original explicit-trap premise excludes hidden callee traps; the arithmetic continuation cannot trap. -/
theorem source_call_notrap {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame}
    {cm : Clif.Mem} {fn : Clif.FnRef} {live called sum : Nat}
    (body : fr.body = [⟨[called],.call fn [live]⟩,⟨[sum],.binary .iadd .i64 called live⟩])
    (term : fr.term = .ret [sum])
    (external : ∀ ext,fr.func.extern? fn = some ext → cp.func? ext.name = none)
    (explicit : TrapsExplicit env cp ⟨fr,[],cm⟩) (fuel : Nat) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel ⟨fr,[],cm⟩ ≠ .trapped code := by
  intro trapped
  cases fuel with
  | zero => cases trapped
  | succ fuel =>
    have step : Clif.step env cp ⟨fr,[],cm⟩ =
        Clif.StepResult.ofRes (instOutcome env cp fr cm (.call fn [live]))
          (fun pair => Clif.continueWith ⟨fr,[],cm⟩ [⟨[sum],.binary .iadd .i64 called live⟩]
            [called] pair.1 pair.2) := by
      simp only [Clif.step,body]
      exact stepCall_eq env cp ⟨fr,[],cm⟩ [⟨[sum],.binary .iadd .i64 called live⟩] [called] fn [live] external
    rw [Clif.runLoop_succ,step] at trapped
    cases outcome : instOutcome env cp fr cm (.call fn [live]) with
    | trap c =>
      have halted : Clif.step env cp ⟨fr,[],cm⟩ = .trapped c := by rw [step,outcome]; rfl
      have impossible := explicit.stmt ⟨fr,[],cm⟩ c ⟨[called],.call fn [live]⟩
        [⟨[sum],.binary .iadd .i64 called live⟩] (.refl _) halted body
      cases impossible
    | stuck message => simp only [outcome,Clif.StepResult.ofRes] at trapped; cases trapped
    | ok pair =>
      obtain ⟨results,after⟩ := pair
      cases results with
      | nil =>
        simp only [outcome,Clif.StepResult.ofRes,Clif.continueWith,Clif.Regs.setMany] at trapped
        cases trapped
      | cons value rest =>
        cases rest with
        | nil =>
          simp only [outcome,Clif.StepResult.ofRes,Clif.continueWith,Clif.Regs.setMany] at trapped
          apply OrdinaryBody.ordinary_source_notrap fuel
            ⟨{fr with body := [⟨[sum],.binary .iadd .i64 called live⟩],regs := fr.regs.set called value},[],after⟩
            rfl ?_ term code trapped
          intro statement member
          have same : statement = ⟨[sum],.binary .iadd .i64 called live⟩ := by simpa using member
          subst statement
          refine ⟨?_,?_⟩
          · constructor
            · intro fn args impossible; cases impossible
            · intro sig callee args impossible; cases impossible
          · intro frame memory trap failed
            simp only [Clif.evalInst,Clif.BinaryOp.isShift,Bool.false_eq_true,↓reduceIte] at failed
            rcases Clif.res_bind_eq_trap failed with first | ⟨a,readA,second⟩
            · exact Clif.Frame.getAs_ne_trap frame called .i64 trap first
            · rcases Clif.res_bind_eq_trap second with next | ⟨b,readB,last⟩
              · exact Clif.Frame.getAs_ne_trap frame live .i64 trap next
              · cases last
        | cons next tail =>
          simp only [outcome,Clif.StepResult.ofRes,Clif.continueWith,Clif.Regs.setMany] at trapped
          cases trapped

/-- Reuse the existing universal call Domain without copying a consumer contract. -/
abbrev Domain := ResultCall.Domain

theorem check_domain {f : Clif.Function} {vc : VCode} (checked : check f vc = true) : Domain f vc := by
  obtain ⟨result,lowered,equal,scope,dominated,abi,⟨layout⟩,_⟩ := check_sound checked
  refine ⟨scope,dominated,abi,⟨result,lowered,equal⟩,?_,?_⟩
  · intro env cp subset args fr cm outMem entered fuel vals returned F ctx X MR calls stable sb syms
      memorySem w memory arguments
    rw [← equal]
    exact layout.return_function lowered scope dominated subset entered returned calls stable memorySem memory arguments
  · intro env cp subset args fr cm entered explicit fuel code
    obtain ⟨blocks,parameters,body,term,params,returns,calleeParams,calleeReturns,integer,lookup,pins,
      separate,sumCalled,sumLive,parameterBytes⟩ := layout.source_fields
    obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := entered
    have first : f.entry? = some layout.data.block := by
      simp only [Clif.Function.entry?,blocks,List.head?_cons]
    cases Option.some.inj (found.symm.trans first)
    have func : fr.func = f := congrArg Clif.Frame.func frame
    have sourceBody : fr.body = [⟨[layout.data.called],.call layout.data.fn [layout.data.live]⟩,
        ⟨[layout.data.sum],.binary .iadd .i64 layout.data.called layout.data.live⟩] :=
      (congrArg Clif.Frame.body frame).trans body
    have sourceTerm : fr.term = .ret [layout.data.sum] := (congrArg Clif.Frame.term frame).trans term
    apply source_call_notrap sourceBody sourceTerm ?_ explicit fuel code
    intro ext found
    have same : ext = layout.data.ext := by
      rw [func,lookup] at found
      exact Option.some.inj found.symm
    subst ext
    exact subset.externCalls layout.data.block (by simp [blocks])
      ⟨[layout.data.called],.call layout.data.fn [layout.data.live]⟩ (by simp [body])
      layout.data.fn [layout.data.live] rfl layout.data.ext lookup

end Backend.Stock.LiveCall

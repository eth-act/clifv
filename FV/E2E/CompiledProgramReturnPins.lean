import FV.E2E.ReturnPinCheckSound
import FV.E2E.LinkCheck

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof LinkCheck
set_option autoImplicit false
set_option Elab.async false

namespace LinkSys
variable (L : LinkSys)

/-- Check actual direct or indirect targets using the retained reachability and GOT boundary.

Since #1003 the check reads the call's **results** only, its first `h.sig.returns.length`
definitions: a call's definitions are its declared results followed, at a `try_call`, by the
exception payload registers x0, x1 that are not result registers (`Isel`'s `callRets`), and a
linked call supplies the declared results only (`LinkSys.progXWithPins`, #587). Checking the
payload definitions against the return pins as well rejected every `try_call` of an `sret`
function compiled by the Stock route (pins `[x8]`, definitions x0, x1): 2 of the survey's 18
executables. -/
def returnPinSiteB (g : Clif.Function) (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match L.P.func? n with
    | some h => ReturnPinCheck.check (info.defs.take h.sig.returns.length) h (L.A h).vc
    | none => true
  | .reg (.vreg t .int) =>
    L.P.funcs.all fun h =>
      !indToB L.syms g h ||
      (match gotOf (L.A g).vcp t with | some n => h.name != n | none => false) ||
      decide ((regLocs h.sig).length ≠ info.uses.length) ||
      ReturnPinCheck.check (info.defs.take h.sig.returns.length) h (L.A h).vc
  | _ => true

/-- The compiler checks every actual call and try-call before it creates the program artifact. -/
def returnPinsB (g : Clif.Function) : Bool :=
  allInsts (L.A g).vcp (siteB (L.returnPinSiteB g))

/-- Static result compatibility follows from actual call metadata, never a caller execution certificate. -/
structure ReturnPinsCompatible (g : Clif.Function) (selected : Clif.Function → List Reg := L.checkedReturnPins) : Prop where
  direct : ∀ info h,L.ProgSite g info h → ∀ definitions,
    info.defs = callDefs definitions → CallReturnPins definitions (selected h)
  indirect : ∀ info,(L.A g).vcp.CallSite info → ∀ t,info.dest = .reg (.vreg t .int) →
    ∀ h ∈ L.P.funcs,L.BlrTo g t h → (regLocs h.sig).length = info.uses.length →
    ∀ definitions,info.defs = callDefs definitions →
      CallReturnPins definitions (selected h)

/-- The checked return pins a call reads: the first `sig.returns.length` of the callee's
(`LinkSys.progXWithPins` returns the values of exactly these). -/
def checkedResultPins (h : Clif.Function) : List Reg :=
  (L.checkedReturnPins h).take h.sig.returns.length

/-- The executable scan derives direct and indirect physical result compatibility.

Statement changed with `returnPinSiteB` (#1003): the scan now checks a call's results (its first
`sig.returns.length` definitions), so it gives agreement of the call's definitions with the pins
a call reads (`checkedResultPins`), no longer with every return pin of the callee; the old
conclusion is false for the accepted `try_call` of a Stock-route `sret` function
(`ReturnPinPayloadWitness`). -/
theorem returnPinsB_sound {g : Clif.Function} (checked : L.returnPinsB g = true) :
    L.ReturnPinsCompatible g L.checkedResultPins := by
  constructor
  · intro info h site definitions defs
    obtain ⟨present,name,dest,found⟩ := site
    have selected := site_sound checked present
    simp only [returnPinSiteB,dest,found] at selected
    rw [defs,callDefs_take] at selected
    have matched := CallReturnPins.take_defs.mp (returnPinCheck_sound selected)
    simpa only [returnPinCheck_pins,checkedResultPins,checkedReturnPins] using matched
  · intro info present t dest h member target arity definitions defs
    have selected := site_sound checked present
    simp only [returnPinSiteB,dest,List.all_eq_true] at selected
    have selected := selected h member
    have reachable := indToB_of target.1
    have got : (match gotOf (L.A g).vcp t with | some n => h.name != n | none => false) = false := by
      cases found : gotOf (L.A g).vcp t with
      | none => rfl
      | some name =>
        have same := target.2 name (gotOf_sound found)
        simp [same]
    simp only [reachable,Bool.not_true,Bool.false_or,got,arity,ne_eq,not_true_eq_false,
      decide_false,Bool.or_false] at selected
    rw [defs,callDefs_take] at selected
    have matched := CallReturnPins.take_defs.mp (returnPinCheck_sound selected)
    simpa only [returnPinCheck_pins,checkedResultPins,checkedReturnPins] using matched

end LinkSys

/-- The compilation field retains the actual return mode and derives static caller compatibility.

`calls` changed with the scan `returnPinsB` it is derived from (#1003): a call's definitions
agree with the pins the call reads, the first `sig.returns.length` return pins of the callee
(`LinkSys.progXWithPins`), which is all `progOsCore_return_pins_results` uses. Agreement with
every return pin (the field before) implies it (`CallReturnPins.take`). -/
structure CompiledProgramReturnPins (L : LinkSys) (g : Clif.Function)
    (modes : Clif.Function → ReturnPinMode := fun h => ReturnPinMode.checked h (L.A h).vc) : Prop where
  artifact : CompiledSemanticReturnPins g (L.A g).k (L.A g).vc (L.A g).vcp (L.A g).rf
    (L.A g).af (L.A g).fa (L.A g).fb (modes g)
  calls : L.ReturnPinsCompatible g
    (fun h => ((modes h).pins h (sigRets h.sig).length).take h.sig.returns.length)

namespace CompiledProgramReturnPins
variable {L : LinkSys} {g : Clif.Function}

/-- Actual executable checks and pipeline observations construct the complete compilation field. -/
theorem of_checks {cleanup : Bool} (lower : SemanticABI.check g (L.A g).vc = true)
    (prepared : Backend.prepare (Stock.Arithmetic.stageF cleanup g (L.A g).vc) = .ok (L.A g).vcp)
    (prepOk : prepCheck (Stock.Arithmetic.stageF cleanup g (L.A g).vc) (L.A g).vcp = true)
    (check : Backend.checkAlloc (L.A g).vcp (L.A g).rf = .ok ())
    (alloc : lowerRFunc (L.A g).vcp (L.A g).rf = .ok (L.A g).af)
    (emit : emitFunc (L.A g).k (L.A g).af = .ok (L.A g).fa)
    (layout : (L.A g).fa.layout = .ok (L.A g).fb)
    (pins : L.returnPinsB g = true) : CompiledProgramReturnPins L g :=
  ⟨CompiledSemanticReturnPins.of_checks lower prepared prepOk check alloc emit layout,
    L.returnPinsB_sound pins⟩

theorem of_checks_calls {cleanup : Bool} (lower : SemanticABI.checkCalls g (L.A g).vc = true)
    (prepared : Backend.prepare (Stock.Arithmetic.stageF cleanup g (L.A g).vc) = .ok (L.A g).vcp)
    (prepOk : prepCheck (Stock.Arithmetic.stageF cleanup g (L.A g).vc) (L.A g).vcp = true)
    (check : Backend.checkAlloc (L.A g).vcp (L.A g).rf = .ok ())
    (alloc : lowerRFunc (L.A g).vcp (L.A g).rf = .ok (L.A g).af)
    (emit : emitFunc (L.A g).k (L.A g).af = .ok (L.A g).fa)
    (layout : (L.A g).fa.layout = .ok (L.A g).fb)
    (pins : L.returnPinsB g = true) : CompiledProgramReturnPins L g :=
  ⟨CompiledSemanticReturnPins.of_checks_calls lower prepared prepOk check alloc emit layout,
    L.returnPinsB_sound pins⟩

theorem check {modes : Clif.Function → ReturnPinMode} (hc : CompiledProgramReturnPins L g modes) : checkAlloc (L.A g).vcp (L.A g).rf = .ok () :=
  hc.artifact.erase.check

theorem alloc {modes : Clif.Function → ReturnPinMode} (hc : CompiledProgramReturnPins L g modes) : lowerRFunc (L.A g).vcp (L.A g).rf = .ok (L.A g).af :=
  hc.artifact.erase.alloc

theorem emit {modes : Clif.Function → ReturnPinMode} (hc : CompiledProgramReturnPins L g modes) : emitFunc (L.A g).k (L.A g).af = .ok (L.A g).fa :=
  hc.artifact.erase.emit

theorem layout {modes : Clif.Function → ReturnPinMode} (hc : CompiledProgramReturnPins L g modes) : (L.A g).fa.layout = .ok (L.A g).fb :=
  hc.artifact.erase.layout

end CompiledProgramReturnPins
end E2E

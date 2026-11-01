import FV.E2E.ReturnPinCheckSound
import FV.E2E.LinkCheck

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof LinkCheck
set_option autoImplicit false
set_option Elab.async false

namespace LinkSys
variable (L : LinkSys)

/-- Check actual direct or indirect targets using the retained reachability and GOT boundary. -/
def returnPinSiteB (g : Clif.Function) (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match L.P.func? n with
    | some h => ReturnPinCheck.check info.defs h (L.A h).vc
    | none => true
  | .reg (.vreg t .int) =>
    L.P.funcs.all fun h =>
      !indToB L.syms g h ||
      (match gotOf (L.A g).vcp t with | some n => h.name != n | none => false) ||
      decide ((regLocs h.sig).length ≠ info.uses.length) ||
      ReturnPinCheck.check info.defs h (L.A h).vc
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

/-- The executable scan derives direct and indirect physical result compatibility. -/
theorem returnPinsB_sound {g : Clif.Function} (checked : L.returnPinsB g = true) :
    L.ReturnPinsCompatible g := by
  constructor
  · intro info h site definitions defs
    obtain ⟨present,name,dest,found⟩ := site
    have selected := site_sound checked present
    simp only [returnPinSiteB,dest,found] at selected
    rw [defs] at selected
    have matched := returnPinCheck_sound selected
    simpa only [returnPinCheck_pins,checkedReturnPins] using matched
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
    rw [defs] at selected
    have matched := returnPinCheck_sound selected
    simpa only [returnPinCheck_pins,checkedReturnPins] using matched

end LinkSys

/-- The compilation field retains the actual return mode and derives static caller compatibility. -/
structure CompiledProgramReturnPins (L : LinkSys) (g : Clif.Function)
    (modes : Clif.Function → ReturnPinMode := fun h => ReturnPinMode.checked h (L.A h).vc) : Prop where
  artifact : CompiledSemanticReturnPins g (L.A g).k (L.A g).vc (L.A g).vcp (L.A g).rf
    (L.A g).af (L.A g).fa (L.A g).fb (modes g)
  calls : L.ReturnPinsCompatible g (fun h => (modes h).pins h (sigRets h.sig).length)

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

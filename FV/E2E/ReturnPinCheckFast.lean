import FV.E2E.CompiledProgramReturnPins
import FV.E2E.LinkCheckFast

namespace E2E.LinkCheck
open Backend
set_option autoImplicit false
set_option Elab.async false

/-- Cache artifact lookup with the same first-name rule, including failed pipeline results. -/
def returnPinArtMap (R : Res) : Std.HashMap String Art :=
  assocMap (R.map fun e => (e.1.name,getOk e.2))

theorem returnPinArtMap_get (R : Res) (g : Clif.Function) :
    ((returnPinArtMap R)[g.name]?).getD default = artOf R g := by
  rw [returnPinArtMap,assocMap_get]
  induction R with
  | nil => rfl
  | cons e R ih =>
    simp only [List.map_cons,List.lookup_cons,artOf,List.find?_cons] at ih ⊢
    by_cases same : e.1.name = g.name
    · simp [same]
    · have reverse : (g.name == e.1.name) = false := by simpa using Ne.symm same
      have forward : (e.1.name == g.name) = false := by simpa using same
      simpa only [forward,reverse,Bool.false_eq_true,if_false] using ih

/-- One target's source function, physical result pins, and argument arity. -/
structure ReturnPinEntry where
  function : Clif.Function
  pins : List Reg
  arity : Nat

def ReturnPinEntry.of (A : Clif.Function → Art) (g : Clif.Function) : ReturnPinEntry :=
  ⟨g,ReturnPinCheck.pins g (A g).vc,(regLocs g.sig).length⟩

def ReturnPinEntry.check (e : ReturnPinEntry) (definitions : List (Reg × Reg)) : Bool :=
  decide ((definitions.map (·.1)).take e.pins.length = e.pins.take definitions.length)

theorem ReturnPinEntry.check_of (A : Clif.Function → Art) (g : Clif.Function)
    (definitions : List (Reg × Reg)) :
    (ReturnPinEntry.of A g).check definitions = ReturnPinCheck.check definitions g (A g).vc := rfl

/-- Preserve duplicate entries for indirect checks. Direct lookup keeps the first entry. -/
structure ReturnPinCtx where
  symbols : String → Option Nat
  artifact : Clif.Function → Art
  entries : List ReturnPinEntry
  direct : String → Option ReturnPinEntry

def ReturnPinCtx.of (I : LinkInput) (R : Res) : ReturnPinCtx :=
  let symbols := assocMap I.syms
  let artifacts := returnPinArtMap R
  let artifact := fun g : Clif.Function => (artifacts[g.name]?).getD default
  let entries := (progOf R).funcs.map (ReturnPinEntry.of artifact)
  let direct := assocMap (entries.map fun e => (e.function.name,e))
  ⟨fun n => symbols[n]?,artifact,entries,fun n => direct[n]?⟩

private theorem entryLookup (A : Clif.Function → Art) (fs : List Clif.Function) (n : String) :
    ((fs.map (ReturnPinEntry.of A)).map (fun e => (e.function.name,e))).lookup n =
      (fs.find? (·.name == n)).map (ReturnPinEntry.of A) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.map_cons,List.lookup_cons,List.find?_cons,ReturnPinEntry.of] at ih ⊢
    by_cases same : f.name = n
    · simp [same,ReturnPinEntry.of]
    · have reverse : (n == f.name) = false := by simpa using Ne.symm same
      have forward : (f.name == n) = false := by simpa using same
      simpa only [forward,reverse,Bool.false_eq_true,if_false] using ih

theorem ReturnPinCtx.of_symbols (I : LinkInput) (R : Res) :
    (ReturnPinCtx.of I R).symbols = fun n => I.syms.lookup n := assocMap_fun I.syms

theorem ReturnPinCtx.of_artifact (I : LinkInput) (R : Res) :
    (ReturnPinCtx.of I R).artifact = artOf R := funext (returnPinArtMap_get R)

theorem ReturnPinCtx.of_entries (I : LinkInput) (R : Res) :
    (ReturnPinCtx.of I R).entries = (progOf R).funcs.map (ReturnPinEntry.of (artOf R)) := by
  simp only [ReturnPinCtx.of,show (fun g : Clif.Function =>
    ((returnPinArtMap R)[g.name]?).getD default) = artOf R from funext (returnPinArtMap_get R)]

theorem ReturnPinCtx.of_direct (I : LinkInput) (R : Res) (n : String) :
    (ReturnPinCtx.of I R).direct n = ((progOf R).func? n).map (ReturnPinEntry.of (artOf R)) := by
  change (assocMap (((progOf R).funcs.map (ReturnPinEntry.of _)).map _))[n]? = _
  rw [assocMap_get,entryLookup]
  rw [show (fun g : Clif.Function => ((returnPinArtMap R)[g.name]?).getD default) = artOf R
    from funext (returnPinArtMap_get R)]
  rfl

/-- Reuse the cached target data at every actual call and try-call. -/
def returnPinSiteWith (C : ReturnPinCtx) (g : Clif.Function) (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match C.direct n with
    | some e => e.check info.defs
    | none => true
  | .reg (.vreg t .int) =>
    let got := gotOf (C.artifact g).vcp t
    C.entries.all fun e =>
      !indToB C.symbols g e.function ||
      (match got with | some n => e.function.name != n | none => false) ||
      decide (e.arity ≠ info.uses.length) || e.check info.defs
  | _ => true

/-- The cache changes no direct, indirect, GOT, or arity decision. -/
theorem returnPinSiteWith_of (I : LinkInput) (R : Res) (g : Clif.Function) (info : CallInfo) :
    returnPinSiteWith (ReturnPinCtx.of I R) g info =
      (ofRes I R closedBase (fun _ => False)).returnPinSiteB g info := by
  unfold returnPinSiteWith LinkSys.returnPinSiteB
  cases info.dest with
  | sym n =>
    simp only
    rw [ReturnPinCtx.of_direct]
    simp only [ofRes]
    cases (progOf R).func? n <;> rfl
  | reg r =>
    cases r <;> try rfl
    rename_i t cls
    cases cls <;> try rfl
    rw [ReturnPinCtx.of_entries,ReturnPinCtx.of_symbols,ReturnPinCtx.of_artifact]
    simp only [List.all_map,Function.comp_def,ReturnPinEntry.of,ReturnPinEntry.check,
      ReturnPinCheck.check,ofRes]
    rfl

/-- The complete scanner reuses one context for the entire program. -/
def returnPinsWith (C : ReturnPinCtx) (g : Clif.Function) : Bool :=
  allInsts (C.artifact g).vcp (siteB (returnPinSiteWith C g))

theorem returnPinsWith_of (I : LinkInput) (R : Res) (g : Clif.Function) :
    returnPinsWith (ReturnPinCtx.of I R) g =
      (ofRes I R closedBase (fun _ => False)).returnPinsB g := by
  unfold returnPinsWith LinkSys.returnPinsB
  rw [ReturnPinCtx.of_artifact,show returnPinSiteWith (ReturnPinCtx.of I R) g =
    (ofRes I R closedBase (fun _ => False)).returnPinSiteB g from
      funext (returnPinSiteWith_of I R g)]
  rfl

end E2E.LinkCheck

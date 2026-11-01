import FV.Backend.Proof.StockEligibilitySinkTarget
import FV.Backend.Proof.StockSinkFrame

namespace Backend.Stock.Proof.SinkRules
open Backend.Proof Isle Isle.Interp Isle.Aarch64 Isle.Interp.RuleFrame
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- Every generated interpreter rule preserves a result-less non-load slot.
Loads and their actual sinking remain permitted at other source positions. -/
theorem protected_slot_frames {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {slot : Nat}
    (safe : NoLoadAt ctx slot) (empty : ctx.insts[slot]!.results = []) :
    ∀ n, CtorFreeAt program (Stock.sem ctx) {} blocked
      (fun a b => b.sunk[slot]! = a.sunk[slot]!) n := by
  apply ctorFreeAt_inductive (p := program) (sem := Stock.sem ctx)
    (cfg := {}) (blocked := blocked) (R := fun a b => b.sunk[slot]! = a.sunk[slot]!)
    (fun _ => rfl) (fun _ _ _ first second => second.trans first)
    (special := Exceptional)
  · intro term vs st value next free run
    exact congrArg (fun bits => bits[slot]!) (stock_ctor_noSink (by simpa [blocked] using free) run)
  · rfl
  · intro t rule member
    exact rule_cases member
  · intro n frames rule special m vs env st tr matched trm out next tr' matchedRun rhsRun
    rcases special with rfl | rfl | rfl | rfl
    · exact pattern_sink_rule_frame safe frames true matchedRun rhsRun
    · exact pattern_sink_rule_frame safe frames false matchedRun rhsRun
    · exact eligibility_sink_rule_frame mapped empty frames false matchedRun rhsRun
    · exact eligibility_sink_rule_frame mapped empty frames true matchedRun rhsRun

/-- Actual helper evaluation preserves the protected slot, including absent results. -/
theorem protected_slot_apply {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {slot : Nat}
    (safe : NoLoadAt ctx slot) (empty : ctx.insts[slot]!.results = [])
    {n ty t : Nat} {vs : List V} {st next : State} {tr tr' : Array RuleId}
    {out : Option V} (notSink : termCtorFree program blocked t = true)
    (run : (applyTerm program (Stock.sem ctx) {} n ty t vs).run (st,tr) =
      .ok (out,next,tr')) : next.sunk[slot]! = st.sunk[slot]! :=
  (protected_slot_frames mapped safe empty n).apply ty t vs st tr out next tr' notSink run

private theorem named_frame {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {slot : Nat}
    (safe : NoLoadAt ctx slot) (empty : ctx.insts[slot]!.results = [])
    {name : String} {vs : List V} {st next : State} {out : Option V} {trace : List RuleId}
    (allowed : ∀ term, program.termByName? name = some term → termCtorFree program blocked term.id = true)
    (run : Stock.runTerm ctx name vs st = .ok (out,next,trace)) :
    next.sunk[slot]! = st.sunk[slot]! := by
  unfold Stock.runTerm at run
  cases executed : Isle.Interp.run program (Stock.sem ctx) {} name vs st with
  | error message => rw [executed] at run; cases run
  | ok result =>
    rw [executed] at run
    cases run
    unfold Isle.Interp.run at executed
    cases lookup : program.termByName? name with
    | none => simp only [lookup] at executed; cases executed
    | some term =>
      simp only [lookup] at executed
      cases call : (applyTerm program (Stock.sem ctx) {} (Config.fuel ({} : Config))
          term.ret term.id vs).run (st,#[]) with
      | error error => simp only [call, bind, Except.bind] at executed; cases executed
      | ok result =>
        obtain ⟨value,next,trace⟩ := result
        simp only [call, bind, Except.bind, pure, Except.pure] at executed
        cases executed
        exact protected_slot_apply mapped safe empty (allowed term lookup) call

/-- The actual statement/return helper preserves a protected source slot. -/
theorem protected_slot_lower {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {slot : Nat}
    (safe : NoLoadAt ctx slot) (empty : ctx.insts[slot]!.results = [])
    {vs : List V} {st next : State} {out : Option V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower" vs st = .ok (out,next,trace)) :
    next.sunk[slot]! = st.sunk[slot]! := by
  apply named_frame mapped safe empty (name := "lower") ?_ run
  intro term lookup
  rw [program_termByName_lower] at lookup
  cases lookup
  rw [term_guard]
  decide +kernel

/-- The actual branch helper preserves the same protected source slot. -/
theorem protected_slot_branch {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {slot : Nat}
    (safe : NoLoadAt ctx slot) (empty : ctx.insts[slot]!.results = [])
    {vs : List V} {st next : State} {out : Option V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" vs st = .ok (out,next,trace)) :
    next.sunk[slot]! = st.sunk[slot]! := by
  apply named_frame mapped safe empty (name := "lower_branch") ?_ run
  intro term lookup
  rw [program_termByName_lower_branch] at lookup
  cases lookup
  rw [term_guard]
  decide +kernel

end Backend.Stock.Proof.SinkRules

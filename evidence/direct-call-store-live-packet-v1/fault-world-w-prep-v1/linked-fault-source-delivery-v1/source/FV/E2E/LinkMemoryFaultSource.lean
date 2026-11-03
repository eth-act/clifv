import FV.E2E.MemoryFaultCallersTransport

namespace E2E.MemoryFaultSource
open Clif
set_option autoImplicit false
set_option Elab.async false

/-- Full-source mapping transfers to every continuing linked source state. -/
theorem runLoop_linkR_mapFaults {P : Program} {base : Env} {f : Function} {syms : String → Option Nat}
    (R : State → Outcome) (F : Nat) (s0 : State) (hnd : (P.funcs.map (·.name)).Nodup)
    (hf : f ∈ P.funcs)
    (hP : ∀ g ∈ P.funcs, LinkFree g) (hio : ¬ IndFree f → IndScope P base syms) {E : Env}
    (hEn : E.names = (linkEnvR P base R).names) (hEs : E.sigOf = (linkEnvR P base R).sigOf)
    (hEb : ∀ n, P.func? n = none → E.extern n = (linkEnvR P base R).extern n)
    (hEp : ∀ h ∈ P.funcs, (h.name ∈ f.externs.map (·.2.name) ∨
      (syms h.name ≠ none ∧ ∃ d, IndSig f d ∧ d.abiMatch h.sig = true)) →
      E.extern h.name = (linkEnvR P base R).extern h.name)
    (hR : ∀ (t0 : State) (K : List (Frame × List ValueId)) (n : Nat), K ≠ [] →
      Reaches base P s0 (t0.below K) → n ≤ F → (∀ msg, runLoop base P n t0 ≠ .stuck msg) →
      runLoop base P n t0 ≠ .outOfFuel → R t0 = runLoop base P n t0)
    {mp : ArmFault.MemMap} (mapped : MapFaults mp base P s0) :
    ∀ (N : Nat) (s : State), N ≤ F + 1 → Reaches base P s0 s → LInv P s → LInv (P.only f) s →
      (¬ IndFree f → s.mem.symbols = syms) →
      (∀ msg, runLoop base P N s ≠ .stuck msg) → runLoop base P N s ≠ .outOfFuel →
      ∃ m, runLoop E P.bare m s = runLoop base P N s ∧
      MapFaults mp E P.bare s := by
  intro N s within reached invariant only symbols notStuck notFuel
  obtain ⟨m,linked,lifted⟩ := Clif.runLoop_linkR_reaches R F s0 hnd hf hP hio hEn hEs hEb hEp hR
    N s within reached invariant only symbols notStuck notFuel
  refine ⟨m,linked,?_⟩
  apply mapFaults_of_reach_simulation mapped
  intro target path
  exact ⟨target,reach_of_reaches (lifted target (reaches_of_reach path)),rfl,rfl⟩

/-- A real full-program call step supplies the reached callee mapping fact.
The step retains the actual callee memory and all original caller frames. -/
theorem mapFaults_at_linked_callee {mp : ArmFault.MemMap}
    {base linked : Clif.Env} {program : Clif.Program} {initial entry caller callee : Clif.State}
    {callers : List (Clif.Frame × List Clif.ValueId)}
    (mapped : MapFaults mp base program initial)
    (lifted : ∀ target, Clif.Reaches linked program.bare entry target →
      Clif.Reaches base program initial target)
    (before : Clif.Reaches linked program.bare entry caller)
    (entered : Clif.step base program caller = .next (callee.below callers)) :
    MapFaults mp base program callee :=
  mapFaults_at_callee mapped (reach_of_reaches ((lifted caller before).snoc entered))

/-- The common call-entry rule derives mapping for the actual entered memory.
Direct, indirect, and try-call paths use this same successful entry rule. -/
theorem mapFaults_at_linked_enterFunc {mp : ArmFault.MemMap}
    {base linked : Clif.Env} {program : Clif.Program} {initial entry caller state : Clif.State}
    {rest : List Clif.Stmt} {results : List Clif.ValueId} {callee : Clif.Function}
    {values : List Clif.Val} {frame : Clif.Frame} {memory : Clif.Mem}
    (mapped : MapFaults mp base program initial)
    (lifted : ∀ target, Clif.Reaches linked program.bare entry target →
      Clif.Reaches base program initial target)
    (before : Clif.Reaches linked program.bare entry caller)
    (stepped : Clif.step base program caller =
      Clif.StepResult.ofRes (Clif.enterFunc callee values state.mem) fun (fr,mem) =>
        .next ⟨fr,({state.frame with body := rest},results) :: state.callers,mem⟩)
    (entered : Clif.enterFunc callee values state.mem = .ok (frame,memory)) :
    MapFaults mp base program ⟨frame,[],memory⟩ := by
  apply mapFaults_at_linked_callee mapped lifted before
  rw [stepped,entered]
  rfl

/-- A direct source call derives its entry step from the actual lookup and ABI check. -/
theorem mapFaults_at_linked_callCont {mp : ArmFault.MemMap}
    {base linked : Clif.Env} {program : Clif.Program} {initial entry caller state : Clif.State}
    {rest : List Clif.Stmt} {results : List Clif.ValueId} {callee : Clif.Function}
    {ext : Clif.ExtFunc} {values : List Clif.Val} {frame : Clif.Frame} {memory : Clif.Mem}
    (mapped : MapFaults mp base program initial)
    (lifted : ∀ target, Clif.Reaches linked program.bare entry target →
      Clif.Reaches base program initial target)
    (before : Clif.Reaches linked program.bare entry caller)
    (stepped : Clif.step base program caller = Opt.callCont base program state rest results ext values)
    (found : program.func? ext.name = some callee)
    (signature : (Clif.AbiParam.tys callee.sig.params == Clif.AbiParam.tys ext.sig.params &&
      Clif.AbiParam.tys callee.sig.returns == Clif.AbiParam.tys ext.sig.returns) = true)
    (entered : Clif.enterFunc callee values state.mem = .ok (frame,memory)) :
    MapFaults mp base program ⟨frame,[],memory⟩ := by
  apply mapFaults_at_linked_enterFunc (state := state) (rest := rest) (results := results)
    (callee := callee) mapped lifted before ?_ entered
  simpa only [Opt.callCont,found,signature,↓reduceIte] using stepped

/-- An indirect source call derives its entry step from the actual symbol and ABI checks. -/
theorem mapFaults_at_linked_indCont {mp : ArmFault.MemMap}
    {base linked : Clif.Env} {program : Clif.Program} {initial entry caller state : Clif.State}
    {rest : List Clif.Stmt} {results : List Clif.ValueId} {callee : Clif.Function}
    {sig address : Nat} {declared : Clif.Signature} {values : List Clif.Val}
    {frame : Clif.Frame} {memory : Clif.Mem}
    (mapped : MapFaults mp base program initial)
    (lifted : ∀ target, Clif.Reaches linked program.bare entry target →
      Clif.Reaches base program initial target)
    (before : Clif.Reaches linked program.bare entry caller)
    (stepped : Clif.step base program caller =
      Clif.indCont base program state rest results sig declared address values)
    (found : (program.funcs.find? fun f => state.mem.symbols f.name == some address) = some callee)
    (signature : declared.abiMatch callee.sig = true)
    (entered : Clif.enterFunc callee values state.mem = .ok (frame,memory)) :
    MapFaults mp base program ⟨frame,[],memory⟩ := by
  apply mapFaults_at_linked_enterFunc (state := state) (rest := rest) (results := results)
    (callee := callee) mapped lifted before ?_ entered
  simpa only [Clif.indCont,found,signature,↓reduceIte] using stepped

end E2E.MemoryFaultSource

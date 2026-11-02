import FV.Backend.Proof.StockRootFlow
import FV.Backend.Proof.StockResults
import FV.Backend.Proof.StockAliasWrites

/-! Result binding preserves source-provenance relations on actual alias entries. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 4096
attribute [local irreducible] Isle.Aarch64.program

private theorem fold_invariant_mem {α β : Type} (P : α → Prop)
    (step : α → β → Except String α) (xs : List β)
    (keeps : ∀ a b next, b ∈ xs → P a → step a b = .ok next → P next)
    {a next : α} (bound : P a) (run : xs.foldlM step a = .ok next) : P next := by
  induction xs generalizing a with
  | nil => cases run; exact bound
  | cons x xs ih =>
    rw [List.foldlM_cons] at run
    cases call : step a x with
    | error e => simp only [call, bind, Except.bind] at run; cases run
    | ok middle =>
      simp only [call, bind, Except.bind] at run
      exact ih (fun a b next member => keeps a b next (List.mem_cons_of_mem _ member))
        (keeps a x middle (List.mem_cons_self ..) bound call) run

/-- Every alias after actual result binding was already present or comes from
an actual virtual output paired with its mapped source result. Repeated result
keys remain allowed: the relation is preserved by each ordered overwrite. -/
theorem stock_bindResults_aliasOrigins {ctx : Ctx} {pairs : List (Nat × List Reg)}
    {before after : State} {copies : Array MInst} (R : Nat → Nat → Prop)
    (mapped : ∀ x r, ctx.valueReg? x = some r → ∃ n, r = .vreg n .int)
    (outputs : ∀ x rs, (x, rs) ∈ pairs → ∀ (key target : Nat),
      ctx.valueReg? x = some (.vreg key .int) → rs = [.vreg target .int] → R key target)
    (run : bindResults ctx pairs before = .ok (after, copies)) :
    after.base = before.base ∧ ∀ (key target : Nat), (after.alias[key]?).join = some target →
      (before.alias[key]?).join = some target ∨ R key target := by
  unfold bindResults at run
  apply fold_invariant_mem (fun acc : State × Array MInst =>
    acc.1.base = before.base ∧ ∀ (key target : Nat), (acc.1.alias[key]?).join = some target →
      (before.alias[key]?).join = some target ∨ R key target) _ pairs ?_ ?_ run
  · intro acc pair next member old step
    rcases acc with ⟨s, code⟩
    rcases pair with ⟨x, rs⟩
    dsimp only at step
    cases hm : ctx.valueReg? x with
    | none => simp only [hm] at step; cases step
    | some r =>
      simp only [hm] at step
      split at step
      · rename_i tail n cls
        cases alias : s.setAlias r (.vreg n cls) with
        | error e => simp only [alias, bind, Except.bind] at step; cases step
        | ok q =>
          simp only [alias, bind, Except.bind, pure, Except.pure] at step
          cases step
          obtain ⟨k, rfl⟩ := mapped x r hm
          cases cls with
          | float => simp [State.setAlias, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at alias
          | int =>
            rw [setAlias_virtual] at alias
            cases alias
            refine ⟨old.1, ?_⟩
            intro key target entry
            rw [aliasStep_get] at entry
            by_cases same : key = k
            · subst key
              simp only [ite_true, Option.some.injEq] at entry
              subst target
              exact .inr (outputs x [.vreg n .int] member k n hm rfl)
            · simp only [same, ite_false] at entry
              exact old.2 key target entry
      · cases step; exact old
      · cases step
  · exact ⟨rfl, fun _ _ h => .inl h⟩

private theorem zip_right {α β : Type} (xs : List α) (ys : List β) {x : α} {y : β}
    (member : (x, y) ∈ xs.zip ys) : y ∈ ys := by
  induction xs generalizing ys with
  | nil => cases member
  | cons a xs ih =>
    cases ys with
    | nil => cases member
    | cons b ys =>
      simp only [List.zip_cons_cons, List.mem_cons] at member
      rcases member with same | member
      · cases same; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih ys member)

private theorem built_empty {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (built : Stock.buildCtx f = .ok (ctx, ranges, initial)) : ctx.tryRegs = ([], []) := by
  obtain ⟨original, st0, requests, old, _, he⟩ := buildCtx_allocation built
  have h := congrArg (fun q => q.1) he
  dsimp only at h
  rw [h]
  exact (ctxSpec_of old).facts.tryRegs

private theorem root_bound_aliasOrigins {f : Clif.Function} (scope : LowerScope f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (built : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (nonempty : info.results ≠ []) {fuel : Nat} {before root bound : State}
    {rss : List (List Reg)} {trace finalTrace : Array RuleId} {copies : Array MInst}
    (run : (applyTerm program (Stock.sem ctx) {} fuel T.lower.ret T.lower.id [.inst ii]).run
      (before, trace) = .ok (some (.regsVec rss), root, finalTrace))
    (binding : bindResults ctx (info.results.zip rss) root = .ok (bound, copies)) :
    bound.base = root.base ∧ ∀ (key target : Nat), (bound.alias[key]?).join = some target →
      (before.alias[key]?).join = some target ∨
      (before.base.nextVreg ≤ target ∧ target < bound.base.nextVreg) ∨
        ∃ x, Prov ctx ii x ∧ ctx.valueReg? x = some (.vreg target .int) := by
  have mapped := buildCtx_mappedInv scope built
  have outputFlow := MappedFlow.stock_root_mapped_flow scope built hi hc run rss rfl nonempty
  have origins := stock_bindResults_aliasOrigins
    (fun _ target => (before.base.nextVreg ≤ target ∧ target < root.base.nextVreg) ∨
      ∃ x, Prov ctx ii x ∧ ctx.valueReg? x = some (.vreg target .int))
    mapped.valueReg (fun x rs member key target _ equal =>
      outputFlow rs (zip_right info.results rss member) target .int equal) binding
  refine ⟨origins.1, ?_⟩
  intro key target entry
  rcases origins.2 key target entry with old | output
  · left
    have unchanged := stock_apply_aliasEntry (key := key) (by
      intro r member c
      rw [built_empty built] at member
      cases member) run
    exact unchanged.symm.trans old
  · right
    simpa only [origins.1] using output

private theorem lower_apply {ctx : Ctx} {ii : Nat} {before after : State}
    {rss : List (List Reg)} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower" [.inst ii] before =
      .ok (some (.regsVec rss), after, trace)) :
    ∃ finalTrace, (applyTerm program (Stock.sem ctx) {} 1000000 T.lower.ret T.lower.id
      [.inst ii]).run (before, #[]) = .ok (some (.regsVec rss), after, finalTrace) := by
  unfold Stock.runTerm Interp.run at run
  rw [program_termByName_lower] at run
  dsimp only at run
  cases applied : (applyTerm program (Stock.sem ctx) {} 1000000 T.lower.ret T.lower.id
      [.inst ii]).run (before, #[]) with
  | error e => simp only [applied, bind, Except.bind] at run; cases run
  | ok result =>
    rcases result with ⟨out, next, fired⟩
    simp only [applied, bind, Except.bind, pure, Except.pure] at run
    cases run
    exact ⟨fired, rfl⟩

/-- Every alias after actual instruction emission is unchanged or targets a
fresh register of that root or a mapped source value in its operand provenance.
The emitter's result binder supplies the alias edge; no edge-origin premise is
required from the caller. -/
theorem stock_emitInstruction_aliasOrigins {f : Clif.Function} (scope : LowerScope f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (built : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (nonempty : info.results ≠ []) {before : State} {emission : Emission}
    (emitted : emitInstruction ctx ii before = .ok emission) :
    ∀ (key target : Nat), (emission.state.alias[key]?).join = some target →
      (before.alias[key]?).join = some target ∨
      (before.base.nextVreg ≤ target ∧ target < emission.state.base.nextVreg) ∨
        ∃ x, Prov ctx ii x ∧ ctx.valueReg? x = some (.vreg target .int) := by
  have infoEq : ctx.insts[ii]! = info := by simp only [getElem!_def, hi]
  unfold emitInstruction at emitted
  rw [infoEq] at emitted
  cases root : Stock.runTerm ctx "lower" [.inst ii] before with
  | error e => simp only [root, bind, Except.bind] at emitted; cases emitted
  | ok result =>
    rcases result with ⟨out, next, fired⟩
    simp only [root, bind, Except.bind] at emitted
    cases out with
    | none => cases emitted
    | some out =>
      cases out <;> try (cases emitted)
      rename_i rss
      dsimp only at emitted
      split at emitted
      · cases emitted
      · cases bound : bindResults ctx (info.results.zip rss) next with
        | error e => simp only [bound] at emitted; cases emitted
        | ok result =>
          rcases result with ⟨after, copies⟩
          simp only [bound, pure, Except.pure] at emitted
          cases emitted
          obtain ⟨finalTrace, applied⟩ := lower_apply root
          exact (root_bound_aliasOrigins scope built hi hc nonempty applied bound).2

private def bindingWitnessCtx : Ctx := { sinkCtx with valReg := #[some (.vreg 192 .int)] }

theorem stock_bindResults_aliasOrigins_witness :
    ∃ after copies, bindResults bindingWitnessCtx [(0, [.vreg 194 .int])] sinkState =
      .ok (after, copies) ∧ after.base = sinkState.base ∧
      (after.alias[192]?).join = some 194 ∧
      ∀ (key target : Nat), (after.alias[key]?).join = some target →
        (sinkState.alias[key]?).join = some target ∨ (key = 192 ∧ target = 194) := by
  have mapped : ∀ x r, bindingWitnessCtx.valueReg? x = some r → ∃ n, r = .vreg n .int := by
    intro x r lookup
    cases x with
    | zero => cases lookup; exact ⟨192, rfl⟩
    | succ n => simp [bindingWitnessCtx, Ctx.valueReg?] at lookup
  have binding := bindResults_virtual bindingWitnessCtx sinkState [(0, 192, 194)] (by
    intro pair member
    have same := List.mem_singleton.mp member
    subst pair
    rfl)
  have origins := stock_bindResults_aliasOrigins (fun key target => key = 192 ∧ target = 194)
    mapped (by
      intro x rs member key target map regs
      have same := List.mem_singleton.mp member
      cases same
      cases map
      cases regs
      exact ⟨rfl, rfl⟩) binding
  refine ⟨_, _, binding, origins.1, ?_, origins.2⟩
  simpa only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    Prod.fst, Prod.snd, ite_true] using aliasStep_get sinkState.alias (192, 194) 192

/-- A successful generated constant root and its actual emitter install193→194,
while source result2 retains dense mapping193. Every construction, source and
emission premise of alias-origin transfer is inhabited. -/
theorem stock_emitInstruction_aliasOrigins_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial : State)
      (info : IInfo) (emission : Emission),
      LowerScope f ∧ Stock.buildCtx f = .ok (ctx, ranges, initial) ∧
      ctx.insts[0]? = some info ∧ info.clif = some (.iconst .i8 9) ∧ info.results = [2] ∧
      ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      emitInstruction ctx 0 sinkState = .ok emission ∧
      (emission.state.alias[193]?).join = some 194 ∧
      ∀ (key target : Nat), (emission.state.alias[key]?).join = some target →
        (sinkState.alias[key]?).join = some target ∨
        (sinkState.base.nextVreg ≤ target ∧ target < emission.state.base.nextVreg) ∨
          ∃ x, Prov ctx 0 x ∧ ctx.valueReg? x = some (.vreg target .int) := by
  obtain ⟨f, ctx, ranges, initial, info, next, trace, scope, built, hi, hc, results, mapped, applied⟩ :=
    stock_statement_selectedConstant_built_witness
  have root : Stock.runTerm ctx "lower" [.inst 0] sinkState =
      .ok (some (.regsVec [[.vreg 194 .int]]), next, (trace.push 582).toList) := by
    unfold Stock.runTerm Interp.run
    rw [program_termByName_lower]
    dsimp only
    rw [applied]
    rfl
  let bound : State := { next with alias := aliasStep next.alias (193, 194) }
  have binding : bindResults ctx [(2, [.vreg 194 .int])] next = .ok (bound, #[]) := by
    have virtual := bindResults_virtual ctx next [(2, 193, 194)] (by
      intro p member
      have same := List.mem_singleton.mp member
      subst p
      exact mapped)
    simpa only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] using virtual
  let emission : Emission := ⟨bound, bound.base.emitted, [[.vreg 194 .int]], (trace.push 582).toList⟩
  have emitted : emitInstruction ctx 0 sinkState = .ok emission := by
    have infoEq : ctx.insts[0]! = info := by simp only [getElem!_def, hi]
    unfold emitInstruction
    rw [infoEq, root]
    simp only [results, bind, Except.bind, List.length_cons, List.length_nil, bne_self_eq_false,
      Bool.false_and, Bool.false_eq_true, ite_false, List.zip_cons_cons, List.zip_nil_right,
      binding, pure, Except.pure, Array.append_empty]
    rfl
  refine ⟨f, ctx, ranges, initial, info, emission, scope, built, hi, hc, results, mapped,
    emitted, ?_, stock_emitInstruction_aliasOrigins scope built hi hc (by rw [results]; simp) emitted⟩
  exact (aliasStep_get next.alias (193, 194) 193).trans (by simp)

end Backend.Stock.Proof

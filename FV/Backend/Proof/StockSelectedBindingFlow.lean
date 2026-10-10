import FV.Backend.Proof.StockReservedScanFlow
import FV.Backend.Proof.StockBindingFlow

/-! Actual selected-context emission supplies source alias origins, even with
nonempty exception reservations. Ordered binding is the real emitter's binder. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 4096
attribute [local irreducible] Isle.Aarch64.program

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

private theorem bound_sourceOrigins {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    {ti ii : Nat} (placeholder : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    (distinct : ii ≠ ti) (data : V)
    {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[ii]? = some info) (original : info.clif = some inst)
    (nonempty : info.results ≠ []) {fuel : Nat} {before root bound : State}
    {rss : List (List Reg)} {trace finalTrace : Array RuleId} {copies : Array MInst}
    (allocation : AllocationLe initial before)
    (run : (applyTerm program
      (Stock.sem { Driver.termCtx ctx ti data with tryRegs := before.tryRegs[ti]! })
      {} fuel T.lower.ret T.lower.id [.inst ii]).run (before, trace) =
        .ok (some (.regsVec rss), root, finalTrace))
    (binding : bindResults { Driver.termCtx ctx ti data with tryRegs := before.tryRegs[ti]! }
      (info.results.zip rss) root = .ok (bound, copies)) :
    bound.base = root.base ∧ ∀ x key target, ctx.valueReg? x = some (.vreg key .int) →
      (bound.alias[key]?).join = some target →
      (before.alias[key]?).join = some target ∨
      (before.base.nextVreg ≤ target ∧ target < bound.base.nextVreg) ∨
        (∃ y, Prov ctx ii y ∧ ctx.valueReg? y = some (.vreg target .int)) ∨
        ((.vreg target .int) ∈ before.tryRegs[ti]!.1 ++ before.tryRegs[ti]!.2 ∧
          target < initial.base.nextVreg ∧ ∀ y, ctx.valueReg? y ≠ some (.vreg target .int)) := by
  have mapped := buildCtx_mappedInv scope build
  have outputFlow := stock_selected_allocated_root_flow build scope placeholder distinct data source
    original allocation run rss rfl nonempty
  have origins := stock_bindResults_aliasOrigins
    (fun _ target => (before.base.nextVreg ≤ target ∧ target < root.base.nextVreg) ∨
      (∃ y, Prov ctx ii y ∧ ctx.valueReg? y = some (.vreg target .int)) ∨
      ((.vreg target .int) ∈ before.tryRegs[ti]!.1 ++ before.tryRegs[ti]!.2 ∧
        target < initial.base.nextVreg ∧ ∀ y, ctx.valueReg? y ≠ some (.vreg target .int)))
    mapped.valueReg (fun x rs member key target _ equal =>
      outputFlow rs (zip_right info.results rss member) target .int equal) binding
  refine ⟨origins.1, ?_⟩
  intro x key target map entry
  rcases origins.2 key target entry with old | output
  · left
    have unchanged := stock_apply_aliasEntry (key := key) (by
      intro r member c same
      change r ∈ before.tryRegs[ti]!.2 at member
      have all : r ∈ before.tryRegs[ti]!.1 ++ before.tryRegs[ti]!.2 :=
        List.mem_append_right _ member
      obtain ⟨n, register, _, separated⟩ := stock_reservation_slot_facts build allocation ti all
      rw [register] at same separated
      cases same
      exact separated x map) run
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

/-- The actual selected-context emitter and ordered binder supply each mapped
source alias target's origin. Existing source aliases survive root execution;
new targets are fresh, source-provenanced, or exact bounded source-disjoint reserves. -/
theorem stock_selected_emitInstruction_sourceAliasOrigins {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    {ti ii : Nat} (placeholder : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    (distinct : ii ≠ ti) (data : V)
    {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[ii]? = some info) (original : info.clif = some inst)
    (nonempty : info.results ≠ []) {before : State} {emission : Emission}
    (allocation : AllocationLe initial before)
    (emitted : emitInstruction
      { Driver.termCtx ctx ti data with tryRegs := before.tryRegs[ti]! }
      ii before = .ok emission) :
    ∀ x key target, ctx.valueReg? x = some (.vreg key .int) →
      (emission.state.alias[key]?).join = some target →
      (before.alias[key]?).join = some target ∨
      (before.base.nextVreg ≤ target ∧ target < emission.state.base.nextVreg) ∨
        (∃ y, Prov ctx ii y ∧ ctx.valueReg? y = some (.vreg target .int)) ∨
        ((.vreg target .int) ∈ before.tryRegs[ti]!.1 ++ before.tryRegs[ti]!.2 ∧
          target < initial.base.nextVreg ∧ ∀ y, ctx.valueReg? y ≠ some (.vreg target .int)) := by
  let selected : Ctx := { Driver.termCtx ctx ti data with tryRegs := before.tryRegs[ti]! }
  have infoEq : selected.insts[ii]! = info := by
    change (Driver.termCtx ctx ti data).insts[ii]! = info
    have h : (Driver.termCtx ctx ti data).insts[ii]? = some info := by
      rw [termCtx_insts_ne distinct]; exact source
    simp only [getElem!_def, h]
  change emitInstruction selected ii before = .ok emission at emitted
  unfold emitInstruction at emitted
  rw [infoEq] at emitted
  cases root : Stock.runTerm selected "lower" [.inst ii] before with
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
      · cases bound : bindResults selected (info.results.zip rss) next with
        | error e => simp only [bound] at emitted; cases emitted
        | ok result =>
          rcases result with ⟨after, copies⟩
          simp only [bound, pure, Except.pure] at emitted
          cases emitted
          obtain ⟨finalTrace, applied⟩ := lower_apply root
          exact (bound_sourceOrigins build scope placeholder distinct data source original nonempty
            allocation applied bound).2

/-- The mapped-source alternative of actual selected emission is available at
an actual source boundary. Reservations retain their exact independent classification. -/
theorem stock_selected_emitInstruction_sourceAliasAvailable {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    (dominated : Dominated f) {ti ii bi j n : Nat}
    (placeholder : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    (distinct : ii ≠ ti) (data : V)
    (available : n ∈ availOf f (availIn f ctx) bi j) (definition : ctx.defInst? n = some ii)
    {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[ii]? = some info) (original : info.clif = some inst)
    (nonempty : info.results ≠ []) {before : State} {emission : Emission}
    (allocation : AllocationLe initial before)
    (emitted : emitInstruction
      { Driver.termCtx ctx ti data with tryRegs := before.tryRegs[ti]! }
      ii before = .ok emission) :
    ∀ x key target, ctx.valueReg? x = some (.vreg key .int) →
      (emission.state.alias[key]?).join = some target →
      (before.alias[key]?).join = some target ∨
      (before.base.nextVreg ≤ target ∧ target < emission.state.base.nextVreg) ∨
        (∃ y, y ∈ availOf f (availIn f ctx) bi j ∧ ctx.valueReg? y = some (.vreg target .int)) ∨
        ((.vreg target .int) ∈ before.tryRegs[ti]!.1 ++ before.tryRegs[ti]!.2 ∧
          target < initial.base.nextVreg ∧ ∀ y, ctx.valueReg? y ≠ some (.vreg target .int)) := by
  intro x key target map entry
  rcases stock_selected_emitInstruction_sourceAliasOrigins build scope placeholder distinct data source
      original nonempty allocation emitted x key target map entry with old | fresh | mapped | reserved
  · exact .inl old
  · exact .inr (.inl fresh)
  · obtain ⟨y, reached, register⟩ := mapped
    exact .inr (.inr (.inl ⟨y,
      stock_available_provenance build dominated available definition reached, register⟩))
  · exact .inr (.inr (.inr reserved))

attribute [local semireducible] Isle.Aarch64.program

private def bindingSignature : Clif.Signature := {
  returns := [⟨.i8, .none, .normal⟩], callConv := some .systemV }
private def bindingTable : Clif.ExnTable := {
  sig := 0, normal := ⟨1, [.ret 0, .val 0]⟩ }
private def bindingFunction : Clif.Function := {
  name := "allocated_selected_root"
  sig := bindingSignature
  sigDecls := [(0, bindingSignature)]
  externs := [(0, { name := "callee", sig := bindingSignature })]
  blocks := [
    { id := 0, params := [], body := [⟨[0], .iconst .i8 9⟩], term := .tryCall 0 [] bindingTable },
    { id := 1, params := [(1, .i8), (2, .i8)], body := [], term := .ret [2] }] }
private def bindingBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx bindingFunction).toOption.getD (sinkCtx, #[], sinkState)
private def bindingData : V :=
  (Backend.tryCallData bindingFunction (.tryCall 0 [] bindingTable)).toOption.getD (.op .unit)
private def bindingCtx : Ctx :=
  { Driver.termCtx bindingBuilt.1 1 bindingData with tryRegs := bindingBuilt.2.2.tryRegs[1]! }
private theorem binding_build : Stock.buildCtx bindingFunction = .ok bindingBuilt := rfl
private theorem binding_scope : LowerScope bindingFunction := lowerScope_of (by decide +kernel)
private def bindingOriginal : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx bindingFunction).toOption.getD (sinkCtx, #[], sinkState.base)
private theorem binding_original_build : Backend.buildCtx bindingFunction = .ok bindingOriginal := rfl
private theorem binding_original_defs : bindingOriginal.1.valDef = #[some 0, none, none] := rfl
private theorem binding_original_args (x : Nat) : defArgs bindingOriginal.1 x = [] := by
  rcases x with _ | (_ | (_ | x)) <;>
    simp [defArgs, Ctx.defInst?, binding_original_defs]
  rfl
private theorem binding_dominated : Dominated bindingFunction := by
  constructor
  · decide +kernel
  · intro ctx ranges st build bi B block
    rcases bi with _ | (_ | bi)
    · simp [bindingFunction] at block
      subst B
      constructor
      · intro j stmt lookup y member
        cases j with
        | zero => simp at lookup; subst stmt; simp [Backend.Proof.Driver.instArgs] at member
        | succ j => simp at lookup
      · intro y member
        change y ∈ [0] at member
        simp only [List.mem_singleton] at member
        subst y
        change 0 ∈ ((availIn bindingFunction ctx).getD 0 [] ++ [0]).filter
          (fun x => decide (x ∉ ([] : List Nat)))
        simp
    · simp [bindingFunction] at block
      subst B
      constructor
      · intro j stmt lookup; simp at lookup
      · intro y member
        change y ∈ [2] at member
        simp only [List.mem_singleton] at member
        subst y
        change 2 ∈ ([1, 2] ++ (availIn bindingFunction ctx).getD 1 [] ++ []).filter
          (fun x => decide (x ∉ ([] : List Nat)))
        simp
    · simp [bindingFunction] at block
  · intro ctx ranges st build tl x available notLocal y member
    rw [binding_original_build] at build
    cases build
    change y ∈ defArgs bindingOriginal.1 x at member
    rw [binding_original_args] at member
    cases member
private theorem binding_allocation : AllocationLe bindingBuilt.2.2 bindingBuilt.2.2 :=
  ⟨Nat.le_refl _, rfl⟩
private theorem binding_available :
    (0 : Nat) ∈ availOf bindingFunction (availIn bindingFunction bindingBuilt.1) 0 1 := by
  change 0 ∈ ((availIn bindingFunction bindingBuilt.1).getD 0 [] ++ [0]).filter
    (fun x => decide (x ∉ ([] : List Nat)))
  simp


/-- The actual emitter runs generated lowering from the successfully allocated
try-call state and binds source192→fresh198 with nonempty reservations193/194/195. -/
theorem stock_selected_emitInstruction_sourceAliasOrigins_witness :
    ∃ emission : Emission,
      Stock.buildCtx bindingFunction = .ok bindingBuilt ∧ LowerScope bindingFunction ∧
      AllocationLe bindingBuilt.2.2 bindingBuilt.2.2 ∧
      Backend.tryCallData bindingFunction (.tryCall 0 [] bindingTable) = .ok bindingData ∧
      bindingCtx.tryRegs.2 ≠ [] ∧ emitInstruction bindingCtx 0 bindingBuilt.2.2 = .ok emission ∧
      (emission.state.alias[192]?).join = some 198 ∧
      ∀ x key target, bindingBuilt.1.valueReg? x = some (.vreg key .int) →
        (emission.state.alias[key]?).join = some target →
        (bindingBuilt.2.2.alias[key]?).join = some target ∨
        (bindingBuilt.2.2.base.nextVreg ≤ target ∧ target < emission.state.base.nextVreg) ∨
          (∃ y, Prov bindingBuilt.1 0 y ∧ bindingBuilt.1.valueReg? y = some (.vreg target .int)) ∨
          ((.vreg target .int) ∈ bindingBuilt.2.2.tryRegs[1]!.1 ++ bindingBuilt.2.2.tryRegs[1]!.2 ∧
            target < bindingBuilt.2.2.base.nextVreg ∧
              ∀ y, bindingBuilt.1.valueReg? y ≠ some (.vreg target .int)) := by
  obtain ⟨next, trace, applied⟩ := stock_statement_selectedConstant_context bindingCtx
    (fun _ => rfl) bindingBuilt.2.2
  have root : Stock.runTerm bindingCtx "lower" [.inst 0] bindingBuilt.2.2 =
      .ok (some (.regsVec [[.vreg 198 .int]]), next, (trace.push 582).toList) := by
    unfold Stock.runTerm Interp.run
    rw [program_termByName_lower]
    dsimp only
    rw [applied]
    rfl
  let bound : State := { next with alias := aliasStep next.alias (192, 198) }
  have binding : bindResults bindingCtx [(0, [.vreg 198 .int])] next = .ok (bound, #[]) := by
    have virtual := bindResults_virtual bindingCtx next [(0, 192, 198)] (by
      intro p member
      have same := List.mem_singleton.mp member
      subst p
      rfl)
    simpa only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] using virtual
  let emission : Emission := ⟨bound, bound.base.emitted, [[.vreg 198 .int]], (trace.push 582).toList⟩
  have emitted : emitInstruction bindingCtx 0 bindingBuilt.2.2 = .ok emission := by
    have result : bindingCtx.insts[0]!.results = [0] := rfl
    unfold emitInstruction
    rw [root]
    simp only [result, bind, Except.bind, List.length_cons, List.length_nil, bne_self_eq_false,
      Bool.false_and, Bool.false_eq_true, ite_false, List.zip_cons_cons, List.zip_nil_right,
      binding, pure, Except.pure, Array.append_empty]
    rfl
  refine ⟨emission, binding_build, binding_scope, binding_allocation, rfl, (by decide), emitted, ?_, ?_⟩
  · exact (aliasStep_get next.alias (192, 198) 192).trans (by simp)
  · exact stock_selected_emitInstruction_sourceAliasOrigins binding_build binding_scope (by rfl)
      (by decide) bindingData (by rfl) (by rfl) (by decide) binding_allocation emitted

/-- Actual selected emission and its new source alias inhabit the availability
classification at source0's post-body boundary with the real nonempty allocator slot. -/
theorem stock_selected_emitInstruction_sourceAliasAvailable_witness :
    ∃ emission : Emission,
      Stock.buildCtx bindingFunction = .ok bindingBuilt ∧ LowerScope bindingFunction ∧
      Dominated bindingFunction ∧ AllocationLe bindingBuilt.2.2 bindingBuilt.2.2 ∧
      bindingCtx.tryRegs.2 ≠ [] ∧
      (0 : Nat) ∈ availOf bindingFunction (availIn bindingFunction bindingBuilt.1) 0 1 ∧
      bindingBuilt.1.defInst? 0 = some 0 ∧
      emitInstruction bindingCtx 0 bindingBuilt.2.2 = .ok emission ∧
      (emission.state.alias[192]?).join = some 198 ∧
      ∀ x key target, bindingBuilt.1.valueReg? x = some (.vreg key .int) →
        (emission.state.alias[key]?).join = some target →
        (bindingBuilt.2.2.alias[key]?).join = some target ∨
        (bindingBuilt.2.2.base.nextVreg ≤ target ∧ target < emission.state.base.nextVreg) ∨
          (∃ y, y ∈ availOf bindingFunction (availIn bindingFunction bindingBuilt.1) 0 1 ∧
            bindingBuilt.1.valueReg? y = some (.vreg target .int)) ∨
          ((.vreg target .int) ∈ bindingBuilt.2.2.tryRegs[1]!.1 ++ bindingBuilt.2.2.tryRegs[1]!.2 ∧
            target < bindingBuilt.2.2.base.nextVreg ∧
              ∀ y, bindingBuilt.1.valueReg? y ≠ some (.vreg target .int)) := by
  obtain ⟨emission, _, _, _, _, nonempty, emitted, alias, _⟩ :=
    stock_selected_emitInstruction_sourceAliasOrigins_witness
  refine ⟨emission, binding_build, binding_scope, binding_dominated, binding_allocation,
    nonempty, binding_available, rfl, emitted, alias, ?_⟩
  exact stock_selected_emitInstruction_sourceAliasAvailable binding_build binding_scope binding_dominated
    (by rfl) (by decide) bindingData binding_available (by rfl) (by rfl) (by rfl) (by decide)
    binding_allocation emitted

end Backend.Stock.Proof

import FV.Backend.Proof.StockSelectedFlow
import FV.Backend.Proof.StockAliasWrites
import FV.Backend.Proof.StockAllocationFlow
import FV.Backend.Proof.LowerDecide

/-! Selected root outputs at the real preallocated exception slot. Bounds and
source-register separation are derived from successful stock allocation. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 4096

/-- The slot selected by the driver remains preallocated as the actual state
advances: its registers are below the initial frontier and separate from every
source mapping. An absent slot contributes no registers. -/
theorem stock_reservation_slot_facts {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial before : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    (allocation : AllocationLe initial before) (ti : Nat) {r : Reg}
    (member : r ∈ before.tryRegs[ti]!.1 ++ before.tryRegs[ti]!.2) :
    ∃ n, r = .vreg n .int ∧ n < initial.base.nextVreg ∧
      ∀ x, ctx.valueReg? x ≠ some r := by
  cases slot : before.tryRegs[ti]? with
  | none =>
    simp only [getElem!_def, slot] at member
    change r ∈ ([] : List Reg) ++ [] at member
    simp at member
  | some rs =>
    have membership : r ∈ rs.1 ++ rs.2 := by
      simpa only [getElem!_def, slot, Option.getD_some] using member
    rw [allocation.2] at slot
    obtain ⟨n, register, below⟩ := buildCtx_reservedBelow build ti rs slot r membership
    refine ⟨n, register, below, ?_⟩
    intro x mapped
    exact buildCtx_valueReservedDisjoint build x r mapped ti rs slot r membership rfl

private theorem reserved_origin {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial before : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    (allocation : AllocationLe initial before) {ti o : Nat} {cls : RegClass}
    (member : (.vreg o cls) ∈ before.tryRegs[ti]!.1 ++ before.tryRegs[ti]!.2) :
    o < initial.base.nextVreg ∧ ∀ x, ctx.valueReg? x ≠ some (.vreg o cls) := by
  obtain ⟨n, register, below, separated⟩ := stock_reservation_slot_facts build allocation ti member
  cases register
  exact ⟨below, separated⟩

/-- Actual generated root execution in the driver's selected slot produces a
fresh register, a mapped source operand, or an exact preallocated reservation.
The reserved alternative is bounded and cannot be a source register. -/
theorem stock_selected_allocated_root_flow {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    {ti ii : Nat} (placeholder : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    (distinct : ii ≠ ti) (data : V)
    {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[ii]? = some info) (original : info.clif = some inst)
    {fuel : Nat} {before after : State} {out : V} {trace finalTrace : Array RuleId}
    (allocation : AllocationLe initial before)
    (run : (applyTerm program
      (Stock.sem { Driver.termCtx ctx ti data with tryRegs := before.tryRegs[ti]! })
      {} fuel T.lower.ret T.lower.id [.inst ii]).run (before, trace) =
        .ok (some out, (after, finalTrace))) :
    ∀ rss, out = .regsVec rss → info.results ≠ [] → ∀ rs ∈ rss, ∀ o cls,
      rs = [.vreg o cls] →
      (before.base.nextVreg ≤ o ∧ o < after.base.nextVreg) ∨
        (∃ x, Prov ctx ii x ∧ ctx.valueReg? x = some (.vreg o cls)) ∨
        ((.vreg o cls) ∈ before.tryRegs[ti]!.1 ++ before.tryRegs[ti]!.2 ∧
          o < initial.base.nextVreg ∧ ∀ x, ctx.valueReg? x ≠ some (.vreg o cls)) := by
  intro rss output results rs member o cls singleton
  rcases stock_selected_root_flow (buildCtx_mappedInv scope build) placeholder distinct data
      before.tryRegs[ti]! source original run rss output results rs member o cls singleton with
      fresh | mapped | ret | payload
  · exact .inl fresh
  · exact .inr (.inl mapped)
  · have reserved : (.vreg o cls) ∈ before.tryRegs[ti]!.1 ++ before.tryRegs[ti]!.2 :=
      List.mem_append_left _ ret
    exact .inr (.inr ⟨reserved, reserved_origin build allocation reserved⟩)
  · have reserved : (.vreg o cls) ∈ before.tryRegs[ti]!.1 ++ before.tryRegs[ti]!.2 :=
      List.mem_append_right _ payload
    exact .inr (.inr ⟨reserved, reserved_origin build allocation reserved⟩)

/-- At an inhabited source boundary, mapped outputs are available; exact
allocator reservations remain a separate, bounded, source-disjoint alternative. -/
theorem stock_selected_allocated_root_available {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    (dominated : Dominated f) {ti ii bi j n : Nat}
    (placeholder : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    (distinct : ii ≠ ti) (data : V)
    (available : n ∈ availOf f (availIn f ctx) bi j) (definition : ctx.defInst? n = some ii)
    {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[ii]? = some info) (original : info.clif = some inst)
    {fuel : Nat} {before after : State} {out : V} {trace finalTrace : Array RuleId}
    (allocation : AllocationLe initial before)
    (run : (applyTerm program
      (Stock.sem { Driver.termCtx ctx ti data with tryRegs := before.tryRegs[ti]! })
      {} fuel T.lower.ret T.lower.id [.inst ii]).run (before, trace) =
        .ok (some out, (after, finalTrace))) :
    ∀ rss, out = .regsVec rss → info.results ≠ [] → ∀ rs ∈ rss, ∀ o cls,
      rs = [.vreg o cls] →
      (before.base.nextVreg ≤ o ∧ o < after.base.nextVreg) ∨
        (∃ x, x ∈ availOf f (availIn f ctx) bi j ∧ ctx.valueReg? x = some (.vreg o cls)) ∨
        ((.vreg o cls) ∈ before.tryRegs[ti]!.1 ++ before.tryRegs[ti]!.2 ∧
          o < initial.base.nextVreg ∧ ∀ x, ctx.valueReg? x ≠ some (.vreg o cls)) := by
  intro rss output results rs member o cls singleton
  rcases stock_selected_allocated_root_flow build scope placeholder distinct data source original
      allocation run rss output results rs member o cls singleton with
      fresh | ⟨x, reached, register⟩ | reserved
  · exact .inl fresh
  · exact .inr (.inl ⟨x, stock_available_provenance build dominated available definition reached, register⟩)
  · exact .inr (.inr reserved)

private def reservedSignature : Clif.Signature := {
  returns := [⟨.i8, .none, .normal⟩], callConv := some .systemV }
private def reservedTable : Clif.ExnTable := {
  sig := 0, normal := ⟨1, [.ret 0, .val 0]⟩ }
private def reservedFunction : Clif.Function := {
  name := "allocated_selected_root"
  sig := reservedSignature
  sigDecls := [(0, reservedSignature)]
  externs := [(0, { name := "callee", sig := reservedSignature })]
  blocks := [
    { id := 0, params := [], body := [⟨[0], .iconst .i8 9⟩], term := .tryCall 0 [] reservedTable },
    { id := 1, params := [(1, .i8), (2, .i8)], body := [], term := .ret [2] }] }
private def reservedBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx reservedFunction).toOption.getD (sinkCtx, #[], sinkState)
private def reservedData : V :=
  (Backend.tryCallData reservedFunction (.tryCall 0 [] reservedTable)).toOption.getD (.op .unit)
private def reservedCtx : Ctx :=
  { Driver.termCtx reservedBuilt.1 1 reservedData with tryRegs := reservedBuilt.2.2.tryRegs[1]! }
private theorem reserved_build : Stock.buildCtx reservedFunction = .ok reservedBuilt := rfl
private theorem reserved_scope : LowerScope reservedFunction := lowerScope_of (by decide +kernel)
private def reservedOriginal : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx reservedFunction).toOption.getD (sinkCtx, #[], sinkState.base)
private theorem reserved_original_build : Backend.buildCtx reservedFunction = .ok reservedOriginal := rfl
private theorem reserved_original_defs : reservedOriginal.1.valDef = #[some 0, none, none] := rfl
private theorem reserved_original_args (x : Nat) : defArgs reservedOriginal.1 x = [] := by
  rcases x with _ | (_ | (_ | x)) <;>
    simp [defArgs, Ctx.defInst?, reserved_original_defs]
  rfl
private theorem reserved_dominated : Dominated reservedFunction := by
  constructor
  · decide +kernel
  · intro ctx ranges st build bi B block
    rcases bi with _ | (_ | bi)
    · simp [reservedFunction] at block
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
        change 0 ∈ ((availIn reservedFunction ctx).getD 0 [] ++ [0]).filter
          (fun x => decide (x ∉ ([] : List Nat)))
        simp
    · simp [reservedFunction] at block
      subst B
      constructor
      · intro j stmt lookup; simp at lookup
      · intro y member
        change y ∈ [2] at member
        simp only [List.mem_singleton] at member
        subst y
        change 2 ∈ ([1, 2] ++ (availIn reservedFunction ctx).getD 1 [] ++ []).filter
          (fun x => decide (x ∉ ([] : List Nat)))
        simp
    · simp [reservedFunction] at block
  · intro ctx ranges st build tl x available notLocal y member
    rw [reserved_original_build] at build
    cases build
    change y ∈ defArgs reservedOriginal.1 x at member
    rw [reserved_original_args] at member
    cases member
private theorem reserved_allocation : AllocationLe reservedBuilt.2.2 reservedBuilt.2.2 :=
  ⟨Nat.le_refl _, rfl⟩
private theorem reserved_available :
    (0 : Nat) ∈ availOf reservedFunction (availIn reservedFunction reservedBuilt.1) 0 1 := by
  change 0 ∈ ((availIn reservedFunction reservedBuilt.1).getD 0 [] ++ [0]).filter
    (fun x => decide (x ∉ ([] : List Nat)))
  simp

/-- Successful real try-call allocation has nonempty reservations193/194/195,
source0 maps192, and later source parameters map196/197. Its slot is genuinely
bounded and separated, including both sides of the allocation point. -/
theorem stock_reservation_slot_facts_witness :
    Stock.buildCtx reservedFunction = .ok reservedBuilt ∧
    AllocationLe reservedBuilt.2.2 reservedBuilt.2.2 ∧
    reservedBuilt.2.2.tryRegs[1]! =
      ([.vreg 193 .int], [.vreg 194 .int, .vreg 195 .int]) ∧
    reservedBuilt.2.2.base.nextVreg = 198 ∧
    reservedBuilt.1.valueReg? 0 = some (.vreg 192 .int) ∧
    reservedBuilt.1.valueReg? 2 = some (.vreg 197 .int) ∧
    (∃ n, (Reg.vreg 194 .int) = Reg.vreg n .int ∧ n < reservedBuilt.2.2.base.nextVreg ∧
      ∀ x, reservedBuilt.1.valueReg? x ≠ some (.vreg 194 .int)) := by
  refine ⟨reserved_build, reserved_allocation, rfl, rfl, rfl, rfl, ?_⟩
  exact stock_reservation_slot_facts reserved_build reserved_allocation 1 (by decide)

/-- Actual generated lowering uses the actual successful allocator state and
its nonempty terminator slot, after installing successfully extracted try-call
data. Fresh198 is distinct from mapped source0→192 and reservations193/194/195. -/
theorem stock_selected_allocated_root_flow_witness :
    ∃ (next : State) (trace : Array RuleId),
      Stock.buildCtx reservedFunction = .ok reservedBuilt ∧ LowerScope reservedFunction ∧
      AllocationLe reservedBuilt.2.2 reservedBuilt.2.2 ∧
      Backend.tryCallData reservedFunction (.tryCall 0 [] reservedTable) = .ok reservedData ∧
      reservedCtx.tryRegs.2 ≠ [] ∧
      (applyTerm program (Stock.sem reservedCtx) {} 1000000 T.lower.ret T.lower.id [.inst 0]).run
        (reservedBuilt.2.2, #[]) = .ok (some (.regsVec [[.vreg 198 .int]]), next, trace.push 582) ∧
      ((reservedBuilt.2.2.base.nextVreg ≤ 198 ∧ 198 < next.base.nextVreg) ∨
        (∃ x, Prov reservedBuilt.1 0 x ∧ reservedBuilt.1.valueReg? x = some (.vreg 198 .int)) ∨
        ((.vreg 198 .int) ∈ reservedBuilt.2.2.tryRegs[1]!.1 ++ reservedBuilt.2.2.tryRegs[1]!.2 ∧
          198 < reservedBuilt.2.2.base.nextVreg ∧
            ∀ x, reservedBuilt.1.valueReg? x ≠ some (.vreg 198 .int))) := by
  obtain ⟨next, trace, run⟩ := stock_statement_selectedConstant_context reservedCtx (fun _ => rfl)
    reservedBuilt.2.2
  refine ⟨next, trace, reserved_build, reserved_scope, reserved_allocation, rfl, (by decide), run, ?_⟩
  exact stock_selected_allocated_root_flow reserved_build reserved_scope (by rfl) (by decide)
    reservedData (by rfl) (by rfl) reserved_allocation run _ rfl (by decide)
    _ (List.mem_singleton_self _) _ _ rfl

/-- The same real nonempty allocator slot and generated root inhabit the
availability result at source0's actual post-body boundary. -/
theorem stock_selected_allocated_root_available_witness :
    ∃ (next : State) (trace : Array RuleId),
      Stock.buildCtx reservedFunction = .ok reservedBuilt ∧ LowerScope reservedFunction ∧
      Dominated reservedFunction ∧ AllocationLe reservedBuilt.2.2 reservedBuilt.2.2 ∧
      reservedCtx.tryRegs.2 ≠ [] ∧
      (0 : Nat) ∈ availOf reservedFunction (availIn reservedFunction reservedBuilt.1) 0 1 ∧
      reservedBuilt.1.defInst? 0 = some 0 ∧
      (applyTerm program (Stock.sem reservedCtx) {} 1000000 T.lower.ret T.lower.id [.inst 0]).run
        (reservedBuilt.2.2, #[]) = .ok (some (.regsVec [[.vreg 198 .int]]), next, trace.push 582) ∧
      ((reservedBuilt.2.2.base.nextVreg ≤ 198 ∧ 198 < next.base.nextVreg) ∨
        (∃ x, x ∈ availOf reservedFunction (availIn reservedFunction reservedBuilt.1) 0 1 ∧
          reservedBuilt.1.valueReg? x = some (.vreg 198 .int)) ∨
        ((.vreg 198 .int) ∈ reservedBuilt.2.2.tryRegs[1]!.1 ++ reservedBuilt.2.2.tryRegs[1]!.2 ∧
          198 < reservedBuilt.2.2.base.nextVreg ∧
            ∀ x, reservedBuilt.1.valueReg? x ≠ some (.vreg 198 .int))) := by
  obtain ⟨next, trace, _, _, _, _, nonempty, run, _⟩ := stock_selected_allocated_root_flow_witness
  refine ⟨next, trace, reserved_build, reserved_scope, reserved_dominated, reserved_allocation,
    nonempty, reserved_available, rfl, run, ?_⟩
  exact stock_selected_allocated_root_available reserved_build reserved_scope reserved_dominated
    (by rfl) (by decide) reservedData reserved_available (by rfl) (by rfl) (by rfl)
    reserved_allocation run _ rfl (by decide) _ (List.mem_singleton_self _) _ _ rfl

end Backend.Stock.Proof

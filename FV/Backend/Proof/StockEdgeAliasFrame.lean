import FV.Backend.Proof.StockDriverBounds
import FV.Backend.Proof.StockDFG

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private def frame (st : State) := (st.base.nextVreg, st.tryRegs, st.alias)

private theorem forIn_frame {α β γ : Type} (field : α → γ)
    (step : β → α → Except String (ForInStep α))
    (keeps : ∀ x a b, step x a = .ok (.yield b) → field b = field a)
    (no_break : ∀ x a b, step x a ≠ .ok (.done b))
    (xs : List β) {a next : α} (h : forIn xs a step = .ok next) :
    field next = field a := by
  induction xs generalizing a with
  | nil => simp only [List.forIn_nil, pure, Except.pure] at h; cases h; rfl
  | cons x xs ih =>
    rw [List.forIn_cons] at h
    cases call : step x a with
    | error e => simp only [call, bind, Except.bind] at h; cases h
    | ok result =>
      cases result with
      | done b => exact False.elim (no_break x a b call)
      | yield b =>
        simp only [call, bind, Except.bind] at h
        exact (ih h).trans (keeps x a b call)

private def argStep (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (acc : State × Array Reg) :
    Except String (ForInStep (State × Array Reg)) := do
  match arg with
  | .val v =>
    let some r := ctx.valueReg? v | throw s!"unknown value v{v}"
    pure (.yield (acc.1.mark v, acc.2.push r))
  | .ret i =>
    if index < nh then throw "try_call return on exception edge"
    let some r := rets[i]? | throw "try_call return index"
    pure (.yield (acc.1, acc.2.push r))
  | .exn i =>
    if index == nh then throw "try_call payload on normal edge"
    let some r := pays[i]? | throw "try_call payload index"
    pure (.yield (acc.1, acc.2.push r))

private theorem arg_frame (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (a b : State × Array Reg)
    (h : argStep ctx rets pays index nh arg a = .ok (.yield b)) :
    frame b.1 = frame a.1 := by
  cases arg <;> unfold argStep at h
  all_goals repeat' first | (solve | cases h <;> rfl) | split at h

private theorem arg_no_break (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (a b : State × Array Reg) :
    argStep ctx rets pays index nh arg a ≠ .ok (.done b) := by
  intro h
  cases arg <;> unfold argStep at h
  all_goals repeat' first | (solve | cases h) | split at h

private theorem branch_frame {ctx : Ctx} {st next : State} {block index : Nat}
    {args : Array Reg} (h : branchArgs ctx st block index = .ok (args, next)) :
    frame next = frame st := by
  unfold branchArgs at h
  dsimp only at h
  split at h
  · rename_i id values lookup
    split at h
    · rename_i target found
      split at h
      · cases h
      · let ti := (st.instBlock.findIdx? (· == block)).getD 0 + ctx.func.blocks[block]!.body.length
        let reservations := st.tryRegs[ti]!
        let nh := match ctx.func.blocks[block]!.term with
          | .tryCall _ _ et | .tryCallIndirect _ _ et => et.handlers.length
          | _ => 0
        change (do
          let result ← forIn values (st, #[]) (argStep ctx reservations.1 reservations.2 index nh)
          pure (result.2, result.1)) = .ok (args, next) at h
        cases loop : forIn values (st, #[]) (argStep ctx reservations.1 reservations.2 index nh) with
        | error e => simp only [loop, bind, Except.bind] at h; cases h
        | ok result =>
          simp only [loop, bind, Except.bind, pure, Except.pure] at h
          cases h
          exact forIn_frame (fun a : State × Array Reg => frame a.1) _
            (arg_frame ctx reservations.1 reservations.2 index nh)
            (arg_no_break ctx reservations.1 reservations.2 index nh) values loop
    · cases h
  · cases h

private theorem fold_fields_eq {α β γ : Type} (field : α → γ)
    (step : α → β → Except String α)
    (hs : ∀ a b next, step a b = .ok next → field next = field a)
    (xs : List β) {a next : α} (h : xs.foldlM step a = .ok next) :
    field next = field a := by
  induction xs generalizing a with
  | nil => cases h; rfl
  | cons x xs ih =>
    rw [List.foldlM_cons] at h
    cases he : step a x with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok middle =>
      simp only [he, bind, Except.bind] at h
      exact (ih h).trans (hs a x middle he)


private theorem outgoing_frame {ctx : Ctx} {order : Order} {bi : Nat} {targets : Array Nat}
    {st next : State} {outgoing : Array (Array Reg)}
    (h : collectOutgoing ctx order bi targets st = .ok (next, outgoing)) :
    frame next = frame st := by
  unfold collectOutgoing at h
  apply fold_fields_eq (fun a : State × Array (Array Reg) => frame a.1) _ ?_ _ h
  intro acc target result step
  unfold outgoingStep at step
  split at step
  · cases step; rfl
  · cases call : branchArgs ctx acc.1 bi target.2 with
    | error e => simp only [call, bind, Except.bind] at step; cases step
    | ok pair =>
      rcases pair with ⟨regs, state⟩
      simp only [call, bind, Except.bind, pure, Except.pure] at step
      cases step
      exact branch_frame call


/-- Actual successor argument handling preserves the complete alias array. -/
theorem stock_branchArgs_alias {ctx : Ctx} {st next : State} {block index : Nat}
    {args : Array Reg} (run : branchArgs ctx st block index = .ok (args, next)) :
    next.alias = st.alias := congrArg (fun x => x.2.2) (branch_frame run)

/-- Collecting ordinary and critical-edge successor vectors does not write aliases. -/
theorem stock_collectOutgoing_alias {ctx : Ctx} {order : Order} {bi : Nat}
    {targets : Array Nat} {st next : State} {args : Array (Array Reg)}
    (run : collectOutgoing ctx order bi targets st = .ok (next, args)) :
    next.alias = st.alias := congrArg (fun x => x.2.2) (outgoing_frame run)

/-- Actual lowering of a synthetic critical edge preserves every recorded alias. -/
theorem stock_lowerNode_edge_alias {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {order : Order} {f : Clif.Function} {paramBytes : List Nat} {label pred k target : Nat}
    {input output : DriverState}
    (edge : order.nodes[label]! = .edge pred k target)
    (run : lowerNode ctx ranges order f paramBytes label input = .ok output) :
    output.state.alias = input.state.alias := by
  unfold lowerNode at run
  simp only [edge] at run
  cases call : branchArgs ctx input.state pred k with
  | error e => simp only [call, bind, Except.bind] at run; cases run
  | ok pair =>
    rcases pair with ⟨args, next⟩
    simp only [call, bind, Except.bind, pure, Except.pure] at run
    cases run
    exact stock_branchArgs_alias call

private def edgeFunction : Clif.Function := {
  name := "alias_edge"
  sig := {}
  blocks := [
    { id := 0, params := [(0, .i64)], body := [], term := .jump ⟨1, [0]⟩ },
    { id := 1, params := [(1, .i64)], body := [], term := .ret [] }] }
private def edgeCtx : Ctx := { sinkCtx with func := edgeFunction, valReg := #[some (.vreg 192 .int)] }
private def edgeInput : State := { sinkState with demand := #[0], alias := aliasStep #[] (192, 193) }
private def edgeNext : State := edgeInput.mark 0
private def edgeOrder : Order := ⟨#[.original 0, .edge 0 0 1, .original 1], #[#[1], #[2], #[]]⟩
private def edgeDriver : DriverState := {
  state := edgeInput
  blocks := Array.replicate 3 default
  edgeArgs := Array.replicate 3 #[]
  schedule := #[]
  scans := #[]
  blockScans := #[]
  rules := #[] }
private def edgeOutput : DriverState := { edgeDriver with
  state := edgeNext
  blocks := edgeDriver.blocks.set! 1 { label := 1, insts := #[.jump 2], branchArgs := #[.vreg 192 .int] }
  edgeArgs := edgeDriver.edgeArgs.set! 1 #[#[.vreg 192 .int]] }

/-- Nonempty argument collection marks a source use and keeps a nonempty alias. -/
theorem stock_branchArgs_alias_witness :
    branchArgs edgeCtx edgeInput 0 0 = .ok (#[.vreg 192 .int], edgeNext) ∧
    edgeNext.demand = #[1] ∧
    edgeNext.alias = edgeInput.alias ∧
    (edgeNext.alias[192]?).join = some 193 := by
  refine ⟨rfl, rfl, stock_branchArgs_alias (ctx := edgeCtx) (block := 0) (index := 0) (args := #[.vreg 192 .int]) rfl, rfl⟩

/-- A real ordinary successor and a synthetic edge exercise both collection cases. -/
theorem stock_collectOutgoing_alias_witness :
    collectOutgoing edgeCtx edgeOrder 0 #[2, 1] edgeInput =
      .ok (edgeNext, #[#[.vreg 192 .int], #[]]) ∧
    edgeNext.alias = edgeInput.alias := by
  refine ⟨rfl, stock_collectOutgoing_alias (ctx := edgeCtx) (args := #[#[.vreg 192 .int], #[]]) (order := edgeOrder) (bi := 0)
    (targets := #[2, 1]) rfl⟩

/-- Synthetic-edge lowering emits a jump, passes a real argument, and marks its demand. -/
theorem stock_lowerNode_edge_alias_witness :
    lowerNode edgeCtx #[] edgeOrder edgeFunction [] 1 edgeDriver = .ok edgeOutput ∧
    edgeOutput.state.demand = #[1] ∧
    edgeOutput.state.alias = edgeDriver.state.alias ∧
    (edgeOutput.state.alias[192]?).join = some 193 := by
  refine ⟨rfl, rfl, stock_lowerNode_edge_alias (ctx := edgeCtx) (ranges := #[]) (order := edgeOrder) (f := edgeFunction) (paramBytes := []) (label := 1) (pred := 0) (k := 0) (target := 1) rfl rfl, rfl⟩

end Backend.Stock.Proof

import FV.Backend.Proof.StockContext
import FV.Backend.Proof.IselFlowGen
import FV.Backend.Proof.IselInterp
import FV.Backend.Proof.IselData

/-! Preallocated exception registers bound the destinations of try-call aliases.
These are facts of the real allocator, with no new input acceptance condition. -/
namespace Backend.Stock.Proof
open Backend.Proof Isle Isle.Interp Isle.Aarch64
attribute [local irreducible] Isle.Aarch64.program
set_option maxRecDepth 4096

/-- Every recorded exception return or payload register lies below the actual
allocation frontier. Absent reservation slots record no registers. -/
def ReservedRegsBelow (a : Allocation) : Prop :=
  ∀ (i : Nat) (rs : List Reg × List Reg), a.tryRegs[i]? = some rs → ∀ r ∈ rs.1 ++ rs.2,
    ∃ n, r = Reg.vreg n .int ∧ n < a.base.nextVreg

private theorem allocation_mono (a : Allocation) (q : AllocationRequest) :
    a.base.nextVreg ≤ (a.step q).base.nextVreg := by
  cases q <;> simp [Allocation.step, LState.fresh] <;> omega

private theorem initial_reserved (values instructions : Nat) :
    ReservedRegsBelow (Allocation.initial values instructions) := by
  intro i rs lookup r mem
  by_cases inside : i < instructions
  · simp [Allocation.initial, inside] at lookup
    subst rs
    simp at mem
  · simp [Allocation.initial, inside] at lookup

private theorem step_reserved {a : Allocation} (bound : ReservedRegsBelow a)
    (q : AllocationRequest) : ReservedRegsBelow (a.step q) := by
  intro i rs lookup r mem
  cases q with
  | value x =>
    obtain ⟨n, reg, old⟩ := bound i rs lookup r mem
    exact ⟨n, reg, Nat.lt_of_lt_of_le old (allocation_mono a (.value x))⟩
  | exception j rets pays =>
    simp only [Allocation.step, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds] at lookup
    by_cases same : i = j
    · subst i
      by_cases inside : j < a.tryRegs.size
      · simp only [inside, ↓reduceIte, Option.some.injEq] at lookup
        subst rs
        simp only [List.mem_append, List.mem_map, List.mem_range] at mem
        rcases mem with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
        · exact ⟨a.base.nextVreg + k, rfl, by simp only [Allocation.step]; omega⟩
        · exact ⟨a.base.nextVreg + rets + k, rfl, by simp only [Allocation.step]; omega⟩
      · simp only [inside, ↓reduceIte] at lookup
        cases lookup
    · simp only [Ne.symm same, ↓reduceIte] at lookup
      obtain ⟨n, reg, old⟩ := bound i rs lookup r mem
      exact ⟨n, reg, Nat.lt_of_lt_of_le old (allocation_mono a (.exception j rets pays))⟩

/-- Actual allocation requests, including overwritten or out-of-range
reservations, keep all recorded exception registers below the final frontier. -/
theorem allocateRequests_reservedBelow (values instructions : Nat)
    (requests : List AllocationRequest) :
    ReservedRegsBelow (allocateRequests values instructions requests) := by
  unfold allocateRequests
  have fold (qs : List AllocationRequest) (a : Allocation) (bound : ReservedRegsBelow a) :
      ReservedRegsBelow (qs.foldl Allocation.step a) := by
    induction qs generalizing a with
    | nil => exact bound
    | cons q qs ih => exact ih (a.step q) (step_reserved bound q)
  exact fold requests _ (initial_reserved values instructions)

/-- Successful stock context construction supplies bounds for every exception
reservation used by its later block scans. -/
theorem buildCtx_reservedBelow {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, st)) :
    ∀ (i : Nat) (rs : List Reg × List Reg), st.tryRegs[i]? = some rs → ∀ r ∈ rs.1 ++ rs.2,
      ∃ n, r = Reg.vreg n .int ∧ n < st.base.nextVreg := by
  obtain ⟨original, st0, requests, _, _, result⟩ := buildCtx_allocation build
  have bound := allocateRequests_reservedBelow original.valTy.size original.insts.size requests
  have state := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2) result
  change st = _ at state
  rw [state]
  exact bound

private def reservations : Allocation :=
  allocateRequests 1 2 [.value 0, .exception 1 1 2]

theorem allocateRequests_reservedBelow_witness :
    reservations.tryRegs[1]? = some ([.vreg 193 .int], [.vreg 194 .int, .vreg 195 .int]) ∧
    reservations.base.nextVreg = 196 ∧ ReservedRegsBelow reservations :=
  ⟨rfl, rfl, allocateRequests_reservedBelow _ _ _⟩

/-- A real successfully constructed context witnesses the reservation bounds.
The allocator witness above separately exercises nonempty exception registers. -/
theorem buildCtx_reservedBelow_witness :
    ∃ f ctx ranges st, Stock.buildCtx f = .ok (ctx, ranges, st) ∧
      (∀ (i : Nat) (rs : List Reg × List Reg), st.tryRegs[i]? = some rs →
        ∀ r ∈ rs.1 ++ rs.2, ∃ n, r = Reg.vreg n .int ∧ n < st.base.nextVreg) := by
  obtain ⟨build, _, _, _⟩ := buildCtx_allocated_witness
  exact ⟨_, _, _, _, build, buildCtx_reservedBelow build⟩

private theorem setAlias_bound {st next : State} {n : Nat} {c : RegClass} {src : Reg}
    {cap : Nat} (bound : st.alias.size ≤ cap) (dest : n < cap)
    (run : st.setAlias (.vreg n c) src = .ok next) : next.alias.size ≤ cap := by
  cases src <;> simp only [State.setAlias, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at run
  all_goals repeat' first | (solve | cases run) | split at run
  all_goals
    cases run
    simp only [Array.size_set!, Array.size_append, Array.size_replicate]
    omega

private def tryAliasStep (ps rets : List Reg) (acc : Except String (State × List Reg))
    (pair : Reg × Reg) : Except String (State × List Reg) := do
  let (s, regs) ← acc
  let (p, r) := pair
  if let some i := ps.idxOf? p then
    let some ret := rets[i]? | throw "try_call return register"
    pure (← s.setAlias r ret, regs ++ [ret])
  else pure (s, regs ++ [r])

private theorem try_fold_error (ps rets : List Reg) (pairs : List (Reg × Reg)) (e : String) :
    pairs.foldl (tryAliasStep ps rets) (.error e) = .error e := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih => exact ih

private theorem try_fold_bound (ps rets : List Reg) (pairs : List (Reg × Reg))
    (st : State) (regs : List Reg) {next : State} {out : List Reg} {cap : Nat}
    (bound : st.alias.size ≤ cap)
    (destinations : ∀ pair ∈ pairs, ∃ n, pair.2 = .vreg n .int ∧ n < cap)
    (run : pairs.foldl (tryAliasStep ps rets) (.ok (st, regs)) = .ok (next, out)) :
    next.alias.size ≤ cap := by
  induction pairs generalizing st regs with
  | nil => cases run; exact bound
  | cons pair pairs ih =>
    rw [List.foldl_cons] at run
    cases step : tryAliasStep ps rets (.ok (st, regs)) pair with
    | error e => rw [step, try_fold_error] at run; cases run
    | ok result =>
      rcases result with ⟨middle, rs⟩
      rw [step] at run
      have mb : middle.alias.size ≤ cap := by
        unfold tryAliasStep at step
        simp only [bind, Except.bind] at step
        cases idx : ps.idxOf? pair.1 with
        | none => simp only [idx, pure, Except.pure] at step; cases step; exact bound
        | some i =>
          simp only [idx] at step
          cases ret : rets[i]? with
          | none => simp only [ret] at step; cases step
          | some r =>
            simp only [ret] at step
            cases alias : st.setAlias pair.2 r with
            | error e => rw [alias] at step; cases step
            | ok q =>
              rw [alias] at step
              simp only [pure, Except.pure] at step
              cases step
              obtain ⟨n, dest, below⟩ := destinations pair (by simp)
              rw [dest] at alias
              exact setAlias_bound bound below alias
      exact ih middle rs mb (fun pair mem => destinations pair (by simp [mem])) run

private theorem delegate_alias {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V} {cap : Nat} (bound : st.alias.size ≤ cap)
    (run : (match Backend.externCtor ctx t args st.base with
      | .ok (v, base) => ExtResult.ok (v, { st with base })
      | .fail => ExtResult.fail
      | .unmodeled e => ExtResult.unmodeled e) = ExtResult.ok (v, next)) :
    next.alias.size ≤ cap := by
  cases call : Backend.externCtor ctx t args st.base with
  | fail => rw [call] at run; cases run
  | unmodeled e => rw [call] at run; cases run
  | ok pair => rw [call] at run; cases run; exact bound

private theorem marks_alias (st : State) (vs : List Nat) :
    (vs.foldl State.mark st).alias = st.alias := by
  induction vs generalizing st with
  | nil => rfl
  | cons x xs ih => exact ih (st.mark x)

/-- Every actual external helper keeps aliases inside a fixed preallocation
cap when its try-call payload destinations were reserved below that cap. -/
theorem stock_ctor_aliasBelow {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V} {cap : Nat}
    (payloads : ∀ r ∈ ctx.tryRegs.2, ∃ n, r = .vreg n .int ∧ n < cap)
    (bound : st.alias.size ≤ cap)
    (run : Stock.externCtor ctx t args st = .ok (v, next)) : next.alias.size ≤ cap := by
  unfold Stock.externCtor at run
  split at run
  all_goals dsimp only at run
  all_goals try solve | exact delegate_alias bound run
  all_goals
    repeat' first
    | (solve | cases run <;> exact bound)
    | (solve | refine delegate_alias ?_ run; simpa only [State.mark, marks_alias] using bound)
    | split at run
  rename_i _ _ sig _ _ ps _ _ s regs step
  cases run
  exact try_fold_bound ps ctx.tryRegs.1 ((payloadRegs sig.callConv).zip ctx.tryRegs.2) st [] bound
    (fun pair mem => payloads pair.2 (List.of_mem_zip mem).2) step

/-- Alias bounds survive successful full interpreter evaluation, including
failed-match rollback and nested helpers, with no selected-rule restriction. -/
theorem stock_apply_aliasBelow {p : Program} {ctx : Ctx} {cfg : Config}
    {n ty t : Nat} {args : List V} {st next : State} {tr tr' : Array RuleId}
    {out : Option V} {cap : Nat}
    (payloads : ∀ r ∈ ctx.tryRegs.2, ∃ n, r = .vreg n .int ∧ n < cap)
    (bound : st.alias.size ≤ cap)
    (run : (applyTerm p (Stock.sem ctx) cfg n ty t args).run (st, tr) =
      .ok (out, next, tr')) : next.alias.size ≤ cap := by
  have relation : st.alias.size ≤ cap → next.alias.size ≤ cap :=
    (presAt (R := fun a b : State => a.alias.size ≤ cap → b.alias.size ≤ cap)
      (fun _ h => h) (fun _ _ _ ab bc h => bc (ab h))
      (fun _ _ _ _ _ ctor bound => stock_ctor_aliasBelow payloads bound ctor) n).apply
        ty t args st tr out next tr' run
  exact relation bound

private theorem fold_invariant {α β : Type} (P : α → Prop)
    (step : α → β → Except String α)
    (keeps : ∀ a b next, P a → step a b = .ok next → P next)
    (xs : List β) {a next : α} (bound : P a)
    (run : xs.foldlM step a = .ok next) : P next := by
  induction xs generalizing a with
  | nil => cases run; exact bound
  | cons x xs ih =>
    rw [List.foldlM_cons] at run
    cases call : step a x with
    | error e => simp only [call, bind, Except.bind] at run; cases run
    | ok middle =>
      simp only [call, bind, Except.bind] at run
      exact ih (keeps a x middle bound call) run

/-- Actual result binding grows aliases only at preallocated source-result
numbers, regardless of how high the selected fresh source register is. -/
theorem stock_bindResults_aliasBelow {ctx : Ctx} {pairs : List (Nat × List Reg)}
    {st next : State} {copies : Array MInst} {cap : Nat}
    (mapped : ∀ x r, ctx.valueReg? x = some r → ∃ n, r = .vreg n .int ∧ n < cap)
    (bound : st.alias.size ≤ cap)
    (run : bindResults ctx pairs st = .ok (next, copies)) : next.alias.size ≤ cap := by
  unfold bindResults at run
  apply fold_invariant (fun a : State × Array MInst => a.1.alias.size ≤ cap) _ ?_ pairs bound run
  intro acc pair result old step
  rcases acc with ⟨s, code⟩
  rcases pair with ⟨v, rs⟩
  dsimp only at step
  cases map : ctx.valueReg? v with
  | none => simp only [map] at step; cases step
  | some r =>
    simp only [map] at step
    split at step
    · rename_i _ n cls
      cases alias : s.setAlias r (.vreg n cls) with
      | error e => simp only [alias, bind, Except.bind] at step; cases step
      | ok q =>
        simp only [alias, bind, Except.bind, pure, Except.pure] at step
        cases step
        obtain ⟨d, rfl, below⟩ := mapped v r map
        exact setAlias_bound old below alias
    · cases step; exact old
    · cases step

private def aliasCtx : Ctx :=
  { sinkCtx with tryRegs := ([.vreg 193 .int], [.vreg 194 .int, .vreg 195 .int]) }
private def aliasInput : State :=
  { sinkState with base := reservations.base, alias := #[some 0], tryRegs := reservations.tryRegs }
private def aliasNext : State :=
  { aliasInput with alias := (aliasInput.alias ++ Array.replicate 194 none).set! 194 (some 193) }
private def aliasSig : Clif.Signature :=
  { returns := [⟨.i64, .none, .normal⟩] }
private def aliasResult : V :=
  .op (.callRets [(.x 0, .vreg 193 .int), (.x 1, .vreg 195 .int)])
private theorem aliasPayloads :
    ∀ r ∈ aliasCtx.tryRegs.2, ∃ n, r = .vreg n .int ∧ n < 196 := by
  intro r mem
  simp only [aliasCtx, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact ⟨194, rfl, by decide⟩
  · exact ⟨195, rfl, by decide⟩
private theorem aliasRun :
    Stock.externCtor aliasCtx T.gen_try_call_rets [.op (.sig aliasSig)] aliasInput =
      .ok (aliasResult, aliasNext) := by
  rfl

/-- A real try-call helper installs an alias for a reserved payload while
retaining an older alias and staying below the actual reservation frontier. -/
theorem stock_ctor_aliasBelow_witness :
    Stock.externCtor aliasCtx T.gen_try_call_rets [.op (.sig aliasSig)] aliasInput =
      .ok (aliasResult, aliasNext) ∧ aliasInput.alias.size = 1 ∧
    aliasNext.alias.size = 195 ∧ aliasNext.alias[194]? = some (some 193) ∧
    aliasNext.alias.size ≤ 196 :=
  ⟨aliasRun, rfl, rfl, rfl, stock_ctor_aliasBelow aliasPayloads (by decide) aliasRun⟩

set_option maxRecDepth 16384 in
private theorem tryTerm : termOf program 300 = .ok T.gen_try_call_rets := by
  unfold termOf Isle.Aarch64.program
  rfl

theorem stock_apply_aliasBelow_witness :
    (applyTerm program (Stock.sem aliasCtx) {} 1 T.gen_try_call_rets.ret 300
      [.op (.sig aliasSig)]).run (aliasInput, #[]) =
        .ok (some aliasResult, aliasNext, #[]) ∧ aliasNext.alias.size ≤ 196 := by
  have run : (applyTerm program (Stock.sem aliasCtx) {} 1 T.gen_try_call_rets.ret 300
      [.op (.sig aliasSig)]).run (aliasInput, #[]) =
        .ok (some aliasResult, aliasNext, #[]) := by
    simp only [applyTerm.eq_2, tryTerm, Stock.sem, T.gen_try_call_rets, isel_data, isel_monad]
    have call := aliasRun
    unfold T.gen_try_call_rets at call
    rw [call]
    rfl
  exact ⟨run, stock_apply_aliasBelow aliasPayloads (by decide) run⟩

private def resultCtx : Ctx := { sinkCtx with valReg := #[some (.vreg 193 .int)] }
private def resultNext : State :=
  { aliasNext with alias := aliasNext.alias.set! 193 (some 197) }

theorem stock_bindResults_aliasBelow_witness :
    bindResults resultCtx [(0, [.vreg 197 .int])] aliasNext = .ok (resultNext, #[]) ∧
      resultNext.alias[193]? = some (some 197) ∧ resultNext.alias.size = 195 ∧
      196 ≤ 197 ∧ resultNext.alias.size ≤ 196 := by
  have maps : ∀ x r, resultCtx.valueReg? x = some r → ∃ n, r = .vreg n .int ∧ n < 196 := by
    intro x r map
    cases x with
    | zero => cases map; exact ⟨193, rfl, by decide⟩
    | succ x => simp [resultCtx, Ctx.valueReg?] at map
  have run : bindResults resultCtx [(0, [.vreg 197 .int])] aliasNext =
      .ok (resultNext, #[]) := rfl
  exact ⟨run, rfl, rfl, by decide, stock_bindResults_aliasBelow maps (by decide) run⟩

end Backend.Stock.Proof

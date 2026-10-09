import FV.Backend.Proof.StockAllocationFlow
import FV.Backend.Proof.StockDFG

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

/-- Register origins read by the mapped source-provenance model. -/
def RegOrigin (ctx : Ctx) (t : Term) (args : List V) (before after : State)
    (r : Reg) : Prop :=
  r ∈ regsInL args ∨
    (∃ n c, r = .vreg n c ∧ before.base.nextVreg ≤ n ∧ n < after.base.nextVreg) ∨
    (∃ x ∈ valsInL args, ctx.valueReg? x = some r) ∨
    (∀ n c, r ≠ .vreg n c) ∨ t.id = TId.invalid_reg

/-- The only additional origins in selected contexts are the exact preallocated
exception return and payload registers. -/
def ReservedRegOrigin (ctx : Ctx) (t : Term) (args : List V) (before after : State)
    (r : Reg) : Prop :=
  RegOrigin ctx t args before after r ∨ r ∈ ctx.tryRegs.1 ∨ r ∈ ctx.tryRegs.2

private theorem legacy_origin {ctx : Ctx} {t : Term} {args : List V}
    {before after : State} {v : V}
    (call : Backend.externCtor ctx t args before.base = .ok (v, after.base)) :
    ∀ r ∈ v.regsIn, ReservedRegOrigin ctx t args before after r := by
  intro r hr
  have origin := (externCtor_ok ctx t args before.base _ _ call).regs r hr
  unfold ReservedRegOrigin RegOrigin
  rcases origin with h | h | h | h | h | h | h
  · exact .inl (.inl h)
  · exact .inl (.inr (.inl h))
  · exact .inl (.inr (.inr (.inl h)))
  · exact .inl (.inr (.inr (.inr (.inl h))))
  · exact .inl (.inr (.inr (.inr (.inr h))))
  · exact .inr (.inl h)
  · exact .inr (.inr h)

private theorem legacy_values {ctx : Ctx} {t : Term} {args : List V}
    {before after : LState} {out : V}
    (call : Backend.externCtor ctx t args before = .ok (out, after)) :
    ∀ x ∈ out.valsIn, x ∈ valsInL args :=
  (externCtor_ok ctx t args before out after call).vals

private def outputStep (acc : List (List Reg) × LState) (_ : Clif.AbiParam) :
    List (List Reg) × LState :=
  let (r, base) := acc.2.fresh .int
  (acc.1 ++ [[r]], base)

private theorem output_origins (returns : List Clif.AbiParam)
    (regs : List (List Reg)) (base : LState) :
    base.nextVreg ≤ (returns.foldl outputStep (regs, base)).2.nextVreg ∧
      ∀ r ∈ (returns.foldl outputStep (regs, base)).1.flatten,
        r ∈ regs.flatten ∨ ∃ n, r = .vreg n .int ∧
          base.nextVreg ≤ n ∧ n < (returns.foldl outputStep (regs, base)).2.nextVreg := by
  induction returns generalizing regs base with
  | nil => exact ⟨Nat.le_refl _, fun r hr => .inl hr⟩
  | cons ret returns ih =>
    simp only [List.foldl_cons, outputStep, LState.fresh]
    have next := ih (regs ++ [[.vreg base.nextVreg .int]]) (base.fresh .int).2
    dsimp only [LState.fresh] at next
    constructor
    · exact Nat.le_trans (by omega) next.1
    · intro r hr
      rcases next.2 r hr with old | fresh
      · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.mem_append, List.mem_singleton] at old
        rcases old with old | rfl
        · exact .inl old
        · exact .inr ⟨base.nextVreg, rfl, Nat.le_refl _, by
            have := next.1
            omega⟩
      · rcases fresh with ⟨n, rfl, lower, upper⟩
        exact .inr ⟨n, rfl, Nat.le_trans (by omega) lower, upper⟩

private theorem marks_base (values : List Nat) (st : State) :
    (values.foldl State.mark st).base = st.base := by
  induction values generalizing st with
  | nil => rfl
  | cons value values ih => exact ih (st.mark value)

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

private theorem try_fold_origins (ps rets pays : List Reg) (pairs : List (Reg × Reg))
    (st : State) (regs : List Reg) {next : State} {out : List Reg}
    (payloads : ∀ pair ∈ pairs, pair.2 ∈ pays)
    (origins : ∀ r ∈ regs, r ∈ rets ∨ r ∈ pays)
    (run : pairs.foldl (tryAliasStep ps rets) (.ok (st, regs)) = .ok (next, out)) :
    ∀ r ∈ out, r ∈ rets ∨ r ∈ pays := by
  induction pairs generalizing st regs with
  | nil => cases run; exact origins
  | cons pair pairs ih =>
    rw [List.foldl_cons] at run
    cases step : tryAliasStep ps rets (.ok (st, regs)) pair with
    | error e => rw [step, try_fold_error] at run; cases run
    | ok result =>
      rcases result with ⟨middle, rs⟩
      rw [step] at run
      have middleOrigins : ∀ r ∈ rs, r ∈ rets ∨ r ∈ pays := by
        unfold tryAliasStep at step
        simp only [bind, Except.bind] at step
        cases idx : ps.idxOf? pair.1 with
        | none =>
          simp only [idx, pure, Except.pure] at step
          cases step
          intro r member
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with old | rfl
          · exact origins r old
          · exact .inr (payloads pair (by simp))
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
              intro r' member
              simp only [List.mem_append, List.mem_singleton] at member
              rcases member with old | rfl
              · exact origins r' old
              · exact .inl (List.mem_of_getElem? ret)
      exact ih middle rs (fun pair mem => payloads pair (by simp [mem])) middleOrigins run

/-- Actual stock constructor outputs carry argument registers, mapped source
values, fresh allocations, physical registers or exact exception reservations.
This covers the actual successful try-call payload/return merge. -/
theorem stock_ctor_output_reserved_origin {ctx : Ctx} {t : Term} {args : List V}
    {before after : State} {out : V} (run : Stock.externCtor ctx t args before = .ok (out, after)) :
    ∀ r ∈ out.regsIn, ReservedRegOrigin ctx t args before after r := by
  unfold Stock.externCtor at run
  split at run
  all_goals dsimp only at run
  all_goals try simp only [marks_base] at *
  all_goals repeat' first
    | (solve | cases run)
    | (solve | cases run; apply legacy_origin; assumption)
    | (solve | cases run; intro r hr; simp [V.regsIn, opRegs, pairRegs] at hr)
    | split at run

  case h_10 =>
    rename_i _ _ sig _
    cases run
    intro r hr
    change r ∈ (sig.returns.foldl outputStep ([], before.base)).1.flatten at hr
    rcases (output_origins sig.returns [] before.base).2 r hr with absent | fresh
    · cases absent
    · rcases fresh with ⟨n, rfl, lower, upper⟩
      exact .inl (.inr (.inl ⟨n, .int, rfl, lower, upper⟩))

  case h_2 =>
    rename_i _ _ sig _ _ ps physical _ next regs merged
    cases run
    intro r member
    simp only [V.regsIn, opRegs, pairRegs, List.mem_flatMap, List.mem_append,
      List.mem_filter, List.mem_cons, List.mem_nil_iff, or_false] at member
    obtain ⟨⟨p, q⟩, pair, which⟩ := member
    rcases pair with pair | ⟨pair, _⟩
    · have both := List.of_mem_zip pair
      rcases which with rfl | rfl
      · exact .inl (.inr (.inr (.inr (.inl (retRegs_phys physical _ both.1)))))
      · exact .inr (.inl both.2)
    · have both := List.of_mem_zip pair
      rcases which with rfl | rfl
      · exact .inl (.inr (.inr (.inr (.inl (payloadRegs_phys sig.callConv _ both.1)))))
      · exact .inr (try_fold_origins ps ctx.tryRegs.1 ctx.tryRegs.2
          ((payloadRegs sig.callConv).zip ctx.tryRegs.2) before []
          (fun _ mem => (List.of_mem_zip mem).2) (by simp) merged _ both.2)

/-- Actual stock constructor outputs carry ordinary origins in contexts with
no reserved exception registers. The original interface is retained. -/
theorem stock_ctor_output_origin {ctx : Ctx} {t : Term} {args : List V}
    {before after : State} {out : V} (empty : ctx.tryRegs = ([], []))
    (run : Stock.externCtor ctx t args before = .ok (out, after)) :
    ∀ r ∈ out.regsIn, RegOrigin ctx t args before after r := by
  intro r member
  rcases stock_ctor_output_reserved_origin run r member with origin | reserved
  · exact origin
  · rw [empty] at reserved
    rcases reserved with absent | absent <;> cases absent

/-- Successful construction supplies the statement context needed by the
register-origin result; callers need no extra source-input assumption. -/
theorem stock_built_ctor_output_origin {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {t : Term} {args : List V} {before after : State} {out : V}
    (run : Stock.externCtor ctx t args before = .ok (out, after)) :
    ∀ r ∈ out.regsIn, RegOrigin ctx t args before after r := by
  obtain ⟨original, st0, requests, sourceBuild, _, fields⟩ := buildCtx_allocation build
  have context := congrArg (fun q => q.1) fields
  dsimp only at context
  have empty : ctx.tryRegs = ([], []) := by
    rw [context]
    exact (Backend.Proof.Driver.ctxSpec_of sourceBuild).facts.tryRegs
  exact stock_ctor_output_origin empty run

/-- Actual stock constructors cannot invent source values inside their outputs. -/
theorem stock_ctor_output_values {ctx : Ctx} {t : Term} {args : List V}
    {before after : State} {out : V}
    (run : Stock.externCtor ctx t args before = .ok (out, after)) :
    ∀ x ∈ out.valsIn, x ∈ valsInL args := by
  unfold Stock.externCtor at run
  split at run
  all_goals dsimp only at run
  all_goals repeat' first
    | (solve | cases run)
    | (solve | cases run; apply legacy_values; assumption)
    | (solve | cases run; intro x hx; simp [V.valsIn, opVals] at hx)
    | split at run

private theorem source_definition {ctx : Ctx} {before : State} {x i : Nat} {unique : Bool}
    (source : Stock.source ctx before x = some (i, unique)) : ctx.defInst? x = some i := by
  unfold Stock.source at source
  cases defined : ctx.defInst? x with
  | none => simp only [defined, bind, Option.bind] at source; cases source
  | some d =>
    simp only [defined, bind, Option.bind] at source
    repeat' first
      | (solve | cases source)
      | (solve | cases source; rfl)
      | split at source

private theorem legacy_instructions {ctx : Ctx} {t : Term} {args : List V}
    {before after : LState} {out : V}
    (call : Backend.externCtor ctx t args before = .ok (out, after)) :
    ∀ i ∈ out.instsIn, i ∈ instsInL args ∨ ∃ x ∈ valsInL args, ctx.defInst? x = some i := by
  intro i hi
  exact .inl ((externCtor_ok ctx t args before out after call).insts i hi)

/-- The stock sinkability constructor may additionally return the defining
instruction of an argument value; all other instruction origins are retained. -/
theorem stock_ctor_output_instructions {ctx : Ctx} {t : Term} {args : List V}
    {before after : State} {out : V}
    (run : Stock.externCtor ctx t args before = .ok (out, after)) :
    ∀ i ∈ out.instsIn, i ∈ instsInL args ∨ ∃ x ∈ valsInL args, ctx.defInst? x = some i := by
  unfold Stock.externCtor at run
  split at run
  all_goals dsimp only at run
  all_goals repeat' first
    | (solve | cases run)
    | (solve | cases run; apply legacy_instructions; assumption)
    | (solve | cases run; intro i hi; simp [V.instsIn] at hi)
    | split at run

  case h_1 =>
    rename_i _ _ x _ _ i defined
    cases run
    intro j hj
    simp only [V.instsIn, List.mem_singleton] at hj
    subst j
    exact .inr ⟨x, by simp [valsInL, V.valsIn], source_definition defined⟩

/-- Actual stock sinkability returns a nonempty definition atom; its source
is traced to the argument value instead of assuming the constructor fails. -/
theorem stock_ctor_output_instructions_witness :
    Stock.externCtor sinkCtx T.is_sinkable_inst [.value 0] sinkState =
      .ok (.inst 0, sinkState) ∧ (0 : Nat) ∈ (V.inst 0).instsIn ∧
      ((0 : Nat) ∈ instsInL [.value 0] ∨
        ∃ x ∈ valsInL [.value 0], sinkCtx.defInst? x = some 0) := by
  refine ⟨rfl, by decide, ?_⟩
  exact stock_ctor_output_instructions (ctx := sinkCtx) (t := T.is_sinkable_inst)
    (before := sinkState) (after := sinkState) (out := .inst 0) rfl _ (by decide)

/-- A real constructor retains two nonempty source-value atoms, rather than
making the containment theorem vacuous through a register-only output. -/
theorem stock_ctor_output_values_witness :
    Stock.externCtor sinkCtx T.value_array_2 [.value 0, .value 1] sinkState =
      .ok (.values [0, 1], sinkState) ∧
      (1 : Nat) ∈ (V.values [0, 1]).valsIn ∧
      (1 : Nat) ∈ valsInL [.value 0, .value 1] := by
  refine ⟨rfl, by decide, ?_⟩
  exact stock_ctor_output_values (ctx := sinkCtx) (t := T.value_array_2)
    (before := sinkState) (after := sinkState) (out := .values [0, 1]) rfl _ (by decide)

private def flowOutputSig : Clif.Signature := {
  returns := [⟨.i64, .none, .normal⟩, ⟨.i32, .none, .normal⟩] }
private def flowOutputNext : State := { sinkState with
  base := ((sinkState.base.fresh .int).2.fresh .int).2 }

/-- The real source demand constructor returns its mapped register192; the
actual call-output constructor allocates distinct fresh194/195. Both branches
inhabit the register-origin theorem. -/
theorem stock_ctor_output_origin_witness :
    sinkCtx.tryRegs = ([], []) ∧ sinkCtx.valueReg? 0 = some (.vreg 192 .int) ∧
      Stock.externCtor sinkCtx T.put_in_reg [.value 0] sinkState =
        .ok (.reg (.vreg 192 .int), sinkState.mark 0) ∧
      Stock.externCtor sinkCtx T.gen_call_output [.op (.sig flowOutputSig)] sinkState =
        .ok (.regsVec [[.vreg 194 .int], [.vreg 195 .int]], flowOutputNext) ∧
      RegOrigin sinkCtx T.put_in_reg [.value 0] sinkState (sinkState.mark 0) (.vreg 192 .int) ∧
      RegOrigin sinkCtx T.gen_call_output [.op (.sig flowOutputSig)] sinkState
        flowOutputNext (.vreg 195 .int) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact stock_ctor_output_origin rfl rfl _ (by decide)
  · exact stock_ctor_output_origin rfl rfl _ (by decide)

private def flowFunction : Clif.Function := {
  name := "mapped_ctor_origin"
  sig := { returns := [⟨.i64, .none, .normal⟩] }
  blocks := [{ id := 0, params := [], body := [⟨[0], .iconst .i64 9⟩], term := .ret [0] }] }
private def flowBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx flowFunction).toOption.getD (sinkCtx, #[], sinkState)

set_option maxRecDepth 4096 in
/-- Actual successful stock construction, not a chosen context field assumption,
inhabits the source-mapped constructor origin result. -/
theorem stock_built_ctor_output_origin_witness :
    Stock.buildCtx flowFunction = .ok flowBuilt ∧
      flowBuilt.1.valueReg? 0 = some (.vreg 192 .int) ∧
      Stock.externCtor flowBuilt.1 T.put_in_reg [.value 0] flowBuilt.2.2 =
        .ok (.reg (.vreg 192 .int), flowBuilt.2.2.mark 0) ∧
      RegOrigin flowBuilt.1 T.put_in_reg [.value 0] flowBuilt.2.2
        (flowBuilt.2.2.mark 0) (.vreg 192 .int) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact stock_built_ctor_output_origin (f := flowFunction) (ctx := flowBuilt.1)
    (initial := flowBuilt.2.2) (ranges := flowBuilt.2.1) rfl rfl _ (by decide)

private def reservedCtx : Ctx :=
  { sinkCtx with tryRegs := ([.vreg 193 .int], [.vreg 194 .int, .vreg 195 .int]) }
private def reservedInput : State :=
  { sinkState with base := { sinkState.base with nextVreg := 196 }, alias := #[] }
private def reservedNext : State :=
  { reservedInput with alias := (reservedInput.alias ++ Array.replicate 195 none).set! 194 (some 193) }
private def reservedSig : Clif.Signature :=
  { returns := [⟨.i64, .none, .normal⟩] }
private def reservedResult : V :=
  .op (.callRets [(.x 0, .vreg 193 .int), (.x 1, .vreg 195 .int)])

set_option maxRecDepth 4096 in
/-- The actual try-call return helper merges payload194 into return193 and
retains payload195. Neither output virtual register is a fresh allocation or a
source argument: both exact reserved alternatives are inhabited. -/
theorem stock_ctor_output_reserved_origin_witness :
    reservedCtx.tryRegs.1 ≠ [] ∧ reservedCtx.tryRegs.2 ≠ [] ∧
    Stock.externCtor reservedCtx T.gen_try_call_rets [.op (.sig reservedSig)] reservedInput =
      .ok (reservedResult, reservedNext) ∧
    reservedNext.alias[194]? = some (some 193) ∧
    reservedNext.base.nextVreg = reservedInput.base.nextVreg ∧
    (.vreg 193 .int) ∈ reservedResult.regsIn ∧
    (.vreg 195 .int) ∈ reservedResult.regsIn ∧
    ReservedRegOrigin reservedCtx T.gen_try_call_rets [.op (.sig reservedSig)]
      reservedInput reservedNext (.vreg 193 .int) ∧
    ReservedRegOrigin reservedCtx T.gen_try_call_rets [.op (.sig reservedSig)]
      reservedInput reservedNext (.vreg 195 .int) ∧
    ¬ RegOrigin reservedCtx T.gen_try_call_rets [.op (.sig reservedSig)]
      reservedInput reservedNext (.vreg 195 .int) := by
  have run : Stock.externCtor reservedCtx T.gen_try_call_rets [.op (.sig reservedSig)]
      reservedInput = .ok (reservedResult, reservedNext) := rfl
  refine ⟨(by decide), (by decide), run, rfl, rfl, (by decide), (by decide),
    stock_ctor_output_reserved_origin run _ (by decide),
    stock_ctor_output_reserved_origin run _ (by decide), ?_⟩
  simp [RegOrigin, regsInL, valsInL, V.regsIn, V.valsIn, opRegs, opVals,
    reservedInput, reservedNext, T.gen_try_call_rets, TId.invalid_reg]

end Backend.Stock.Proof

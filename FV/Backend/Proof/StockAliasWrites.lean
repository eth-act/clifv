import FV.Backend.Proof.StockAliasBounds
import FV.Backend.Proof.LowerAlias

/-! Alias entry preservation through the real stock interpreter. Only exception
payload destinations can be aliased by its external constructors. Source-result
binding is separate and must be excluded by the driver's SSA/order invariant. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
attribute [local irreducible] Isle.Aarch64.program
set_option maxRecDepth 4096

/-- Current source mappings are disjoint from all current exception registers. -/
def AllocationDisjoint (a : Allocation) : Prop :=
  ∀ (x : Nat) (r : Reg), (a.valReg[x]?).join = some r → ∀ (i : Nat) (rs : List Reg × List Reg), a.tryRegs[i]? = some rs →
    ∀ q ∈ rs.1 ++ rs.2, r ≠ q

private theorem initial_disjoint (values instructions : Nat) :
    AllocationDisjoint (Allocation.initial values instructions) := by
  intro x r mapped
  by_cases inside : x < values <;> simp [Allocation.initial, inside] at mapped

private theorem value_lookup (a : Allocation) (x y : Nat) :
    ((a.step (.value x)).valReg[y]?).join =
      if y = x then if x < a.valReg.size then some (.vreg a.base.nextVreg .int)
        else none else (a.valReg[y]?).join := by
  simp only [Allocation.step, LState.fresh, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  by_cases same : y = x
  · subst y
    by_cases inside : x < a.valReg.size <;> simp [inside]
  · simp [same, Ne.symm same]

private theorem step_disjoint {a : Allocation} (valid : AllocationValid a)
    (reserved : ReservedRegsBelow a) (old : AllocationDisjoint a)
    (request : AllocationRequest) : AllocationDisjoint (a.step request) := by
  intro x r mapped i rs slot q mem
  cases request with
  | value y =>
    change a.tryRegs[i]? = some rs at slot
    rw [value_lookup] at mapped
    split at mapped
    · split at mapped
      · cases mapped
        obtain ⟨n, rfl, below⟩ := reserved i rs slot q mem
        intro equal
        cases equal
        omega
      · cases mapped
    · exact old x r mapped i rs slot q mem
  | exception j rets pays =>
    change (a.valReg[x]?).join = some r at mapped
    simp only [Allocation.step, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds] at slot
    by_cases same : i = j
    · subst i
      by_cases inside : j < a.tryRegs.size
      · simp only [inside, ↓reduceIte, Option.some.injEq] at slot
        subst rs
        obtain ⟨n, rfl, _, below⟩ := valid.2.1 x r mapped
        simp only [List.mem_append, List.mem_map, List.mem_range] at mem
        rcases mem with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;> intro equal <;> cases equal <;> omega
      · simp only [inside, ↓reduceIte] at slot
        cases slot
    · simp only [Ne.symm same, ↓reduceIte] at slot
      exact old x r mapped i rs slot q mem

/-- The real allocation fold always separates source mappings from exception
registers; this is a construction fact, not an extra source restriction. -/
theorem allocateRequests_valueReservedDisjoint (values instructions : Nat)
    (requests : List AllocationRequest) :
    AllocationDisjoint (allocateRequests values instructions requests) := by
  have reversed (qs : List AllocationRequest) :
      AllocationDisjoint (allocateRequests values instructions qs.reverse) := by
    induction qs with
    | nil => exact initial_disjoint values instructions
    | cons request qs ih =>
      rw [List.reverse_cons]
      have step := step_disjoint (allocation_valid values instructions qs.reverse)
        (allocateRequests_reservedBelow values instructions qs.reverse) ih request
      simpa only [allocateRequests, List.foldl_append, List.foldl_cons, List.foldl_nil] using step
  simpa only [List.reverse_reverse] using reversed requests.reverse

/-- Every successful context build supplies source-register separation from
all exception return and payload reservations used by its later scans. -/
theorem buildCtx_valueReservedDisjoint {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, st)) :
    ∀ (x : Nat) (r : Reg), ctx.valueReg? x = some r → ∀ (i : Nat) (rs : List Reg × List Reg), st.tryRegs[i]? = some rs →
      ∀ q ∈ rs.1 ++ rs.2, r ≠ q := by
  obtain ⟨original, st0, requests, _, _, result⟩ := buildCtx_allocation build
  have separation := allocateRequests_valueReservedDisjoint
    original.valTy.size original.insts.size requests
  have hc := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.1) result
  have hs := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2) result
  change ctx = _ at hc
  change st = _ at hs
  rw [hc, hs]
  exact separation

private def interleaved : Allocation :=
  allocateRequests 2 1 [.value 0, .exception 0 1 2, .value 1]

/-- A real interleaved allocation reserves three exception registers between
two source registers, demonstrating nonempty separation in both directions. -/
theorem allocateRequests_valueReservedDisjoint_witness :
    (interleaved.valReg[0]?).join = some (.vreg 192 .int) ∧
      interleaved.tryRegs[0]? = some ([.vreg 193 .int], [.vreg 194 .int, .vreg 195 .int]) ∧
      (interleaved.valReg[1]?).join = some (.vreg 196 .int) ∧
      AllocationDisjoint interleaved :=
  ⟨rfl, rfl, rfl, allocateRequests_valueReservedDisjoint _ _ _⟩

/-- An actual successful context build inhabits the sole build premise. The
allocation witness separately exercises nonempty exception reservations. -/
theorem buildCtx_valueReservedDisjoint_witness :
    ∃ f ctx ranges st, Stock.buildCtx f = .ok (ctx, ranges, st) ∧
      (∀ (x : Nat) (r : Reg), ctx.valueReg? x = some r → ∀ (i : Nat) (rs : List Reg × List Reg), st.tryRegs[i]? = some rs →
        ∀ q ∈ rs.1 ++ rs.2, r ≠ q) := by
  obtain ⟨build, _, _, _⟩ := buildCtx_allocated_witness
  exact ⟨_, _, _, _, build, buildCtx_valueReservedDisjoint build⟩


private theorem setAlias_entry {st next : State} {dst src : Reg} {key : Nat}
    (apart : ∀ c, dst ≠ .vreg key c)
    (run : st.setAlias dst src = .ok next) :
    (next.alias[key]?).join = (st.alias[key]?).join := by
  cases dst <;> cases src <;> simp only [State.setAlias, bind, Except.bind,
    pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
  all_goals try solve | cases run
  rename_i n c m d
  split at run
  · cases run
  · cases run
    change ((aliasStep st.alias (n, m))[key]?).join = (st.alias[key]?).join
    rw [aliasStep_get]
    have different : key ≠ n := by
      intro same
      subst n
      exact apart c rfl
    simp only [different, ite_false]

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

private theorem try_fold_entry (ps rets : List Reg) (pairs : List (Reg × Reg))
    (st : State) (regs : List Reg) {next : State} {out : List Reg} {key : Nat}
    (destinations : ∀ pair ∈ pairs, ∀ c, pair.2 ≠ .vreg key c)
    (run : pairs.foldl (tryAliasStep ps rets) (.ok (st, regs)) = .ok (next, out)) :
    (next.alias[key]?).join = (st.alias[key]?).join := by
  induction pairs generalizing st regs with
  | nil => cases run; rfl
  | cons pair pairs ih =>
    rw [List.foldl_cons] at run
    cases step : tryAliasStep ps rets (.ok (st, regs)) pair with
    | error e => rw [step, try_fold_error] at run; cases run
    | ok result =>
      rcases result with ⟨middle, rs⟩
      rw [step] at run
      have mb : (middle.alias[key]?).join = (st.alias[key]?).join := by
        unfold tryAliasStep at step
        simp only [bind, Except.bind] at step
        cases idx : ps.idxOf? pair.1 with
        | none => simp only [idx, pure, Except.pure] at step; cases step; rfl
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
              exact setAlias_entry (destinations pair (by simp)) alias
      exact (ih middle rs (fun pair mem => destinations pair (by simp [mem])) run).trans mb

private theorem delegate_entry {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V} {key : Nat}
    (run : (match Backend.externCtor ctx t args st.base with
      | .ok (v, base) => ExtResult.ok (v, { st with base })
      | .fail => ExtResult.fail
      | .unmodeled e => ExtResult.unmodeled e) = ExtResult.ok (v, next)) :
    (next.alias[key]?).join = (st.alias[key]?).join := by
  cases call : Backend.externCtor ctx t args st.base with
  | fail => rw [call] at run; cases run
  | unmodeled e => rw [call] at run; cases run
  | ok pair => rw [call] at run; cases run; rfl

private theorem marks_alias (st : State) (vs : List Nat) :
    (vs.foldl State.mark st).alias = st.alias := by
  induction vs generalizing st with
  | nil => rfl
  | cons x xs ih => exact ih (st.mark x)

/-- Actual constructors preserve every alias entry outside the exception
payload destinations, regardless of selected rule, incoming aliases or fuel. -/
theorem stock_ctor_aliasEntry {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V} {key : Nat}
    (payloads : ∀ r ∈ ctx.tryRegs.2, ∀ c, r ≠ .vreg key c)
    (run : Stock.externCtor ctx t args st = .ok (v, next)) :
    (next.alias[key]?).join = (st.alias[key]?).join := by
  unfold Stock.externCtor at run
  split at run
  all_goals dsimp only at run
  all_goals try solve | exact delegate_entry run
  all_goals
    repeat' first
    | (solve | cases run <;> rfl)
    | (solve | have h := delegate_entry (key := key) run; simpa only [State.mark, marks_alias] using h)
    | split at run
  rename_i _ _ sig _ _ ps _ _ s regs step
  cases run
  exact try_fold_entry ps ctx.tryRegs.1 ((payloadRegs sig.callConv).zip ctx.tryRegs.2) st []
    (fun pair mem => payloads pair.2 (List.of_mem_zip mem).2) step

/-- Nested term evaluation, matching failures and rollback preserve the same
entry. This uses the actual interpreter rather than a selected-path receipt. -/
theorem stock_apply_aliasEntry {p : Program} {ctx : Ctx} {cfg : Config}
    {n ty t : Nat} {args : List V} {st next : State} {tr tr' : Array RuleId}
    {out : Option V} {key : Nat}
    (payloads : ∀ r ∈ ctx.tryRegs.2, ∀ c, r ≠ .vreg key c)
    (run : (applyTerm p (Stock.sem ctx) cfg n ty t args).run (st, tr) =
      .ok (out, next, tr')) :
    (next.alias[key]?).join = (st.alias[key]?).join := by
  exact (presAt (R := fun a b : State => (b.alias[key]?).join = (a.alias[key]?).join)
    (fun _ => rfl) (fun _ _ _ ab bc => bc.trans ab)
    (fun _ _ _ _ _ ctor => stock_ctor_aliasEntry payloads ctor) n).apply
      ty t args st tr out next tr' run

private theorem fold_entry {α β γ : Type} (field : α → γ)
    (step : α → β → Except String α) (xs : List β) {a next : α}
    (keeps : ∀ b ∈ xs, ∀ input output, step input b = .ok output →
      field output = field input)
    (run : xs.foldlM step a = .ok next) : field next = field a := by
  induction xs generalizing a with
  | nil => cases run; rfl
  | cons b bs ih =>
    rw [List.foldlM_cons] at run
    cases call : step a b with
    | error e => simp only [call, bind, Except.bind] at run; cases run
    | ok middle =>
      simp only [call, bind, Except.bind] at run
      exact (ih (fun b mem => keeps b (List.mem_cons_of_mem _ mem)) run).trans
        (keeps b (by simp) a middle call)

/-- Actual ordered binding preserves an alias entry whenever none of its
source-result mappings names that destination. Physical-result copies preserve
all alias entries. -/
theorem stock_bindResults_aliasEntry {ctx : Ctx} {pairs : List (Nat × List Reg)}
    {st next : State} {copies : Array MInst} {key : Nat}
    (apart : ∀ pair ∈ pairs, ∀ r, ctx.valueReg? pair.1 = some r →
      ∀ c, r ≠ .vreg key c)
    (run : bindResults ctx pairs st = .ok (next, copies)) :
    (next.alias[key]?).join = (st.alias[key]?).join := by
  unfold bindResults at run
  apply fold_entry (fun a : State × Array MInst => (a.1.alias[key]?).join) _ pairs ?_ run
  intro pair member acc result step
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
        exact setAlias_entry (apart _ member r map) alias
    · cases step; rfl
    · cases step

/-- Actual initialization's injective typed source mapping discharges the
register exclusion from a different source-result ID. The driver still must
establish that the protected source ID is absent from later result lists. -/
theorem stock_bindResults_sourceAliasEntry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {x key : Nat} (mapped : ctx.valueReg? x = some (.vreg key .int))
    {pairs : List (Nat × List Reg)} (apart : ∀ pair ∈ pairs, pair.1 ≠ x)
    {st next : State} {copies : Array MInst}
    (run : bindResults ctx pairs st = .ok (next, copies)) :
    (next.alias[key]?).join = (st.alias[key]?).join := by
  apply stock_bindResults_aliasEntry ?_ run
  intro pair member r mapping c same
  have allocated := buildCtx_allocated build
  obtain ⟨n, reg, _⟩ := allocated.2.2.1 pair.1 r mapping
  subst r
  cases reg
  exact apart pair member (allocated.2.1 pair.1 x key mapping mapped)

/-- Actual initialization supplies the payload exclusion automatically for a
mapped source value. The chosen reservation slot is exactly the context update
used by block lowering; absent slots contain no payload destinations. -/
theorem stock_apply_sourceAliasEntry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {x key bi : Nat} (mapped : ctx.valueReg? x = some (.vreg key .int))
    {p : Program} {cfg : Config} {n ty t : Nat} {args : List V}
    {st next : State} {tr tr' : Array RuleId} {out : Option V}
    (run : (applyTerm p (Stock.sem { ctx with tryRegs := initial.tryRegs[bi]! })
      cfg n ty t args).run (st, tr) = .ok (out, next, tr')) :
    (next.alias[key]?).join = (st.alias[key]?).join := by
  apply stock_apply_aliasEntry ?_ run
  intro r member c same
  change r ∈ initial.tryRegs[bi]!.2 at member
  cases slot : initial.tryRegs[bi]? with
  | none =>
    simp only [getElem!_def, slot] at member
    change r ∈ ([] : List Reg) at member
    cases member
  | some rs =>
    have mem : r ∈ rs.1 ++ rs.2 := by
      apply List.mem_append.mpr
      right
      simpa only [getElem!_def, slot, Option.getD_some] using member
    have separate := buildCtx_valueReservedDisjoint build x (.vreg key .int)
      mapped bi rs slot r mem
    obtain ⟨k, reg, _⟩ := buildCtx_reservedBelow build bi rs slot r mem
    subst r
    cases reg
    exact separate rfl

private def entryCtx : Ctx :=
  { sinkCtx with tryRegs := ([.vreg 193 .int], [.vreg 194 .int, .vreg 195 .int]) }
private def entryInput : State :=
  { sinkState with
    base := { sinkState.base with nextVreg := 198 }
    alias := aliasStep #[] (193, 197) }
private def entryNext : State :=
  { entryInput with alias := aliasStep entryInput.alias (194, 193) }
private def entrySig : Clif.Signature := { returns := [⟨.i64, .none, .normal⟩] }
private def entryResult : V :=
  .op (.callRets [(.x 0, .vreg 193 .int), (.x 1, .vreg 195 .int)])
private theorem entryPayloads :
    ∀ r ∈ entryCtx.tryRegs.2, ∀ c, r ≠ .vreg 193 c := by
  intro r mem c
  simp only [entryCtx, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl <;> simp
private theorem entryRun :
    Stock.externCtor entryCtx T.gen_try_call_rets [.op (.sig entrySig)] entryInput =
      .ok (entryResult, entryNext) := rfl

/-- A real try-call constructor installs a nonempty payload alias while
preserving the older binding of 193 to fresh register 197. -/
theorem stock_ctor_aliasEntry_witness :
    Stock.externCtor entryCtx T.gen_try_call_rets [.op (.sig entrySig)] entryInput =
      .ok (entryResult, entryNext) ∧
      (∀ r ∈ entryCtx.tryRegs.2, ∀ c, r ≠ .vreg 193 c) ∧
      (entryInput.alias[193]?).join = some 197 ∧
      (entryNext.alias[194]?).join = some 193 ∧
      (entryNext.alias[193]?).join = (entryInput.alias[193]?).join :=
  ⟨entryRun, entryPayloads, by decide, by decide,
    stock_ctor_aliasEntry entryPayloads entryRun⟩

set_option maxRecDepth 16384 in
private theorem tryTerm : termOf program 300 = .ok T.gen_try_call_rets := by
  unfold termOf Isle.Aarch64.program
  rfl

/-- The actual exported external term provides an inhabited full-evaluation
premise and preserves the existing alias while changing another destination. -/
theorem stock_apply_aliasEntry_witness :
    (applyTerm program (Stock.sem entryCtx) {} 1 T.gen_try_call_rets.ret 300
      [.op (.sig entrySig)]).run (entryInput, #[]) =
        .ok (some entryResult, entryNext, #[]) ∧
      (∀ r ∈ entryCtx.tryRegs.2, ∀ c, r ≠ .vreg 193 c) ∧
      (entryInput.alias[193]?).join = some 197 ∧
      (entryNext.alias[194]?).join = some 193 ∧
      (entryNext.alias[193]?).join = (entryInput.alias[193]?).join := by
  have run : (applyTerm program (Stock.sem entryCtx) {} 1 T.gen_try_call_rets.ret 300
      [.op (.sig entrySig)]).run (entryInput, #[]) =
        .ok (some entryResult, entryNext, #[]) := by
    simp only [applyTerm.eq_2, tryTerm, Stock.sem, T.gen_try_call_rets, isel_data, isel_monad]
    have call := entryRun
    unfold T.gen_try_call_rets at call
    rw [call]
    rfl
  exact ⟨run, entryPayloads, by decide, by decide, stock_apply_aliasEntry entryPayloads run⟩

private def sourceFunction : Clif.Function := {
  name := "source_alias_entry"
  sig := {
    params := [⟨.i64, .none, .normal⟩, ⟨.i64, .none, .normal⟩]
    returns := [⟨.i64, .none, .normal⟩] }
  blocks := [{ id := 0, params := [(0, .i64), (1, .i64)], term := .ret [0] }] }
private def sourceBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx sourceFunction).toOption.getD (sinkCtx, #[], sinkState)
private def sourceBase : LState :=
  ((((sourceBuilt.2.2.base.fresh .int).2.fresh .int).2.fresh .int).2.fresh .int).2
private def sourceInput : State :=
  { sourceBuilt.2.2 with base := sourceBase, alias := aliasStep #[] (192, 196) }
private def sourceNext : State :=
  { sourceInput with base := (sourceInput.base.fresh .int).2 }
private def sourceResult : V := .regsVec [[.vreg 198 .int]]

set_option maxRecDepth 16384 in
private theorem callTerm : termOf program 296 = .ok T.gen_call_output := by
  unfold termOf Isle.Aarch64.program
  rfl

/-- Actual source initialization maps value 0 to register 192. Subsequent real
call-output evaluation allocates register 198 and preserves 192's older alias to
196, with no supplied exception-payload exclusion premise. -/
theorem stock_apply_sourceAliasEntry_witness :
    Stock.buildCtx sourceFunction = .ok sourceBuilt ∧
      sourceBuilt.1.valueReg? 0 = some (.vreg 192 .int) ∧
      (applyTerm program
        (Stock.sem { sourceBuilt.1 with tryRegs := sourceBuilt.2.2.tryRegs[0]! })
        {} 1 T.gen_call_output.ret T.gen_call_output.id [.op (.sig entrySig)]).run
        (sourceInput, #[]) = .ok (some sourceResult, sourceNext, #[]) ∧
      sourceNext.base.nextVreg = sourceInput.base.nextVreg + 1 ∧
      (sourceInput.alias[192]?).join = some 196 ∧
      (sourceNext.alias[192]?).join = (sourceInput.alias[192]?).join := by
  have build : Stock.buildCtx sourceFunction = .ok sourceBuilt := rfl
  have mapped : sourceBuilt.1.valueReg? 0 = some (.vreg 192 .int) := rfl
  have run : (applyTerm program
      (Stock.sem { sourceBuilt.1 with tryRegs := sourceBuilt.2.2.tryRegs[0]! })
      {} 1 T.gen_call_output.ret T.gen_call_output.id [.op (.sig entrySig)]).run
      (sourceInput, #[]) = .ok (some sourceResult, sourceNext, #[]) := by
    simp only [applyTerm.eq_2, callTerm, Stock.sem, T.gen_call_output, isel_data, isel_monad]
    rfl
  exact ⟨build, mapped, run, rfl, by decide, stock_apply_sourceAliasEntry build mapped run⟩

private def bindingNext : State :=
  { sourceInput with alias := aliasStep sourceInput.alias (193, 197) }
private theorem bindingRun :
    bindResults sourceBuilt.1 [(1, [Reg.vreg 197 .int])] sourceInput = .ok (bindingNext, #[]) := rfl
private theorem bindingApart :
    ∀ pair ∈ [(1, [Reg.vreg 197 .int])], ∀ r, sourceBuilt.1.valueReg? pair.1 = some r →
      ∀ c, r ≠ .vreg 192 c := by
  intro pair member r mapping c same
  have equal := List.mem_singleton.mp member
  subst pair
  change some (.vreg 193 .int) = some r at mapping
  cases mapping
  cases same

/-- Actual binding installs a distinct source-result alias while retaining the
protected source's older nonempty binding. -/
theorem stock_bindResults_aliasEntry_witness :
    bindResults sourceBuilt.1 [(1, [Reg.vreg 197 .int])] sourceInput = .ok (bindingNext, #[]) ∧
      (∀ pair ∈ [(1, [Reg.vreg 197 .int])], ∀ r, sourceBuilt.1.valueReg? pair.1 = some r →
        ∀ c, r ≠ .vreg 192 c) ∧
      (bindingNext.alias[193]?).join = some 197 ∧
      (sourceInput.alias[192]?).join = some 196 ∧
      (bindingNext.alias[192]?).join = (sourceInput.alias[192]?).join :=
  ⟨bindingRun, bindingApart, by decide, by decide,
    stock_bindResults_aliasEntry bindingApart bindingRun⟩

/-- A successful actual build, protected source mapping and nonempty different
result list satisfy all premises of the source-ID binding frame theorem. -/
theorem stock_bindResults_sourceAliasEntry_witness :
    Stock.buildCtx sourceFunction = .ok sourceBuilt ∧
      sourceBuilt.1.valueReg? 0 = some (.vreg 192 .int) ∧
      (∀ pair ∈ [(1, [Reg.vreg 197 .int])], pair.1 ≠ (0 : Nat)) ∧
      bindResults sourceBuilt.1 [(1, [Reg.vreg 197 .int])] sourceInput = .ok (bindingNext, #[]) ∧
      (bindingNext.alias[193]?).join = some 197 ∧
      (bindingNext.alias[192]?).join = (sourceInput.alias[192]?).join := by
  have build : Stock.buildCtx sourceFunction = .ok sourceBuilt := rfl
  have mapped : sourceBuilt.1.valueReg? 0 = some (.vreg 192 .int) := rfl
  have apart : ∀ pair ∈ [(1, [Reg.vreg 197 .int])], pair.1 ≠ (0 : Nat) := by simp
  exact ⟨build, mapped, apart, bindingRun, by decide,
    stock_bindResults_sourceAliasEntry build mapped apart bindingRun⟩

end Backend.Stock.Proof

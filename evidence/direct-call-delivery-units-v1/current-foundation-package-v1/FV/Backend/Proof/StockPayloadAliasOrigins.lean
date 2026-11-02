import FV.Backend.Proof.LowerLoopCode
import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.StockReservedTerminal

/-! Only actual try-call return registers can be new constructor alias targets.
This is the target-origin ingredient for reserved-payload chain termination. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- A selected alias entry points only into the allowed return-register set. -/
def EntryAllowed (allowed : Nat → Prop) (key : Nat) (st : State) : Prop :=
  ∀ n, (st.alias[key]?).join = some n → allowed n

private theorem setAlias_allowed {allowed : Nat → Prop} {key : Nat} {st next : State}
    {dst src : Reg} (old : EntryAllowed allowed key st)
    (source : ∃ n, src = .vreg n .int ∧ allowed n)
    (run : st.setAlias dst src = .ok next) : EntryAllowed allowed key next := by
  obtain ⟨m, rfl, permitted⟩ := source
  cases dst <;> simp only [State.setAlias, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at run
  all_goals try solve | cases run
  rename_i n c
  split at run
  · cases run
  · cases run
    intro target entry
    change ((aliasStep st.alias (n, m))[key]?).join = some target at entry
    rw [aliasStep_get] at entry
    by_cases same : key = n
    · simp only [same, ite_true, Option.some.injEq] at entry
      subst target
      exact permitted
    · simp only [same, ite_false] at entry
      exact old target entry

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

private theorem try_fold_allowed {allowed : Nat → Prop} {key : Nat}
    (ps rets : List Reg) (pairs : List (Reg × Reg))
    (st : State) (regs : List Reg) {next : State} {out : List Reg}
    (old : EntryAllowed allowed key st)
    (returns : ∀ r ∈ rets, ∃ n, r = .vreg n .int ∧ allowed n)
    (run : pairs.foldl (tryAliasStep ps rets) (.ok (st, regs)) = .ok (next, out)) :
    EntryAllowed allowed key next := by
  induction pairs generalizing st regs with
  | nil => cases run; exact old
  | cons pair pairs ih =>
    rw [List.foldl_cons] at run
    cases call : tryAliasStep ps rets (.ok (st, regs)) pair with
    | error e => rw [call, try_fold_error] at run; cases run
    | ok result =>
      rcases result with ⟨middle, rs⟩
      rw [call] at run
      have kept : EntryAllowed allowed key middle := by
        unfold tryAliasStep at call
        simp only [bind, Except.bind] at call
        cases idx : ps.idxOf? pair.1 with
        | none => simp only [idx, pure, Except.pure] at call; cases call; exact old
        | some i =>
          simp only [idx] at call
          cases ret : rets[i]? with
          | none => simp only [ret] at call; cases call
          | some r =>
            simp only [ret] at call
            cases alias : st.setAlias pair.2 r with
            | error e => rw [alias] at call; cases call
            | ok q =>
              rw [alias] at call
              simp only [pure, Except.pure] at call
              cases call
              exact setAlias_allowed old (returns r (List.mem_of_getElem? ret)) alias
      exact ih middle rs kept run

private theorem delegate_entry {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V} {key : Nat}
    (run : (match Backend.externCtor ctx t args st.base with
      | .ok (v, base) => ExtResult.ok (v, {st with base})
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

/-- Actual external constructors preserve allowed alias targets: every new
entry comes from a current try-call return register. -/
theorem stock_ctor_aliasTargetsAllowed {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V} {allowed : Nat → Prop} {key : Nat}
    (old : EntryAllowed allowed key st)
    (returns : ∀ r ∈ ctx.tryRegs.1, ∃ n, r = .vreg n .int ∧ allowed n)
    (run : Stock.externCtor ctx t args st = .ok (v, next)) : EntryAllowed allowed key next := by
  unfold Stock.externCtor at run
  split at run
  all_goals dsimp only at run
  all_goals try solve |
    intro target entry
    exact old target ((delegate_entry run).symm.trans entry)
  all_goals
    repeat' first
    | (solve | cases run <;> exact old)
    | (solve |
        have h := delegate_entry (key := key) run
        simp only [State.mark, marks_alias] at h
        intro target entry
        exact old target (h.symm.trans entry))
    | split at run
  rename_i _ _ sig _ _ ps _ _ s regs step
  cases run
  exact try_fold_allowed ps ctx.tryRegs.1 ((payloadRegs sig.callConv).zip ctx.tryRegs.2) st [] old returns step

/-- Actual nested helper evaluation preserves the same allowed-target invariant. -/
theorem stock_apply_aliasTargetsAllowed {p : Program} {ctx : Ctx} {cfg : Config}
    {n ty t : Nat} {args : List V} {st next : State} {tr tr' : Array RuleId}
    {out : Option V} {allowed : Nat → Prop} {key : Nat}
    (old : EntryAllowed allowed key st)
    (returns : ∀ r ∈ ctx.tryRegs.1, ∃ k, r = .vreg k .int ∧ allowed k)
    (run : (applyTerm p (Stock.sem ctx) cfg n ty t args).run (st, tr) = .ok (out, next, tr')) :
    EntryAllowed allowed key next := by
  have kept := (presAt
    (R := fun a b : State => EntryAllowed allowed key a → EntryAllowed allowed key b)
    (fun _ => id) (fun _ _ _ ab bc h => bc (ab h))
    (fun _ _ _ _ _ ctor h => stock_ctor_aliasTargetsAllowed h returns ctor) n).apply
      ty t args st tr out next tr' run
  exact kept old

private theorem named_allowed {ctx : Ctx} {term : String} {args : List V}
    {st next : State} {out : Option V} {trace : List RuleId} {key : Nat} {allowed : Nat → Prop}
    (old : EntryAllowed allowed key st)
    (returns : ∀ r ∈ ctx.tryRegs.1, ∃ k, r = .vreg k .int ∧ allowed k)
    (h : Stock.runTerm ctx term args st = .ok (out, next, trace)) :
    EntryAllowed allowed key next := by
  unfold Stock.runTerm at h
  cases hr : Isle.Interp.run program (Stock.sem ctx) {} term args st with
  | error e => rw [hr] at h; cases h
  | ok result =>
    rw [hr] at h
    cases h
    unfold Isle.Interp.run at hr
    cases ht : program.termByName? term with
    | none => simp only [ht] at hr; cases hr
    | some t =>
      simp only [ht] at hr
      cases ha : (applyTerm program (Stock.sem ctx) {} (Config.fuel ({} : Config))
          t.ret t.id args).run (st, #[]) with
      | error e => simp only [ha, bind, Except.bind] at hr; cases hr
      | ok result =>
        rcases result with ⟨out, next, trace⟩
        simp only [ha, bind, Except.bind, pure, Except.pure] at hr
        cases hr
        exact stock_apply_aliasTargetsAllowed old returns ha


private theorem emitted_allowed {ctx : Ctx} {i : Nat} {st : State}
    {emission : Emission} {key : Nat} {allowed : Nat → Prop}
    (old : EntryAllowed allowed key st)
    (returns : ∀ r ∈ ctx.tryRegs.1, ∃ k, r = .vreg k .int ∧ allowed k)
    (mapped : ∀ x ∈ ctx.insts[i]!.results, ∀ r,
      ctx.valueReg? x = some r → ∀ c, r ≠ .vreg key c)
    (h : emitInstruction ctx i st = .ok emission) :
    EntryAllowed allowed key emission.state := by
  unfold emitInstruction at h
  cases hr : Stock.runTerm ctx "lower" [.inst i] st with
  | error e => simp only [hr, bind, Except.bind] at h; cases h
  | ok root =>
    rcases root with ⟨out, next, trace⟩
    simp only [hr, bind, Except.bind] at h
    cases out with
    | none => cases h
    | some out =>
      cases out <;> try (cases h)
      rename_i rss
      dsimp only at h
      split at h
      · cases h
      · cases hb : bindResults ctx (ctx.insts[i]!.results.zip rss) next with
        | error e => simp only [hb] at h; cases h
        | ok result =>
          rcases result with ⟨final, copies⟩
          simp only [hb, pure, Except.pure] at h
          cases h
          have bound := stock_bindResults_aliasEntry
            (key := key) (fun pair member r hr c => mapped pair.1 (List.of_mem_zip member).1 r hr c) hb
          have kept := named_allowed old returns hr
          intro target entry
          exact kept target (bound.symm.trans entry)

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


private theorem opportunity_values_entry {ctx : Ctx} {values : List Nat}
    {st next : State} {key : Nat}
    (mapped : ∀ x ∈ values, ∀ r, ctx.valueReg? x = some r → ∀ c, r ≠ .vreg key c)
    (h : commitOpportunisticValues ctx values st = .ok next) :
    (next.alias[key]?).join = (st.alias[key]?).join := by
  unfold commitOpportunisticValues at h
  apply fold_entry (fun s : State => (s.alias[key]?).join) _ values ?_ h
  intro v member a b step
  split at step
  · split at step
    · rename_i dst hdst
      split at step
      · rename_i src _
        cases hs : a.setAlias dst src with
        | error e => simp only [hs, bind, Except.bind] at step; cases step
        | ok q =>
          simp only [hs, bind, Except.bind, pure, Except.pure] at step
          cases step
          exact setAlias_entry (next := q) (mapped v member dst hdst) hs
      · cases step
    · cases step
  · cases step; rfl

private theorem opportunity_entry {ctx : Ctx} {block i : Nat}
    {st next : State} {key : Nat}
    (mapped : ∀ x ∈ ctx.insts[i]!.results, ∀ r,
      ctx.valueReg? x = some r → ∀ c, r ≠ .vreg key c)
    (h : commitOpportunistic ctx block i st = .ok (some next)) :
    (next.alias[key]?).join = (st.alias[key]?).join := by
  unfold commitOpportunistic at h
  dsimp only at h
  split at h
  · cases h
  · cases hv : commitOpportunisticValues ctx (ctx.insts[i]!.results) st with
    | error e => simp only [hv, bind, Except.bind] at h; cases h
    | ok q =>
      simp only [hv, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact opportunity_values_entry mapped hv

private theorem scan_state_entry (st : State) (i key : Nat) :
    ((scanState st i).alias[key]?).join = (st.alias[key]?).join := by
  unfold scanState
  dsimp only
  split <;> rfl

private theorem scan_allowed {ctx : Ctx} {block i ti : Nat} {branch : Bool}
    {st : State} {output : Scan} {key : Nat} {allowed : Nat → Prop}
    (old : EntryAllowed allowed key st)
    (returns : ∀ r ∈ ctx.tryRegs.1, ∃ k, r = .vreg k .int ∧ allowed k)
    (mapped : ∀ x ∈ ctx.insts[i]!.results, ∀ r,
      ctx.valueReg? x = some r → ∀ c, r ≠ .vreg key c)
    (h : scanInstruction ctx block i ti branch st = .ok output) :
    EntryAllowed allowed key output.state := by
  have before := scan_state_entry st i key
  have oldBefore : EntryAllowed allowed key (scanState st i) := by
    intro target entry
    exact old target (before.symm.trans entry)
  have emit (h : (emitInstruction ctx i (scanState st i) >>= fun e =>
      pure (e.scan block i (scanState st i))) = .ok output) :
      EntryAllowed allowed key output.state := by
    cases he : emitInstruction ctx i (scanState st i) with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok e =>
      simp only [he, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact emitted_allowed oldBefore returns mapped he
  unfold scanInstruction at h
  dsimp only at h
  generalize hm : (if i == ti then true else ctx.insts[i]!.clif.any mustLower) = mandatory at h
  split at h
  · cases h; exact old
  · split at h
    · cases h; exact oldBefore
    · split at h
      · cases h; exact oldBefore
      · split at h
        · cases hc : commitOpportunistic ctx block i (scanState st i) with
          | error e => simp only [hc, bind, Except.bind] at h; cases h
          | ok result =>
            simp only [hc, bind, Except.bind] at h
            cases result with
            | none => exact emit h
            | some q =>
              cases h
              have kept := opportunity_entry (key := key) mapped hc
              intro target entry
              exact oldBefore target (kept.symm.trans entry)
        · exact emit h

private theorem scanBlock_allowed {ctx : Ctx} {block ti : Nat} {branch : Bool}
    {indices : List Nat} {st : State} {output : BlockScan} {key : Nat} {allowed : Nat → Prop}
    (old : EntryAllowed allowed key st)
    (returns : ∀ r ∈ ctx.tryRegs.1, ∃ k, r = .vreg k .int ∧ allowed k)
    (mapped : ∀ i ∈ indices, ∀ x ∈ ctx.insts[i]!.results, ∀ r,
      ctx.valueReg? x = some r → ∀ c, r ≠ .vreg key c)
    (h : scanBlock ctx block ti branch indices st = .ok output) :
    EntryAllowed allowed key output.state := by
  have cert := runScans_spec h
  clear h
  induction cert with
  | nil st => exact old
  | cons head rest ih =>
    exact ih (scan_allowed old returns (mapped _ (List.mem_cons_self ..)) head)
      (fun i mem => mapped i (List.mem_cons_of_mem _ mem))

/-- A target allocated as a return in an actual initial reservation slot. -/
def ReservedReturn (initial : State) (target : Nat) : Prop :=
  ∃ (owner : Nat) (rs : List Reg × List Reg), initial.tryRegs[owner]? = some rs ∧ (Reg.vreg target .int) ∈ rs.1

section Traversal
attribute [local irreducible] Stock.runTerm emitBranch scanBlock

private theorem returns_allowed {f : Clif.Function} {source ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} {slot : Nat}
    (build : Stock.buildCtx f = .ok (source, ranges, initial))
    (reserved : ctx.tryRegs = initial.tryRegs[slot]!) :
    ∀ r ∈ ctx.tryRegs.1, ∃ n, r = .vreg n .int ∧ ReservedReturn initial n := by
  intro r member
  rw [reserved] at member
  cases lookup : initial.tryRegs[slot]? with
  | none => simp only [getElem!_def, lookup] at member; cases member
  | some rs =>
    have mem : r ∈ rs.1 := by simpa only [getElem!_def, lookup, Option.getD_some] using member
    obtain ⟨n, reg, _⟩ := buildCtx_reservedBelow build slot rs lookup r (List.mem_append_left _ mem)
    exact ⟨n, reg, slot, rs, lookup, by simpa only [reg] using mem⟩

private theorem payload_source_apart {f : Clif.Function} {source ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} {owner key : Nat} {rs : List Reg × List Reg}
    (build : Stock.buildCtx f = .ok (source, ranges, initial))
    (lookup : initial.tryRegs[owner]? = some rs) (member : (.vreg key .int) ∈ rs.2)
    (values : ∀ x, ctx.valueReg? x = source.valueReg? x) :
    ∀ x r, ctx.valueReg? x = some r → ∀ c, r ≠ .vreg key c := by
  intro x r mapped c equal
  rw [values] at mapped
  obtain ⟨n, reg, _⟩ := (buildCtx_allocated build).2.2.1 x r mapped
  have classes : (.int : RegClass) = c := (Reg.vreg.inj (reg.symm.trans equal)).2
  subst c
  exact buildCtx_valueReservedDisjoint build x r mapped owner rs lookup
    (.vreg key .int) (List.mem_append_right _ member) equal

private theorem branch_allowed {ctx : Ctx} {f : Clif.Function} {t : Clif.Terminator}
    {bi ti : Nat} {targets : Array Nat} {input : State} {output : BranchEmission} {key : Nat} {allowed : Nat → Prop}
    (old : EntryAllowed allowed key input)
    (returns : ∀ r ∈ ctx.tryRegs.1, ∃ n, r = .vreg n .int ∧ allowed n)
    (run : emitBranch ctx f t bi ti targets input = .ok output) :
    EntryAllowed allowed key output.state := by
  unfold emitBranch at run
  dsimp only at run
  let before := { input with current := some ti, color := none, base.emitted := #[] }
  change ((do
    let (out, next, fired) ← Stock.runTerm ctx "lower_branch" [.inst ti, .labels targets.toList] before
    if out.isNone then throw s!"no lowering rule for terminator {repr t}"
    let code ← branchCode f t targets next.base.emitted
    pure ⟨next, code, ⟨bi, ti, .emitted, before, next, [], fired, code⟩, fired⟩) : Except String BranchEmission) = .ok output at run
  cases root : Stock.runTerm ctx "lower_branch" [.inst ti, .labels targets.toList] before with
  | error e => simp only [root, bind, Except.bind] at run; cases run
  | ok result =>
    rcases result with ⟨out, next, fired⟩
    simp only [root, bind, Except.bind] at run
    split at run
    · cases run
    · cases code : branchCode f t targets next.base.emitted with
      | error e => simp only [code] at run; cases run
      | ok instructions =>
        simp only [code, pure, Except.pure] at run
        cases run
        have same := named_allowed (st := before) old returns root
        exact same

private theorem core_allowed {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
     {owner key bi : Nat} {rs : List Reg × List Reg}
    (lookup : initial.tryRegs[owner]? = some rs) (member : (.vreg key .int) ∈ rs.2)
    {second : Clif.Block} {start stop : Nat}
    {order : Order} {data : V} {targets : Array Nat} {input : State} {output : LoweredBlockCore}
    (reservations : input.tryRegs = initial.tryRegs)
    (old : EntryAllowed (ReservedReturn initial) key input)
    (run : lowerBlockCore ctx order f second bi start stop data targets input = .ok output) :
    EntryAllowed (ReservedReturn initial) key output.state := by
  let ti := stop - 1
  let selected := { Driver.termCtx ctx ti data with tryRegs := input.tryRegs[ti]! }
  let branch : Bool := match second.term with | .ret .. | .trap .. | .returnCall .. => false | _ => true
  let branchCall : Except String (Option BranchEmission) :=
    if branch then some <$> emitBranch selected f second.term bi ti targets input else pure none
  have returns := returns_allowed (ctx := selected) (slot := ti) build
    (by simp only [selected, reservations])
  have branchKeeps {br : Option BranchEmission} (call : branchCall = .ok br) :
      EntryAllowed (ReservedReturn initial) key ((br.map (·.state)).getD input) := by
    unfold branchCall at call
    split at call
    · cases emitted : emitBranch selected f second.term bi ti targets input with
      | error e => simp only [emitted, Functor.map, Except.map] at call; cases call
      | ok e =>
        simp only [emitted, Functor.map, Except.map] at call
        cases call
        exact branch_allowed old returns emitted
    · cases call; exact old
  have normal : lowerBlockCore ctx order f second bi start stop data targets input = (do
      let br ← branchCall
      let (next, outgoing) ← collectOutgoing ctx order bi targets (br.map (·.state) |>.getD input)
      let before := { next with color := some next.endColor[bi]! }
      let indices := ((Array.range (stop - start)).map (start + ·)).reverse.toList
      let body ← scanBlock selected bi ti branch indices before
      pure ⟨body.state, body.code ++ (br.map (·.code) |>.getD #[]), outgoing,
        br, ⟨selected, bi, ti, branch, indices, before, body⟩⟩) := by
    unfold lowerBlockCore
    dsimp only [branchCall, branch, selected, ti, Driver.termCtx]
    split <;> simp_all only [branch, selected, ti] <;> rfl
  rw [normal] at run
  cases call : branchCall with
  | error e => simp only [call, bind, Except.bind] at run; cases run
  | ok br =>
    simp only [call, bind, Except.bind] at run
    cases edges : collectOutgoing ctx order bi targets (br.map (·.state) |>.getD input) with
    | error e => simp only [edges] at run; cases run
    | ok pair =>
      rcases pair with ⟨next, outgoing⟩
      simp only [edges] at run
      let before := { next with color := some next.endColor[bi]! }
      let indices := ((Array.range (stop - start)).map (start + ·)).reverse.toList
      have keeps : EntryAllowed (ReservedReturn initial) key before := by
        have unchanged := congrArg (fun a => (a[key]?).join) (stock_collectOutgoing_alias edges)
        have kept := branchKeeps call
        intro target entry
        exact kept target (unchanged.symm.trans entry)
      change (scanBlock selected bi ti branch indices before >>= fun body =>
        pure (⟨body.state, body.code ++ (br.map (·.code) |>.getD #[]), outgoing,
          br, ⟨selected, bi, ti, branch, indices, before, body⟩⟩ : LoweredBlockCore)) = .ok output at run
      cases scan : scanBlock selected bi ti branch indices before with
      | error e => simp only [scan, bind, Except.bind] at run; cases run
      | ok body =>
        simp only [scan, bind, Except.bind, pure, Except.pure] at run
        cases run
        exact scanBlock_allowed (st := before) keeps returns
          (fun i _ x _ r mapping c => payload_source_apart (ctx := selected) build lookup member
            (fun _ => rfl) x r mapping c) scan

private theorem node_allowed {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) 
    {owner key : Nat} {rs : List Reg × List Reg}
    (lookup : initial.tryRegs[owner]? = some rs) (member : (.vreg key .int) ∈ rs.2)
    {order : Order} {params : List Nat} {label : Nat} {input output : DriverState}
    (reservations : input.state.tryRegs = initial.tryRegs)
    (old : EntryAllowed (ReservedReturn initial) key input.state)
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    EntryAllowed (ReservedReturn initial) key output.state := by
  cases node : order.nodes[label]! with
  | edge pred k target =>
    unfold lowerNode at run
    simp only [node] at run
    cases args : branchArgs ctx input.state pred k with
    | error e => simp only [args, bind, Except.bind] at run; cases run
    | ok pair =>
      rcases pair with ⟨args, next⟩
      simp only [args, bind, Except.bind, pure, Except.pure] at run
      cases run
      have unchanged := congrArg (fun a => (a[key]?).join) (stock_branchArgs_alias args)
      intro target entry
      exact old target (unchanged.symm.trans entry)
  | original bi =>
    let b := f.blocks[bi]!
    let start := ranges[bi]!.1
    let stop := ranges[bi]!.2
    let fetchData : Except String V := match b.term with
      | .tryCall .. | .tryCallIndirect .. => tryCallData f b.term
      | _ => termData (abiTerm f b.term)
    let reject : Bool := (match b.term with | .ret .. => true | _ => false) &&
      (sretRet f).isEmpty && (sigRets f.sig != f.sig.returns)
    have normal : lowerNode ctx ranges order f params label input = (do
        let data ← fetchData
        if reject then throw "sret parameter is not an entry-block parameter"
        let lowered ← lowerBlockCore ctx order f b bi start stop data order.successors[label]! input.state
        let assembled ← assembleOriginalBlock ctx f b bi label order.successors[label]!
          lowered.outgoing params lowered.state.uses lowered.code
        pure { recordCore input lowered bi stop with
          blocks := input.blocks.set! label assembled,
          edgeArgs := input.edgeArgs.set! label lowered.outgoing }) := by
      unfold lowerNode
      simp only [node]
      dsimp only [fetchData, reject, b, start, stop]
      split <;> simp_all only [reject] <;> rfl
    rw [normal] at run
    cases dataRun : fetchData with
    | error e => simp only [dataRun, bind, Except.bind] at run; cases run
    | ok data =>
      simp only [dataRun, bind, Except.bind] at run
      split at run
      · cases run
      · cases core : lowerBlockCore ctx order f b bi start stop data order.successors[label]! input.state with
        | error e => simp only [core] at run; cases run
        | ok lowered =>
          simp only [core] at run
          cases assembled : assembleOriginalBlock ctx f b bi label order.successors[label]!
              lowered.outgoing params lowered.state.uses lowered.code with
          | error e => simp only [assembled] at run; cases run
          | ok block =>
            simp only [assembled, pure, Except.pure] at run
            cases run
            exact core_allowed build lookup member reservations old core

private theorem traversal_allowed {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) 
    {owner key : Nat} {rs : List Reg × List Reg}
    (lookup : initial.tryRegs[owner]? = some rs) (member : (.vreg key .int) ∈ rs.2)
    {order : Order} {params labels : List Nat} {input output : DriverState}
    (bound : input.state.alias.size ≤ initial.base.nextVreg ∧
      initial.base.nextVreg ≤ input.state.base.nextVreg ∧ input.state.tryRegs = initial.tryRegs)
    (old : EntryAllowed (ReservedReturn initial) key input.state)
    (run : labels.foldlM (fun d label => lowerNode ctx ranges order f params label d) input = .ok output) :
    EntryAllowed (ReservedReturn initial) key output.state := by
  induction labels generalizing input with
  | nil => cases run; exact old
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call, bind, Except.bind] at run; cases run
    | ok next =>
      simp only [call, bind, Except.bind] at run
      exact ih (stock_lowerNode_allocationBounds build bound call)
        (node_allowed build lookup member bound.2.2 old call) run


/-- Every final alias from an initially reserved payload targets an initially
reserved return. Source writes cannot change that payload entry. -/
theorem stock_lower_payload_aliasOrigin {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {owner key : Nat} {rs : List Reg × List Reg}
    (lookup : result.initial.tryRegs[owner]? = some rs) (member : (.vreg key .int) ∈ rs.2)
    {target : Nat} (entry : (result.final.alias[key]?).join = some target) :
    ReservedReturn result.initial target := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  change built.2.2.tryRegs[owner]? = some rs at lookup
  have initial : built.2.2.alias = #[] := by
    obtain ⟨original, before, requests, _, _, same⟩ := buildCtx_allocation hbuild
    exact congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2.alias) same
  have bound : built.2.2.alias.size ≤ built.2.2.base.nextVreg ∧
      built.2.2.base.nextVreg ≤ built.2.2.base.nextVreg ∧ built.2.2.tryRegs = built.2.2.tryRegs :=
    ⟨by rw [initial]; exact Nat.zero_le _, Nat.le_refl _, rfl⟩
  have empty : EntryAllowed (ReservedReturn built.2.2) key built.2.2 := by
    intro n entry
    rw [initial] at entry
    cases entry
  exact traversal_allowed hbuild lookup member bound empty hdriver target entry

end Traversal
/-- Any installed payload alias resolves to its actual reserved return target. -/
theorem stock_lower_payload_resolves {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {owner key : Nat} {rs : List Reg × List Reg}
    (lookup : result.initial.tryRegs[owner]? = some rs) (member : (.vreg key .int) ∈ rs.2)
    {target : Nat} (entry : (result.final.alias[key]?).join = some target) :
    aliasNum result.final.alias key = target := by
  obtain ⟨slot, returns, allocated, returned⟩ := stock_lower_payload_aliasOrigin run lookup member entry
  exact stock_lower_reservedReturn_resolves run allocated returned entry

/-- Every initially reserved payload resolves to an unaliased final endpoint,
including payloads that were never aliased. No chain-validity check is assumed. -/
theorem stock_lower_payload_terminal {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {owner key : Nat} {rs : List Reg × List Reg}
    (lookup : result.initial.tryRegs[owner]? = some rs) (member : (.vreg key .int) ∈ rs.2) :
    (result.final.alias[aliasNum result.final.alias key]?).join = none := by
  cases entry : (result.final.alias[key]?).join with
  | none =>
    have resolved : aliasNum result.final.alias key = key := chaseF_none entry _
    rw [resolved]
    exact entry
  | some target =>
    rw [stock_lower_payload_resolves run lookup member entry]
    obtain ⟨slot, returns, allocated, returned⟩ := stock_lower_payload_aliasOrigin run lookup member entry
    exact (stock_lower_reservedReturn_terminal run allocated returned).1

/-- Transport an already-held value through an actual final payload alias.
Execution establishing the return value remains a separate obligation. -/
theorem stock_lower_payload_value {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {owner key : Nat} {rs : List Reg × List Reg}
    (lookup : result.initial.tryRegs[owner]? = some rs) (member : (.vreg key .int) ∈ rs.2)
    {target : Nat} (entry : (result.final.alias[key]?).join = some target)
    {regs : Nat → CV} {value : Clif.Val} (held : VHolds value (regs target)) :
    VHolds value (regs (aliasNum result.final.alias key)) := by
  rw [stock_lower_payload_resolves run lookup member entry]
  exact held

private def targetCtx : Ctx :=
  { sinkCtx with tryRegs := ([.vreg 193 .int], [.vreg 194 .int, .vreg 195 .int]) }
private def targetInput : State :=
  { sinkState with base := { sinkState.base with nextVreg := 198 }, alias := aliasStep #[] (194, 197) }
private def targetNext : State :=
  { targetInput with alias := aliasStep targetInput.alias (194, 193) }
private def targetSig : Clif.Signature := { returns := [⟨.i64, .none, .normal⟩] }
private def targetResult : V :=
  .op (.callRets [(.x 0, .vreg 193 .int), (.x 1, .vreg 195 .int)])
private def targetAllowed (n : Nat) : Prop := n = 193 ∨ n = 197
private theorem targetOld : EntryAllowed targetAllowed 194 targetInput := by
  intro n entry
  have old : (targetInput.alias[194]?).join = some 197 := by decide +kernel
  rw [old] at entry
  cases entry
  exact Or.inr rfl
private theorem targetReturns :
    ∀ r ∈ targetCtx.tryRegs.1, ∃ n, r = .vreg n .int ∧ targetAllowed n := by
  intro r member
  simp only [targetCtx, List.mem_cons, List.not_mem_nil, or_false] at member
  subst r
  exact ⟨193, rfl, Or.inl rfl⟩
private theorem targetRun :
    Stock.externCtor targetCtx T.gen_try_call_rets [.op (.sig targetSig)] targetInput =
      .ok (targetResult, targetNext) := rfl

/-- An actual constructor overwrites an existing payload alias197 with return193;
both the incoming allowed-target premise and reservation premise are inhabited. -/
theorem stock_ctor_aliasTargetsAllowed_witness :
    Stock.externCtor targetCtx T.gen_try_call_rets [.op (.sig targetSig)] targetInput =
      .ok (targetResult, targetNext) ∧
    EntryAllowed targetAllowed 194 targetInput ∧
    (∀ r ∈ targetCtx.tryRegs.1, ∃ n, r = .vreg n .int ∧ targetAllowed n) ∧
    (targetInput.alias[194]?).join = some 197 ∧
    (targetNext.alias[194]?).join = some 193 ∧ EntryAllowed targetAllowed 194 targetNext :=
  ⟨targetRun, targetOld, targetReturns, by decide +kernel, by decide +kernel,
    stock_ctor_aliasTargetsAllowed targetOld targetReturns targetRun⟩

set_option maxRecDepth 16384 in
private theorem tryTerm : termOf program 300 = .ok T.gen_try_call_rets := by
  unfold termOf Isle.Aarch64.program
  rfl

/-- The real exported helper evaluates successfully and installs the same alias. -/
theorem stock_apply_aliasTargetsAllowed_witness :
    (applyTerm program (Stock.sem targetCtx) {} 1 T.gen_try_call_rets.ret 300
      [.op (.sig targetSig)]).run (targetInput, #[]) =
        .ok (some targetResult, targetNext, #[]) ∧
    EntryAllowed targetAllowed 194 targetInput ∧
    (∀ r ∈ targetCtx.tryRegs.1, ∃ n, r = .vreg n .int ∧ targetAllowed n) ∧
    (targetNext.alias[194]?).join = some 193 ∧ EntryAllowed targetAllowed 194 targetNext := by
  have run : (applyTerm program (Stock.sem targetCtx) {} 1 T.gen_try_call_rets.ret 300
      [.op (.sig targetSig)]).run (targetInput, #[]) =
        .ok (some targetResult, targetNext, #[]) := by
    simp only [applyTerm.eq_2, tryTerm, Stock.sem, T.gen_try_call_rets, isel_data, isel_monad]
    have call := targetRun
    unfold T.gen_try_call_rets at call
    rw [call]
    rfl
  exact ⟨run, targetOld, targetReturns, by decide +kernel,
    stock_apply_aliasTargetsAllowed targetOld targetReturns run⟩

/-- A complete try-call lowering run supplies a reserved payload194, its final
alias193, the target origin, resolver endpoint and inhabited value transport. -/
theorem stock_lower_payload_witness :
    ∃ (f : Clif.Function) (result : Result) (regs : Nat → CV),
      Stock.lower f = .ok result ∧
      result.initial.tryRegs[1]? = some ([.vreg 193 .int], [.vreg 194 .int, .vreg 195 .int]) ∧
      (result.final.alias[194]?).join = some 193 ∧
      ReservedReturn result.initial 193 ∧ aliasNum result.final.alias 194 = 193 ∧
      (result.final.alias[aliasNum result.final.alias 194]?).join = none ∧
      VHolds (.ofInt .i8 7) (regs 193) ∧ VHolds (.ofInt .i8 7) (regs (aliasNum result.final.alias 194)) := by
  obtain ⟨f, result, run, lookup, entry, resolves⟩ := stock_lower_reservedReturn_resolves_witness
  have member : (Reg.vreg 194 .int) ∈ ([Reg.vreg 194 .int, Reg.vreg 195 .int] : List Reg) := by simp
  let regs : Nat → CV := fun _ => BitVec.ofNat 128 7
  have held : VHolds (.ofInt .i8 7) (regs 193) := rfl
  exact ⟨f, result, regs, run, lookup, entry,
    stock_lower_payload_aliasOrigin run lookup member entry,
    stock_lower_payload_resolves run lookup member entry,
    stock_lower_payload_terminal run lookup member, held,
    stock_lower_payload_value run lookup member entry held⟩

end Backend.Stock.Proof

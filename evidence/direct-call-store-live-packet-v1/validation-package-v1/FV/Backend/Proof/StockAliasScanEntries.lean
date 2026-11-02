import FV.Backend.Proof.StockAliasWrites
import FV.Backend.Proof.StockBlockScan

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
attribute [local irreducible] Isle.Aarch64.program
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

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


private theorem named_entry {ctx : Ctx} {term : String} {args : List V}
    {st next : State} {out : Option V} {trace : List RuleId} {key : Nat}
    (payloads : ∀ r ∈ ctx.tryRegs.2, ∀ c, r ≠ .vreg key c)
    (h : Stock.runTerm ctx term args st = .ok (out, next, trace)) :
    (next.alias[key]?).join = (st.alias[key]?).join := by
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
        exact stock_apply_aliasEntry payloads ha


private theorem emitted_entry {ctx : Ctx} {i : Nat} {st : State}
    {emission : Emission} {key : Nat}
    (payloads : ∀ r ∈ ctx.tryRegs.2, ∀ c, r ≠ .vreg key c)
    (mapped : ∀ x ∈ ctx.insts[i]!.results, ∀ r,
      ctx.valueReg? x = some r → ∀ c, r ≠ .vreg key c)
    (h : emitInstruction ctx i st = .ok emission) :
    (emission.state.alias[key]?).join = (st.alias[key]?).join := by
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
          exact (stock_bindResults_aliasEntry
            (fun pair member r hr c => mapped pair.1 (List.of_mem_zip member).1 r hr c)
            hb).trans (named_entry payloads hr)

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

/-- Every actual scan decision preserves an alias whose key is absent from the
current source-result destinations and reserved exception payload destinations. -/
theorem stock_scan_aliasEntry {ctx : Ctx} {block i ti : Nat} {branch : Bool}
    {st : State} {output : Scan} {key : Nat}
    (payloads : ∀ r ∈ ctx.tryRegs.2, ∀ c, r ≠ .vreg key c)
    (mapped : ∀ x ∈ ctx.insts[i]!.results, ∀ r,
      ctx.valueReg? x = some r → ∀ c, r ≠ .vreg key c)
    (h : scanInstruction ctx block i ti branch st = .ok output) :
    (output.state.alias[key]?).join = (st.alias[key]?).join := by
  have before := scan_state_entry st i key
  have emit (h : (emitInstruction ctx i (scanState st i) >>= fun e =>
      pure (e.scan block i (scanState st i))) = .ok output) :
      (output.state.alias[key]?).join = (st.alias[key]?).join := by
    cases he : emitInstruction ctx i (scanState st i) with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok e =>
      simp only [he, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact (emitted_entry payloads mapped he).trans before
  unfold scanInstruction at h
  dsimp only at h
  generalize hm : (if i == ti then true else ctx.insts[i]!.clif.any mustLower) = mandatory at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; exact before
    · split at h
      · cases h; exact before
      · split at h
        · cases hc : commitOpportunistic ctx block i (scanState st i) with
          | error e => simp only [hc, bind, Except.bind] at h; cases h
          | ok result =>
            simp only [hc, bind, Except.bind] at h
            cases result with
            | none => exact emit h
            | some q => cases h; exact (opportunity_entry mapped hc).trans before
        · exact emit h

/-- The actual complete block scan composes that preservation through any
number of omitted, sunk, opportunistic or emitted instructions. -/
theorem stock_scanBlock_aliasEntry {ctx : Ctx} {block ti : Nat} {branch : Bool}
    {indices : List Nat} {st : State} {output : BlockScan} {key : Nat}
    (payloads : ∀ r ∈ ctx.tryRegs.2, ∀ c, r ≠ .vreg key c)
    (mapped : ∀ i ∈ indices, ∀ x ∈ ctx.insts[i]!.results, ∀ r,
      ctx.valueReg? x = some r → ∀ c, r ≠ .vreg key c)
    (h : scanBlock ctx block ti branch indices st = .ok output) :
    (output.state.alias[key]?).join = (st.alias[key]?).join := by
  have cert := runScans_spec h
  clear h
  induction cert with
  | nil st => rfl
  | cons head rest ih =>
    exact (ih (fun i mem => mapped i (List.mem_cons_of_mem _ mem))).trans
      (stock_scan_aliasEntry payloads (mapped _ (List.mem_cons_self ..)) head)

private theorem source_payloads_apart {f : Clif.Function} {source ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} {slot x key : Nat}
    (build : Stock.buildCtx f = .ok (source, ranges, initial))
    (mapped : source.valueReg? x = some (.vreg key .int))
    (reserved : ctx.tryRegs = initial.tryRegs[slot]!) :
    ∀ r ∈ ctx.tryRegs.2, ∀ c, r ≠ .vreg key c := by
  intro r member c same
  rw [reserved] at member
  cases entry : initial.tryRegs[slot]? with
  | none =>
    simp only [getElem!_def, entry] at member
    change r ∈ ([] : List Reg) at member
    cases member
  | some rs =>
    have mem : r ∈ rs.1 ++ rs.2 := by
      apply List.mem_append.mpr
      right
      simpa only [getElem!_def, entry, Option.getD_some] using member
    have separate := buildCtx_valueReservedDisjoint build x (.vreg key .int)
      mapped slot rs entry r mem
    obtain ⟨k, reg, _⟩ := buildCtx_reservedBelow build slot rs entry r mem
    subst r
    cases reg
    exact separate rfl

private theorem source_results_apart {f : Clif.Function} {source ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} {x key i : Nat}
    (build : Stock.buildCtx f = .ok (source, ranges, initial))
    (mapped : source.valueReg? x = some (.vreg key .int))
    (values : ∀ y, ctx.valueReg? y = source.valueReg? y)
    (exclude : x ∉ ctx.insts[i]!.results) :
    ∀ y ∈ ctx.insts[i]!.results, ∀ r, ctx.valueReg? y = some r →
      ∀ c, r ≠ .vreg key c := by
  intro y member r mapping c same
  rw [values] at mapping
  have allocated := buildCtx_allocated build
  obtain ⟨n, reg, _⟩ := allocated.2.2.1 y r mapping
  subst r
  cases reg
  have eq := allocated.2.1 y x key mapping mapped
  subst y
  exact exclude member

/-- For an actually allocated source value, both destination exclusions follow
from allocation injectivity and reservation separation. Only source-ID exclusion
from the current instruction's result list remains. Context overrides may change
instructions while retaining the source map and selected reservation slot. -/
theorem stock_scan_sourceAliasEntry {f : Clif.Function} {source ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} {slot x key : Nat}
    (build : Stock.buildCtx f = .ok (source, ranges, initial))
    (mapped : source.valueReg? x = some (.vreg key .int))
    (values : ∀ y, ctx.valueReg? y = source.valueReg? y)
    (reserved : ctx.tryRegs = initial.tryRegs[slot]!)
    {block i ti : Nat} {branch : Bool} {st : State} {output : Scan}
    (exclude : x ∉ ctx.insts[i]!.results)
    (run : scanInstruction ctx block i ti branch st = .ok output) :
    (output.state.alias[key]?).join = (st.alias[key]?).join := by
  exact stock_scan_aliasEntry (source_payloads_apart build mapped reserved)
    (source_results_apart build mapped values exclude) run

/-- Source-ID exclusion composes through the complete actual backward scan;
there are no extra register-injectivity or exception-separation assumptions. -/
theorem stock_scanBlock_sourceAliasEntry {f : Clif.Function} {source ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} {slot x key : Nat}
    (build : Stock.buildCtx f = .ok (source, ranges, initial))
    (mapped : source.valueReg? x = some (.vreg key .int))
    (values : ∀ y, ctx.valueReg? y = source.valueReg? y)
    (reserved : ctx.tryRegs = initial.tryRegs[slot]!)
    {block ti : Nat} {branch : Bool} {indices : List Nat}
    {st : State} {output : BlockScan}
    (exclude : ∀ i ∈ indices, x ∉ ctx.insts[i]!.results)
    (run : scanBlock ctx block ti branch indices st = .ok output) :
    (output.state.alias[key]?).join = (st.alias[key]?).join := by
  exact stock_scanBlock_aliasEntry (source_payloads_apart build mapped reserved)
    (fun i member => source_results_apart build mapped values (exclude i member)) run

private def entryFunction : Clif.Function := {
  name := "scan_alias_entry"
  sig := { params := [⟨.i64, .none, .normal⟩], returns := [⟨.i64, .none, .normal⟩] }
  blocks := [{
    id := 0
    params := [(1, .i64)]
    body := [⟨[0], .iconst .i64 9⟩]
    term := .ret [0] }] }
private def entryBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx entryFunction).toOption.getD (sinkCtx, #[], sinkState)
private def scanEntryCtx : Ctx :=
  { entryBuilt.1 with tryRegs := entryBuilt.2.2.tryRegs[1]! }
private def scanEntryBase : LState :=
  let a := (entryBuilt.2.2.base.fresh .int).2
  let b := (a.fresh .int).2
  let c := (b.fresh .int).2
  (c.fresh .int).2
private def scanEntryInput : State :=
  { entryBuilt.2.2 with
    base := scanEntryBase
    demand := #[1, 0]
    entryColor := #[0, 0]
    alias := aliasStep #[] (192, 196)
    opportunistic := #[some ⟨0, [.vreg 197 .int], 1⟩, none] }
private def scanEntryNext : State :=
  { scanState scanEntryInput 0 with
    alias := aliasStep scanEntryInput.alias (193, 197)
    opportunistic := #[none, none] }
private def scanEntryOutput : Scan :=
  ⟨scanEntryNext, some ⟨0, 0, .opportunistic, scanState scanEntryInput 0,
    scanEntryNext, [], [], #[]⟩, #[]⟩
private def scanEntryBlock : BlockScan :=
  ⟨scanEntryNext, [⟨0, scanEntryInput, scanEntryOutput⟩], #[]⟩
private theorem entry_build : Stock.buildCtx entryFunction = .ok entryBuilt := rfl
private theorem entry_mapping : entryBuilt.1.valueReg? 1 = some (.vreg 192 .int) := rfl
private theorem entry_excluded : (1 : Nat) ∉ scanEntryCtx.insts[0]!.results := by decide
private theorem entry_payloads : ∀ r ∈ scanEntryCtx.tryRegs.2, ∀ c, r ≠ .vreg 192 c := by
  intro r member c
  change r ∈ ([] : List Reg) at member
  cases member
private theorem entry_results : ∀ x ∈ scanEntryCtx.insts[0]!.results, ∀ r,
    scanEntryCtx.valueReg? x = some r → ∀ c, r ≠ .vreg 192 c := by
  intro x member r mapped c same
  change x ∈ [0] at member
  have eq := List.mem_singleton.mp member
  subst x
  change some (.vreg 193 .int) = some r at mapped
  cases mapped
  cases same
private theorem entry_scan : scanInstruction scanEntryCtx 0 0 1 false scanEntryInput =
    .ok scanEntryOutput := rfl
private theorem entry_block : scanBlock scanEntryCtx 0 1 false [0] scanEntryInput =
    .ok scanEntryBlock := by
  unfold scanBlock
  rw [runScans_ref]
  simp only [runScansRef, entry_scan, bind, Except.bind, pure, Except.pure, Array.empty_append]
  rfl

/-- Nonempty opportunistic binding writes 193→197 while preserving 192→196. -/
theorem stock_scan_aliasEntry_witness :
    (∀ r ∈ scanEntryCtx.tryRegs.2, ∀ c, r ≠ .vreg 192 c) ∧
    (∀ x ∈ scanEntryCtx.insts[0]!.results, ∀ r,
      scanEntryCtx.valueReg? x = some r → ∀ c, r ≠ .vreg 192 c) ∧
    scanInstruction scanEntryCtx 0 0 1 false scanEntryInput = .ok scanEntryOutput ∧
    (scanEntryInput.alias[192]?).join = some 196 ∧
    (scanEntryOutput.state.alias[193]?).join = some 197 ∧
    (scanEntryOutput.state.alias[192]?).join = (scanEntryInput.alias[192]?).join := by
  exact ⟨entry_payloads, entry_results, entry_scan, by decide, by decide,
    stock_scan_aliasEntry entry_payloads entry_results entry_scan⟩

/-- The inhabited complete block has one real opportunistic scan record. -/
theorem stock_scanBlock_aliasEntry_witness :
    scanBlock scanEntryCtx 0 1 false [0] scanEntryInput = .ok scanEntryBlock ∧
    scanEntryBlock.records.length = 1 ∧
    (scanEntryBlock.state.alias[193]?).join = some 197 ∧
    (scanEntryBlock.state.alias[192]?).join = (scanEntryInput.alias[192]?).join := by
  refine ⟨entry_block, rfl, by decide, stock_scanBlock_aliasEntry entry_payloads ?_ entry_block⟩
  intro i member
  have eq := List.mem_singleton.mp member
  subst i
  exact entry_results

/-- The source variant uses an actual context build and protected source ID1;
allocation supplies the register and exception exclusions. -/
theorem stock_scan_sourceAliasEntry_witness :
    Stock.buildCtx entryFunction = .ok entryBuilt ∧
    entryBuilt.1.valueReg? 1 = some (.vreg 192 .int) ∧
    (∀ y, scanEntryCtx.valueReg? y = entryBuilt.1.valueReg? y) ∧
    scanEntryCtx.tryRegs = entryBuilt.2.2.tryRegs[1]! ∧
    (1 : Nat) ∉ scanEntryCtx.insts[0]!.results ∧
    scanInstruction scanEntryCtx 0 0 1 false scanEntryInput = .ok scanEntryOutput ∧
    (scanEntryOutput.state.alias[192]?).join = (scanEntryInput.alias[192]?).join := by
  exact ⟨entry_build, entry_mapping, fun _ => rfl, rfl, entry_excluded, entry_scan,
    stock_scan_sourceAliasEntry (ctx := scanEntryCtx) (slot := 1) entry_build entry_mapping (fun _ => rfl) rfl
      entry_excluded entry_scan⟩

/-- Actual initialization and a nonempty backward scan inhabit every premise
of the source-ID block preservation theorem. -/
theorem stock_scanBlock_sourceAliasEntry_witness :
    Stock.buildCtx entryFunction = .ok entryBuilt ∧
    entryBuilt.1.valueReg? 1 = some (.vreg 192 .int) ∧
    (∀ y, scanEntryCtx.valueReg? y = entryBuilt.1.valueReg? y) ∧
    scanEntryCtx.tryRegs = entryBuilt.2.2.tryRegs[1]! ∧
    (∀ i ∈ [0], (1 : Nat) ∉ scanEntryCtx.insts[i]!.results) ∧
    scanBlock scanEntryCtx 0 1 false [0] scanEntryInput = .ok scanEntryBlock ∧
    (scanEntryBlock.state.alias[192]?).join = (scanEntryInput.alias[192]?).join := by
  have exclude : ∀ i ∈ [0], (1 : Nat) ∉ scanEntryCtx.insts[i]!.results := by
    intro i member
    have eq := List.mem_singleton.mp member
    subst i
    exact entry_excluded
  exact ⟨entry_build, entry_mapping, fun _ => rfl, rfl, exclude, entry_block,
    stock_scanBlock_sourceAliasEntry (ctx := scanEntryCtx) (slot := 1) entry_build entry_mapping (fun _ => rfl) rfl
      exclude entry_block⟩

end Backend.Stock.Proof

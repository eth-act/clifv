module

public import FV.Backend.Proof.StockSinkFrame
public import FV.Backend.Proof.StockPolicy

@[expose] public section

/-! Immutable instruction colors and zero-color sink safety.
This leaf frame retains the existing constructor-model interfaces. -/
namespace Backend.Stock.Proof
open Backend.Proof Isle Isle.Interp Isle.Aarch64
attribute [local irreducible] Isle.Aarch64.program
set_option maxRecDepth 4096

private def fields (st : State) := st.entryColor

private theorem marks_fields (st : State) (vs : List Nat) :
    fields (vs.foldl State.mark st) = fields st := by
  induction vs generalizing st with
  | nil => rfl
  | cons v vs ih => exact ih (st.mark v)

private theorem setAlias_fields {st next : State} {dst src : Reg}
    (h : st.setAlias dst src = .ok next) : fields next = fields st := by
  cases dst <;> cases src <;>
    simp only [State.setAlias, bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at h
  all_goals repeat' first | (solve | cases h) | (solve | cases h; rfl) | split at h

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

private theorem try_fold_fields (ps rets : List Reg) (pairs : List (Reg × Reg))
    (st : State) (regs : List Reg) {next : State} {out : List Reg}
    (h : pairs.foldl (tryAliasStep ps rets) (.ok (st, regs)) = .ok (next, out)) :
    fields next = fields st := by
  induction pairs generalizing st regs with
  | nil => cases h; rfl
  | cons pair pairs ih =>
    rw [List.foldl_cons] at h
    cases hs : tryAliasStep ps rets (.ok (st, regs)) pair with
    | error e => rw [hs, try_fold_error] at h; cases h
    | ok result =>
      rcases result with ⟨middle, rs⟩
      rw [hs] at h
      have hm : fields middle = fields st := by
        unfold tryAliasStep at hs
        simp only [bind, Except.bind] at hs
        cases hi : ps.idxOf? pair.1 with
        | none => simp only [hi, pure, Except.pure] at hs; cases hs; rfl
        | some i =>
          simp only [hi] at hs
          cases hr : rets[i]? with
          | none => simp only [hr] at hs; cases hs
          | some r =>
            simp only [hr] at hs
            cases ha : st.setAlias pair.2 r with
            | error e => rw [ha] at hs; cases hs
            | ok q =>
              rw [ha] at hs
              simp only [pure, Except.pure] at hs
              cases hs
              exact setAlias_fields ha
      exact (ih middle rs h).trans hm


private theorem delegate_fields {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V}
    (h : (match Backend.externCtor ctx t args st.base with
      | .ok (v, base) => ExtResult.ok (v, { st with base })
      | .fail => ExtResult.fail
      | .unmodeled e => ExtResult.unmodeled e) = ExtResult.ok (v, next)) :
    fields next = fields st := by
  cases call : Backend.externCtor ctx t args st.base with
  | fail => rw [call] at h; cases h
  | unmodeled e => rw [call] at h; cases h
  | ok pair =>
    rcases pair with ⟨value, base⟩
    rw [call] at h
    cases h
    rfl

/-- Actual constructors retain the instruction-color table, including sinks,
payload aliases and demand updates. -/
theorem stock_ctor_entryColor {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V} (h : Stock.externCtor ctx t args st = .ok (v, next)) :
    next.entryColor = st.entryColor := by
  change fields next = fields st
  unfold Stock.externCtor at h
  split at h
  all_goals dsimp only at h
  all_goals try solve | exact delegate_fields h
  all_goals repeat' first
    | (solve | cases h <;> rfl)
    | (solve | exact (delegate_fields h).trans (by rfl))
    | (solve | exact (delegate_fields h).trans (marks_fields st _))
    | split at h
  all_goals
    rename_i _ _ sig _ _ ps _ _ s regs step
    cases h
    exact try_fold_fields ps ctx.tryRegs.1
      ((payloadRegs sig.callConv).zip ctx.tryRegs.2) st [] step



private theorem delegate_unsunk {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V} {i : Nat} (safe : st.sunk[i]! = false)
    (h : (match Backend.externCtor ctx t args st.base with
      | .ok (v, base) => ExtResult.ok (v, {st with base})
      | .fail => ExtResult.fail
      | .unmodeled e => ExtResult.unmodeled e) = ExtResult.ok (v,next)) :
    next.sunk[i]! = false := by
  cases call : Backend.externCtor ctx t args st.base with
  | fail => rw [call] at h; cases h
  | unmodeled e => rw [call] at h; cases h
  | ok pair =>
    rcases pair with ⟨value,base⟩
    rw [call] at h
    cases h
    exact safe

private theorem set_sink_other {st : State} {i target : Nat}
    (zero : st.entryColor[i]! = 0) (safe : st.sunk[i]! = false)
    (nonzero : st.entryColor[target]! ≠ 0) : (st.sunk.set! target true)[i]! = false := by
  have different : i ≠ target := by intro same; subst target; exact nonzero zero
  simpa [getElem!_def,Array.getElem?_setIfInBounds,different,Ne.symm different] using safe

/-- A successful helper cannot sink an instruction with original color zero. -/
theorem stock_ctor_zeroColor_unsunk {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V} {i : Nat}
    (zero : st.entryColor[i]! = 0) (safe : st.sunk[i]! = false)
    (h : Stock.externCtor ctx t args st = .ok (v,next)) : next.sunk[i]! = false := by
  by_cases sink : t.id = TId.sink_inst
  · simp only [Stock.externCtor,sink] at h
    split at h
    all_goals try solve | simp_all [TId.sink_inst]
    all_goals try solve | exact delegate_unsunk safe h
    split at h
    · cases h
    · rename_i accepted
      cases h
      apply set_sink_other zero safe
      intro equal
      apply accepted
      simp only [equal,beq_self_eq_true,Bool.true_or]
  · rw [stock_ctor_noSink sink h]
    exact safe

def ZeroColorLe (st next : State) : Prop :=
  next.entryColor = st.entryColor ∧
    ∀ i : Nat, st.entryColor[i]! = 0 → st.sunk[i]! = false → next.sunk[i]! = false

private theorem zeroColor_refl (st : State) : ZeroColorLe st st := ⟨rfl,fun _ _ h => h⟩
private theorem zeroColor_trans {a b c : State} (ab : ZeroColorLe a b) (bc : ZeroColorLe b c) :
    ZeroColorLe a c := by
  refine ⟨bc.1.trans ab.1,?_⟩
  intro i color safe
  exact bc.2 i (by rw [ab.1]; exact color) (ab.2 i color safe)

/-- The actual interpreter transports zero-color unsunk facts through every
successful helper, including failed pattern attempts and their rollback. -/
theorem stock_apply_zeroColorLe {p : Program} {ctx : Ctx} {cfg : Config}
    {n ty t : Nat} {args : List V} {st next : State} {out : Option V}
    {tr tr' : Array RuleId}
    (h : (applyTerm p (Stock.sem ctx) cfg n ty t args).run (st,tr) = .ok (out,next,tr')) :
    ZeroColorLe st next :=
  (presAt zeroColor_refl (fun _ _ _ => zeroColor_trans)
    (fun _ _ _ _ _ h => ⟨stock_ctor_entryColor h,fun _ z s => stock_ctor_zeroColor_unsunk z s h⟩)
    n).apply ty t args st tr out next tr' h

private theorem named_zeroColorLe {ctx : Ctx} {term : String} {args : List V}
    {st next : State} {out : Option V} {trace : List RuleId}
    (h : Stock.runTerm ctx term args st = .ok (out, next, trace)) :
    ZeroColorLe st next := by
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
        exact stock_apply_zeroColorLe ha


/-- Named entry into the real Stock interpreter retains the same invariant. -/
theorem stock_runTerm_zeroColorLe {ctx : Ctx} {term : String} {args : List V}
    {st next : State} {out : Option V} {trace : List RuleId}
    (h : Stock.runTerm ctx term args st = .ok (out,next,trace)) : ZeroColorLe st next :=
  named_zeroColorLe h


private def stableFields (st : State) := (st.entryColor,st.sunk)
private theorem stableFields_rel {st next : State} (h : stableFields next = stableFields st) :
    ZeroColorLe st next := by
  have colors := congrArg Prod.fst h
  have bits := congrArg Prod.snd h
  refine ⟨colors,?_⟩
  intro i _ safe
  change next.sunk = st.sunk at bits
  rw [bits]
  exact safe
private theorem setAlias_stableFields {st next : State} {dst src : Reg}
    (h : st.setAlias dst src = .ok next) : stableFields next = stableFields st := by
  cases dst <;> cases src <;>
    simp only [State.setAlias,bind,Except.bind,pure,Except.pure,
      throw,throwThe,MonadExceptOf.throw] at h
  all_goals repeat' first | (solve | cases h) | (solve | cases h; rfl) | split at h
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

private theorem binding_stableFields {ctx : Ctx} {pairs : List (Nat × List Reg)}
    {st next : State} {copies : Array MInst}
    (h : bindResults ctx pairs st = .ok (next, copies)) : stableFields next = stableFields st := by
  unfold bindResults at h
  apply fold_fields_eq (fun a : State × Array MInst => stableFields a.1) _ ?_ pairs h
  intro acc pair next he
  rcases acc with ⟨s, code⟩
  rcases pair with ⟨v, rs⟩
  dsimp only at he
  cases hm : ctx.valueReg? v with
  | none => simp only [hm] at he; cases he
  | some r =>
    simp only [hm] at he
    split at he
    · rename_i _ n cls
      cases ha : s.setAlias r (.vreg n cls) with
      | error e => simp only [ha, bind, Except.bind] at he; cases he
      | ok q =>
        simp only [ha, bind, Except.bind, pure, Except.pure] at he
        cases he
        exact setAlias_stableFields ha
    · cases he; rfl
    · cases he

private theorem commit_stableFields {ctx : Ctx} {block i : Nat} {st next : State}
    (h : commitOpportunistic ctx block i st = .ok (some next)) : stableFields next = stableFields st := by
  have values {values : List Nat} {a b : State}
      (h : commitOpportunisticValues ctx values a = .ok b) : stableFields b = stableFields a := by
    unfold commitOpportunisticValues at h
    apply fold_fields_eq stableFields _ ?_ values h
    intro a v b he
    split at he
    · split at he
      · rename_i dst hdst
        split at he
        · rename_i src _
          cases hs : a.setAlias dst src with
          | error e => simp only [hs, bind, Except.bind] at he; cases he
          | ok q =>
            simp only [hs, bind, Except.bind, pure, Except.pure] at he
            cases he
            exact setAlias_stableFields (next := q) hs
        · cases he
      · cases he
    · cases he; rfl
  unfold commitOpportunistic at h
  dsimp only at h
  split at h
  · cases h
  · cases hv : commitOpportunisticValues ctx (ctx.insts[i]!.results) st with
    | error e => simp only [hv, bind, Except.bind] at h; cases h
    | ok q =>
      simp only [hv, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact values hv

private theorem scan_state_stableFields (st : State) (i : Nat) : stableFields (scanState st i) = stableFields st := by
  unfold scanState
  dsimp only
  split <;> rfl

private theorem emitted_zeroColorLe {ctx : Ctx} {i : Nat} {st : State}
    {emission : Emission}
    (h : emitInstruction ctx i st = .ok emission) : ZeroColorLe st emission.state := by
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
          exact zeroColor_trans (named_zeroColorLe hr) (stableFields_rel (binding_stableFields hb))


/-- Actual scans retain colors and do not sink zero-color instructions. -/
theorem stock_scan_zeroColorLe {ctx : Ctx} {block i ti : Nat} {branch : Bool}
    {st : State} {output : Scan}
    (h : scanInstruction ctx block i ti branch st = .ok output) : ZeroColorLe st output.state := by
  have refl : ZeroColorLe st (scanState st i) := stableFields_rel (scan_state_stableFields st i)
  have emit (h : (emitInstruction ctx i (scanState st i) >>= fun e =>
      pure (e.scan block i (scanState st i))) = .ok output) : ZeroColorLe st output.state := by
    cases he : emitInstruction ctx i (scanState st i) with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok e =>
      simp only [he, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact zeroColor_trans refl (emitted_zeroColorLe he)
  unfold scanInstruction at h
  dsimp only at h
  generalize hm : (if i == ti then true else ctx.insts[i]!.clif.any mustLower) = mandatory at h
  split at h
  · cases h; exact zeroColor_refl _
  · split at h
    · cases h; exact refl
    · split at h
      · cases h; exact refl
      · split at h
        · cases hc : commitOpportunistic ctx block i (scanState st i) with
          | error e => simp only [hc, bind, Except.bind] at h; cases h
          | ok result =>
            simp only [hc, bind, Except.bind] at h
            cases result with
            | none => exact emit h
            | some q =>
              cases h
              exact zeroColor_trans refl (stableFields_rel (commit_stableFields hc))
        · exact emit h

/-- Complete tail-recursive scans transport the zero-color unsunk invariant. -/
theorem stock_scanBlock_zeroColorLe {ctx : Ctx} {block ti : Nat} {branch : Bool}
    {indices : List Nat} {st : State} {output : BlockScan}
    (h : scanBlock ctx block ti branch indices st = .ok output) : ZeroColorLe st output.state := by
  have cert := runScans_spec h
  clear h
  induction cert with
  | nil st => exact zeroColor_refl _
  | cons head rest ih => exact zeroColor_trans (stock_scan_zeroColorLe head) ih




/-- Preserve the invariant at every real retained-record boundary, including
intermediate records rather than only the final scan state. -/
theorem stock_scans_zeroColorLe {ctx : Ctx} {block ti : Nat} {branch : Bool}
    {indices : List Nat} {st : State} {output : BlockScan}
    (cert : ScansSpec (fun i => scanInstruction ctx block i ti branch) indices st output) :
    ZeroColorLe st output.state ∧
      ∀ r ∈ output.records, ZeroColorLe st r.input ∧ ZeroColorLe st r.output.state := by
  induction cert with
  | nil st => exact ⟨zeroColor_refl _,by simp⟩
  | cons head rest ih =>
    have step := stock_scan_zeroColorLe head
    refine ⟨zeroColor_trans step ih.1,?_⟩
    intro r member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨zeroColor_refl _,step⟩
    · obtain ⟨pre,post⟩ := ih.2 r member
      exact ⟨zeroColor_trans step pre,zeroColor_trans step post⟩

private def twoSlotState : State :=
  {sinkState with entryColor := #[1,0], sunk := #[false,false]}
private def sunkFirst : State :=
  {twoSlotState with color := some 1, sunk := #[true,false]}
private def sinkProgram : Program := {(default : Program) with terms := #[T.sink_inst]}

/-- A real successful sink changes a nonzero-color slot while retaining an
in-bounds zero-color neighbor; it inhabits both constructor frame results. -/
theorem stock_zeroColor_sink_witness :
    Stock.externCtor sinkCtx T.sink_inst [.inst 0] twoSlotState = .ok (.op .unit,sunkFirst) ∧
    twoSlotState.entryColor[1]! = 0 ∧ twoSlotState.sunk[1]! = false ∧
    sunkFirst.sunk[0]! = true ∧ ZeroColorLe twoSlotState sunkFirst := by
  have h : Stock.externCtor sinkCtx T.sink_inst [.inst 0] twoSlotState = .ok (.op .unit,sunkFirst) := rfl
  exact ⟨h,rfl,rfl,rfl,stock_ctor_entryColor h,fun _ z safe => stock_ctor_zeroColor_unsunk z safe h⟩

/-- The same nontrivial sink executes through the actual interpreter. -/
theorem stock_zeroColor_apply_witness :
    (applyTerm sinkProgram (Stock.sem sinkCtx) {} 1 T.sink_inst.ret 0 [.inst 0]).run
      (twoSlotState,#[]) = .ok (some (.op .unit),sunkFirst,#[]) ∧
    ZeroColorLe twoSlotState sunkFirst ∧ sunkFirst.sunk[1]! = false := by
  have h : (applyTerm sinkProgram (Stock.sem sinkCtx) {} 1 T.sink_inst.ret 0 [.inst 0]).run
      (twoSlotState,#[]) = .ok (some (.op .unit),sunkFirst,#[]) := rfl
  exact ⟨h,stock_apply_zeroColorLe h,rfl⟩

end Backend.Stock.Proof

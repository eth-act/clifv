import FV.Backend.Proof.StockDemandMono
import FV.Backend.Proof.StockSinkFrame

/-! Demand protects a colored source definition across actual Stock helpers and
nested evaluation. Unlike zero-color preservation, this also applies to division.
The original result membership and actual demand are internal driver facts. -/
namespace Backend.Stock.Proof
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
attribute [local irreducible] Isle.Aarch64.program

private theorem delegate_unsunk {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V} {i : Nat} (safe : st.sunk[i]! = false)
    (h : (match Backend.externCtor ctx t args st.base with
      | .ok (value,base) => ExtResult.ok (value,{st with base})
      | .fail => ExtResult.fail
      | .unmodeled message => ExtResult.unmodeled message) = .ok (v,next)) :
    next.sunk[i]! = false := by
  cases call : Backend.externCtor ctx t args st.base with
  | fail => rw [call] at h; cases h
  | unmodeled message => rw [call] at h; cases h
  | ok pair => rw [call] at h; cases h; exact safe

/-- Actual nonzero demand forbids sinking its source definition, including
colored definitions; other legal sink operations may still proceed. -/
theorem stock_ctor_demanded_unsunk {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V} {i x : Nat}
    (result : x ∈ ctx.insts[i]!.results) (demanded : st.demand[x]! ≠ 0)
    (safe : st.sunk[i]! = false)
    (run : Stock.externCtor ctx t args st = .ok (v,next)) : next.sunk[i]! = false := by
  by_cases sink : t.id = TId.sink_inst
  · simp only [Stock.externCtor,sink] at run
    split at run
    all_goals try solve | simp_all [TId.sink_inst]
    all_goals try solve | exact delegate_unsunk safe run
    split at run
    · cases run
    · rename_i target _ accepted
      cases run
      have different : target ≠ i := by
        intro equal
        subst target
        have used : ctx.insts[i]!.results.any (fun value => st.demand[value]! != 0) = true :=
          List.any_eq_true.mpr ⟨x,result,by simp [demanded]⟩
        exact accepted (by simp [used])
      simpa [getElem!_def,Array.getElem?_setIfInBounds,different,Ne.symm different] using safe
  · rw [stock_ctor_noSink sink run]
    exact safe

/-- Demand grows while every already-demanded original result keeps its
unsunk source definition. This relation composes across interpreter rollback. -/
def DemandedUnsunkLe (ctx : Ctx) (st next : State) : Prop :=
  (∀ x : Nat,st.demand[x]! ≤ next.demand[x]!) ∧
  ∀ i x : Nat,x ∈ ctx.insts[i]!.results → st.demand[x]! ≠ 0 →
    st.sunk[i]! = false → next.sunk[i]! = false

private theorem demanded_refl (ctx : Ctx) (st : State) : DemandedUnsunkLe ctx st st :=
  ⟨fun _ => Nat.le_refl _,fun _ _ _ _ safe => safe⟩

private theorem demanded_trans {ctx : Ctx} {a b c : State}
    (first : DemandedUnsunkLe ctx a b) (second : DemandedUnsunkLe ctx b c) :
    DemandedUnsunkLe ctx a c := by
  refine ⟨fun x => Nat.le_trans (first.1 x) (second.1 x),?_⟩
  intro i x result demanded safe
  have grows := first.1 x
  exact second.2 i x result (by omega) (first.2 i x result demanded safe)

/-- Successful nested Stock interpretation retains demanded colored source
slots without restricting rule families or strengthening source assumptions. -/
theorem stock_apply_demanded_unsunk {p : Program} {ctx : Ctx} {cfg : Config}
    {n ty t : Nat} {args : List V} {st next : State} {out : Option V}
    {trace trace' : Array RuleId}
    (run : (applyTerm p (Stock.sem ctx) cfg n ty t args).run
      (st,trace) = .ok (out,next,trace')) : DemandedUnsunkLe ctx st next :=
  (presAt (R := DemandedUnsunkLe ctx) (demanded_refl ctx)
    (fun _ _ _ => demanded_trans)
    (fun _ _ _ _ _ h => ⟨stock_ctor_demand_mono h,
      fun _ _ member used safe => stock_ctor_demanded_unsunk member used safe h⟩)
    n).apply ty t args st trace out next trace' run

/-- Named actual Stock calls preserve demanded colored definitions. -/
theorem stock_named_demanded_unsunk {ctx : Ctx} {term : String} {args : List V}
    {st next : State} {out : Option V} {trace : List RuleId}
    (h : Stock.runTerm ctx term args st = .ok (out, next, trace)) :
    DemandedUnsunkLe ctx st next := by
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
        exact stock_apply_demanded_unsunk ha


private def stableFields (st : State) := (st.demand,st.sunk)
private theorem stableFields_rel {ctx : Ctx} {st next : State}
    (same : stableFields next = stableFields st) : DemandedUnsunkLe ctx st next := by
  have demand := congrArg Prod.fst same
  have sunk := congrArg Prod.snd same
  change next.demand = st.demand at demand
  change next.sunk = st.sunk at sunk
  refine ⟨?_,?_⟩
  · intro x; rw [demand]
  · intro i x result used safe; rw [sunk]; exact safe

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

private theorem emitted_demanded_unsunk {ctx : Ctx} {i : Nat} {st : State}
    {emission : Emission}
    (h : emitInstruction ctx i st = .ok emission) : DemandedUnsunkLe ctx st emission.state := by
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
          exact demanded_trans (stock_named_demanded_unsunk hr) (stableFields_rel (binding_stableFields hb))


/-- Every actual scan decision preserves demanded colored definitions. -/
theorem stock_scan_demanded_unsunk {ctx : Ctx} {block i ti : Nat} {branch : Bool}
    {st : State} {output : Scan}
    (h : scanInstruction ctx block i ti branch st = .ok output) : DemandedUnsunkLe ctx st output.state := by
  have refl : DemandedUnsunkLe ctx st (scanState st i) := stableFields_rel (scan_state_stableFields st i)
  have emit (h : (emitInstruction ctx i (scanState st i) >>= fun e =>
      pure (e.scan block i (scanState st i))) = .ok output) : DemandedUnsunkLe ctx st output.state := by
    cases he : emitInstruction ctx i (scanState st i) with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok e =>
      simp only [he, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact demanded_trans refl (emitted_demanded_unsunk he)
  unfold scanInstruction at h
  dsimp only at h
  generalize hm : (if i == ti then true else ctx.insts[i]!.clif.any mustLower) = mandatory at h
  split at h
  · cases h; exact demanded_refl _ _
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
              exact demanded_trans refl (stableFields_rel (commit_stableFields hc))
        · exact emit h

/-- Complete tail-recursive scans transport the demanded colored unsunk invariant. -/
theorem stock_scanBlock_demanded_unsunk {ctx : Ctx} {block ti : Nat} {branch : Bool}
    {indices : List Nat} {st : State} {output : BlockScan}
    (h : scanBlock ctx block ti branch indices st = .ok output) : DemandedUnsunkLe ctx st output.state := by
  have cert := runScans_spec h
  clear h
  induction cert with
  | nil st => exact demanded_refl _ _
  | cons head rest ih => exact demanded_trans (stock_scan_demanded_unsunk head) ih




/-- Preserve the invariant at every real retained-record boundary, including
intermediate records rather than only the final scan state. -/
theorem stock_scans_demanded_unsunk {ctx : Ctx} {block ti : Nat} {branch : Bool}
    {indices : List Nat} {st : State} {output : BlockScan}
    (cert : ScansSpec (fun i => scanInstruction ctx block i ti branch) indices st output) :
    DemandedUnsunkLe ctx st output.state ∧
      ∀ r ∈ output.records, DemandedUnsunkLe ctx st r.input ∧ DemandedUnsunkLe ctx st r.output.state := by
  induction cert with
  | nil st => exact ⟨demanded_refl _ _,by simp⟩
  | cons head rest ih =>
    have step := stock_scan_demanded_unsunk head
    refine ⟨demanded_trans step ih.1,?_⟩
    intro r member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨demanded_refl _ _,step⟩
    · obtain ⟨pre,post⟩ := ih.2 r member
      exact ⟨demanded_trans step pre,demanded_trans step post⟩
private def protectedCtx : Ctx :=
  {sinkCtx with insts := #[{sinkCtx.insts[0]! with results := [0]},{sinkCtx.insts[0]! with results := [1]}]}
private def protectedState : State :=
  {sinkState with entryColor := #[1,2],color := some 3,demand := #[1,0],sunk := #[false,false]}
private def sunkOther : State :=
  {protectedState with color := some 2,sunk := #[false,true]}
private def sinkProgram : Program := {(default : Program) with terms := #[T.sink_inst]}

/-- A real sink consumes another colored instruction while retaining a
nonzero-color, demanded original definition; the premises are inhabited. -/
theorem stock_ctor_demanded_unsunk_witness :
    Stock.externCtor protectedCtx T.sink_inst [.inst 1] protectedState =
      .ok (.op .unit,sunkOther) ∧
    protectedState.entryColor[0]! ≠ 0 ∧ protectedState.demand[0]! ≠ 0 ∧
    sunkOther.sunk[1]! = true ∧ sunkOther.sunk[0]! = false := by
  have run : Stock.externCtor protectedCtx T.sink_inst [.inst 1] protectedState =
      .ok (.op .unit,sunkOther) := rfl
  exact ⟨run,by decide,by decide,rfl,
    stock_ctor_demanded_unsunk (by decide : 0 ∈ protectedCtx.insts[0]!.results)
      (by decide) rfl run⟩

/-- The same nontrivial sink also inhabits the actual nested interpreter
relation, with positive demand and a real changed neighboring sunk bit. -/
theorem stock_apply_demanded_unsunk_witness :
    (applyTerm sinkProgram (Stock.sem protectedCtx) {} 1 T.sink_inst.ret 0 [.inst 1]).run
      (protectedState,#[]) = .ok (some (.op .unit),sunkOther,#[]) ∧
    DemandedUnsunkLe protectedCtx protectedState sunkOther ∧
    sunkOther.sunk[1]! = true ∧ sunkOther.sunk[0]! = false := by
  have run : (applyTerm sinkProgram (Stock.sem protectedCtx) {} 1 T.sink_inst.ret 0 [.inst 1]).run
      (protectedState,#[]) = .ok (some (.op .unit),sunkOther,#[]) := rfl
  exact ⟨run,stock_apply_demanded_unsunk run,rfl,rfl⟩

end Backend.Stock.Proof

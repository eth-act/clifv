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

theorem DemandedUnsunkLe.refl (ctx : Ctx) (st : State) : DemandedUnsunkLe ctx st st :=
  ⟨fun _ => Nat.le_refl _,fun _ _ _ _ safe => safe⟩

theorem DemandedUnsunkLe.trans {ctx : Ctx} {a b c : State}
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
  (presAt (R := DemandedUnsunkLe ctx) (DemandedUnsunkLe.refl ctx)
    (fun _ _ _ => DemandedUnsunkLe.trans)
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


set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
private theorem named_sink_run :
    Stock.runTerm protectedCtx "sink_inst" [.inst 1] protectedState =
      .ok (some (.op .unit),sunkOther,[]) := by
  unfold Stock.runTerm Isle.Interp.run program
  rfl

/-- A real named helper sinks the neighboring colored slot while retaining
positive demand and the protected colored definition. -/
theorem stock_named_demanded_unsunk_witness :
    Stock.runTerm protectedCtx "sink_inst" [.inst 1] protectedState =
      .ok (some (.op .unit),sunkOther,[]) ∧
    DemandedUnsunkLe protectedCtx protectedState sunkOther ∧
    sunkOther.sunk[1]! = true ∧ sunkOther.sunk[0]! = false :=
  ⟨named_sink_run,stock_named_demanded_unsunk named_sink_run,rfl,rfl⟩

/-- Reflexivity and composition are inhabited beside the actual changed
neighboring sink, rather than requiring an empty or zero-demand state. -/
theorem stock_demanded_unsunk_relation_witness :
    DemandedUnsunkLe protectedCtx protectedState protectedState ∧
    DemandedUnsunkLe protectedCtx protectedState sunkOther :=
  ⟨DemandedUnsunkLe.refl _ _,DemandedUnsunkLe.trans
    (DemandedUnsunkLe.refl _ _) stock_apply_demanded_unsunk_witness.2.1⟩

end Backend.Stock.Proof

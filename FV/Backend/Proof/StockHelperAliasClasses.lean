import FV.Backend.Proof.StockBindingClassContracts

namespace Backend.Stock.Proof.HelperAliasClassDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.BindingClassDraft Backend.Stock.Proof.ClassGrowthDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- The fixed context's return/payload reservations are actual classed integer
virtual registers. Real context construction supplies this internal invariant. -/
def ReservedClasses (ctx : Ctx) (st : State) : Prop :=
  ∀ r ∈ ctx.tryRegs.1 ++ ctx.tryRegs.2,IntCls st.base.classes r

private theorem grow_alias {before after : State} (growth : ClassGrowth before after)
    (same : after.alias = before.alias) (old : AliasClasses before) : AliasClasses after := by
  intro key target entry
  rw [same] at entry
  obtain ⟨left,right⟩ := old key target entry
  exact ⟨regCls_vreg.mp (regCls_step growth (regCls_vreg.mpr left)),
    regCls_vreg.mp (regCls_step growth (regCls_vreg.mpr right))⟩

private theorem alias_install {st : State} {key target : Nat} (old : AliasClasses st)
    (left : RegCls st.base.classes (.vreg key .int)) (right : RegCls st.base.classes (.vreg target .int)) :
    AliasClasses {st with alias := aliasStep st.alias (key,target)} := by
  intro k t entry
  change ((aliasStep st.alias (key,target))[k]?).join = some t at entry
  rw [aliasStep_get] at entry
  by_cases same : k = key
  · subst k
    simp only [ite_true,Option.some.injEq] at entry
    subst t
    exact ⟨regCls_vreg.mp left,regCls_vreg.mp right⟩
  · simp only [same,ite_false] at entry
    exact old k t entry

private theorem setAlias_facts {st next : State} {key target : Nat}
    (old : AliasClasses st) (left : RegCls st.base.classes (.vreg key .int))
    (right : RegCls st.base.classes (.vreg target .int))
    (run : st.setAlias (.vreg key .int) (.vreg target .int) = .ok next) :
    next.base = st.base ∧ AliasClasses next := by
  rw [setAlias_virtual] at run
  cases run
  exact ⟨rfl,alias_install old left right⟩

private def tryAliasStep (ps rets : List Reg) (acc : Except String (State × List Reg))
    (pair : Reg × Reg) : Except String (State × List Reg) := do
  let (s,regs) ← acc
  if let some i := ps.idxOf? pair.1 then
    let some ret := rets[i]? | throw "try_call return register"
    pure (← s.setAlias pair.2 ret,regs ++ [ret])
  else pure (s,regs ++ [pair.2])

private theorem try_fold_error (ps rets : List Reg) (pairs : List (Reg × Reg)) (e : String) :
    pairs.foldl (tryAliasStep ps rets) (.error e) = .error e := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih => exact ih

private theorem try_step_alias (ps rets pays : List Reg) (st : State) (regs : List Reg)
    (pair : Reg × Reg) (allowed : pair.2 ∈ pays)
    (classes : ∀ r ∈ rets ++ pays,IntCls st.base.classes r)
    (old : AliasClasses st) {next : State} {out : List Reg}
    (run : tryAliasStep ps rets (.ok (st,regs)) pair = .ok (next,out)) :
    next.base = st.base ∧ AliasClasses next := by
  unfold tryAliasStep at run
  simp only [bind,Except.bind] at run
  cases found : ps.idxOf? pair.1 with
  | none => simp only [found,pure,Except.pure] at run; cases run; exact ⟨rfl,old⟩
  | some i =>
    simp only [found] at run
    cases ret : rets[i]? with
    | none => simp only [ret] at run; cases run
    | some r =>
      simp only [ret] at run
      obtain ⟨left,⟨key,leftShape⟩⟩ := classes pair.2 (List.mem_append_right _ allowed)
      obtain ⟨right,⟨target,rfl⟩⟩ := classes r (List.mem_append_left _ (List.mem_of_getElem? ret))
      rw [leftShape] at run left
      cases alias : st.setAlias (.vreg key .int) (.vreg target .int) with
      | error e => simp only [alias,bind,Except.bind] at run; cases run
      | ok q =>
        simp only [alias,bind,Except.bind,pure,Except.pure] at run
        cases run
        exact setAlias_facts old left right alias

private theorem try_fold_alias (ps rets pays : List Reg) (pairs : List (Reg × Reg))
    (st : State) (regs : List Reg) (allowed : ∀ pair ∈ pairs,pair.2 ∈ pays)
    (classes : ∀ r ∈ rets ++ pays,IntCls st.base.classes r) (old : AliasClasses st)
    {next : State} {out : List Reg}
    (run : pairs.foldl (tryAliasStep ps rets) (.ok (st,regs)) = .ok (next,out)) :
    next.base = st.base ∧ AliasClasses next := by
  induction pairs generalizing st regs with
  | nil => cases run; exact ⟨rfl,old⟩
  | cons pair pairs ih =>
    rw [List.foldl_cons] at run
    cases call : tryAliasStep ps rets (.ok (st,regs)) pair with
    | error e => rw [call,try_fold_error] at run; cases run
    | ok result =>
      rcases result with ⟨middle,rs⟩
      rw [call] at run
      obtain ⟨base,middleAliases⟩ := try_step_alias ps rets pays st regs pair (allowed pair (by simp)) classes old call
      obtain ⟨tail,final⟩ := ih middle rs (fun p hp => allowed p (List.mem_cons_of_mem pair hp))
        (fun r hr => by rw [base]; exact classes r hr) middleAliases run
      exact ⟨tail.trans base,final⟩

private theorem delegate_alias {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V}
    (run : (match Backend.externCtor ctx t args st.base with
      | .ok (v,base) => ExtResult.ok (v,{st with base})
      | .fail => ExtResult.fail
      | .unmodeled e => ExtResult.unmodeled e) = .ok (v,next)) : next.alias = st.alias := by
  cases call : Backend.externCtor ctx t args st.base with
  | fail => rw [call] at run; cases run
  | unmodeled e => rw [call] at run; cases run
  | ok result =>
    rcases result with ⟨value,base⟩
    rw [call] at run
    cases run
    rfl

private theorem marks_alias (st : State) (vs : List Nat) : (vs.foldl State.mark st).alias = st.alias := by
  induction vs generalizing st with
  | nil => rfl
  | cons v vs ih => exact ih (st.mark v)

/-- Every successful actual Stock helper preserves alias classes, including
merged return/payload writes. Class growth transports all old entries; the real
reservation classes justify each new entry. No rule-family restriction is used. -/
theorem stock_ctor_alias_classes {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V} (reserved : ReservedClasses ctx st) (old : AliasClasses st)
    (run : Stock.externCtor ctx t args st = .ok (v,next)) : AliasClasses next := by
  have growth := stock_ctor_classGrowth run
  have keeps : next.alias = st.alias → AliasClasses next := fun same => grow_alias growth same old
  unfold Stock.externCtor at run
  split at run
  all_goals dsimp only at run
  all_goals try solve | exact keeps (delegate_alias run)
  all_goals repeat' first
    | (solve | cases run <;> exact keeps rfl)
    | (solve | exact keeps (delegate_alias run))
    | (solve | exact keeps (delegate_alias (st := st.mark _) run))
    | (solve | have same := delegate_alias run; exact keeps (same.trans (marks_alias st _)))
    | split at run
  all_goals
    rename_i _ _ sig _ _ ps _ _ s regs step
    cases run
    exact (try_fold_alias ps ctx.tryRegs.1 ctx.tryRegs.2
      ((payloadRegs sig.callConv).zip ctx.tryRegs.2) st []
      (fun p member => (List.of_mem_zip member).2) reserved old step).2

/-- Internal class-and-reservation preservation composed by the generic
interpreter invariant proof; no abstract-summary acceptance premise is needed. -/
def AliasClassStep (ctx : Ctx) (before after : State) : Prop :=
  ClassGrowth before after ∧ (AliasClasses before → ReservedClasses ctx before → AliasClasses after ∧ ReservedClasses ctx after)

private theorem step_refl (ctx : Ctx) (st : State) : AliasClassStep ctx st st :=
  ⟨clsStep_refl _,fun aliases reserved => ⟨aliases,reserved⟩⟩
private theorem step_trans {ctx : Ctx} {a b c : State} (ab : AliasClassStep ctx a b)
    (bc : AliasClassStep ctx b c) : AliasClassStep ctx a c := by
  refine ⟨clsStep_trans ab.1 bc.1,fun aliases reserved => ?_⟩
  obtain ⟨aliasesB,reservedB⟩ := ab.2 aliases reserved
  exact bc.2 aliasesB reservedB
private theorem ctor_step {ctx : Ctx} {t : Term} {args : List V} {st next : State} {v : V}
    (run : Stock.externCtor ctx t args st = .ok (v,next)) : AliasClassStep ctx st next := by
  have growth := stock_ctor_classGrowth run
  exact ⟨growth,fun aliases reserved => ⟨stock_ctor_alias_classes reserved aliases run,
    fun r member => intCls_step growth (reserved r member)⟩⟩

/-- Arbitrarily nested actual evaluation preserves aliases and real reservation
classes, including failed-match rollback and every successful helper sequence. -/
theorem stock_apply_alias_classes {p : Program} {ctx : Ctx} {cfg : Config}
    {fuel ty term : Nat} {args : List V} {before after : State} {trace finalTrace : Array RuleId} {out : Option V}
    (reserved : ReservedClasses ctx before) (old : AliasClasses before)
    (run : (applyTerm p (Stock.sem ctx) cfg fuel ty term args).run (before,trace) = .ok (out,after,finalTrace)) :
    AliasClasses after ∧ ReservedClasses ctx after := by
  have step := (presAt (step_refl ctx) (fun _ _ _ => step_trans)
    (fun _ _ _ _ _ => ctor_step) fuel).apply ty term args before trace out after finalTrace run
  exact step.2 old reserved


/-- Actual named roots retain alias and reservation classes under the same
internal invariant, independently of the generated selected rule family. -/
theorem stock_named_alias_classes {ctx : Ctx} {term : String} {args : List V}
    {st next : State} {out : Option V} {trace : List RuleId}
    (reserved : ReservedClasses ctx st) (old : AliasClasses st)
    (h : Stock.runTerm ctx term args st = .ok (out, next, trace)) :
    AliasClasses next ∧ ReservedClasses ctx next := by
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
        exact stock_apply_alias_classes reserved old ha



end Backend.Stock.Proof.HelperAliasClassDraft

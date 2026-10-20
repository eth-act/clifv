import FV.Backend.Proof.StockClassGrowthContracts
import FV.Backend.Proof.SpillClsModel

namespace Backend.Stock.Proof.OperandClassDraft
open Backend.Proof Backend.Proof.Spill Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem marks_base (st : State) (vs : List Nat) :
    (vs.foldl State.mark st).base = st.base := by
  induction vs generalizing st with
  | nil => rfl
  | cons v vs ih => exact ih (st.mark v)

private theorem setAlias_base {st next : State} {dst src : Reg}
    (h : st.setAlias dst src = .ok next) : next.base = st.base := by
  cases dst <;> cases src <;>
    simp only [State.setAlias,bind,Except.bind,pure,Except.pure,
      throw,throwThe,MonadExceptOf.throw] at h
  all_goals repeat' first | (solve | cases h) | (solve | cases h; rfl) | split at h

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

private theorem try_step_facts (ps rets pays : List Reg) (st : State) (regs : List Reg)
    (pair : Reg × Reg) (allowed : pair.2 ∈ pays)
    (old : ∀ r ∈ regs,r ∈ rets ∨ r ∈ pays) {next : State} {out : List Reg}
    (run : tryAliasStep ps rets (.ok (st,regs)) pair = .ok (next,out)) :
    next.base = st.base ∧ ∀ r ∈ out,r ∈ rets ∨ r ∈ pays := by
  unfold tryAliasStep at run
  simp only [bind,Except.bind] at run
  cases found : ps.idxOf? pair.1 with
  | none =>
    simp only [found,pure,Except.pure] at run
    cases run
    refine ⟨rfl,fun r member => ?_⟩
    rcases List.mem_append.mp member with member | member
    · exact old r member
    · exact .inr ((List.mem_singleton.mp member) ▸ allowed)
  | some i =>
    simp only [found] at run
    cases ret : rets[i]? with
    | none => simp only [ret] at run; cases run
    | some r =>
      simp only [ret] at run
      cases alias : st.setAlias pair.2 r with
      | error e => simp only [alias,bind,Except.bind] at run; cases run
      | ok q =>
        simp only [alias,bind,Except.bind,pure,Except.pure] at run
        cases run
        refine ⟨setAlias_base alias,fun v member => ?_⟩
        rcases List.mem_append.mp member with member | member
        · exact old v member
        · exact .inl ((List.mem_singleton.mp member) ▸ List.mem_of_getElem? ret)

private theorem try_fold_facts (ps rets pays : List Reg) (pairs : List (Reg × Reg))
    (st : State) (regs : List Reg) (allowed : ∀ pair ∈ pairs,pair.2 ∈ pays)
    (old : ∀ r ∈ regs,r ∈ rets ∨ r ∈ pays) {next : State} {out : List Reg}
    (run : pairs.foldl (tryAliasStep ps rets) (.ok (st,regs)) = .ok (next,out)) :
    next.base = st.base ∧ ∀ r ∈ out,r ∈ rets ∨ r ∈ pays := by
  induction pairs generalizing st regs with
  | nil => cases run; exact ⟨rfl,old⟩
  | cons pair pairs ih =>
    rw [List.foldl_cons] at run
    cases call : tryAliasStep ps rets (.ok (st,regs)) pair with
    | error e => rw [call,try_fold_error] at run; cases run
    | ok result =>
      rcases result with ⟨middle,rs⟩
      rw [call] at run
      obtain ⟨base,values⟩ := try_step_facts ps rets pays st regs pair (allowed pair (by simp)) old call
      obtain ⟨tail,all⟩ := ih middle rs (fun p hp => allowed p (List.mem_cons_of_mem pair hp)) values run
      exact ⟨tail.trans base,all⟩

private theorem delegate_cls {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V}
    (h : (match Backend.externCtor ctx t args st.base with
      | .ok (v,base) => ExtResult.ok (v,{st with base})
      | .fail => ExtResult.fail
      | .unmodeled e => ExtResult.unmodeled e) = ExtResult.ok (v,next)) :
    CtorCls ctx t.id args st.base v next.base := by
  cases call : Backend.externCtor ctx t args st.base with
  | fail => rw [call] at h; cases h
  | unmodeled e => rw [call] at h; cases h
  | ok result =>
    rcases result with ⟨value,base⟩
    rw [call] at h
    cases h
    exact externCtor_cls ctx t args st.base _ _ call

private theorem call_output_cls {ctx : Ctx} {id : TermId} {args : List V}
    (returns : List Clif.AbiParam) (st : LState) :
    let q := returns.foldl (fun (rs,base) _ =>
      let (r,next) := base.fresh .int
      (rs ++ [[r]],next)) (([] : List (List Reg)),st)
    CtorCls ctx id args st (.regsVec q.1) q.2 := by
  dsimp only
  have invariant := foldl_inv (fun q : List (List Reg) × LState =>
      ClsStep st q.2 ∧ (Sz st → ∀ rs ∈ q.1,∀ r ∈ rs,RegCls q.2.classes r) ∧
      q.2.emitted = st.emitted)
    (fun (rs,base) (_ : Clif.AbiParam) =>
      let (r,next) := base.fresh .int
      (rs ++ [[r]],next)) returns ([],st)
    ⟨clsStep_refl st,by simp,rfl⟩ (by
      intro ret _ q old
      rcases old with ⟨growth,values,emitted⟩
      have fresh := clsStep_fresh q.2 .int
      refine ⟨clsStep_trans growth fresh,fun size rs member r hr => ?_,emitted⟩
      rcases List.mem_append.mp member with member | member
      · exact regCls_step fresh (values size rs member r hr)
      · cases List.mem_singleton.mp member
        cases List.mem_singleton.mp hr
        exact fresh_cls (sz_step growth size) .int)
  obtain ⟨growth,values,emitted⟩ := invariant
  refine ⟨growth,fun size r member => ?_,⟨[],by simp [emitted],by simp⟩⟩
  simp only [V.regsIn,List.mem_flatten] at member
  obtain ⟨rs,member,hr⟩ := member
  exact .inr (.inl (values size rs member r hr))

private theorem try_result_cls {ctx : Ctx} {id : TermId} {args : List V} {st next : State}
    {ps : List Reg} {sig : Clif.Signature} {regs : List Reg}
    (physical : retRegs sig.returns.length = some ps)
    (run : ((payloadRegs sig.callConv).zip ctx.tryRegs.2).foldl (tryAliasStep ps ctx.tryRegs.1)
      (.ok (st,[])) = .ok (next,regs)) :
    CtorCls ctx id args st.base
      (.op (.callRets (ps.zip ctx.tryRegs.1 ++
        ((payloadRegs sig.callConv).zip regs).filter (fun (p,_) => !ps.contains p)))) next.base := by
  obtain ⟨base,values⟩ := try_fold_facts ps ctx.tryRegs.1 ctx.tryRegs.2 _ st []
    (fun p member => (List.of_mem_zip member).2) (by simp) run
  rw [base]
  refine ⟨clsStep_refl _,fun _ r member => ?_,⟨[],by simp,by simp⟩⟩
  simp only [V.regsIn,opRegs,pairRegs,List.mem_flatMap,List.mem_append,List.mem_filter,
    List.mem_cons,List.mem_nil_iff,or_false] at member
  obtain ⟨⟨a,b⟩,pair,hr⟩ := member
  rcases pair with pair | ⟨pair,_⟩
  · have hz := List.of_mem_zip pair
    rcases hr with rfl | rfl
    · exact .inr (.inl (regCls_real (retRegs_phys physical _ hz.1)))
    · exact .inr (.inr (.inr (.inr (.inl hz.2))))
  · have hz := List.of_mem_zip pair
    rcases hr with rfl | rfl
    · exact .inr (.inl (regCls_real (payloadRegs_phys sig.callConv _ hz.1)))
    · rcases values _ hz.2 with ret | pay
      · exact .inr (.inr (.inr (.inr (.inl ret))))
      · exact .inr (.inr (.inr (.inr (.inr pay))))

/-- Every actual Stock helper satisfies the existing complete register-class
contract, including revised return ABI, fresh call outputs and merged payloads.
The source register map may be non-identity; no new caller certificate is used. -/
theorem stock_ctor_classes {ctx : Ctx} {t : Term} {args : List V}
    {st next : State} {v : V} (run : Stock.externCtor ctx t args st = .ok (v,next)) :
    CtorCls ctx t.id args st.base v next.base := by
  unfold Stock.externCtor at run
  split at run
  all_goals dsimp only at run
  all_goals try solve | exact delegate_cls run
  all_goals repeat' first
    | (solve | cases run <;> exact ctorCls_same (by simp [V.regsIn,opRegs]))
    | (solve | exact delegate_cls run)
    | (solve | exact delegate_cls (st := st.mark _) run)
    | (solve | simpa only [marks_base] using delegate_cls run)
    | (solve | cases run
               rename_i call
               have contract := externCtor_cls ctx t _ _ _ _ call
               simpa only [marks_base] using contract)
    | (solve | cases run; exact ctorCls_rets (by assumption) (by assumption))
    | split at run
  case h_10 =>
    cases run
    exact call_output_cls _ st.base
  all_goals
    rename_i _ _ sig _ _ ps _ _ s regs step
    cases run
    exact try_result_cls (by assumption) step

end Backend.Stock.Proof.OperandClassDraft

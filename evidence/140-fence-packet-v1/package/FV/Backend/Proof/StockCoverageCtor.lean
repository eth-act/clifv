import FV.Backend.Proof.StockSourceView
import FV.Backend.Proof.IselCovCtor

/-! Abstract constructor contracts with actual mapped source register numbers.
This reuses IselCovCtor's case proof and result model without its identity-map premise. -/
namespace Backend.Stock.Proof.Coverage
open Backend.Proof Backend.Proof.Flow Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private theorem regsVec_single_vreg_mapped {ctx : Ctx} (hvr : ∀ x r, ctx.valueReg? x = some r → ∃ n, r = .vreg n .int)
    {vs : List Nat} {rs : List Reg} (h : vs.mapM ctx.valueReg? = some rs) :
    (∀ r ∈ (V.regsVec (rs.map fun r => [r])).regsIn, ∃ n, r = .vreg n .int) ∧
      covV (V.regsVec (rs.map fun r => [r])) = true := by
  refine ⟨fun r hr => ?_, rfl⟩
  have hr' : r ∈ rs := by
    simp only [V.regsIn, List.mem_flatten, List.mem_map] at hr
    obtain ⟨_, ⟨a, ha, rfl⟩, hr⟩ := hr
    simp only [List.mem_singleton] at hr
    exact hr ▸ ha
  obtain ⟨x, -, he⟩ := mapM_mem h r hr'
  exact hvr _ _ he

set_option maxHeartbeats 8000000 in
/-- **Every extern constructor** past the type predicates satisfies `CtorCov`. -/
private theorem externCtor_cov_mapped (ctx : Ctx) (hvr : ∀ x r, ctx.valueReg? x = some r → ∃ n, r = .vreg n .int) (t : Term) (args : List V) (st : LState) (v : V) (st' : LState)
    (h : Backend.externCtor ctx t args st = .ok (v, st')) :
    (∃ q ty, tyPred t.id = some q ∧ args = [.ty ty] ∧ q ty = true ∧ v = .ty ty ∧ st' = st) ∨
      CtorCov t.id args st v st' := by
  unfold Backend.externCtor at h
  split at h
  · rename_i q ty hq
    split at h
    · cases h; exact .inl ⟨q, ty, hq, rfl, ‹_›, rfl, rfl⟩
    · cases h
  · right
    revert h v st'
    apply externCtor_split _ (CtorCovP st)
    all_goals
      intros
      unfold CtorCovP
      intro v st' h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals cases h
    all_goals refine ⟨by decide, ?_, ?_⟩
    all_goals try (rename_i heq; simp only [Option.map_eq_some_iff, Function.comp_apply] at heq
                   obtain ⟨_, _, rfl⟩ := heq)
    all_goals first
      | (refine ⟨[], ?_, fun _ h => by cases h⟩; simp [LState.fresh]; done)
      | (apply emit_one; exact .inl rfl)
      | (apply emit_one; exact .inr (.inl ⟨by decide, _, rfl, ‹_›⟩))
      | exact callArgs_fold st _ _ _ _ (fun _ _ => rfl) (callArgs_mem ‹_›)
      | (obtain ⟨-, -, ms, h5, h6⟩ := loadConstantFull_cov _ _ _ _ st
         exact ⟨ms, h5, fun m hm => .inl (h6 m hm)⟩)
      | (refine ⟨[], (callOutput_fold st _ _ (fun _ _ => ⟨_, rfl⟩)).1.trans (by simp), by simp⟩)
      | skip
    all_goals first
      | (simp (config := { decide := true }) only [CtorRes, ite_true, ite_false, Bool.false_eq_true,
          Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, ↓reduceIte]; done)
      | (simp (config := { decide := true }) only [CtorRes, ite_true, ite_false, Bool.false_eq_true,
          Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, ↓reduceIte]
         first
         | (intro _; rfl)
         | (intro hc; simp only [covVL, Bool.and_true] at hc; exact hc)
         | (intro _; simp [covV_data, covVL]; done)
         | exact ⟨_, _, _, rfl, ‹_›, rfl⟩
         | (rename_i heq; obtain ⟨n, rfl⟩ := hvr _ _ heq; exact ⟨n, rfl⟩)
         | exact regsVec_single_vreg_mapped hvr ‹_›
         | (refine ⟨fun r hr => ?_, rfl, _, rfl⟩
            simp only [V.regsIn, List.mem_flatten] at hr
            obtain ⟨rs, hrs, hr⟩ := hr
            exact (callOutput_fold st _ _ (fun _ _ => ⟨_, rfl⟩)).2 rs hrs r hr)
         | (obtain ⟨⟨n, hn⟩, -⟩ := loadConstantFull_cov _ _ _ _ st; exact ⟨n, by rw [hn]⟩)
         | exact ⟨_, _, _, _, rfl, rfl, logicSize_of ‹_›, ofNat?_value ‹_›⟩
         | exact ⟨_, _, _, _, rfl, rfl, logicSize64_lt ‹_›, ofNat?_value ‹_›⟩
         | exact ⟨_, _, _, _, rfl, rfl, logicSize64_ge ‹_› ‹_›, ofNat?_value ‹_›⟩
         | exact ⟨_, rfl, ofNat?_value ‹_›⟩
         | exact ⟨_, _, _, rfl, rfl, uimm12_of ‹_›⟩
         | exact ⟨_, rfl, simm9_of ‹_›⟩
         | exact ⟨_, _, rfl, rfl⟩
         | exact ⟨_, rfl, rfl⟩
         | exact ⟨_, _, _, _, rfl, rfl⟩
         | exact ⟨_, _, _, rfl, List.mem_of_getElem? ‹_›, rfl⟩
         | exact ⟨fun r hr => by simp_all [V.regsIn, regsInL], fun _ => rfl⟩
         | (refine ⟨fun r hr => ?_, rfl⟩
            simp only [V.regsIn, List.mem_singleton] at hr
            subst hr
            exact hvr _ _ ‹_›)
         | skip)
      | skip


private def ConstructorContract (t : Term) (args : List V) (st : LState)
    (v : V) (next : LState) : Prop :=
  (∃ q ty, tyPred t.id = some q ∧ args = [.ty ty] ∧ q ty = true ∧ v = .ty ty ∧ next = st) ∨
    CtorCov t.id args st v next

set_option maxHeartbeats 4000000 in
private theorem constructorContract_sound {f : Clif.Function} {ctx : Ctx}
    (hLI : LogicImmComplete) (s0 : LState) (as : List AW) (vs : List V) (term : Term)
    (v : V) (st st' : LState) (hvs : Holds2 f ctx as vs) (hIs : CovSince s0 st)
    (hpre : apre term.id as = true) (contract : ConstructorContract term vs st v st') :
    γ f ctx (actor term.id as) v ∧ CovSince s0 st' := by
  rcases contract with
    ⟨q, ty, hq, rfl, hqt, rfl, rfl⟩ | hc
  · refine ⟨?_, hIs⟩
    obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    unfold Cov.actor
    rw [hq]
    simp only
    split
    · rename_i ts hts
      cases a with
      | ty ts' =>
        simp only [tysOf, Option.some.injEq] at hts
        subst hts
        obtain ⟨t, ht, he⟩ := ha
        cases he
        exact ⟨_, List.mem_filter.mpr ⟨ht, hqt⟩, rfl⟩
      | _ => simp [tysOf] at hts
    · exact γ_c0 ⟨rfl, rfl⟩
  refine ⟨?_, ?_⟩
  rotate_left
  · obtain ⟨ms0, h0, h1⟩ := hIs
    obtain ⟨ms, h2, h3⟩ := hc.emit
    refine ⟨ms0 ++ ms, by rw [h2, h0]; simp, fun m hm => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact h1 m hm
    · exact emitOk_cov hvs hpre (h3 m hm)
  have hr := hc.res
  unfold CtorRes at hr
  rw [actor_none hc.tp]
  unfold actorRest
  by_cases hid : (term.id == TId.temp_writable_reg) = true
  · rw [if_pos hid] at hr ⊢
    obtain ⟨ty, cls, n, rfl, hcls, rfl⟩ := hr
    obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    simp only
    split
    · rename_i ts hts
      cases a with
      | ty ts' =>
        simp only [tysOf, Option.some.injEq] at hts
        subst hts
        obtain ⟨t, ht, he⟩ := ha
        cases he
        exact ⟨_, rfl, clsMask_mem ht hcls⟩
      | _ => simp [tysOf] at hts
    · refine ⟨_, rfl, ?_⟩
      cases cls <;> simp [Reg.kind]
  rw [if_neg hid] at hr ⊢
  by_cases hid1' : (term.id == TId.put_in_reg || term.id == TId.put_extended_in_reg || term.id == TId.load_constant_full) = true
  · rw [if_pos hid1'] at hr ⊢
    obtain ⟨n, rfl⟩ := hr
    exact ⟨_, rfl, by simp [Reg.kind]⟩
  rw [if_neg hid1'] at hr ⊢
  by_cases hid2' : (term.id == TId.put_in_regs || term.id == TId.put_in_regs_vec) = true
  · rw [if_pos hid2'] at hr ⊢
    exact ⟨fun r hrr => by obtain ⟨n, rfl⟩ := hr.1 r hrr; simp [Reg.kind], fun _ => hr.2⟩
  rw [if_neg hid2'] at hr ⊢
  by_cases hid2o : (term.id == TId.gen_call_output) = true
  · rw [if_pos hid2o] at hr ⊢
    exact ⟨fun r hrr => by obtain ⟨n, c, rfl⟩ := hr.1 r hrr; cases c <;> simp [Reg.kind],
      fun _ => hr.2.1⟩
  rw [if_neg hid2o] at hr ⊢
  by_cases hid3' : (term.id == TId.zero_reg || term.id == TId.writable_zero_reg) = true
  · rw [if_pos hid3'] at hr ⊢
    subst hr
    exact ⟨_, rfl, by simp [Reg.kind]⟩
  rw [if_neg hid3'] at hr ⊢
  by_cases hid4' : (term.id == TId.is_pic) = true
  · rw [if_pos hid4'] at hr ⊢; exact hr
  rw [if_neg hid4'] at hr ⊢
  by_cases hid5' : (term.id == TId.use_fp16) = true
  · rw [if_pos hid5'] at hr ⊢; exact hr
  rw [if_neg hid5'] at hr ⊢
  by_cases hid6' : (term.id == TId.emit) = true
  · rw [if_pos hid6'] at hr ⊢; subst hr; exact γ_c0 ⟨rfl, rfl⟩
  rw [if_neg hid6'] at hr ⊢
  by_cases hid7' : (term.id == TId.writable_reg_to_reg) = true
  · rw [if_pos hid7'] at hr ⊢
    subst hr
    obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    exact ha
  rw [if_neg hid7'] at hr ⊢
  by_cases hid8' : (term.id == TId.value_regs_get) = true
  · rw [if_pos hid8'] at hr ⊢
    obtain ⟨a', i, r, rfl, hra, rfl⟩ := hr
    obtain ⟨a, b, rfl, ha, -⟩ := holds2_two hvs
    exact ⟨r, rfl, (deep_sound a a' ha).1 r hra⟩
  rw [if_neg hid8'] at hr ⊢
  by_cases hid9' : (term.id == TId.value_reg || term.id == TId.value_regs || term.id == TId.output || term.id == TId.output_vec || term.id == TId.output_none) = true
  · rw [if_pos hid9'] at hr ⊢
    refine ⟨fun r hrr => ?_, fun hcv => hr.2 (covVL_of_deepL hvs hcv)⟩
    obtain ⟨w, hw, hrw⟩ := regsInL_mem' (hr.1 r hrr)
    exact (deepL_sound as vs hvs w hw).1 r hrw
  rw [if_neg hid9'] at hr ⊢
  by_cases hid10' : (term.id == TId.imm_logic_from_u64 || term.id == TId.u64_into_imm_logic) = true
  · rw [if_pos hid10'] at hr ⊢
    obtain ⟨t, n, i, sz, rfl, rfl, hls, hi⟩ := hr
    obtain ⟨a, b, rfl, ha, -⟩ := holds2_two hvs
    simp only
    split
    · rename_i ts hts
      cases a with
      | ty ts' =>
        simp only [tysOf, Option.some.injEq] at hts
        subst hts
        obtain ⟨t', ht, he⟩ := ha
        cases he
        exact oneSize_sound hLI ht hls hi
      | _ => simp [tysOf] at hts
    · exact γ_c0 ⟨rfl, rfl⟩
  rw [if_neg hid10'] at hr ⊢
  by_cases hid11' : (term.id == TId.imm_logic_from_imm64) = true
  · rw [if_pos hid11'] at hr ⊢
    obtain ⟨t, n, i, sz, rfl, rfl, hls, hi⟩ := hr
    obtain ⟨a, b, rfl, ha, -⟩ := holds2_two hvs
    simp only
    split
    · rename_i ts hts
      cases a with
      | ty ts' =>
        simp only [tysOf, Option.some.injEq] at hts
        subst hts
        obtain ⟨t', ht, he⟩ := ha
        cases he
        exact oneSize_sound hLI ht hls hi
      | _ => simp [tysOf] at hts
    · exact γ_c0 ⟨rfl, rfl⟩
  rw [if_neg hid11'] at hr ⊢
  by_cases hid12' : (term.id == TId.shift_mask || term.id == TId.rotr_mask) = true
  · rw [if_pos hid12'] at hr ⊢
    obtain ⟨i, rfl, hi⟩ := hr
    exact ⟨i, rfl, hi, fun op hop => hLI i _ op hi hop⟩
  rw [if_neg hid12'] at hr ⊢
  by_cases hid13' : (term.id == TId.uimm12_scaled_from_i64 || term.id == TId.uimm12_scaled_nonzero_from_i64) = true
  · rw [if_pos hid13'] at hr ⊢
    obtain ⟨x, t, o, rfl, rfl, h1, h2⟩ := hr
    obtain ⟨a, b, rfl, -, hb⟩ := holds2_two hvs
    simp only
    split
    · rename_i ts hts
      cases b with
      | ty ts' =>
        simp only [tysOf, Option.some.injEq] at hts
        subst hts
        obtain ⟨t', ht, he⟩ := hb
        cases he
        exact oneScale_sound ht h1 h2
      | _ => simp [tysOf] at hts
    · exact γ_c0 ⟨rfl, rfl⟩
  rw [if_neg hid13'] at hr ⊢
  by_cases hid14' : (term.id == TId.simm9_from_i64) = true
  · rw [if_pos hid14'] at hr ⊢
    obtain ⟨i, rfl, h1, h2⟩ := hr
    exact ⟨i, rfl, h1, h2⟩
  rw [if_neg hid14'] at hr ⊢
  by_cases hid15' : (term.id == TId.abi_stackslot_addr) = true
  · rw [if_pos hid15'] at hr ⊢
    obtain ⟨rd, sv, off, x, rfl, rfl⟩ := hr
    obtain ⟨a, b, c, rfl, ha, -, -⟩ := holds2_three hvs
    exact ⟨_, rfl, ha, ⟨_, rfl, γ_c0 ⟨rfl, rfl⟩, trivial⟩, trivial⟩
  rw [if_neg hid15'] at hr ⊢
  by_cases hid16' : (term.id == TId.cond_br_zero) = true
  · rw [if_pos hid16'] at hr ⊢
    obtain ⟨r, sv, rfl, rfl⟩ := hr
    obtain ⟨a, b, rfl, ha, hb⟩ := holds2_two hvs
    exact ⟨_, rfl, ha, hb, trivial⟩
  rw [if_neg hid16'] at hr ⊢
  by_cases hid17' : (term.id == TId.cond_br_not_zero) = true
  · rw [if_pos hid17'] at hr ⊢
    obtain ⟨r, sv, rfl, rfl⟩ := hr
    obtain ⟨a, b, rfl, ha, hb⟩ := holds2_two hvs
    exact ⟨_, rfl, ha, hb, trivial⟩
  rw [if_neg hid17'] at hr ⊢
  by_cases hid18' : (term.id == TId.cond_br_cond) = true
  · rw [if_pos hid18'] at hr ⊢
    obtain ⟨c, rfl, rfl⟩ := hr
    obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    exact ⟨_, rfl, ha, trivial⟩
  rw [if_neg hid18'] at hr ⊢
  exact ⟨fun r _ => kind_and_15 r, fun hcv => hr (covVL_of_deepL hvs hcv)⟩

private theorem delegate_contract {ctx : Ctx}
    (mapped : ∀ x r, ctx.valueReg? x = some r → ∃ n, r = .vreg n .int)
    {t : Term} {args : List V} {st next : State} {v : V}
    (h : (match Backend.externCtor ctx t args st.base with
      | .ok (v, base) => ExtResult.ok (v, { st with base })
      | .fail => ExtResult.fail
      | .unmodeled e => ExtResult.unmodeled e) = ExtResult.ok (v, next)) :
    ConstructorContract t args st.base v next.base := by
  cases call : Backend.externCtor ctx t args st.base with
  | fail => rw [call] at h; cases h
  | unmodeled e => rw [call] at h; cases h
  | ok pair =>
    rcases pair with ⟨value, base⟩
    rw [call] at h
    cases h
    exact externCtor_cov_mapped ctx mapped t args st.base _ base call

private theorem marks_base (st : State) (vs : List Nat) :
    (vs.foldl State.mark st).base = st.base := by
  induction vs generalizing st with
  | nil => rfl
  | cons v vs ih => exact ih (st.mark v)

private def fields (st : State) := st.base

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


private def callOutputList (returns : List Clif.AbiParam) (st : LState) : List (List Reg) × LState :=
  returns.foldl (fun acc _ =>
    (acc.1 ++ [[(acc.2.fresh .int).1]], (acc.2.fresh .int).2)) ([], st)

private theorem callOutputList_fields (returns : List Clif.AbiParam) (st : LState) :
    (callOutputList returns st).2.emitted = st.emitted ∧
      ∀ r ∈ (V.regsVec (callOutputList returns st).1).regsIn, ∃ n, r = .vreg n .int := by
  have inv : ∀ acc : List (List Reg) × LState,
      acc.2.emitted = st.emitted ∧
        (∀ rs ∈ acc.1, ∀ r ∈ rs, ∃ n, r = .vreg n .int) →
      (returns.foldl (fun acc _ =>
        (acc.1 ++ [[(acc.2.fresh .int).1]], (acc.2.fresh .int).2)) acc).2.emitted = st.emitted ∧
        ∀ rs ∈ (returns.foldl (fun acc _ =>
          (acc.1 ++ [[(acc.2.fresh .int).1]], (acc.2.fresh .int).2)) acc).1,
          ∀ r ∈ rs, ∃ n, r = .vreg n .int := by
    intro acc holds
    apply foldl_inv (fun a : List (List Reg) × LState =>
      a.2.emitted = st.emitted ∧ ∀ rs ∈ a.1, ∀ r ∈ rs, ∃ n, r = .vreg n .int)
      _ returns acc holds
    intro ret member a old
    refine ⟨by simp [LState.fresh, old.1], ?_⟩
    intro rs hrs r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hrs
    rcases hrs with hrs | rfl
    · exact old.2 rs hrs r hr
    · simp only [List.mem_singleton] at hr
      subst r
      exact ⟨_, rfl⟩
  have result := inv ([], st) ⟨rfl, by simp⟩
  refine ⟨result.1, ?_⟩
  intro r member
  change r ∈ (callOutputList returns st).1.flatten at member
  obtain ⟨rs, hrs, hr⟩ := List.mem_flatten.mp member
  exact result.2 rs hrs r hr

private theorem stock_constructor_contract {ctx : Ctx}
    (mapped : ∀ x r, ctx.valueReg? x = some r → ∃ n, r = .vreg n .int)
    {t : Term} {args : List V} {st next : State} {v : V}
    (h : Stock.externCtor ctx t args st = .ok (v, next)) :
    ConstructorContract t args st.base v next.base := by
  unfold ConstructorContract
  unfold Stock.externCtor at h
  split at h
  all_goals dsimp only at h
  all_goals try simp only [marks_base] at *
  all_goals try solve | exact delegate_contract mapped h
  all_goals repeat' first
    | (solve | cases h)
    | (solve | cases h; right; refine ⟨?_, emitOk_nil, ?_⟩ <;>
        simp_all (config := {decide := true}) [tyPred, CtorRes, covV, State.mark])
    | (solve |
        cases h
        right
        refine ⟨?_, ?_, ?_⟩
        · simp_all (config := {decide := true}) [tyPred]
        · exact emit_one _ _ _ (.inl rfl)
        · simp_all (config := {decide := true}) [CtorRes, covV])
    | (solve | exact delegate_contract mapped h)
    | (solve | cases h; exact externCtor_cov_mapped ctx mapped _ _ _ _ _ (by assumption))
    | (solve | cases h; simpa only [marks_base] using
        (externCtor_cov_mapped ctx mapped _ _ _ _ _ (by assumption)))
    | (solve | simp_all (config := {decide := true}))
    | split at h
  case h_10 =>
    rename_i _ _ sig same
    cases h
    right
    have result := callOutputList_fields sig.returns st.base
    refine ⟨by simp_all (config := {decide := true}) [tyPred], ?_, ?_⟩
    · exact ⟨[], by simpa [callOutputList] using result.1, by simp⟩
    · simpa (config := {decide := true}) only [same, CtorRes, ite_false, ite_true, callOutputList] using
        (show (∀ r ∈ (V.regsVec (callOutputList sig.returns st.base).1).regsIn,
            ∃ n c, r = .vreg n c) ∧ covV (V.regsVec (callOutputList sig.returns st.base).1) = true ∧
            ∃ s, [V.op (.sig sig)] = [V.op (.sig s)] from
          ⟨fun r hr => by obtain ⟨n, rfl⟩ := result.2 r hr; exact ⟨n, _, rfl⟩, rfl, sig, rfl⟩)
  case h_2 =>
    rename_i _ _ sig _ _ ps _ merged middle regs folded
    cases h
    have base := try_fold_fields ps ctx.tryRegs.1
      ((payloadRegs sig.callConv).zip ctx.tryRegs.2) st [] folded
    right
    refine ⟨by simp_all (config := {decide := true}) [tyPred], ?_, ?_⟩
    · simp only [fields] at base
      exact ⟨[], by simp [base], by simp⟩
    · simp_all (config := {decide := true}) [CtorRes, covV]

/-- Actual Stock constructors return the values described by the unchanged
coverage transfer function even when source IDs differ from register IDs. -/
theorem ctor_value_sound {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (hLI : LogicImmComplete)
    {as : List AW} {vs : List V} {term : Term} {v : V} {st next : State}
    (held : Holds2 f (sourceIdentityCtx ctx) as vs) (pre : apre term.id as = true)
    (run : (Stock.sem ctx).ctor term vs st = .ok (v, next)) :
    γ f (sourceIdentityCtx ctx) (Cov.actor term.id as) v := by
  have contract := stock_constructor_contract mapped.valueReg run
  have initial : CovSince st.base st.base := ⟨[], by simp, by simp⟩
  exact (constructorContract_sound hLI st.base as vs term v st.base next.base held initial pre contract).1

/-- Stock's `gen_call_output` gives int vregs: `Stock.externCtor` allocates one int vreg per
explicit return (typed calls, S11e5a, type `Backend.externCtor`'s only), and one it delegates (an
argument other than a signature) fails, since `Backend.externCtor`'s needs a signature
(`CtorRes`). -/
private theorem stock_gen_call_output_int {ctx : Ctx}
    (mapped : ∀ x r, ctx.valueReg? x = some r → ∃ n, r = .vreg n .int)
    {t : Term} {args : List V} {st next : State} {v : V} (hid : t.id = TId.gen_call_output)
    (h : Stock.externCtor ctx t args st = .ok (v, next)) :
    (∀ r ∈ v.regsIn, ∃ n, r = .vreg n .int) ∧ covV v = true := by
  unfold Stock.externCtor at h
  split at h
  all_goals dsimp only at h
  all_goals try (exfalso; clear h; simp_all (config := {decide := true}); done)
  all_goals first
    | (rename_i sig _
       cases h
       exact ⟨(callOutputList_fields sig.returns st.base).2, rfl⟩)
    | (split at h
       all_goals try (cases h; done)
       rename_i v' b hb
       cases h
       rcases externCtor_cov_mapped ctx mapped _ _ _ _ _ hb with ⟨q, ty, hq, -, -, -, -⟩ | hc
       · rw [hid] at hq
         have h0 : tyPred TId.gen_call_output = none := rfl
         rw [h0] at hq
         cases hq
       · have hr := hc.res
         unfold CtorRes at hr
         rw [hid] at hr
         simp (config := { decide := true }) only [↓reduceIte] at hr
         obtain ⟨-, -, s, hs⟩ := hr
         exfalso
         clear hb hc
         simp_all)

/-- **Stock constructors with integer calls**: actual Stock constructors return the values
described by `Cov.actorI`, the coverage transfer function whose `gen_call_output` gives int vregs
(`Cov.actor` before typed calls, S11e5a); `ctor_value_sound` is the same for `Cov.actor`, whose
`gen_call_output` gives vregs of either class. -/
theorem ctor_value_sound_int {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (hLI : LogicImmComplete)
    {as : List AW} {vs : List V} {term : Term} {v : V} {st next : State}
    (held : Holds2 f (sourceIdentityCtx ctx) as vs) (pre : apre term.id as = true)
    (run : (Stock.sem ctx).ctor term vs st = .ok (v, next)) :
    γ f (sourceIdentityCtx ctx) (Cov.actorI term.id as) v := by
  unfold Cov.actorI
  by_cases hid : term.id = TId.gen_call_output
  · rw [if_pos (beq_iff_eq.mpr hid)]
    obtain ⟨hregs, hcov⟩ := stock_gen_call_output_int mapped.valueReg hid run
    exact ⟨fun r hr => by obtain ⟨n, rfl⟩ := hregs r hr; simp [Reg.kind], fun _ => hcov⟩
  · rw [if_neg (fun h => hid (beq_iff_eq.mp h))]
    exact ctor_value_sound mapped hLI held pre run


end Backend.Stock.Proof.Coverage

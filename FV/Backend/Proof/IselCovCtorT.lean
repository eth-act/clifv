import FV.Backend.Proof.IselCovCtor
import FV.Backend.Proof.IselCovLeT
import FV.Backend.Proof.IselCovExtT

/-!
# Form coverage over float-capable contexts: the extern constructors

`externCtor_covT`: every successful extern constructor call (past the type predicates) emits only
covered instructions, `emit`'s instruction, or `gen_call_args`' stores of argument registers, and
returns what `CtorResT` states — `CtorRes` with the register-producing constructors class-aware
(`put_in_reg`/`put_extended_in_reg` give a vreg of any class, as `ctx.valueReg?` returns the
value's own vreg). `ctor_soundT`: `actorC` describes the result and the emitted instructions are
covered, over a float-capable context.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

/-!
# Form coverage of the ISLE lowering (V3): the extern constructors

`externCtor_cov`: every successful extern constructor call (past the type predicates) emits only
covered instructions, `emit`'s instruction, or `gen_call_args`' stores of argument registers, and
returns what `CtorResT` states (the shapes `actor` relies on).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

/-- The result of extern constructor `id` on `args`, as `actor` needs it. -/
def CtorResT (id : TermId) (args : List V) (v : V) : Prop :=
  if id == TId.temp_writable_reg then
    ∃ ty cls n, args = [.ty ty] ∧ ty.regClass? = some cls ∧ v = .reg (.vreg n cls)
  else if id == TId.put_in_reg || id == TId.put_extended_in_reg || id == TId.load_constant_full then
    ∃ n c, v = .reg (.vreg n c)
  else if id == TId.put_in_regs || id == TId.put_in_regs_vec then
    (∀ r ∈ v.regsIn, ∃ n c, r = .vreg n c) ∧ covV v
  else if id == TId.gen_call_output then
    (∀ r ∈ v.regsIn, ∃ n c, r = .vreg n c) ∧ covV v ∧ ∃ s, args = [.op (.sig s)]
  else if id == TId.zero_reg || id == TId.writable_zero_reg then v = .reg .xzr
  else if id == TId.is_pic then v = .bool true
  else if id == TId.use_fp16 then v = .bool false
  else if id == TId.emit then v = .op .unit
  else if id == TId.writable_reg_to_reg then args = [v]
  else if id == TId.value_regs_get then ∃ a i r, args = [a, i] ∧ r ∈ a.regsIn ∧ v = .reg r
  else if id == TId.value_reg || id == TId.value_regs || id == TId.output || id == TId.output_vec ||
      id == TId.output_none then
    (∀ r ∈ v.regsIn, r ∈ regsInL args) ∧ (covVL args = true → covV v = true)
  else if id == TId.imm_logic_from_u64 || id == TId.u64_into_imm_logic then
    ∃ t n i sz, args = [.ty t, .int n] ∧ v = .op (.immLogic i) ∧ logicSize t = some sz ∧
      ImmLogic.ofNat? i.value sz = some i
  else if id == TId.imm_logic_from_imm64 then
    ∃ t n i sz, args = [.ty t, .int n] ∧ v = .op (.immLogic i) ∧ logicSize64 t = some sz ∧
      ImmLogic.ofNat? i.value sz = some i
  else if id == TId.shift_mask || id == TId.rotr_mask then
    ∃ i, v = .op (.immLogic i) ∧ ImmLogic.ofNat? i.value .size32 = some i
  else if id == TId.uimm12_scaled_from_i64 || id == TId.uimm12_scaled_nonzero_from_i64 then
    ∃ x t o, args = [.int x, .ty t] ∧ v = .op (.uimm12Scaled o) ∧ o % t.bytes = 0 ∧ o / t.bytes < 4096
  else if id == TId.simm9_from_i64 then ∃ i, v = .op (.simm9 i) ∧ -256 ≤ i ∧ i < 256
  else if id == TId.abi_stackslot_addr then
    ∃ rd s off x, args = [rd, s, off] ∧
      v = .data tyMInst VIdx.MInst.LoadAddr [rd, .data tyAMode VIdx.AMode.SlotOffset [.int x]]
  else if id == TId.cond_br_zero then
    ∃ r s, args = [r, s] ∧ v = .data tyCondBrKind VIdx.CondBrKind.Zero [r, s]
  else if id == TId.cond_br_not_zero then
    ∃ r s, args = [r, s] ∧ v = .data tyCondBrKind VIdx.CondBrKind.NotZero [r, s]
  else if id == TId.cond_br_cond then
    ∃ c, args = [c] ∧ v = .data tyCondBrKind VIdx.CondBrKind.Cond [c]
  else covVL args = true → covV v = true

/-- The contract of one constructor call past the type predicates. -/
structure CtorCovT (id : TermId) (args : List V) (st : LState) (v : V) (st' : LState) : Prop where
  tp : tyPred id = none
  emit : ∃ ms : List MInst, st'.emitted = st.emitted ++ ms.toArray ∧ ∀ m ∈ ms, EmitOk id args m
  res : CtorResT id args v

/-- `CtorCovT` of every successful result. -/
def CtorCovP (st : LState) (id : TermId) (args : List V) (r : ExtResult (V × LState)) : Prop :=
  ∀ v st', r = .ok (v, st') → CtorCovT id args st v st'

/-! ## Helpers -/

theorem regsVec_single_vregT {ctx : Ctx} (hvr : ∀ x r, ctx.valueReg? x = some r →
    ∃ n c, r = .vreg n c) {vs : List Nat} {rs : List Reg} (h : vs.mapM ctx.valueReg? = some rs) :
    (∀ r ∈ (V.regsVec (rs.map fun r => [r])).regsIn, ∃ n c, r = .vreg n c) ∧
      covV (V.regsVec (rs.map fun r => [r])) = true := by
  refine ⟨fun r hr => ?_, rfl⟩
  have hr' : r ∈ rs := by
    simp only [V.regsIn, List.mem_flatten, List.mem_map] at hr
    obtain ⟨_, ⟨a, ha, rfl⟩, hr⟩ := hr
    simp only [List.mem_singleton] at hr
    exact hr ▸ ha
  obtain ⟨x, -, he⟩ := mapM_mem h r hr'
  obtain ⟨n, c, hn⟩ := hvr _ _ he
  exact ⟨n, c, hn⟩

/-- **Every extern constructor** past the type predicates satisfies `CtorCovT`. -/
theorem externCtor_covT (ctx : Ctx) (hvr : ∀ x r, ctx.valueReg? x = some r →
    ∃ n c, r = .vreg n c) (t : Term) (args : List V) (st : LState) (v : V) (st' : LState)
    (h : externCtor ctx t args st = .ok (v, st')) :
    (∃ q ty, tyPred t.id = some q ∧ args = [.ty ty] ∧ q ty = true ∧ v = .ty ty ∧ st' = st) ∨
      CtorCovT t.id args st v st' := by
  unfold externCtor at h
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
      | (simp (config := { decide := true }) only [CtorResT, ite_true, ite_false, Bool.false_eq_true,
          Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, ↓reduceIte]; done)
      | (simp (config := { decide := true }) only [CtorResT, ite_true, ite_false, Bool.false_eq_true,
          Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, ↓reduceIte]
         first
         | (intro _; rfl)
         | (intro hcv; simp only [covVL, Bool.and_true] at hcv; refine ⟨fun r hr => ?_, hcv⟩
            simp only [V.regsIn, List.mem_flatten] at hr
            obtain ⟨rs, hrs, hr⟩ := hr
            exact ⟨_, _, (callOutput_fold st _ _ (fun _ _ => ⟨_, rfl⟩)).2 rs hrs r hr⟩)
         | (intro _; simp [covV_data, covVL]; done)
         | exact ⟨_, _, _, rfl, ‹_›, rfl⟩
         | (rename_i heq; obtain ⟨n, c, hn⟩ := hvr _ _ heq; exact ⟨n, c, hn⟩)
         | (rename_i heq; obtain ⟨n, c, hn⟩ := hvr _ _ heq
            exact ⟨fun r hr => ⟨n, c, hn⟩, by rfl⟩)
         | (rename_i heq; obtain ⟨n, c, hn⟩ := hvr _ _ heq; exact ⟨n, c, hn⟩)
         | (obtain ⟨⟨n, hn⟩, -⟩ := loadConstantFull_cov _ _ _ _ st; exact ⟨n, .int, by rw [hn]⟩)
         -- class-aware residuals: pass-through ids, the `value_reg`/`output` family, `put_in_reg`
         | (intro hcv; exact covVL_iff.mp hcv _ (by simp))
         | (refine ⟨fun r hr => ?_, fun _ => rfl⟩
            simp [V.regsIn, regsInL] at hr ⊢
            exact hr)
         | (refine ⟨fun r hr => ?_, rfl⟩
            simp only [V.regsIn, List.mem_singleton] at hr
            subst hr
            exact hvr _ _ ‹_›)
         | exact regsVec_single_vregT hvr ‹_›
         | (obtain ⟨n, c, hn⟩ := hvr _ _ ‹_›; exact ⟨n, c, by rw [hn]⟩)
         | (refine ⟨_, _, _, rfl, ?_, rfl⟩; simp only [V.regsIn]; exact List.mem_of_getElem? ‹_›)
         | exact ⟨_, _, _, _, rfl, rfl⟩
         | (exact ⟨fun r hr => by
              simp only [V.regsIn, List.mem_flatten] at hr
              obtain ⟨rs, hrs, hr⟩ := hr
              exact (callOutput_fold st _ _ (fun _ _ => ⟨_, rfl⟩)).2 rs hrs r hr, rfl, ⟨_, rfl⟩⟩)
         | (exact ⟨_, _, _, _, rfl, rfl, ?_, ?_⟩; exact logicSize_of ‹_›; exact ofNat?_value ‹_›)
         | (exact ⟨_, _, _, _, rfl, rfl, ?_, ?_⟩; exact logicSize64_lt ‹_›; exact ofNat?_value ‹_›)
         | (exact ⟨_, _, _, _, rfl, rfl, ?_, ?_⟩; exact logicSize64_ge ‹_› ‹_›; exact ofNat?_value ‹_›)
         | (exact ⟨_, rfl, ?_⟩; exact ofNat?_value ‹_›)
         | (exact ⟨_, _, _, rfl, rfl, ?_⟩; exact uimm12_of ‹_›)
         | (exact ⟨_, rfl, ?_⟩; exact simm9_of ‹_›)
         | exact ⟨_, _, rfl, rfl⟩
         | exact ⟨_, rfl, rfl⟩
         | (exact ⟨_, _, _, _, rfl, rfl, logicSize_of ‹_›, ofNat?_value ‹_›⟩)
         | (exact ⟨_, _, _, _, rfl, rfl, logicSize64_lt ‹_›, ofNat?_value ‹_›⟩)
         | (exact ⟨_, _, _, _, rfl, rfl, logicSize64_ge ‹_› ‹_›, ofNat?_value ‹_›⟩)
         | (exact ⟨_, rfl, ofNat?_value ‹_›⟩)
         | (exact ⟨_, _, _, rfl, rfl, uimm12_of ‹_›⟩)
         | (exact ⟨_, rfl, simm9_of ‹_›⟩)
         | skip)

/-! ## The model's constructor field -/

variable {f : Clif.Function} {ctx : Ctx}

theorem kind_oneT {r : Reg} {m : Nat} (hk : r.kind &&& m ≠ 0) (hm : m &&& 14 = 0) :
    ∃ n c, r = .vreg n c := by
  rcases kind_cases r with h1 | h1 | h1 | h1
  · obtain ⟨n, h1⟩ := kind_int h1
    exact ⟨n, .int, h1⟩
  · obtain ⟨n, h1⟩ := kind_float h1
    exact ⟨n, .float, h1⟩
  · exfalso; apply hk; apply Nat.eq_of_testBit_eq; intro i
    have := congrArg (·.testBit i) hm
    simp only [Nat.testBit_and, Nat.zero_testBit] at this ⊢
    rw [h1] at hk
    rcases i with _ | _ | _ | _ | i <;> simp_all [Nat.testBit_succ]
  · exfalso; apply hk; apply Nat.eq_of_testBit_eq; intro i
    have := congrArg (·.testBit i) hm
    simp only [Nat.testBit_and, Nat.zero_testBit] at this ⊢
    rw [h1] at hk
    rcases i with _ | _ | _ | _ | i <;> simp_all [Nat.testBit_succ]

theorem oneSize_soundT (hLI : LogicImmComplete) {ts : List CTy} {g : CTy → Option OperandSize} {t : CTy} (ht : t ∈ ts)
    {sz : OperandSize} (hg : g t = some sz) {i : ImmLogic} (hi : ImmLogic.ofNat? i.value sz = some i) :
    γT S iOps fOps f ctx (oneSize ts g) (.op (.immLogic i)) := by
  unfold oneSize
  split
  · rename_i hn
    have : sz ∈ ts.filterMap g := List.mem_filterMap.mpr ⟨t, ht, hg⟩
    rw [hn] at this; cases this
  · rename_i s rest hsr
    split
    · rename_i hall
      have hm : sz ∈ s :: rest := hsr ▸ List.mem_filterMap.mpr ⟨t, ht, hg⟩
      have hss : sz = s := by
        rcases List.mem_cons.mp hm with h | h
        · exact h
        · have := List.all_eq_true.mp hall sz h
          cases sz <;> cases s <;> simp_all
      subst hss
      exact ⟨i, rfl, hi, fun op hop => hLI i _ op hi hop⟩
    · exact γ_c0T ⟨rfl, rfl⟩

theorem oneScale_soundT {ts : List CTy} {t : CTy} (ht : t ∈ ts) {o : Nat}
    (h1 : o % t.bytes = 0) (h2 : o / t.bytes < 4096) :
    γT S iOps fOps f ctx (oneScale ts) (.op (.uimm12Scaled o)) := by
  unfold oneScale
  split
  · rename_i b rest hbr
    split
    · rename_i hall
      have hm : t.bytes ∈ b :: rest := hbr ▸ List.mem_map.mpr ⟨t, ht, rfl⟩
      have hb : t.bytes = b := by
        rcases List.mem_cons.mp hm with h | h
        · exact h
        · have := List.all_eq_true.mp hall _ h; simpa using this
      rw [← hb]
      exact ⟨o, rfl, h1, h2⟩
    · exact γ_c0T ⟨rfl, rfl⟩
  · rename_i hn
    have : t.bytes ∈ ts.map CTy.bytes := List.mem_map.mpr ⟨t, ht, rfl⟩
    rw [hn] at this; cases this

theorem covVL_of_deepLT {as : List AW} {vs : List V} (h : Holds2T S iOps fOps f ctx as vs)
    (hc : (AW.deepL as).2 = true) : covVL vs = true :=
  covVL_iff.mpr fun w hw => (deepL_soundT as vs h w hw).2 hc

theorem emitOk_covT {id : TermId} {as : List AW} {vs : List V} (hvs : Holds2T S iOps fOps f ctx as vs)
    (hpre : apre id as = true) {m : MInst} (h : EmitOk id vs m) : Covered m = true := by
  rcases h with h | ⟨rfl, i, rfl, hi⟩ | ⟨rfl, r, b', off, rfl, s, rss, rfl, hr⟩
  · exact h
  · obtain ⟨a, rfl, ha⟩ := holds2_oneT hvs
    simp only [apre, beq_self_eq_true, ↓reduceIte] at hpre
    exact covV_ofV ((deep_soundT  a i ha).2 hpre) hi
  · obtain ⟨a, b, rfl, -, hb⟩ := holds2_twoT hvs
    have hne : (TId.gen_call_args == TId.emit) = false := by decide
    simp only [apre, hne, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, beq_iff_eq] at hpre
    obtain ⟨n, c, rfl⟩ := kind_oneT ((deep_soundT b _ hb).1 r hr) hpre
    have hop : storeOpOfBytes b' ≠ .fpuStore128 := by unfold storeOpOfBytes; split <;> simp
    cases c with
    | int => simp [stackArgStore, Reg.homeCls, Covered, FormOk, hop, memOk]
    | float =>
      have hsz : (if b' = 4 then ScalarSize.size32 else ScalarSize.size64) = .size64 ∨
          (if b' = 4 then ScalarSize.size32 else ScalarSize.size64) = .size32 := by
        by_cases h4 : b' = 4 <;> simp [h4]
      rcases hsz with hsz | hsz
      · rw [stackArgStore]; simp [Reg.homeCls, hsz, Covered, FormOk, hop, memOk]
      · rw [stackArgStore]; simp [Reg.homeCls, hsz, Covered, FormOk, hop, memOk]

set_option maxHeartbeats 4000000 in
/-- **Constructors**: `actor` describes the result, the emitted instructions are covered. -/
theorem ctor_soundT (hLI : LogicImmComplete) (hctx : CtxInvT f ctx) (s0 : LState) (as : List AW) (vs : List V) (term : Term)
    (v : V) (st st' : LState) (hvs : Holds2T S iOps fOps f ctx as vs) (hIs : CovSince s0 st)
    (hpre : apre term.id as = true) (h : (sem ctx).ctor term vs st = .ok (v, st')) :
    γT S iOps fOps f ctx (actorC term.id as) v ∧ CovSince s0 st' := by
  rw [sem_ctor] at h
  rcases externCtor_covT ctx (fun x r h => ⟨x, valClassOf ctx x, hctx.valueReg x r h⟩) term vs st v st' h with
    ⟨q, ty, hq, rfl, hqt, rfl, rfl⟩ | hc
  · refine ⟨?_, hIs⟩
    obtain ⟨a, rfl, ha⟩ := holds2_oneT hvs
    unfold actorC
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
    · exact γ_c0T ⟨rfl, rfl⟩
  refine ⟨?_, ?_⟩
  rotate_left
  · obtain ⟨ms0, h0, h1⟩ := hIs
    obtain ⟨ms, h2, h3⟩ := hc.emit
    refine ⟨ms0 ++ ms, by rw [h2, h0]; simp, fun m hm => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact h1 m hm
    · exact emitOk_covT hvs hpre (h3 m hm)
  have hr := hc.res
  have htp := hc.tp
  unfold CtorResT at hr
  unfold actorC
  simp only [htp]
  -- `actorC` overrides `put_in_reg`/`put_extended_in_reg`/`load_constant_full` (`.reg 3`) and
  -- `put_in_regs`/`put_in_regs_vec` (`.flat 3 true`), delegating the rest (incl.
  -- `temp_writable_reg`) to `actorRest`; dispatch `hr`'s chain in its own order
  by_cases hid0 : (term.id == TId.temp_writable_reg) = true
  · rw [if_pos hid0] at hr
    obtain ⟨ty, cls, n, rfl, hcls, rfl⟩ := hr
    by_cases hid1' : (term.id == TId.put_in_reg || term.id == TId.put_extended_in_reg || term.id == TId.load_constant_full) = true
    · rw [if_pos hid1'] at ⊢
      exact ⟨_, rfl, by cases cls <;> simp [Reg.kind]⟩
    rw [if_neg hid1'] at ⊢
    by_cases hid2' : (term.id == TId.put_in_regs || term.id == TId.put_in_regs_vec) = true
    · rw [if_pos hid2'] at ⊢
      refine ⟨fun r hrr => ?_, fun _ => rfl⟩
      simp only [V.regsIn, List.mem_singleton] at hrr
      subst hrr
      cases cls <;> simp [Reg.kind]
    rw [if_neg hid2'] at ⊢
    unfold actorRest
    rw [if_pos hid0] at ⊢
    obtain ⟨a, rfl, ha⟩ := holds2_oneT hvs
    cases a with
    | ty ts' =>
      simp only [tysOf]
      obtain ⟨t, ht, he⟩ := ha
      cases he
      exact ⟨_, rfl, clsMask_mem ht hcls⟩
    | _ =>
      simp only [tysOf]
      refine ⟨_, rfl, ?_⟩
      cases cls <;> simp [Reg.kind]
  rw [if_neg hid0] at hr
  by_cases hid1' : (term.id == TId.put_in_reg || term.id == TId.put_extended_in_reg || term.id == TId.load_constant_full) = true
  · rw [if_pos hid1'] at hr ⊢
    obtain ⟨n, c, rfl⟩ := hr
    exact ⟨_, rfl, by cases c <;> simp [Reg.kind]⟩
  rw [if_neg hid1'] at hr ⊢
  by_cases hid2' : (term.id == TId.put_in_regs || term.id == TId.put_in_regs_vec) = true
  · rw [if_pos hid2'] at hr ⊢
    exact ⟨fun r hrr => by obtain ⟨n, c, rfl⟩ := hr.1 r hrr; cases c <;> simp [Reg.kind], fun _ => hr.2⟩
  rw [if_neg hid2'] at hr ⊢
  unfold actorRest
  rw [if_neg hid0, if_neg hid1', if_neg hid2']
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
  · rw [if_pos hid6'] at hr ⊢; subst hr; exact γ_c0T ⟨rfl, rfl⟩
  rw [if_neg hid6'] at hr ⊢
  by_cases hid7' : (term.id == TId.writable_reg_to_reg) = true
  · rw [if_pos hid7'] at hr ⊢
    subst hr
    obtain ⟨a, rfl, ha⟩ := holds2_oneT hvs
    exact ha
  rw [if_neg hid7'] at hr ⊢
  by_cases hid8' : (term.id == TId.value_regs_get) = true
  · rw [if_pos hid8'] at hr ⊢
    obtain ⟨a', i, r, rfl, hra, rfl⟩ := hr
    obtain ⟨a, b, rfl, ha, -⟩ := holds2_twoT hvs
    exact ⟨r, rfl, (deep_soundT a a' ha).1 r hra⟩
  rw [if_neg hid8'] at hr ⊢
  by_cases hid9' : (term.id == TId.value_reg || term.id == TId.value_regs || term.id == TId.output || term.id == TId.output_vec || term.id == TId.output_none) = true
  · rw [if_pos hid9'] at hr ⊢
    refine ⟨fun r hrr => ?_, fun hcv => hr.2 (covVL_of_deepLT hvs hcv)⟩
    obtain ⟨w, hw, hrw⟩ := regsInL_mem' (hr.1 r hrr)
    exact (deepL_soundT as vs hvs w hw).1 r hrw
  rw [if_neg hid9'] at hr ⊢
  by_cases hid10' : (term.id == TId.imm_logic_from_u64 || term.id == TId.u64_into_imm_logic) = true
  · rw [if_pos hid10'] at hr ⊢
    obtain ⟨t, n, i, sz, rfl, rfl, hls, hi⟩ := hr
    obtain ⟨a, b, rfl, ha, -⟩ := holds2_twoT hvs
    simp only
    split
    · rename_i ts hts
      cases a with
      | ty ts' =>
        simp only [tysOf, Option.some.injEq] at hts
        subst hts
        obtain ⟨t', ht, he⟩ := ha
        cases he
        exact oneSize_soundT hLI ht hls hi
      | _ => simp [tysOf] at hts
    · exact γ_c0T ⟨rfl, rfl⟩
  rw [if_neg hid10'] at hr ⊢
  by_cases hid11' : (term.id == TId.imm_logic_from_imm64) = true
  · rw [if_pos hid11'] at hr ⊢
    obtain ⟨t, n, i, sz, rfl, rfl, hls, hi⟩ := hr
    obtain ⟨a, b, rfl, ha, -⟩ := holds2_twoT hvs
    simp only
    split
    · rename_i ts hts
      cases a with
      | ty ts' =>
        simp only [tysOf, Option.some.injEq] at hts
        subst hts
        obtain ⟨t', ht, he⟩ := ha
        cases he
        exact oneSize_soundT hLI ht hls hi
      | _ => simp [tysOf] at hts
    · exact γ_c0T ⟨rfl, rfl⟩
  rw [if_neg hid11'] at hr ⊢
  by_cases hid12' : (term.id == TId.shift_mask || term.id == TId.rotr_mask) = true
  · rw [if_pos hid12'] at hr ⊢
    obtain ⟨i, rfl, hi⟩ := hr
    exact ⟨i, rfl, hi, fun op hop => hLI i _ op hi hop⟩
  rw [if_neg hid12'] at hr ⊢
  by_cases hid13' : (term.id == TId.uimm12_scaled_from_i64 || term.id == TId.uimm12_scaled_nonzero_from_i64) = true
  · rw [if_pos hid13'] at hr ⊢
    obtain ⟨x, t, o, rfl, rfl, h1, h2⟩ := hr
    obtain ⟨a, b, rfl, -, hb⟩ := holds2_twoT hvs
    simp only
    split
    · rename_i ts hts
      cases b with
      | ty ts' =>
        simp only [tysOf, Option.some.injEq] at hts
        subst hts
        obtain ⟨t', ht, he⟩ := hb
        cases he
        exact oneScale_soundT ht h1 h2
      | _ => simp [tysOf] at hts
    · exact γ_c0T ⟨rfl, rfl⟩
  rw [if_neg hid13'] at hr ⊢
  by_cases hid14' : (term.id == TId.simm9_from_i64) = true
  · rw [if_pos hid14'] at hr ⊢
    obtain ⟨i, rfl, h1, h2⟩ := hr
    exact ⟨i, rfl, h1, h2⟩
  rw [if_neg hid14'] at hr ⊢
  by_cases hid15' : (term.id == TId.abi_stackslot_addr) = true
  · rw [if_pos hid15'] at hr ⊢
    obtain ⟨rd, sv, off, x, rfl, rfl⟩ := hr
    obtain ⟨a, b, c, rfl, ha, -, -⟩ := holds2_threeT hvs
    exact ⟨_, rfl, ha, ⟨_, rfl, γ_c0T ⟨rfl, rfl⟩, trivial⟩, trivial⟩
  rw [if_neg hid15'] at hr ⊢
  by_cases hid16' : (term.id == TId.cond_br_zero) = true
  · rw [if_pos hid16'] at hr ⊢
    obtain ⟨r, sv, rfl, rfl⟩ := hr
    obtain ⟨a, b, rfl, ha, hb⟩ := holds2_twoT hvs
    exact ⟨_, rfl, ha, hb, trivial⟩
  rw [if_neg hid16'] at hr ⊢
  by_cases hid17' : (term.id == TId.cond_br_not_zero) = true
  · rw [if_pos hid17'] at hr ⊢
    obtain ⟨r, sv, rfl, rfl⟩ := hr
    obtain ⟨a, b, rfl, ha, hb⟩ := holds2_twoT hvs
    exact ⟨_, rfl, ha, hb, trivial⟩
  rw [if_neg hid17'] at hr ⊢
  by_cases hid18' : (term.id == TId.cond_br_cond) = true
  · rw [if_pos hid18'] at hr ⊢
    obtain ⟨c, rfl, rfl⟩ := hr
    obtain ⟨a, rfl, ha⟩ := holds2_oneT hvs
    exact ⟨_, rfl, ha, trivial⟩
  rw [if_neg hid18'] at hr ⊢
  exact ⟨fun r _ => kind_and_15 r, fun hcv => hr (covVL_of_deepLT hvs hcv)⟩
end Backend.Proof.Cov
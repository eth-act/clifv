import FV.Backend.Proof.IselCovTExt
import FV.Backend.Proof.IselCovCtor

/-!
# Form coverage over float-capable contexts (typed V3): the extern constructors

`externCtor_covT`: `IselCovCtor`'s `externCtor_cov` without the integer value registers: the
value register constructors (`put_in_reg`, `put_extended_in_reg`, `put_in_regs`,
`put_in_regs_vec`) give the values' registers (`CtorResT`), and the zero `movi` immediate is
`movModImmZero`. `ctor_sound`: `actor` describes the result over a float-capable context (a
value's vreg has its type's class, `CtxInvT.valueReg`), the emitted instructions are covered.
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
open Backend.Proof.Cov (EmitOk emitOk_nil emit_one LCCov
  loadConstantFull_cov ofNat?_value logicSize_of logicSize64_lt logicSize64_ge uimm12_of simm9_of
  callOutput_fold callArgs_fold callArgs_mem kind_one clsMask_mem sem_ctor
  regsInL_mem' LogicImmComplete logicSize logicSize64 clsMask)

/-- Every instruction emitted since `s0` is covered (`Covered`, the typed analysis's coverage). -/
def CovSince (s0 st : LState) : Prop :=
  ∃ ms : List MInst, st.emitted = s0.emitted ++ ms.toArray ∧ ∀ m ∈ ms, Covered m = true

/-- The integer analysis's `Cov.CovSince` gives the typed one. -/
theorem covSince_of_cov {s0 st : LState} (h : Cov.CovSince s0 st) : CovSince s0 st :=
  let ⟨ms, h1, h2⟩ := h
  ⟨ms, h1, fun m hm => covered_of_cov (h2 m hm)⟩

theorem covSince_refl (s : LState) : CovSince s s := ⟨[], by simp, by simp⟩

theorem covV_ofV {v : V} {m : MInst} (hc : covV v = true) (h : MInst.ofV v = some m) :
    Covered m = true := by
  cases v with
  | data t k fs =>
    rw [covV_data] at hc
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hc
    rcases hc.1 with h1 | h1
    · exfalso
      unfold MInst.ofV at h
      obtain ⟨_, he, -⟩ := bind_some_ex h
      simp only [V.enumOf?] at he
      split at he
      · contradiction
      · cases he
    · rw [h] at h1; exact h1
  | _ =>
    unfold MInst.ofV at h
    obtain ⟨_, he, -⟩ := bind_some_ex h
    simp [V.enumOf?] at he

/-- The result of extern constructor `id` on `args`, as the typed `actor` needs it (the value
register constructors give the value's register, of its class). -/
def CtorResT (ctx : Ctx) (id : TermId) (args : List V) (v : V) : Prop :=
  if id == TId.temp_writable_reg then
    ∃ ty cls n, args = [.ty ty] ∧ ty.regClass? = some cls ∧ v = .reg (.vreg n cls)
  else if id == TId.put_in_reg then
    ∃ x r, args = [.value x] ∧ ctx.valueReg? x = some r ∧ v = .reg r
  else if id == TId.put_extended_in_reg then
    ∃ x e r, args = [.op (.extended x e)] ∧ ctx.valueReg? x = some r ∧ v = .reg r
  else if id == TId.load_constant_full then ∃ n, v = .reg (.vreg n .int)
  else if id == TId.is_sinkable_inst then False
  else if id == TId.emit_u64_le_const then ∃ n, v = .op (.vcodeConst n)
  else if id == TId.put_in_regs then
    ∃ x r, args = [.value x] ∧ ctx.valueReg? x = some r ∧ v = .regs [r]
  else if id == TId.put_in_regs_vec then
    ∃ xs rs, args = [.values xs] ∧ xs.mapM ctx.valueReg? = some rs ∧ v = .regsVec (rs.map fun r => [r])
  else if id == TId.asimd_mov_mod_imm_zero then
    ∃ s sz, args = [s] ∧ s.scalarSize? = some sz ∧ v = .op (.movModImm (movModImmZero sz))
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
structure CtorCovT (ctx : Ctx) (id : TermId) (args : List V) (st : LState) (v : V) (st' : LState) :
    Prop where
  tp : tyPred id = none
  emit : ∃ ms : List MInst, st'.emitted = st.emitted ++ ms.toArray ∧ ∀ m ∈ ms, EmitOk id args m
  res : CtorResT ctx id args v

/-- `CtorCovT` of every successful result. -/
def CtorCovTP (ctx : Ctx) (st : LState) (id : TermId) (args : List V) (r : ExtResult (V × LState)) :
    Prop :=
  ∀ v st', r = .ok (v, st') → CtorCovT ctx id args st v st'

set_option maxHeartbeats 8000000 in
/-- **Every extern constructor** past the type predicates satisfies `CtorCov`. -/
theorem externCtor_covT (ctx : Ctx) (t : Term) (args : List V) (st : LState) (v : V) (st' : LState)
    (h : externCtor ctx t args st = .ok (v, st')) :
    (∃ q ty, tyPred t.id = some q ∧ args = [.ty ty] ∧ q ty = true ∧ v = .ty ty ∧ st' = st) ∨
      CtorCovT ctx t.id args st v st' := by
  unfold externCtor at h
  split at h
  · rename_i q ty hq
    split at h
    · cases h; exact .inl ⟨q, ty, hq, rfl, ‹_›, rfl, rfl⟩
    · cases h
  · right
    revert h v st'
    apply externCtor_split _ (CtorCovTP ctx st)
    all_goals
      intros
      unfold CtorCovTP
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
         | (intro hc; simp only [covVL, Bool.and_true] at hc; exact hc)
         | (intro _; simp [covV_data, covVL]; done)
         | exact ⟨_, _, _, rfl, ‹_›, rfl⟩
         | exact ⟨_, _, rfl, ‹_›, rfl⟩
         | exact ⟨_, _, _, rfl, ‹_›, rfl⟩
         | exact ⟨_, _, rfl, ‹_›, rfl⟩
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
         | exact ⟨_, rfl⟩
         | exact ⟨_, _, rfl, rfl⟩
         | exact ⟨_, rfl, rfl⟩
         | exact ⟨_, _, _, _, rfl, rfl⟩
         | exact ⟨_, _, _, rfl, List.mem_of_getElem? ‹_›, rfl⟩
         | exact ⟨fun r hr => by simp_all [V.regsIn, regsInL], fun _ => rfl⟩
         | exact ⟨_, _, rfl, ‹_›, rfl⟩
         | skip)
      | skip

theorem or_and_ne {a b k : Nat} (h : a &&& k ≠ 0) : (a ||| b) &&& k ≠ 0 := by
  intro h0; apply h; apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (·.testBit i) h0
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at this ⊢
  cases ha : a.testBit i <;> cases hk : k.testBit i <;> simp_all

theorem or_and_ne' {a b k : Nat} (h : b &&& k ≠ 0) : (a ||| b) &&& k ≠ 0 := by
  rw [Nat.or_comm]; exact or_and_ne h

/-- A bit of the start or of one element survives an or-fold. -/
theorem foldl_or_ne {α : Type} (g : α → Nat) (k : Nat) : ∀ (l : List α) (m0 : Nat),
    (m0 &&& k ≠ 0 ∨ ∃ t ∈ l, g t &&& k ≠ 0) → l.foldl (fun m t => m ||| g t) m0 &&& k ≠ 0
  | [], _, h => by
    rcases h with h | ⟨t, ht, _⟩
    · exact h
    · cases ht
  | a :: l, m0, h => by
    rw [List.foldl_cons]
    apply foldl_or_ne g k l
    rcases h with h | ⟨t, ht, hg⟩
    · exact .inl (or_and_ne h)
    · rcases List.mem_cons.mp ht with rfl | ht
      · exact .inl (or_and_ne' hg)
      · exact .inr ⟨t, ht, hg⟩

theorem kind_vreg3 (n : Nat) (c : RegClass) : (Reg.vreg n c).kind &&& 3 ≠ 0 := by
  cases c <;> simp [Reg.kind]

/-- The vreg of a value of one of the types `ts` is of a kind of `vcls ts`. -/
theorem vcls_valIn {x : Nat} {ts : List CTy} (h : ValIn ctx x ts) :
    (Reg.vreg x (valClassOf ctx x)).kind &&& vcls ts ≠ 0 := by
  unfold vcls
  rw [Nat.and_comm]
  refine foldl_or_ne (fun t : CTy => match t.valClass with | .int => 1 | .float => 2) _ ts 0 (.inr ?_)
  cases hty : ctx.valueType? x with
  | none =>
    obtain ⟨t, ht, hc⟩ := h.2 hty
    refine ⟨t, ht, ?_⟩
    have h1 : t.valClass = .int := by simp [CTy.valClass, hc]
    have h2 : valClassOf ctx x = .int := by simp [valClassOf, hty]
    simp only [h1, h2]
    simp [Reg.kind]
  | some t =>
    refine ⟨t, h.1 t hty, ?_⟩
    have h2 : valClassOf ctx x = t.valClass := by simp [valClassOf, hty]
    simp only [h2]
    generalize t.valClass = c
    cases c <;> simp [Reg.kind]

theorem vclsL_valIn {x : Nat} {ts : List CTy} {tss : List (List CTy)} (h : ValIn ctx x ts)
    (hm : ts ∈ tss) : (Reg.vreg x (valClassOf ctx x)).kind &&& vclsL tss ≠ 0 :=
  by
  rw [Nat.and_comm]
  exact foldl_or_ne vcls _ tss 0 (.inr ⟨ts, hm, by rw [Nat.and_comm]; exact vcls_valIn h⟩)

theorem oneSize_sound (hLI : LogicImmComplete) {ts : List CTy} {g : CTy → Option OperandSize} {t : CTy} (ht : t ∈ ts)
    {sz : OperandSize} (hg : g t = some sz) {i : ImmLogic} (hi : ImmLogic.ofNat? i.value sz = some i) :
    γ f ctx (oneSize ts g) (.op (.immLogic i)) := by
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
    · exact γ_c0 ⟨rfl, rfl⟩

theorem oneScale_sound {ts : List CTy} {t : CTy} (ht : t ∈ ts) {o : Nat}
    (h1 : o % t.bytes = 0) (h2 : o / t.bytes < 4096) :
    γ f ctx (oneScale ts) (.op (.uimm12Scaled o)) := by
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
    · exact γ_c0 ⟨rfl, rfl⟩
  · rename_i hn
    have : t.bytes ∈ ts.map CTy.bytes := List.mem_map.mpr ⟨t, ht, rfl⟩
    rw [hn] at this; cases this

theorem holds2_one {as : List AT} {v : V} (h : Holds2 f ctx as [v]) : ∃ a, as = [a] ∧ γ f ctx a v := by
  obtain ⟨a, bs, rfl, ha, hb⟩ := γL_cons h
  obtain rfl := γL_nil hb
  exact ⟨a, rfl, ha⟩

theorem holds2_two {as : List AT} {v w : V} (h : Holds2 f ctx as [v, w]) :
    ∃ a b, as = [a, b] ∧ γ f ctx a v ∧ γ f ctx b w := by
  obtain ⟨a, bs, rfl, ha, hb⟩ := γL_cons h
  obtain ⟨b, cs, rfl, hb', hc⟩ := γL_cons hb
  obtain rfl := γL_nil hc
  exact ⟨a, b, rfl, ha, hb'⟩

theorem holds2_three {as : List AT} {u v w : V} (h : Holds2 f ctx as [u, v, w]) :
    ∃ a b c, as = [a, b, c] ∧ γ f ctx a u ∧ γ f ctx b v ∧ γ f ctx c w := by
  obtain ⟨a, bs, rfl, ha, hb⟩ := γL_cons h
  obtain ⟨b, cs, rfl, hb', hc⟩ := γL_cons hb
  obtain ⟨c, ds, rfl, hc', hd⟩ := γL_cons hc
  obtain rfl := γL_nil hd
  exact ⟨a, b, c, rfl, ha, hb', hc'⟩

theorem covVL_of_deepL {as : List AT} {vs : List V} (h : Holds2 f ctx as vs)
    (hc : (AT.deepL as).2 = true) : covVL vs = true :=
  covVL_iff.mpr fun w hw => (deepL_sound as vs h w hw).2 hc

theorem sem_ctor (ctx : Ctx) : (sem ctx).ctor = externCtor ctx := rfl

/-- The emitted instructions of a constructor call with its precondition are covered. -/
theorem emitOk_cov {id : TermId} {as : List AT} {vs : List V} (hvs : Holds2 f ctx as vs)
    (hpre : apre id as = true) {m : MInst} (h : EmitOk id vs m) : Covered m = true := by
  rcases h with h | ⟨rfl, i, rfl, hi⟩ | ⟨rfl, r, b', off, rfl, s, rss, rfl, hr⟩
  · exact covered_of_cov h
  · obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    simp only [apre, beq_self_eq_true, ↓reduceIte] at hpre
    exact covV_ofV ((deep_sound a i ha).2 hpre) hi
  · obtain ⟨a, b, rfl, -, hb⟩ := holds2_two hvs
    have hne : (TId.gen_call_args == TId.emit) = false := by decide
    simp only [apre, hne, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, beq_iff_eq] at hpre
    obtain ⟨n, rfl⟩ := kind_one ((deep_sound b _ hb).1 r hr) hpre
    have hop : storeOpOfBytes b' ≠ .fpuStore128 := by unfold storeOpOfBytes; split <;> simp
    simp [stackArgStore, Reg.homeCls, Covered, FormOk, hop, memOk]

set_option maxHeartbeats 4000000 in
/-- **Constructors**: `actor` describes the result, the emitted instructions are covered. -/
theorem ctor_sound (hLI : LogicImmComplete) (hctx : CtxInvT f ctx) (s0 : LState) (as : List AT) (vs : List V) (term : Term)
    (v : V) (st st' : LState) (hvs : Holds2 f ctx as vs) (hIs : CovSince s0 st)
    (hpre : apre term.id as = true) (h : (sem ctx).ctor term vs st = .ok (v, st')) :
    γ f ctx (actor term.id as) v ∧ CovSince s0 st' := by
  rw [sem_ctor] at h
  rcases externCtor_covT ctx term vs st v st' h with
    ⟨q, ty, hq, rfl, hqt, rfl, rfl⟩ | hc
  · refine ⟨?_, hIs⟩
    obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    unfold actor
    rw [hq]
    simp only
    split
    · rename_i ts hts
      cases a with
      | ty ts' =>
        simp only [tysOf', Option.some.injEq] at hts
        subst hts
        obtain ⟨t, ht, he⟩ := ha
        cases he
        exact ⟨_, List.mem_filter.mpr ⟨ht, hqt⟩, rfl⟩
      | _ => simp [tysOf'] at hts
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
  unfold CtorResT at hr
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
        simp only [tysOf', Option.some.injEq] at hts
        subst hts
        obtain ⟨t, ht, he⟩ := ha
        cases he
        exact ⟨_, rfl, clsMask_mem ht hcls⟩
      | _ => simp [tysOf'] at hts
    · refine ⟨_, rfl, ?_⟩
      cases cls <;> simp [Reg.kind]
  rw [if_neg hid] at hr ⊢
  by_cases hpr : (term.id == TId.put_in_reg) = true
  · rw [if_pos hpr] at hr ⊢
    obtain ⟨x, r, rfl, hxr, rfl⟩ := hr
    obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    rw [hctx.valueReg x r hxr]
    split
    · rename_i ts heq; simp only [List.cons.injEq, and_true] at heq; subst heq
      obtain ⟨y, hy, hyv⟩ := ha
      cases hy
      exact ⟨_, rfl, vcls_valIn hyv⟩
    · exact ⟨_, rfl, kind_vreg3 _ _⟩
  rw [if_neg hpr] at hr ⊢
  by_cases hpe : (term.id == TId.put_extended_in_reg) = true
  · rw [if_pos hpe] at hr ⊢
    obtain ⟨x, e, r, rfl, hxr, rfl⟩ := hr
    obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    rw [hctx.valueReg x r hxr]
    split
    · rename_i heq; simp only [List.cons.injEq, and_true] at heq; subst heq
      obtain ⟨x', e', b, he, hb⟩ := ha
      cases he
      refine ⟨_, rfl, ?_⟩
      have hcls : valClassOf ctx x = .int := by
        simp only [valClassOf, hb, Option.map_some, Option.getD_some, CTy.valClass, CTy.regClass?]
        split <;> rfl
      rw [hcls]; simp [Reg.kind]
    · exact ⟨_, rfl, kind_vreg3 _ _⟩
  rw [if_neg hpe] at hr ⊢
  by_cases hlc : (term.id == TId.load_constant_full) = true
  · rw [if_pos hlc] at hr ⊢
    obtain ⟨n, rfl⟩ := hr
    exact ⟨_, rfl, by simp [Reg.kind]⟩
  rw [if_neg hlc] at hr ⊢
  by_cases hsk : (term.id == TId.is_sinkable_inst) = true
  · rw [if_pos hsk] at hr; exact hr.elim
  rw [if_neg hsk] at hr ⊢
  by_cases hlp : (term.id == TId.emit_u64_le_const) = true
  · rw [if_pos hlp] at hr ⊢
    obtain ⟨n, rfl⟩ := hr
    exact γ_c0 ⟨rfl, rfl⟩
  rw [if_neg hlp] at hr ⊢
  by_cases hps : (term.id == TId.put_in_regs) = true
  · rw [if_pos hps] at hr ⊢
    obtain ⟨x, r, rfl, hxr, rfl⟩ := hr
    obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    rw [hctx.valueReg x r hxr]
    split
    · rename_i ts heq; simp only [List.cons.injEq, and_true] at heq; subst heq
      obtain ⟨y, hy, hyv⟩ := ha
      cases hy
      refine ⟨fun r' hr' => ?_, fun _ => rfl⟩
      simp only [V.regsIn, List.mem_singleton] at hr'
      subst hr'
      exact vcls_valIn hyv
    · refine ⟨fun r' hr' => ?_, fun _ => rfl⟩
      simp only [V.regsIn, List.mem_singleton] at hr'
      subst hr'
      exact kind_vreg3 _ _
  rw [if_neg hps] at hr ⊢
  by_cases hpv : (term.id == TId.put_in_regs_vec) = true
  · rw [if_pos hpv] at hr ⊢
    obtain ⟨xs, rs, rfl, hxr, rfl⟩ := hr
    obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    have hreg : ∀ r' ∈ (V.regsVec (rs.map fun r => [r])).regsIn, ∃ x ∈ xs,
        r' = .vreg x (valClassOf ctx x) := by
      intro r' hr'
      have hr'' : r' ∈ rs := by
        simp only [V.regsIn, List.mem_flatten, List.mem_map] at hr'
        obtain ⟨_, ⟨q, hq, rfl⟩, hr'⟩ := hr'
        simp only [List.mem_singleton] at hr'
        exact hr' ▸ hq
      obtain ⟨x, hx, hxe⟩ := mapM_mem hxr r' hr''
      exact ⟨x, hx, hctx.valueReg x r' hxe⟩
    split
    · rename_i tss heq; simp only [List.cons.injEq, and_true] at heq; subst heq
      obtain ⟨ys, hy, hlen, hall⟩ := ha
      cases hy
      refine ⟨fun r' hr' => ?_, fun _ => rfl⟩
      obtain ⟨x, hx, rfl⟩ := hreg r' hr'
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
      have hit : i < tss.length := hlen ▸ (List.getElem?_eq_some_iff.mp hi).1
      exact vclsL_valIn (hall i x _ hi (List.getElem?_eq_getElem hit)) (List.getElem_mem hit)
    · rename_i ts heq; simp only [List.cons.injEq, and_true] at heq; subst heq
      obtain ⟨ys, hy, hall⟩ := ha
      cases hy
      refine ⟨fun r' hr' => ?_, fun _ => rfl⟩
      obtain ⟨x, hx, rfl⟩ := hreg r' hr'
      exact vcls_valIn (hall x hx)
    · refine ⟨fun r' hr' => ?_, fun _ => rfl⟩
      obtain ⟨x, hx, rfl⟩ := hreg r' hr'
      exact kind_vreg3 _ _
  rw [if_neg hpv] at hr ⊢
  by_cases hmz : (term.id == TId.asimd_mov_mod_imm_zero) = true
  · rw [if_pos hmz] at hr ⊢
    obtain ⟨s, sz, rfl, hs, rfl⟩ := hr
    obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    split
    · rename_i t k heq; simp only [List.cons.injEq, and_true] at heq; subst heq
      obtain ⟨vs, rfl, hl⟩ := ha
      cases vs with
      | cons _ _ => exact hl.elim
      | nil =>
        split
        · rename_i hk
          simp only [beq_iff_eq] at hk
          subst hk
          have : sz = .size32 := by
            simp only [V.scalarSize?, V.enum?, V.enumOf?] at hs
            split at hs <;> simp_all [ScalarSize.ofIdx?, bind, Option.bind]
          subst this
          exact ⟨_, rfl, rfl, rfl, rfl⟩
        · exact γ_c0 ⟨rfl, rfl⟩
    · exact γ_c0 ⟨rfl, rfl⟩
  rw [if_neg hmz] at hr ⊢
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
        simp only [tysOf', Option.some.injEq] at hts
        subst hts
        obtain ⟨t', ht, he⟩ := ha
        cases he
        exact oneSize_sound hLI ht hls hi
      | _ => simp [tysOf'] at hts
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
        simp only [tysOf', Option.some.injEq] at hts
        subst hts
        obtain ⟨t', ht, he⟩ := ha
        cases he
        exact oneSize_sound hLI ht hls hi
      | _ => simp [tysOf'] at hts
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
        simp only [tysOf', Option.some.injEq] at hts
        subst hts
        obtain ⟨t', ht, he⟩ := hb
        cases he
        exact oneScale_sound ht h1 h2
      | _ => simp [tysOf'] at hts
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

end Backend.Proof.CovT

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
open Backend.Proof.Cov (Covered covV covVL EmitOk CovSince emitOk_nil emit_one LCCov
  loadConstantFull_cov ofNat?_value logicSize_of logicSize64_lt logicSize64_ge uimm12_of simm9_of
  callOutput_fold callArgs_fold callArgs_mem covV_ofV kind_one clsMask_mem sem_ctor covV_data
  regsInL_mem' covVL_iff LogicImmComplete logicSize logicSize64 clsMask)

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
         | exact ⟨_, _, rfl, rfl⟩
         | exact ⟨_, rfl, rfl⟩
         | exact ⟨_, _, _, _, rfl, rfl⟩
         | exact ⟨_, _, _, rfl, List.mem_of_getElem? ‹_›, rfl⟩
         | exact ⟨fun r hr => by simp_all [V.regsIn, regsInL], fun _ => rfl⟩
         | exact ⟨_, _, rfl, ‹_›, rfl⟩
         | skip)
      | skip

end Backend.Proof.CovT

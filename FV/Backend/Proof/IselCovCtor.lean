import FV.Backend.Proof.IselCovExt

/-!
# Form coverage of the ISLE lowering (V3): the extern constructors

`externCtor_cov`: every successful extern constructor call (past the type predicates) emits only
covered instructions, `emit`'s instruction, or `gen_call_args`' stores of argument registers, and
returns what `CtorRes` states (the shapes `actor` relies on).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

/-- The result of extern constructor `id` on `args`, as `actor` needs it. -/
def CtorRes (id : TermId) (args : List V) (v : V) : Prop :=
  if id == TId.temp_writable_reg then
    ∃ ty cls n, args = [.ty ty] ∧ ty.regClass? = some cls ∧ v = .reg (.vreg n cls)
  else if id == TId.put_in_reg || id == TId.put_extended_in_reg || id == TId.load_constant_full then
    ∃ n, v = .reg (.vreg n .int)
  else if id == TId.put_in_regs || id == TId.put_in_regs_vec || id == TId.gen_call_output then
    (∀ r ∈ v.regsIn, ∃ n, r = .vreg n .int) ∧ covV v = true
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

/-- An instruction a constructor may emit: covered, `emit`'s instruction, or a store of an
argument register to the outgoing area (`gen_call_args`). -/
def EmitOk (id : TermId) (args : List V) (m : MInst) : Prop :=
  Covered m = true ∨ (id = TId.emit ∧ ∃ i, args = [i] ∧ MInst.ofV i = some m) ∨
    (id = TId.gen_call_args ∧ ∃ op r off fl, m = .store op r (.spOffset off) fl ∧ op ≠ .fpuStore128 ∧
      ∃ s rss, args = [.op (.sig s), .regsVec rss] ∧ r ∈ (V.regsVec rss).regsIn)

/-- The contract of one constructor call past the type predicates. -/
structure CtorCov (id : TermId) (args : List V) (st : LState) (v : V) (st' : LState) : Prop where
  tp : tyPred id = none
  emit : ∃ ms : List MInst, st'.emitted = st.emitted ++ ms.toArray ∧ ∀ m ∈ ms, EmitOk id args m
  res : CtorRes id args v

/-- `CtorCov` of every successful result. -/
def CtorCovP (st : LState) (id : TermId) (args : List V) (r : ExtResult (V × LState)) : Prop :=
  ∀ v st', r = .ok (v, st') → CtorCov id args st v st'

/-! ## Helpers -/

theorem emit_none (st : LState) : ∃ ms : List MInst, st.emitted = st.emitted ++ ms.toArray ∧
    ∀ m ∈ ms, ∀ (P : MInst → Prop), P m := ⟨[], by simp, fun _ h => by cases h⟩

theorem emitOk_nil {id : TermId} {args : List V} {st : LState} :
    ∃ ms : List MInst, st.emitted = st.emitted ++ ms.toArray ∧ ∀ m ∈ ms, EmitOk id args m :=
  ⟨[], by simp, fun _ h => by cases h⟩

/-- `loadConstantFull`'s state: the register is a fresh int vreg, every emitted instruction is
covered. -/
def LCCov (st0 : LState) (rd : Reg) (s : LState) : Prop :=
  (∃ n, rd = .vreg n .int) ∧ s.outgoing = st0.outgoing ∧
    ∃ ms : List MInst, s.emitted = st0.emitted ++ ms.toArray ∧ ∀ m ∈ ms, Covered m = true

theorem lcCov_step {st0 s : LState} {m : MInst} (hm : Covered m = true)
    (hout : s.outgoing = st0.outgoing)
    (hem : ∃ ms : List MInst, s.emitted = st0.emitted ++ ms.toArray ∧ ∀ m ∈ ms, Covered m = true) :
    LCCov st0 (s.fresh .int).1 ((s.fresh .int).2.emit m) := by
  obtain ⟨ms, h5, h6⟩ := hem
  refine ⟨⟨s.nextVreg, rfl⟩, by simp [LState.fresh, LState.emit, hout],
    ⟨ms ++ [m], by simp [LState.fresh, LState.emit, h5], ?_⟩⟩
  intro m' hm'
  rcases List.mem_append.mp hm' with hm' | hm'
  · exact h6 m' hm'
  · simp only [List.mem_singleton] at hm'; subst hm'; exact hm

theorem loadConstantFull_cov (bits : Nat) (se : Bool) (sz : OperandSize) (value : Nat) (st : LState) :
    LCCov st (loadConstantFull bits se sz value st).1 (loadConstantFull bits se sz value st).2 := by
  unfold loadConstantFull
  dsimp only
  refine foldl_inv (fun x : Reg × LState × Nat => LCCov st x.1 x.2.1) _ _ _ ?_ ?_
  · exact lcCov_step rfl rfl ⟨[], by simp, by simp⟩
  · intro sh _ x hx
    refine ite_inv (I := fun x : Reg × LState × Nat => LCCov st x.1 x.2.1) (fun _ => hx) fun _ => ?_
    refine ite_inv (I := fun x : Reg × LState × Nat => LCCov st x.1 x.2.1) (fun _ => ?_) fun _ => hx
    obtain ⟨⟨n, hrd⟩, h4, ms, h5, h6⟩ := hx
    refine lcCov_step ?_ h4 ⟨ms, h5, h6⟩
    rw [hrd]; rfl

theorem ofNat?_eq {v : Nat} {s : OperandSize} {i : ImmLogic} (h : ImmLogic.ofNat? v s = some i) :
    i = ⟨v, s⟩ := by
  simp only [ImmLogic.ofNat?, Option.ite_none_right_eq_some, Option.some.injEq] at h
  exact h.2.symm

theorem ofNat?_value {v : Nat} {s : OperandSize} {i : ImmLogic} (h : ImmLogic.ofNat? v s = some i) :
    ImmLogic.ofNat? i.value s = some i := by
  have e := ofNat?_eq h
  subst e
  exact h

theorem ctyBeq_int {ty : CTy} {b : Nat} (h : (ty == CTy.int b) = true) : ty = .int b := by
  cases ty with
  | int n =>
    have : (n == b) = true := h
    simp only [beq_iff_eq] at this
    rw [this]
  | _ => cases h

theorem logicSize_of {ty : CTy} (h : (ty == CTy.int 32 || ty == CTy.int 64) = true) :
    logicSize ty = some (OperandSize.ofBits ty.bits) := by
  simp only [Bool.or_eq_true] at h
  rcases h with h | h <;> rw [ctyBeq_int h] <;> rfl

theorem logicSize64_lt {ty : CTy} (h : ty.bits < 32) : logicSize64 ty = some .size32 := by
  simp [logicSize64, h]; rfl

theorem logicSize64_ge {ty : CTy} (h : ¬ty.bits < 32) (h2 : (ty == CTy.int 32 || ty == CTy.int 64) = true) :
    logicSize64 ty = some (OperandSize.ofBits ty.bits) := by
  simp only [logicSize64, h, ite_false]; exact logicSize_of h2

theorem uimm12_of {x : Int} {b o : Nat} (h : uimm12Scaled? x b = some o) : o % b = 0 ∧ o / b < 4096 := by
  unfold uimm12Scaled? at h
  split at h
  · rename_i hc
    cases h
    obtain ⟨h1, h2, h3⟩ := hc
    simp only [beq_iff_eq] at h3
    refine ⟨h3, ?_⟩
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · have : x.toNat ≤ 4095 * b := by omega
      exact Nat.div_lt_of_lt_mul (by omega)
  · cases h

theorem simm9_of {x i : Int} (h : simm9? x = some i) : -256 ≤ i ∧ i < 256 := by
  unfold simm9? at h
  split at h
  · cases h; omega
  · cases h

/-- `gen_call_output`'s fold: fresh int vregs, nothing emitted. -/
theorem callOutput_fold {β : Type} (st : LState)
    (F : Array (List Reg) × LState → β → Array (List Reg) × LState) (l : List β)
    (hF : ∀ a b, F a b = (a.1.push [(a.2.fresh .int).1], (a.2.fresh .int).2)) :
    (l.foldl F (#[], st)).2.emitted = st.emitted ∧
      ∀ rs ∈ (l.foldl F (#[], st)).1.toList, ∀ r ∈ rs, ∃ n, r = .vreg n .int := by
  have := foldl_inv (fun a : Array (List Reg) × LState =>
      a.2.emitted = st.emitted ∧ ∀ rs ∈ a.1.toList, ∀ r ∈ rs, ∃ n, r = .vreg n .int)
    F l (#[], st) ⟨rfl, by simp⟩ (by
      intro b _ a ⟨h1, h2⟩
      rw [hF]
      refine ⟨by simp [LState.fresh, h1], fun rs hrs r hr => ?_⟩
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hrs
      rcases hrs with hrs | rfl
      · exact h2 rs hrs r hr
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, rfl⟩)
  exact this

/-- `gen_call_args`' fold: stores of argument registers. -/
theorem callArgs_fold (st : LState) (s : Clif.Signature) (rss : List (List Reg))
    (F : Array (Reg × Reg) × LState → (ArgLoc × Reg) × Nat → Array (Reg × Reg) × LState)
    (l : List ((ArgLoc × Reg) × Nat))
    (hF : ∀ a b, F a b = match b.1.1 with
      | .reg p => (a.1.push (b.1.2, p), a.2)
      | .stack off => (a.1, a.2.emit (.store (storeOpOfBytes b.2) b.1.2 (.spOffset off) trustedFlags)))
    (hl : ∀ b ∈ l, b.1.2 ∈ (V.regsVec rss).regsIn) :
    ∃ ms : List MInst, (l.foldl F (#[], st)).2.emitted = st.emitted ++ ms.toArray ∧
      ∀ m ∈ ms, EmitOk TId.gen_call_args [.op (.sig s), .regsVec rss] m := by
  have := foldl_inv (fun a : Array (Reg × Reg) × LState =>
      ∃ ms : List MInst, a.2.emitted = st.emitted ++ ms.toArray ∧
        ∀ m ∈ ms, EmitOk TId.gen_call_args [.op (.sig s), .regsVec rss] m)
    F l (#[], st) ⟨[], by simp, by simp⟩ (by
      intro b hb a ⟨ms, h1, h2⟩
      rw [hF]
      split
      · exact ⟨ms, h1, h2⟩
      · rename_i off _
        refine ⟨ms ++ [.store (storeOpOfBytes b.2) b.1.2 (.spOffset off) trustedFlags],
          by simp [LState.emit, h1], fun m hm => ?_⟩
        rcases List.mem_append.mp hm with hm | hm
        · exact h2 m hm
        · simp only [List.mem_singleton] at hm
          subst hm
          refine .inr (.inr ⟨rfl, _, _, _, _, rfl, ?_, s, rss, rfl, hl b hb⟩)
          unfold storeOpOfBytes; split <;> simp)
  exact this

theorem emit_one (st : LState) (m : MInst) (P : MInst → Prop) (hm : P m) :
    ∃ ms : List MInst, (st.emit m).emitted = st.emitted ++ ms.toArray ∧ ∀ m' ∈ ms, P m' :=
  ⟨[m], by simp [LState.emit], fun m' hm' => by simp only [List.mem_singleton] at hm'; subst hm'; exact hm⟩

theorem regsVec_single_vreg {ctx : Ctx} (hvr : ∀ x r, ctx.valueReg? x = some r → r = .vreg x .int)
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
  exact ⟨_, hvr _ _ he⟩

theorem callArgs_mem {rss : List (List Reg)} {rs : List Reg}
    (h : rss.mapM (fun | [r] => some r | _ => none) = some rs) {locs : List ArgLoc} {bytes : List Nat} :
    ∀ b ∈ (locs.zip rs).zip bytes, b.1.2 ∈ (V.regsVec rss).regsIn := by
  intro b hb
  have hz := List.of_mem_zip hb
  have hz1 := List.of_mem_zip hz.1
  obtain ⟨l, hl, hrl⟩ := single_mem h _ hz1.2
  simp only [V.regsIn, List.mem_flatten]
  exact ⟨l, hl, hrl⟩

set_option maxHeartbeats 8000000 in
/-- **Every extern constructor** past the type predicates satisfies `CtorCov`. -/
theorem externCtor_cov (ctx : Ctx) (hvr : ∀ x r, ctx.valueReg? x = some r → r = .vreg x .int) (t : Term) (args : List V) (st : LState) (v : V) (st' : LState)
    (h : externCtor ctx t args st = .ok (v, st')) :
    (∃ q ty, tyPred t.id = some q ∧ args = [.ty ty] ∧ q ty = true ∧ v = .ty ty ∧ st' = st) ∨
      CtorCov t.id args st v st' := by
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
      | (refine ⟨[], (callOutput_fold st _ _ (fun _ _ => rfl)).1.trans (by simp), by simp⟩)
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
         | (rename_i heq; exact ⟨_, congrArg V.reg (hvr _ _ heq)⟩)
         | exact regsVec_single_vreg hvr ‹_›
         | (refine ⟨fun r hr => ?_, rfl⟩
            simp only [V.regsIn, List.mem_flatten] at hr
            obtain ⟨rs, hrs, hr⟩ := hr
            exact (callOutput_fold st _ _ (fun _ _ => rfl)).2 rs hrs r hr)
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
            exact ⟨_, hvr _ _ ‹_›⟩)
         | skip)
      | skip

/-! ## The model's constructor field -/

/-- Every instruction emitted since `s0` is covered. -/
def CovSince (s0 st : LState) : Prop :=
  ∃ ms : List MInst, st.emitted = s0.emitted ++ ms.toArray ∧ ∀ m ∈ ms, Covered m = true

variable {f : Clif.Function} {ctx : Ctx}

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

theorem kind_one {r : Reg} {m : Nat} (hk : r.kind &&& m ≠ 0) (hm : m &&& 14 = 0) :
    ∃ n, r = .vreg n .int := by
  apply kind_int
  rcases kind_cases r with h1 | h1 | h1 | h1 <;> rw [h1] at hk ⊢ <;> try rfl
  all_goals exfalso; apply hk; apply Nat.eq_of_testBit_eq; intro i
  all_goals have := congrArg (·.testBit i) hm
  all_goals simp only [Nat.testBit_and] at this ⊢
  all_goals rcases i with _ | _ | _ | _ | i <;> simp_all [Nat.testBit_succ]

theorem clsMask_mem {ts : List CTy} {t : CTy} (ht : t ∈ ts) {c : RegClass} (hc : t.regClass? = some c)
    {n : Nat} : (Reg.vreg n c).kind &&& clsMask ts ≠ 0 := by
  have key : ∀ (l : List CTy) (m0 : Nat), (∀ x, m0 &&& x ≠ 0 → (List.foldl (fun m t => m ||| match t.regClass? with
      | some .int => 1 | some .float => 2 | none => 0) m0 l) &&& x ≠ 0) := by
    intro l
    induction l with
    | nil => intro m0 x h; exact h
    | cons a l ih =>
      intro m0 x h
      apply ih
      intro h0; apply h
      apply Nat.eq_of_testBit_eq; intro i
      have := congrArg (·.testBit i) h0
      simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at this ⊢
      cases hm : m0.testBit i <;> cases hx : x.testBit i <;> simp_all
  have hfold : ∀ (l : List CTy) (m0 : Nat), t ∈ l →
      (Reg.vreg n c).kind &&& (List.foldl (fun m t => m ||| match t.regClass? with
        | some .int => 1 | some .float => 2 | none => 0) m0 l) ≠ 0 := by
    intro l
    induction l with
    | nil => intro _ h; cases h
    | cons a l ih =>
      intro m0 h
      rcases List.mem_cons.mp h with rfl | h
      · rw [List.foldl_cons]
        rw [Nat.and_comm]
        apply key l
        rw [hc]
        cases c
        · intro h0; have := congrArg (·.testBit 0) h0
          simp [Nat.testBit_and, Nat.testBit_or, Reg.kind] at this
        · intro h0; have := congrArg (·.testBit 1) h0
          simp [Nat.testBit_and, Nat.testBit_or, Reg.kind] at this
          exact absurd (this (.inr (by decide))) (by decide)
      · exact ih _ h
  exact hfold ts 0 ht

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

theorem holds2_one {as : List AW} {v : V} (h : Holds2 f ctx as [v]) : ∃ a, as = [a] ∧ γ f ctx a v := by
  obtain ⟨a, bs, rfl, ha, hb⟩ := γL_cons h
  obtain rfl := γL_nil hb
  exact ⟨a, rfl, ha⟩

theorem holds2_two {as : List AW} {v w : V} (h : Holds2 f ctx as [v, w]) :
    ∃ a b, as = [a, b] ∧ γ f ctx a v ∧ γ f ctx b w := by
  obtain ⟨a, bs, rfl, ha, hb⟩ := γL_cons h
  obtain ⟨b, cs, rfl, hb', hc⟩ := γL_cons hb
  obtain rfl := γL_nil hc
  exact ⟨a, b, rfl, ha, hb'⟩

theorem holds2_three {as : List AW} {u v w : V} (h : Holds2 f ctx as [u, v, w]) :
    ∃ a b c, as = [a, b, c] ∧ γ f ctx a u ∧ γ f ctx b v ∧ γ f ctx c w := by
  obtain ⟨a, bs, rfl, ha, hb⟩ := γL_cons h
  obtain ⟨b, cs, rfl, hb', hc⟩ := γL_cons hb
  obtain ⟨c, ds, rfl, hc', hd⟩ := γL_cons hc
  obtain rfl := γL_nil hd
  exact ⟨a, b, c, rfl, ha, hb', hc'⟩

theorem covVL_of_deepL {as : List AW} {vs : List V} (h : Holds2 f ctx as vs)
    (hc : (AW.deepL as).2 = true) : covVL vs = true :=
  covVL_iff.mpr fun w hw => (deepL_sound as vs h w hw).2 hc

theorem sem_ctor (ctx : Ctx) : (sem ctx).ctor = externCtor ctx := rfl

/-- The emitted instructions of a constructor call with its precondition are covered. -/
theorem emitOk_cov {id : TermId} {as : List AW} {vs : List V} (hvs : Holds2 f ctx as vs)
    (hpre : apre id as = true) {m : MInst} (h : EmitOk id vs m) : Covered m = true := by
  rcases h with h | ⟨rfl, i, rfl, hi⟩ | ⟨rfl, op, r, off, fl, rfl, hop, s, rss, rfl, hr⟩
  · exact h
  · obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    simp only [apre, beq_self_eq_true, ↓reduceIte] at hpre
    exact covV_ofV ((deep_sound a i ha).2 hpre) hi
  · obtain ⟨a, b, rfl, -, hb⟩ := holds2_two hvs
    have hne : (TId.gen_call_args == TId.emit) = false := by decide
    simp only [apre, hne, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, beq_iff_eq] at hpre
    obtain ⟨n, rfl⟩ := kind_one ((deep_sound b _ hb).1 r hr) hpre
    simp [Covered, FormOk, hop, memOk]

set_option maxHeartbeats 4000000 in
/-- **Constructors**: `actor` describes the result, the emitted instructions are covered. -/
theorem ctor_sound (hLI : LogicImmComplete) (hctx : CtxInv f ctx) (s0 : LState) (as : List AW) (vs : List V) (term : Term)
    (v : V) (st st' : LState) (hvs : Holds2 f ctx as vs) (hIs : CovSince s0 st)
    (hpre : apre term.id as = true) (h : (sem ctx).ctor term vs st = .ok (v, st')) :
    γ f ctx (actor term.id as) v ∧ CovSince s0 st' := by
  rw [sem_ctor] at h
  rcases externCtor_cov ctx hctx.valueReg term vs st v st' h with
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
  by_cases hid2' : (term.id == TId.put_in_regs || term.id == TId.put_in_regs_vec || term.id == TId.gen_call_output) = true
  · rw [if_pos hid2'] at hr ⊢
    exact ⟨fun r hrr => by obtain ⟨n, rfl⟩ := hr.1 r hrr; simp [Reg.kind], fun _ => hr.2⟩
  rw [if_neg hid2'] at hr ⊢
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

end Backend.Proof.Cov

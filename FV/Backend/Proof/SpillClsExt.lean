import FV.Backend.Proof.SpillClsInst

/-!
# Register classes through the extern constructors (V4 classes)

`externCtor_cls`: every successful extern constructor call (`CtorCls`) only appends classes,
one per fresh vreg (`ClsStep`), and, from a state whose classes cover its vregs (`Sz`): every
register of its result comes from its arguments, has the class the state records, is a value's
register, the context's `try_call` registers, or `invalid_reg`'s; every instruction it emits
holds registers of the classes the state records, or (`emit`, `gen_return`, `gen_call_args`
only) registers of its arguments. Proven like `IselFlowExt.externCtor_ok`, alternative by
alternative.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Aarch64

/-! ## The state change -/

/-- `st'` appends classes to `st`'s, one per fresh vreg. -/
def ClsStep (st st' : LState) : Prop :=
  ∃ ext : Array RegClass, st'.classes = st.classes ++ ext ∧ st'.nextVreg = st.nextVreg + ext.size

/-- The classes cover exactly the vregs allocated so far. -/
def Sz (st : LState) : Prop := st.classes.size = st.nextVreg

theorem clsStep_refl (st : LState) : ClsStep st st := ⟨#[], by simp, by simp⟩

theorem clsStep_trans {a b c : LState} (h1 : ClsStep a b) (h2 : ClsStep b c) : ClsStep a c := by
  obtain ⟨e1, h1, h1'⟩ := h1
  obtain ⟨e2, h2, h2'⟩ := h2
  exact ⟨e1 ++ e2, by rw [h2, h1, Array.append_assoc], by simp [h2', h1']; omega⟩

theorem clsStep_of_eq {st st' : LState} (h1 : st'.classes = st.classes) (h2 : st'.nextVreg = st.nextVreg) :
    ClsStep st st' := ⟨#[], by simp [h1], by simp [h2]⟩

theorem clsStep_fresh (st : LState) (c : RegClass) : ClsStep st (st.fresh c).2 :=
  ⟨#[c], by simp [LState.fresh], by simp [LState.fresh]⟩

theorem sz_step {st st' : LState} (h : ClsStep st st') (hs : Sz st) : Sz st' := by
  obtain ⟨e, h1, h2⟩ := h
  simp only [Sz, h1, h2, Array.size_append] at hs ⊢
  omega

theorem regCls_step {st st' : LState} (h : ClsStep st st') {r : Reg} (hr : RegCls st.classes r) :
    RegCls st'.classes r := by
  obtain ⟨e, h1, -⟩ := h
  rw [h1]
  exact regCls_append e hr

theorem fresh_cls {st : LState} (hs : Sz st) (c : RegClass) :
    RegCls (st.fresh c).2.classes (st.fresh c).1 := by
  simp only [LState.fresh, regCls_vreg]
  rw [Array.getElem?_push, ← hs]
  simp

/-! ## The contract -/

/-- The constructors whose emitted instructions hold registers of their arguments. -/
def emitIds : List TermId := [TId.emit, TId.gen_return, TId.gen_call_args]

/-- The classes contract of one extern constructor call `id args` from `st` returning `v` in
`st'`. -/
structure CtorCls (ctx : Ctx) (id : TermId) (args : List V) (st : LState) (v : V) (st' : LState) :
    Prop where
  step : ClsStep st st'
  regs : Sz st → ∀ r ∈ v.regsIn, r ∈ regsInL args ∨ RegCls st'.classes r ∨
    (∃ x ∈ valsInL args, ctx.valueReg? x = some r) ∨ id = TId.invalid_reg ∨
    r ∈ ctx.tryRegs.1 ∨ r ∈ ctx.tryRegs.2
  emit : ∃ ms : List MInst, st'.emitted = st.emitted ++ ms.toArray ∧ (Sz st → ∀ m ∈ ms,
    RegsFrom (fun r => (id ∈ emitIds ∧ r ∈ regsInL args) ∨ RegCls st'.classes r) m)

/-- `CtorCls` of every successful result of a constructor call. -/
def CtorClsP (ctx : Ctx) (st : LState) (id : TermId) (args : List V) (r : ExtResult (V × LState)) :
    Prop :=
  ∀ v st', r = .ok (v, st') → CtorCls ctx id args st v st'

/-! ## Helpers -/

variable {ctx : Ctx} {id : TermId} {args : List V} {st : LState}

theorem ctorCls_same {v : V}
    (hr : ∀ r ∈ v.regsIn, r ∈ regsInL args ∨ (∃ x ∈ valsInL args, ctx.valueReg? x = some r) ∨
      (∀ n c, r ≠ .vreg n c)) : CtorCls ctx id args st v st := by
  refine ⟨clsStep_refl st, fun _ r h => ?_, ⟨[], by simp, by simp⟩⟩
  rcases hr r h with h | h | h
  · exact .inl h
  · exact .inr (.inr (.inl h))
  · exact .inr (.inl (regCls_real h))

theorem ctorCls_invalid : CtorCls ctx TId.invalid_reg [] st (.reg Reg.invalid) st :=
  ⟨clsStep_refl st, fun _ _ _ => .inr (.inr (.inr (.inl rfl))), ⟨[], by simp, by simp⟩⟩

theorem ctorCls_fresh {c : RegClass} : CtorCls ctx id args st (.reg (st.fresh c).1) (st.fresh c).2 := by
  refine ⟨clsStep_fresh st c, fun hs r hr => ?_, ⟨[], by simp [LState.fresh], by simp⟩⟩
  simp only [V.regsIn, List.mem_singleton] at hr
  subst hr
  exact .inr (.inl (fresh_cls hs c))

theorem ctorCls_emit {i : V} {m : MInst} (hid : id = TId.emit) (h : MInst.ofV i = some m) :
    CtorCls ctx id [i] st (.op .unit) (st.emit m) := by
  refine ⟨clsStep_of_eq rfl rfl, fun _ r hr => by simp [V.regsIn, opRegs] at hr,
    ⟨[m], by simp [LState.emit], fun _ m' hm => ?_⟩⟩
  simp only [List.mem_singleton] at hm
  subst hm
  refine (regsFrom_ofV h).mono fun r hr => .inl ⟨by simp [hid, emitIds], by simpa using hr⟩

/-- The return registers are physical. -/
theorem rets_regsFrom {ps rs : List Reg} {P : Reg → Prop} (h : ∀ r ∈ rs, P r) :
    RegsFrom P (.rets (rs.zip ps)) := by
  intro g hg
  simp only [MInst.mapRegs, MInst.rets.injEq]
  conv => rhs; rw [← List.map_id (rs.zip ps)]
  exact List.map_congr_left fun x hx => by
    rw [hg x.1 (h _ (List.of_mem_zip hx).1)]; rfl

theorem ctorCls_rets {rss : List (List Reg)} {rs ps : List Reg} (hid : id = TId.gen_return)
    (hrs : rss.mapM (fun | [r] => some r | _ => none) = some rs) :
    CtorCls ctx id [.regsVec rss] st (.op .unit) (st.emit (.rets (rs.zip ps))) := by
  refine ⟨clsStep_of_eq rfl rfl, fun _ r hr => by simp [V.regsIn, opRegs] at hr,
    ⟨[.rets (rs.zip ps)], by simp [LState.emit], fun _ m hm => ?_⟩⟩
  simp only [List.mem_singleton] at hm
  subst hm
  refine rets_regsFrom fun r hr => .inl ⟨by simp [hid, emitIds], ?_⟩
  obtain ⟨l, hl, hrl⟩ := single_mem hrs r hr
  simp [V.regsIn]; exact ⟨l, hl, hrl⟩

/-- The state of `loadConstantFull` (register `rd` and state `s` reached from `st0`). -/
def LCCls (st0 : LState) (rd : Reg) (s : LState) : Prop :=
  ClsStep st0 s ∧ (Sz st0 → RegCls s.classes rd) ∧ s.outgoing = st0.outgoing ∧
    ∃ ms : List MInst, s.emitted = st0.emitted ++ ms.toArray ∧
      (Sz st0 → ∀ m ∈ ms, RegsFrom (RegCls s.classes) m)

theorem regsFrom_step {P : Reg → Prop} {m : MInst} {st st' : LState} (h : ClsStep st st')
    (hm : RegsFrom (fun r => P r ∨ RegCls st.classes r) m) : RegsFrom (fun r => P r ∨ RegCls st'.classes r) m :=
  hm.mono fun r hr => hr.imp_right (regCls_step h)

theorem lcCls_step {st0 s : LState} {rd : Reg} (m : Reg → MInst) (hm : ∀ rd', RegCls (s.fresh .int).2.classes rd' →
      RegCls (s.fresh .int).2.classes rd → RegsFrom (RegCls (s.fresh .int).2.classes) (m rd'))
    (hx : LCCls st0 rd s) : LCCls st0 (s.fresh .int).1 (((s.fresh .int).2).emit (m (s.fresh .int).1)) := by
  obtain ⟨h1, h2, h3, ms, h4, h5⟩ := hx
  have hs1 : ClsStep s (s.fresh .int).2 := clsStep_fresh s .int
  refine ⟨clsStep_trans h1 (clsStep_trans hs1 (clsStep_of_eq rfl rfl)), fun hs => ?_,
    by simp [LState.fresh, LState.emit, h3], ms ++ [m (s.fresh .int).1],
    by simp [LState.fresh, LState.emit, h4], fun hs m' hm' => ?_⟩
  · exact fresh_cls (sz_step h1 hs) .int
  · rcases List.mem_append.mp hm' with hm' | hm'
    · exact (h5 hs m' hm').mono fun r hr => regCls_step hs1 hr
    · simp only [List.mem_singleton] at hm'
      subst hm'
      exact hm _ (fresh_cls (sz_step h1 hs) .int) (regCls_step hs1 (h2 hs))

theorem movWide_regsFrom {P : Reg → Prop} {rd : Reg} (h : P rd) (op : MoveWideOp) (i : MoveWideConst)
    (s : OperandSize) : RegsFrom P (.movWide op rd i s) := by
  intro g hg; simp [MInst.mapRegs, hg rd h]

theorem movK_regsFrom {P : Reg → Prop} {rd rn : Reg} (h1 : P rd) (h2 : P rn) (i : MoveWideConst)
    (s : OperandSize) : RegsFrom P (.movK rd rn i s) := by
  intro g hg; simp [MInst.mapRegs, hg rd h1, hg rn h2]

/-- **`loadConstantFull`**: fresh int registers, `movz`/`movn` and `movk`s on them. -/
theorem loadConstantFull_cls (bits : Nat) (se : Bool) (sz : OperandSize) (value : Nat)
    (st : LState) :
    LCCls st (loadConstantFull bits se sz value st).1 (loadConstantFull bits se sz value st).2 := by
  unfold loadConstantFull
  dsimp only
  refine foldl_inv (fun x : Reg × LState × Nat => LCCls st x.1 x.2.1) _ _ _ ?_ ?_
  · refine ⟨clsStep_trans (clsStep_fresh st .int) (clsStep_of_eq rfl rfl), fun hs => fresh_cls hs .int,
      by simp [LState.fresh, LState.emit], [_], rfl, fun hs m hm => ?_⟩
    simp only [List.mem_singleton] at hm
    subst hm
    exact movWide_regsFrom (fresh_cls hs .int) _ _ _
  · intro sh _ x hx
    refine ite_inv (I := fun x : Reg × LState × Nat => LCCls st x.1 x.2.1) (fun _ => hx) fun _ => ?_
    refine ite_inv (I := fun x : Reg × LState × Nat => LCCls st x.1 x.2.1) (fun _ => ?_) fun _ => hx
    exact lcCls_step (s := x.2.1) (fun rd' => MInst.movK rd' x.1 _ _)
      (fun rd' h1 h2 => movK_regsFrom h1 h2 _ _) hx

theorem ctorCls_lc {r : Reg} {st' : LState} (h : LCCls st r st') : CtorCls ctx id args st (.reg r) st' := by
  obtain ⟨h1, h2, -, ms, h4, h5⟩ := h
  refine ⟨h1, fun hs r' hr => ?_, ⟨ms, h4, fun hs m hm => (h5 hs m hm).mono fun r hr => .inr hr⟩⟩
  simp only [V.regsIn, List.mem_singleton] at hr
  subst hr
  exact .inr (.inl (h2 hs))

/-- `gen_call_output`: fresh registers. -/
theorem ctorCls_callOutput {β : Type}
    (F : Array (List Reg) × LState → β → Array (List Reg) × LState) (l : List β)
    (hF : ∀ a b, F a b = (a.1.push [(a.2.fresh .int).1], (a.2.fresh .int).2)) :
    CtorCls ctx id args st (.regsVec (l.foldl F (#[], st)).1.toList) (l.foldl F (#[], st)).2 := by
  have := foldl_inv (fun a : Array (List Reg) × LState =>
      ClsStep st a.2 ∧ (Sz st → ∀ rs ∈ a.1.toList, ∀ r ∈ rs, RegCls a.2.classes r) ∧
      a.2.emitted = st.emitted)
    F l (#[], st) ⟨clsStep_refl st, by simp, rfl⟩ (by
      intro b _ a ⟨h1, h2, h3⟩
      rw [hF]
      have hs1 := clsStep_fresh a.2 .int
      refine ⟨clsStep_trans h1 hs1, fun hs rs hrs r hr => ?_, by simp [LState.fresh, h3]⟩
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hrs
      rcases hrs with hrs | rfl
      · exact regCls_step hs1 (h2 hs rs hrs r hr)
      · simp only [List.mem_singleton] at hr
        subst hr
        exact fresh_cls (sz_step h1 hs) .int)
  obtain ⟨h1, h2, h3⟩ := this
  refine ⟨h1, fun hs r hr => ?_, ⟨[], by simp [h3], by simp⟩⟩
  simp only [V.regsIn, List.mem_flatten] at hr
  obtain ⟨rs, hrs, hr⟩ := hr
  exact .inr (.inl (h2 hs rs hrs r hr))

theorem store_regsFrom {P : Reg → Prop} {r : Reg} (h : P r) (op : StoreOp) (off : Int)
    (fl : Clif.MemFlags) : RegsFrom P (.store op r (.spOffset off) fl) := by
  intro g hg; simp [MInst.mapRegs, AMode.mapRegs, hg r h]

/-- `gen_call_args`: register uses from the arguments, stores of the stack arguments. -/
theorem ctorCls_callArgs (hid : id = TId.gen_call_args)
    (F : Array (Reg × Reg) × LState → (ArgLoc × Reg) × Nat → Array (Reg × Reg) × LState)
    (l : List ((ArgLoc × Reg) × Nat))
    (hF : ∀ a b, F a b = match b.1.1 with
      | .reg p => (a.1.push (b.1.2, p), a.2)
      | .stack off => (a.1, a.2.emit (.store (storeOpOfBytes b.2) b.1.2 (.spOffset off) trustedFlags)))
    (hl : ∀ b ∈ l, (∀ p, b.1.1 = .reg p → ∀ n c, p ≠ .vreg n c) ∧ b.1.2 ∈ regsInL args) :
    CtorCls ctx id args st (.op (.callArgs (l.foldl F (#[], st)).1.toList)) (l.foldl F (#[], st)).2 := by
  have := foldl_inv (fun a : Array (Reg × Reg) × LState =>
      (∀ q ∈ a.1.toList, q.1 ∈ regsInL args ∧ ∀ n c, q.2 ≠ .vreg n c) ∧
      a.2.classes = st.classes ∧ a.2.nextVreg = st.nextVreg ∧
      ∃ ms : List MInst, a.2.emitted = st.emitted ++ ms.toArray ∧
        ∀ m ∈ ms, RegsFrom (fun r => r ∈ regsInL args) m)
    F l (#[], st) ⟨by simp, rfl, rfl, [], by simp, by simp⟩ (by
      intro b hb a ⟨h1, h2, h3, ms, h4, h5⟩
      rw [hF]
      obtain ⟨hp, hr⟩ := hl b hb
      split
      · rename_i p hbp
        refine ⟨?_, h2, h3, ms, h4, h5⟩
        intro q hq
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact h1 q hq
        · exact ⟨hr, hp p hbp⟩
      · rename_i off _
        refine ⟨h1, by simp [LState.emit, h2], by simp [LState.emit, h3],
          ms ++ [MInst.store (storeOpOfBytes b.2) b.1.2 (.spOffset off) trustedFlags],
          by simp [LState.emit, h4], ?_⟩
        intro m hm
        rcases List.mem_append.mp hm with hm | hm
        · exact h5 m hm
        · simp only [List.mem_singleton] at hm
          subst hm
          exact store_regsFrom hr _ _ _)
  obtain ⟨h1, h2, h3, ms, h4, h5⟩ := this
  refine ⟨clsStep_of_eq h2 h3, fun _ r hr => ?_,
    ⟨ms, h4, fun _ m hm => (h5 m hm).mono fun r hr => .inl ⟨by simp [hid, emitIds], hr⟩⟩⟩
  simp only [V.regsIn, opRegs, pairRegs, List.mem_flatMap, List.mem_cons, List.mem_nil_iff,
    or_false] at hr
  obtain ⟨q, hq, hr⟩ := hr
  obtain ⟨hq1, hq2⟩ := h1 q hq
  rcases hr with rfl | rfl
  · exact .inl hq1
  · exact .inr (.inl (regCls_real hq2))

theorem ctorCls_callInfo {c : CallInfo} {k : Nat} (hr : ∀ r ∈ opRegs (.callInfo c), r ∈ regsInL args) :
    CtorCls ctx id args st (.op (.callInfo c)) { st with outgoing := max st.outgoing k } :=
  ⟨clsStep_of_eq rfl rfl, fun _ r h => .inl (hr r h), ⟨[], by simp, by simp⟩⟩

theorem ctorCls_putRegsVec {vs : List Nat} {rs : List Reg} (h : vs.mapM ctx.valueReg? = some rs) :
    CtorCls ctx id [.values vs] st (.regsVec (rs.map fun r => [r])) st := by
  refine ctorCls_same fun r hr => ?_
  have hr' : r ∈ rs := by
    simp only [V.regsIn, List.mem_flatten, List.mem_map] at hr
    obtain ⟨_, ⟨a, ha, rfl⟩, hr⟩ := hr
    simp only [List.mem_singleton] at hr
    exact hr ▸ ha
  obtain ⟨x, hx, he⟩ := mapM_mem h r hr'
  exact .inr (.inl ⟨x, by simpa [V.valsIn] using hx, he⟩)

theorem ctorCls_tryRets {k : Nat} {ps : List Reg} (hps : retRegs k = some ps) (cc : Option Clif.CallConv)
    (f : Reg × Reg → Bool) :
    CtorCls ctx id args st
      (.op (.callRets (ps.zip ctx.tryRegs.1 ++ List.filter f ((payloadRegs cc).zip ctx.tryRegs.2))))
      st := by
  refine ⟨clsStep_refl st, fun _ r hr => ?_, ⟨[], by simp, by simp⟩⟩
  simp only [V.regsIn, opRegs, pairRegs, List.mem_flatMap, List.mem_append, List.mem_filter,
    List.mem_cons, List.mem_nil_iff, or_false] at hr
  obtain ⟨⟨a, b⟩, hq, hr⟩ := hr
  rcases hq with hq | ⟨hq, -⟩
  · have hz := List.of_mem_zip hq
    rcases hr with rfl | rfl
    · exact .inr (.inl (regCls_real (retRegs_phys hps _ hz.1)))
    · exact .inr (.inr (.inr (.inr (.inl hz.2))))
  · have hz := List.of_mem_zip hq
    rcases hr with rfl | rfl
    · exact .inr (.inl (regCls_real (payloadRegs_phys cc _ hz.1)))
    · exact .inr (.inr (.inr (.inr (.inr hz.2))))

/-- Close `CtorCls` of a constructor that keeps the state. -/
macro "cls_same" : tactic => `(tactic| (refine ctorCls_same ?_; simp_all (config := { decide := true }) [V.regsIn, opRegs, pairRegs, V.valsIn, opVals]; done))

set_option maxHeartbeats 2000000 in
/-- **Every extern constructor** satisfies `CtorCls`. -/
theorem externCtor_cls (ctx : Ctx) (t : Term) (args : List V) (st : LState) :
    CtorClsP ctx st t.id args (externCtor ctx t args st) := by
  unfold externCtor
  split
  · intro v st' h
    split at h
    · cases h
      exact ctorCls_same (by simp [V.regsIn])
    · cases h
  · apply externCtor_split _ (CtorClsP ctx st)
    all_goals
      intros
      unfold CtorClsP
      intro v st' h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals cases h
    all_goals first
      | cls_same
      | (rename_i heq; simp only [Option.map_eq_some_iff, Function.comp_apply] at heq
         obtain ⟨_, _, rfl⟩ := heq; cls_same)
      | exact ctorCls_invalid
      | exact ctorCls_fresh
      | exact ctorCls_emit rfl ‹_›
      | exact ctorCls_rets rfl ‹_›
      | exact ctorCls_lc (loadConstantFull_cls _ _ _ _ _)
      | exact ctorCls_callOutput _ _ (fun _ _ => rfl)
      | (refine ctorCls_callInfo ?_
         intro r hr
         simp only [opRegs, List.mem_append, List.mem_singleton, List.mem_nil_iff, false_or] at hr
         simp only [regsInL_cons, regsInL_nil, V.regsIn, opRegs, List.mem_append,
           List.mem_singleton, List.mem_nil_iff, List.append_nil]
         first | (rcases hr with (h | h) | h <;> simp [h]) | (rcases hr with h | h <;> simp [h]))
      | (refine ctorCls_same fun r hr => ?_
         simp only [V.regsIn, List.mem_flatten, List.mem_map] at hr
         obtain ⟨_, ⟨r', hr', rfl⟩, hr⟩ := hr
         simp only [List.mem_singleton] at hr
         subst hr
         obtain ⟨x, hx, he⟩ := mapM_mem ‹_› r' hr'
         exact .inr (.inl ⟨x, by simpa [V.valsIn] using hx, he⟩))
      | (refine ctorCls_same fun r hr => ?_
         simp only [V.regsIn, List.mem_singleton] at hr
         subst hr
         exact .inl (by simpa [V.regsIn] using List.mem_of_getElem? ‹_›))
      | (refine ctorCls_same fun r hr => ?_
         simp only [V.regsIn, opRegs, pairRegs, List.mem_flatMap, List.mem_cons, List.mem_nil_iff,
           or_false] at hr
         obtain ⟨⟨a, b⟩, hq, hr⟩ := hr
         have hz := List.of_mem_zip hq
         rcases hr with rfl | rfl
         · exact .inr (.inr (retRegs_phys ‹_› _ hz.1))
         · obtain ⟨l, hl, hrl⟩ := single_mem ‹_› _ hz.2
           exact .inl (by simp [V.regsIn, opRegs]; exact ⟨l, hl, hrl⟩))
      | (refine ctorCls_callArgs rfl _ _ (fun _ _ => rfl) ?_
         intro b hb
         have hz := List.of_mem_zip hb
         have hz1 := List.of_mem_zip hz.1
         refine ⟨fun p hp => sigArgLocs_phys ‹_› _ (hp ▸ hz1.1) p rfl, ?_⟩
         obtain ⟨l, hl, hrl⟩ := single_mem ‹_› _ hz1.2
         simp [V.regsIn, opRegs]; exact ⟨l, hl, hrl⟩)
      | exact ctorCls_putRegsVec ‹_›
      | exact ctorCls_tryRets ‹_› _ _

end Backend.Proof.Spill

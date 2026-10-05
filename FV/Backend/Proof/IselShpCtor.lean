import FV.Backend.Proof.IselShpBase
import FV.Backend.Proof.IselShpFns
import FV.Backend.Proof.IselCovModel
import FV.Backend.Proof.LogicImmComplete

/-!
# Control shapes of the ISLE lowering (V4): `emit`ted instructions and extern constructors

* `ctlA_sound`: an `emit`ted instruction whose abstract value passes the shape check `ctlA`
  has its control shape (`CtlShape`), if it is a control form.
* `ctorS_sound`: an extern constructor call with the precondition `apreS` returns a value
  `actor` describes (V3's `ctor_sound`) and keeps the state invariant `ShpIs`: the instructions
  it emits are not control forms, except `emit`'s (`ctlA_sound`) and `gen_return`'s `Rets` of
  int vregs in x0..x7 (`externCtor_shp`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Spill Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx}

/-! ## `emit`ted instructions -/

theorem condBrKind_reg {v : V} {kd : CondBrKind} (h : v.condBrKind? = some kd) :
    KindOk kd ∨ ∃ t k r sv, (k = VIdx.CondBrKind.Zero ∨ k = VIdx.CondBrKind.NotZero) ∧
      v = .data t k [.reg r, sv] ∧ (KindOk kd ↔ ∃ n, r = .vreg n .int) := by
  unfold V.condBrKind? at h
  obtain ⟨⟨k, fs⟩, he, h2⟩ := bind_some_ex h
  rw [enumOf_eq he]
  dsimp only at h2
  split at h2
  · rename_i rv sv
    obtain ⟨r, hr, h2⟩ := bind_some_ex h2
    obtain ⟨s, -, h2⟩ := bind_some_ex h2
    cases h2
    cases rv <;> simp [V.reg?] at hr
    subst hr
    exact .inr ⟨_, _, _, _, .inl rfl, rfl, Iff.rfl⟩
  · rename_i rv sv
    obtain ⟨r, hr, h2⟩ := bind_some_ex h2
    obtain ⟨s, -, h2⟩ := bind_some_ex h2
    cases h2
    cases rv <;> simp [V.reg?] at hr
    subst hr
    exact .inr ⟨_, _, _, _, .inr rfl, rfl, Iff.rfl⟩
  · obtain ⟨c, -, h2⟩ := bind_some_ex h2
    cases h2
    exact .inl trivial
  · cases h2

theorem kindA1_sound {a : AW} {v : V} {kd : CondBrKind} (ha : kindA1 a = true)
    (hv : γ f ctx a v) (h : v.condBrKind? = some kd) : KindOk kd := by
  rcases condBrKind_reg h with h | ⟨t, k, r, sv, hk, rfl, hiff⟩
  · exact h
  · refine hiff.mpr ?_
    match a, ha, hv with
    | .data t' k' fs, ha, hv =>
      obtain ⟨vs, he, hl⟩ := hv
      cases he
      obtain ⟨ra, bs, rfl, hra, -⟩ := γL_cons hl
      have hz : (k == VIdx.CondBrKind.Zero || k == VIdx.CondBrKind.NotZero) = true := by
        rcases hk with rfl | rfl <;> rfl
      simp only [kindA1, hz, ite_true] at ha
      exact isV_sound ha hra

theorem kindA_sound {a : AW} {v : V} {kd : CondBrKind} (ha : kindA a = true)
    (hv : γ f ctx a v) (h : v.condBrKind? = some kd) : KindOk kd := by
  cases a with
  | alts as =>
    simp only [kindA, Bool.and_eq_true, List.all_eq_true] at ha
    obtain ⟨b, hb, hbv⟩ := γAny_iff.mp hv
    exact kindA1_sound (ha.2 b hb) hbv h
  | _ => exact kindA1_sound (by simpa only [kindA] using ha) hv h


theorem ofV_ctl (N : Nat) {t : TypeId} {k : Nat} {as : List AW} {vs : List V} {m : MInst}
    (hl : γL f ctx as vs) (hc1 : ctl1 k as = true) (hm : MInst.ofV (.data t k vs) = some m)
    (hc : m.isCtl = true) : CtlShape N m := by
  unfold MInst.ofV at hm
  obtain ⟨⟨k', fs⟩, he, h2⟩ := bind_some_ex hm
  clear hm
  simp only [V.enumOf?, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨-, rfl, rfl⟩ := he
  dsimp only at h2
  revert as
  revert hc
  revert h2
  revert m
  apply ofV_split _ (fun k fs (r : Option MInst) => ∀ (m : MInst), r = some m → m.isCtl = true →
    ∀ as, γL f ctx as fs → ctl1 k as = true → CtlShape N m)
  all_goals
    intros
    rename_i m hm hc as hl hc1
    try simp only at hm
    repeat' (first | (obtain ⟨_, _, hm⟩ := bind_some_ex hm) | split at hm)
    all_goals first
      | (cases hm; done)
      | (simp only [pure, Option.some.injEq] at hm
         subst hm
         first
         | (cases hc; done)
         | (simp (config := { decide := true }) [ctl1, defCtl] at hc1; done)
         | constructor
         | skip)
  all_goals first
    | (obtain ⟨a1, a2, a3, rfl, -, -, h3⟩ := holds2_three hl
       simp only [ctl1, beq_self_eq_true, ite_true] at hc1
       exact kindA_sound hc1 h3 (by assumption))
    | (obtain ⟨a1, a2, rfl, h1, -⟩ := holds2_two hl
       simp (config := { decide := true }) only [ctl1, ite_true, ite_false]
         at hc1
       exact kindA_sound hc1 h1 (by assumption))
    | (obtain ⟨a1, _, rfl, -, hl⟩ := γL_cons hl
       obtain ⟨a2, _, rfl, -, hl⟩ := γL_cons hl
       obtain ⟨a3, _, rfl, -, hl⟩ := γL_cons hl
       obtain ⟨a4, _, rfl, h4, hl⟩ := γL_cons hl
       obtain ⟨a5, _, rfl, -, hl⟩ := γL_cons hl
       obtain rfl := γL_nil hl
       simp (config := { decide := true }) only [ctl1, ite_true, ite_false]
         at hc1
       obtain rfl := reg?_eq ‹V.reg? _ = some _›
       obtain ⟨n, rfl⟩ := isV_sound hc1 h4
       exact .tbb _ _ _ _ _)


theorem ctlA1_sound (N : Nat) {a : AW} {v : V} {m : MInst} (hv : γ f ctx a v) (ha : ctlA1 a = true)
    (hm : MInst.ofV v = some m) (hc : m.isCtl = true) : CtlShape N m := by
  match a, ha, hv with
  | .data t k fs, ha, hv =>
    obtain ⟨vs, rfl, hl⟩ := hv
    exact ofV_ctl N hl ha hm hc

/-- **An `emit`ted instruction the shape check passes** has its control shape. -/
theorem ctlA_sound {f ctx} {a : AW} {v : V} {m : MInst} (N : Nat) (hv : γ f ctx a v)
    (ha : ctlA a = true) (hm : MInst.ofV v = some m) (hc : m.isCtl = true) : CtlShape N m := by
  cases a with
  | alts as =>
    simp only [ctlA, Bool.and_eq_true, List.all_eq_true] at ha
    obtain ⟨b, hb, hbv⟩ := γAny_iff.mp hv
    exact ctlA1_sound N hbv (ha.2 b hb) hm hc
  | _ => exact ctlA1_sound N hv (by simpa only [ctlA] using ha) hm hc


/-! ## Extern constructors -/

/-- Every instruction emitted from `s0` to `s` is not a control form. -/
def NcSince (s0 s : LState) : Prop :=
  ∃ ms : List MInst, s.emitted = s0.emitted ++ ms.toArray ∧ ∀ m ∈ ms, m.isCtl = false

theorem ncSince_emit {s0 s : LState} {m : MInst} (h : NcSince s0 s) (hm : m.isCtl = false) :
    NcSince s0 (s.emit m) := by
  obtain ⟨ms, h1, h2⟩ := h
  refine ⟨ms ++ [m], by simp [LState.emit, h1], fun m' hm' => ?_⟩
  rcases List.mem_append.mp hm' with hm' | hm'
  · exact h2 m' hm'
  · simp only [List.mem_singleton] at hm'; subst hm'; exact hm

theorem ncSince_fresh {s0 s : LState} {c : RegClass} (h : NcSince s0 s) :
    NcSince s0 (s.fresh c).2 := h

theorem loadConstantFull_nc (bits : Nat) (se : Bool) (sz : OperandSize) (value : Nat)
    (st : LState) : NcSince st (loadConstantFull bits se sz value st).2 := by
  unfold loadConstantFull
  dsimp only
  refine foldl_inv (fun x : Reg × LState × Nat => NcSince st x.2.1) _ _ _ ?_ ?_
  · exact ncSince_emit (ncSince_fresh ⟨[], by simp, by simp⟩) rfl
  · intro sh _ x hx
    refine ite_inv (I := fun x : Reg × LState × Nat => NcSince st x.2.1) (fun _ => hx) fun _ => ?_
    refine ite_inv (I := fun x : Reg × LState × Nat => NcSince st x.2.1) (fun _ => ?_) fun _ => hx
    exact ncSince_emit (ncSince_fresh hx) rfl

theorem callArgs_nc (st : LState)
    (F : Array (Reg × Reg) × LState → (ArgLoc × Reg) × Nat → Array (Reg × Reg) × LState)
    (l : List ((ArgLoc × Reg) × Nat))
    (hF : ∀ a b, F a b = match b.1.1 with
      | .reg p => (a.1.push (b.1.2, p), a.2)
      | .stack off => (a.1, a.2.emit (.store (storeOpOfBytes b.2) b.1.2 (.spOffset off) trustedFlags))) :
    NcSince st (l.foldl F (#[], st)).2 := by
  refine foldl_inv (fun a : Array (Reg × Reg) × LState => NcSince st a.2) F l (#[], st)
    ⟨[], by simp, by simp⟩ ?_
  intro b _ a ha
  rw [hF]
  split
  · exact ha
  · exact ncSince_emit ha rfl

/-- An instruction an extern constructor may emit: not a control form, `emit`'s instruction, or
`gen_return`'s `Rets` of argument registers in the return registers. -/
def EmitS (id : TermId) (args : List V) (m : MInst) : Prop :=
  m.isCtl = false ∨ (id = TId.emit ∧ ∃ i, args = [i] ∧ MInst.ofV i = some m) ∨
    (id = TId.gen_return ∧ ∃ (rss : List (List Reg)) (ps rs : List Reg), args = [.regsVec rss] ∧ retRegs rss.length = some ps ∧
      (∀ r ∈ rs, ∃ l ∈ rss, r ∈ l) ∧ m = .rets (rs.zip ps))

/-- The emitted instructions of every successful result meet `EmitS`. -/
def ShpP (st : LState) (id : TermId) (args : List V) (r : ExtResult (V × LState)) : Prop :=
  ∀ v st', r = .ok (v, st') →
    ∃ ms : List MInst, st'.emitted = st.emitted ++ ms.toArray ∧ ∀ m ∈ ms, EmitS id args m

theorem emitS_of_nc {id : TermId} {args : List V} {st st' : LState} (h : NcSince st st') :
    ∃ ms : List MInst, st'.emitted = st.emitted ++ ms.toArray ∧ ∀ m ∈ ms, EmitS id args m :=
  let ⟨ms, h1, h2⟩ := h
  ⟨ms, h1, fun m hm => .inl (h2 m hm)⟩

/-- **Every extern constructor** emits only non-control instructions, `emit`'s instruction, and
`gen_return`'s `Rets`. -/
theorem externCtor_shp (ctx : Ctx) (t : Term) (args : List V) (st : LState) :
    ShpP st t.id args (externCtor ctx t args st) := by
  unfold externCtor
  split
  · intro v st' h
    split at h
    · cases h; exact ⟨[], by simp, by simp⟩
    · cases h
  · apply externCtor_split _ (ShpP st)
    all_goals
      intros
      unfold ShpP
      intro v st' h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals cases h
    all_goals first
      | (refine ⟨[], ?_, fun _ h => by cases h⟩; simp [LState.fresh]; done)
      | (apply emit_one; exact .inr (.inl ⟨rfl, _, rfl, ‹_›⟩))
      | (apply emit_one; exact .inr (.inr ⟨rfl, _, _, _, rfl, ‹_›, single_mem ‹_›, rfl⟩))
      | exact emitS_of_nc (callArgs_nc st _ _ (fun _ _ => rfl))
      | exact emitS_of_nc (loadConstantFull_nc _ _ _ _ st)
      | exact ⟨[], (callOutput_fold st _ _ (fun _ _ => rfl)).1.trans (by simp), by simp⟩

/-! ## `gen_return`'s `Rets` -/

theorem zip_retPairs : ∀ (rs ps : List Reg), (∀ r ∈ rs, ∃ n, r = .vreg n .int) →
    ∃ ns : List (Nat × Reg), retPairs ns = rs.zip ps ∧ (ns.map (·.2)).Sublist ps
  | [], ps, _ => ⟨[], rfl, List.nil_sublist _⟩
  | _ :: _, [], _ => ⟨[], rfl, List.Sublist.slnil⟩
  | r :: rs, p :: ps, h => by
    obtain ⟨n, rfl⟩ := h r List.mem_cons_self
    obtain ⟨ns, h1, h2⟩ := zip_retPairs rs ps fun r' hr' => h r' (List.mem_cons_of_mem _ hr')
    exact ⟨(n, p) :: ns, by simp [retPairs, ← h1], h2.cons_cons p⟩

/-- `gen_return`'s `Rets` of int vregs has its control shape. -/
theorem rets_shape (N : Nat) {k : Nat} {rs ps : List Reg} (hk : retRegs k = some ps)
    (hrs : ∀ r ∈ rs, ∃ n, r = .vreg n .int) : CtlShape N (.rets (rs.zip ps)) := by
  obtain ⟨h8, rfl⟩ := retRegs_eq hk
  obtain ⟨ns, h1, h2⟩ := zip_retPairs rs _ hrs
  rw [← h1]
  refine .rets ns (fun q hq => ?_) ?_
  · obtain ⟨j, hj, hjq⟩ := List.mem_map.mp (h2.subset (List.mem_map_of_mem hq))
    exact ⟨j, by simp at hj; omega, hjq.symm⟩
  · exact h2.nodup (List.Pairwise.map Reg.x (fun _ _ hab h => hab (by cases h; rfl)) List.nodup_range)

/-! ## Constructors -/

theorem apre_of_apreS {id : TermId} {as : List AW} (h : apreS id as = true) : apre id as = true := by
  simp only [apreS, Bool.and_eq_true] at h
  exact h.1

/-- An instruction a constructor call with `apreS` emits has its control shape. -/
theorem emitS_shape {N : Nat} {id : TermId} {as : List AW} {vs : List V}
    (hvs : Holds2 f ctx as vs) (hpre : apreS id as = true) {m : MInst} (h : EmitS id vs m)
    (hc : m.isCtl = true) : CtlShape N m := by
  rcases h with h | ⟨rfl, i, rfl, hi⟩ | ⟨rfl, rss, ps, rs, rfl, hps, hrs, rfl⟩
  · rw [h] at hc; cases hc
  · obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    simp only [apreS, beq_self_eq_true, ite_true, Bool.and_eq_true] at hpre
    exact ctlA_sound N ha hpre.2 hi hc
  · obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    have hne : (TId.gen_return == TId.emit) = false := by decide
    simp only [apreS, hne, beq_self_eq_true, ite_true, ite_false, Bool.false_eq_true,
      Bool.and_eq_true, beq_iff_eq] at hpre
    refine rets_shape N hps fun r hr => ?_
    obtain ⟨l, hl, hrl⟩ := hrs r hr
    exact kind_one ((deep_sound a _ ha).1 r (List.mem_flatten.mpr ⟨l, hl, hrl⟩)) hpre.2

/-- **Constructors** (V4): `actor` describes the result, the state invariant is kept. -/
theorem ctorS_sound {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (N : Nat) (s0 : LState)
    (as : List AW) (vs : List V) (term : Term) (v : V) (st st' : LState)
    (hvs : Holds2 f ctx as vs) (hIs : ShpIs N s0 st) (hpre : apreS term.id as = true)
    (h : (sem ctx).ctor term vs st = .ok (v, st')) :
    γ f ctx (actor term.id as) v ∧ ShpIs N s0 st' := by
  refine ⟨(ctor_sound logicImmComplete hctx st as vs term v st st' hvs ⟨[], by simp, by simp⟩
    (apre_of_apreS hpre) h).1, ?_, ?_⟩
  · obtain ⟨ms0, h0, h1⟩ := hIs.1
    obtain ⟨ms, h2, h3⟩ := externCtor_shp ctx term vs st v st' h
    refine ⟨ms0 ++ ms, by rw [h2, h0]; simp, fun m hm => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact h1 m hm
    · exact emitS_shape hvs hpre (h3 m hm)
  · exact Nat.le_trans hIs.2 (externCtor_ok ctx term vs st v st' h).vreg

end Backend.Proof.Cov


import FV.Backend.Proof.IselShpTFns
import FV.Backend.Proof.IselShpTBase
import FV.Backend.Proof.IselShpCtor
import FV.Backend.Proof.IselCovTCtor

/-!
# Control shapes of the typed ISLE lowering: `emit`ted instructions and extern constructors

`IselShpCtor` over the typed domain `AT`:

* `ctlAT_sound`: an `emit`ted instruction whose abstract value passes `ctlAT` has its control
  shape, if it is a control form;
* `ctorST_sound`: an extern constructor call with the precondition `apreST` returns a value
  `actor` describes (the typed `ctor_sound`) and keeps the state invariant `ShpIsT`: the
  instructions it emits are not control forms, except `emit`'s (`ctlAT_sound`) and
  `gen_return`'s `Rets` of vregs (`rets_shapeT`). Which instructions an extern constructor emits
  does not depend on the domain (`Cov.externCtor_shp`).
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Spill Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
open Backend.Proof.Cov (condBrKind_reg EmitS externCtor_shp reg?_eq kind_cases LogicImmComplete)

variable {f : Clif.Function} {ctx : Ctx}

/-! ## `emit`ted instructions -/

theorem kindAT1_sound {a : AT} {v : V} {kd : CondBrKind} (ha : kindAT1 a = true)
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
      simp only [kindAT1, hz, ite_true] at ha
      exact isV_sound ha hra

theorem kindAT_sound {a : AT} {v : V} {kd : CondBrKind} (ha : kindAT a = true)
    (hv : γ f ctx a v) (h : v.condBrKind? = some kd) : KindOk kd := by
  cases a with
  | alts as =>
    simp only [kindAT, Bool.and_eq_true, List.all_eq_true] at ha
    obtain ⟨b, hb, hbv⟩ := γAny_iff.mp hv
    exact kindAT1_sound (ha.2 b hb) hbv h
  | _ => exact kindAT1_sound (by simpa only [kindAT] using ha) hv h

theorem ofV_ctlT (N : Nat) {t : TypeId} {k : Nat} {as : List AT} {vs : List V} {m : MInst}
    (hl : γL f ctx as vs) (hc1 : ctlT1 k as = true) (hm : MInst.ofV (.data t k vs) = some m)
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
    ∀ as, γL f ctx as fs → ctlT1 k as = true → CtlShape N m)
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
         | (simp (config := { decide := true }) [ctlT1, Cov.defCtl] at hc1; done)
         | constructor
         | skip)
  all_goals first
    | (obtain ⟨a1, a2, a3, rfl, -, -, h3⟩ := holds2_three hl
       simp only [ctlT1, beq_self_eq_true, ite_true] at hc1
       exact kindAT_sound hc1 h3 (by assumption))
    | (obtain ⟨a1, a2, rfl, h1, -⟩ := holds2_two hl
       simp (config := { decide := true }) only [ctlT1, ite_true, ite_false]
         at hc1
       exact kindAT_sound hc1 h1 (by assumption))
    | (obtain ⟨a1, _, rfl, -, hl⟩ := γL_cons hl
       obtain ⟨a2, _, rfl, -, hl⟩ := γL_cons hl
       obtain ⟨a3, _, rfl, -, hl⟩ := γL_cons hl
       obtain ⟨a4, _, rfl, h4, hl⟩ := γL_cons hl
       obtain ⟨a5, _, rfl, -, hl⟩ := γL_cons hl
       obtain rfl := γL_nil hl
       simp (config := { decide := true }) only [ctlT1, ite_true, ite_false]
         at hc1
       obtain rfl := reg?_eq ‹V.reg? _ = some _›
       obtain ⟨n, rfl⟩ := isV_sound hc1 h4
       exact .tbb _ _ _ _ _)

theorem ctlAT1_sound (N : Nat) {a : AT} {v : V} {m : MInst} (hv : γ f ctx a v)
    (ha : ctlAT1 a = true) (hm : MInst.ofV v = some m) (hc : m.isCtl = true) : CtlShape N m := by
  match a, ha, hv with
  | .data t k fs, ha, hv =>
    obtain ⟨vs, rfl, hl⟩ := hv
    exact ofV_ctlT N hl ha hm hc

/-- **An `emit`ted instruction the shape check passes** has its control shape. -/
theorem ctlAT_sound {a : AT} {v : V} {m : MInst} (N : Nat) (hv : γ f ctx a v)
    (ha : ctlAT a = true) (hm : MInst.ofV v = some m) (hc : m.isCtl = true) : CtlShape N m := by
  cases a with
  | alts as =>
    simp only [ctlAT, Bool.and_eq_true, List.all_eq_true] at ha
    obtain ⟨b, hb, hbv⟩ := γAny_iff.mp hv
    exact ctlAT1_sound N hbv (ha.2 b hb) hm hc
  | _ => exact ctlAT1_sound N hv (by simpa only [ctlAT] using ha) hm hc

/-! ## Constructors -/

/-- A register of a kind in a mask without the `xzr`/real-register bits is a vreg. -/
theorem kind_vreg {r : Reg} {m : Nat} (hk : r.kind &&& m ≠ 0) (hm : m &&& 12 = 0) :
    ∃ n c, r = .vreg n c := by
  cases r with
  | vreg n c => exact ⟨n, c, rfl⟩
  | _ =>
    exfalso; apply hk
    first
      | (show 4 &&& m = 0
         apply Nat.eq_of_testBit_eq; intro i
         have := congrArg (·.testBit i) hm
         simp only [Nat.testBit_and] at this ⊢
         rcases i with _ | _ | _ | _ | i <;> simp_all [Nat.testBit_succ])
      | (show 8 &&& m = 0
         apply Nat.eq_of_testBit_eq; intro i
         have := congrArg (·.testBit i) hm
         simp only [Nat.testBit_and] at this ⊢
         rcases i with _ | _ | _ | _ | i <;> simp_all [Nat.testBit_succ])

theorem apre_of_apreST {id : TermId} {as : List AT} (h : apreST id as = true) : apre id as = true := by
  simp only [apreST, Bool.and_eq_true] at h
  exact h.1

/-- An instruction a constructor call with `apreST` emits has its typed control shape. -/
theorem emitS_shapeT {N : Nat} {id : TermId} {as : List AT} {vs : List V}
    (hvs : Holds2 f ctx as vs) (hpre : apreST id as = true) {m : MInst} (h : EmitS id vs m)
    (hc : m.isCtl = true) : CtlShapeT N m := by
  rcases h with h | ⟨rfl, i, rfl, hi⟩ | ⟨rfl, -⟩
  · rw [h] at hc; cases hc
  · obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    simp only [apreST, beq_self_eq_true, ite_true, Bool.and_eq_true] at hpre
    exact (ctlAT_sound N ha hpre.2 hi hc).toT
  · have hne : (TId.gen_return == TId.emit) = false := by decide
    simp [apreST, hne] at hpre

/-- **Constructors** (typed V4): `actor` describes the result, the state invariant is kept. -/
theorem ctorST_sound (hLI : LogicImmComplete) (hctx : CtxInvT f ctx) (N : Nat) (s0 : LState)
    (as : List AT) (vs : List V) (term : Term) (v : V) (st st' : LState)
    (hvs : Holds2 f ctx as vs) (hIs : ShpIsT N s0 st) (hpre : apreST term.id as = true)
    (h : (sem ctx).ctor term vs st = .ok (v, st')) :
    γ f ctx (actor term.id as) v ∧ ShpIsT N s0 st' := by
  refine ⟨(ctor_sound hLI hctx st as vs term v st st' hvs ⟨[], by simp, by simp⟩
    (apre_of_apreST hpre) h).1, ?_, ?_⟩
  · obtain ⟨ms0, h0, h1⟩ := hIs.1
    obtain ⟨ms, h2, h3⟩ := externCtor_shp ctx term vs st v st' h
    refine ⟨ms0 ++ ms, by rw [h2, h0]; simp, fun m hm => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact h1 m hm
    · exact emitS_shapeT hvs hpre (h3 m hm)
  · exact Nat.le_trans hIs.2 (externCtor_ok ctx term vs st v st' h).vreg

end Backend.Proof.CovT

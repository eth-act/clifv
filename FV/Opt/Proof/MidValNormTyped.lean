import FV.Opt.Proof.MidValNormAlg2

/-!
# The typed rules are a sound normaliser under typing (#1119 stage 2, the typed seam)

`Norm.stdT f = Norm.orElse Norm.std (Norm.guard (typedStep (atomTy f)))` (`FV/Opt/MidVal.lean`).
The typed rules read an atom's static type in `f` (`atomTy`), so they hold only in frames where
the atoms below the node hold values of those types (`AtomsTyped`): their obligation is
`NormSoundT f` (`FV/Opt/Proof/MidValTerm.lean`), proved here against `Clif.evalInst`:

* `selTyped` — `select ty c 1 0` with `c` a term of integer type `tc` (an atom by `atomTy`, a
  node by `nodeTy`; `tyAt_val`) is `icmp ne tc c 0` at `i8`, its `uextend ty` at a wider type;
  `select ty c 0 1` is the same with `icmp eq`. With `c` of type `tc` both sides read `c`'s
  truth (`icmp_zero_ne`, `icmp_zero_eq`); with no value for `c` neither side has one. Without the
  typing the rewrite is false: with `c` of another type the `icmp` is stuck and the `select` is
  not (`FVTest/Opt/MidValTypedWitness.lean`);
* `redTyped` — `ireduce ty (extend op uty x)` with `x` an atom of static type `xt`, both
  narrower than `uty`: `x` if `xt = ty`, `extend op ty x` if narrower, `ireduce ty x` if wider
  (as `redExt`, whose `x` is a node typed by `nodeTy`).

Main results: `ruleSoundT_selTyped`, `ruleSoundT_redTyped`, `normSoundT_typed`, and
**`normSoundT_stdT : NormSoundT f (Norm.stdT f)`** (the validator's default normaliser).
-/

namespace Opt.MidVal

open Clif

/-! ## Combinators -/

/-- `NormSoundT` for a rule whose result has its operands before each of its occurrences. -/
def RuleSoundT (f : Function) (r : Norm) : Prop :=
  ∀ (tms : Array Tm) (i : Inst) (x : Tm), r tms i = some x →
    (∀ t, tms[t]? = some x → ∀ o ∈ x.ops, o < t) →
    ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x → AtomsTyped f tms fr mem i →
      tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem i

theorem normSoundT_guard {f : Function} {r : Norm} (h : RuleSoundT f r) :
    NormSoundT f (Norm.guard r) := by
  intro tms i x hx
  obtain ⟨hr, ho⟩ := guard_spec hx
  exact h tms i x hr ho

theorem normSoundT_orElse {f : Function} {a b : Norm} (ha : NormSoundT f a)
    (hb : NormSoundT f b) : NormSoundT f (Norm.orElse a b) := by
  intro tms i x hx
  simp only [Norm.orElse] at hx
  cases h : a tms i with
  | some y =>
    rw [h] at hx
    cases hx
    exact ha tms i _ h
  | none =>
    rw [h] at hx
    exact hb tms i x hx

/-! ## Static types -/

/-- The static type `tyAt` gives a term reachable from `i`'s operands is its value's type, in a
frame where the atoms below `i` are typed. -/
theorem tyAt_val {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {i : Inst} {c : Nat}
    {tc : Ty} (hA : AtomsTyped f tms fr mem i) (hc : TmReach tms i c)
    (h : tyAt (atomTy f) tms c = some tc) {v : Val} (hv : tmVal f tms fr mem c = some v) :
    v.ty = tc := by
  unfold tyAt at h
  cases hc' : tms[c]? with
  | none => rw [hc'] at h; cases h
  | some a =>
    rw [hc'] at h
    cases a with
    | node j =>
      simp only at h
      by_cases ho : ((operands j).all fun o => decide (o < c)) = true
      · rw [if_pos ho] at h
        simp only [List.all_eq_true, decide_eq_true_eq] at ho
        rw [tmVal_node hc' ho] at hv
        exact evalNode_ty_of_nodeTy h hv
      · rw [if_neg ho] at h
        cases h
    | param b k => exact hA c _ tc v hc hc' h hv
    | res b k j => exact hA c _ tc v hc hc' h hv
    | poison b k => exact hA c _ tc v hc hc' h hv

/-! ## `selTyped` -/

theorem selCC_spec {w : Nat} {vx vy : BitVec w} {cc : IntCC} (h : selCC vx vy = some cc) :
    (vx = 1 ∧ vy = 0 ∧ cc = .ne) ∨ (vx = 0 ∧ vy = 1 ∧ cc = .eq) := by
  unfold selCC at h
  by_cases h10 : (vx == 1 && vy == 0) = true
  · rw [if_pos h10] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h10
    cases h
    exact .inl ⟨h10.1, h10.2, rfl⟩
  · rw [if_neg h10] at h
    by_cases h01 : (vx == 0 && vy == 1) = true
    · rw [if_pos h01] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h01
      cases h
      exact .inr ⟨h01.1, h01.2, rfl⟩
    · rw [if_neg h01] at h
      cases h

/-- `icmp ne c 0` is the `i8` 0/1 of `c`'s truth. -/
theorem icmp_zero_ne {w : Nat} (cb : BitVec w) : Sem.icmp .ne cb 0 = Sem.bool8 (Sem.truthy cb) :=
  rfl

/-- `icmp eq c 0` is the `i8` 0/1 of `c`'s falsity. -/
theorem icmp_zero_eq {w : Nat} (cb : BitVec w) :
    Sem.icmp .eq cb 0 = Sem.bool8 (!Sem.truthy cb) := by
  simp [Sem.icmp, Sem.intcc, Sem.truthy, bne]

theorem select_one_zero {v w : Nat} (c : BitVec v) :
    Sem.select c (1 : BitVec w) 0 = if Sem.truthy c then 1 else 0 :=
  rfl

theorem select_zero_one {v w : Nat} (c : BitVec v) :
    Sem.select c (0 : BitVec w) 1 = if !Sem.truthy c then 1 else 0 := by
  cases h : Sem.truthy c <;> simp [Sem.select, h]

theorem ruleSoundT_selTyped {f : Function} {ty : Ty} {c x y : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), selTyped (atomTy f) tms ty c x y = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        AtomsTyped f tms fr mem (.select ty c x y) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.select ty c x y) := by
  intro tms x' h hord fr mem t ht hA
  unfold selTyped at h
  split at h
  · cases h
  · split at h
    · rename_i tc vx vy htc hvx hvy
      split at h
      · obtain ⟨cc, hcc, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨n, hn, hw⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨hz1, hz2⟩ := findTm_spec hz
        obtain ⟨hn1, hn2⟩ := findTm_spec hn
        have hx : (tmFrame f tms fr mem).regs x = some ⟨ty, vx⟩ := constAt_spec hvx
        have hy : (tmFrame f tms fr mem).regs y = some ⟨ty, vy⟩ := constAt_spec hvy
        have hzv : (tmFrame f tms fr mem).regs z = some ⟨tc, 0⟩ := by
          show tmVal f tms fr mem z = _
          rw [tmVal_node hz1 hz2]
          rfl
        have hn' : tmVal f tms fr mem n = evalNode (tmFrame f tms fr mem) mem (.icmp cc tc c z) :=
          tmVal_node hn1 hn2
        rw [evalNode_select hx hy]
        unfold selWrap at hw
        rcases hcv : (tmFrame f tms fr mem).regs c with _ | cv
        · -- `c` has no value: neither side has one
          have hnone : evalNode (tmFrame f tms fr mem) mem (.icmp cc tc c z) = none := by
            rw [evalNode_icmp, hcv]
            rfl
          by_cases h8 : (ty == .i8) = true
          · rw [if_pos h8, hn1] at hw
            cases hw
            rw [tmVal_node ht (hord t ht), hnone]
            rfl
          · rw [if_neg h8] at hw
            split at hw
            · cases hw
              rw [tmVal_node ht (hord t ht), evalNode_uextend]
              show (tmVal f tms fr mem n).bind _ = _
              rw [hn', hnone]
              rfl
            · cases hw
        · -- `c` holds a value of its static type `tc`
          have hct : cv.ty = tc := tyAt_val hA (.op (by simp [operands])) htc hcv
          obtain ⟨cty, cb⟩ := cv
          simp only at hct
          subst hct
          have hic : evalNode (tmFrame f tms fr mem) mem (.icmp cc cty c z) =
              some ⟨.i8, Sem.icmp cc cb 0⟩ := by
            rw [evalNode_icmp, hcv, hzv]
            simp
          by_cases h8 : (ty == .i8) = true
          · rw [if_pos h8, hn1] at hw
            cases hw
            simp only [beq_iff_eq] at h8
            subst h8
            rw [tmVal_node ht (hord t ht), hic]
            rcases selCC_spec hcc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
            · simp only [Option.map_some, icmp_zero_ne, select_one_zero]
              cases Sem.truthy cb <;> decide
            · simp only [Option.map_some, icmp_zero_eq, select_zero_one]
              cases Sem.truthy cb <;> decide
          · rw [if_neg h8] at hw
            split at hw
            · rename_i hw8
              cases hw
              have h8w : (Ty.i8).width < ty.width := hw8
              rw [tmVal_node ht (hord t ht), evalNode_uextend]
              show (tmVal f tms fr mem n).bind _ = _
              rw [hn', hic]
              rcases selCC_spec hcc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
              · simp only [Option.map_some, Option.bind_some, h8w, ite_true, icmp_zero_ne,
                  select_one_zero, uextend_bool8 _ hw8, uextend_bool8' _ hw8]
              · simp only [Option.map_some, Option.bind_some, h8w, ite_true, icmp_zero_eq,
                  select_zero_one, uextend_bool8 _ hw8, uextend_bool8' _ hw8]
            · cases hw
      · cases h
    · cases h

/-! ## `redTyped` -/

theorem ruleSoundT_redTyped {f : Function} {ty : Ty} {u : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), redTyped (atomTy f) tms ty u = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        AtomsTyped f tms fr mem (.ireduce ty u) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.ireduce ty u) := by
  intro tms x' h hord fr mem t ht hA
  unfold redTyped at h
  split at h
  · rename_i op uty x hu
    split at h
    · rename_i a xt hx hxt
      rw [hx] at hxt
      simp only [Option.bind_some] at hxt
      have hna : ∀ j, a ≠ .node j := by
        rintro j rfl
        simp [atomTy] at hxt
      have hxv : tmVal f tms fr mem x = (atomVal f a).bind fr.regs := tmVal_atom hx hna
      have hreach : TmReach tms (.ireduce ty u) x :=
        .sub (.op (by simp [operands])) (nodeAt_spec hu).1 (by simp [operands])
      split at h
      · rename_i hw
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
        have hu' : (tmFrame f tms fr mem).regs u =
            evalNode (tmFrame f tms fr mem) mem (.extend op uty x) := by
          show tmVal f tms fr mem u = _
          exact tmVal_node (nodeAt_spec hu).1 (nodeAt_spec hu).2
        rw [evalNode_ireduce, hu', evalNode_extend]
        rcases hv : (tmFrame f tms fr mem).regs x with _ | v
        · -- `x` has no value: neither side has one
          simp only [Option.bind_none]
          split at h
          · cases h
            rw [tmVal_atom ht hna, ← hxv]
            exact hv
          · split at h
            · cases h
              rw [tmVal_node ht (hord t ht), evalNode_extend, hv]
              rfl
            · split at h
              · cases h
                rw [tmVal_node ht (hord t ht), evalNode_ireduce, hv]
                rfl
              · cases h
        · have hvt : v.ty = xt := hA x a xt v hreach hx hxt hv
          obtain ⟨vt, vb⟩ := v
          simp only at hvt
          subst hvt
          simp only [Option.bind_some, hw.1, hw.2, ite_true]
          split at h
          · rename_i he
            simp only [beq_iff_eq] at he
            subst he
            cases h
            rw [tmVal_atom ht hna, ← hxv, show tmVal f tms fr mem x = some ⟨vt, vb⟩ from hv,
              setWidth_extOp op vb (Nat.le_of_lt hw.2), extOp_same]
          · split at h
            · rename_i hlt
              cases h
              rw [tmVal_node ht (hord t ht), evalNode_extend, hv]
              simp only [Option.bind_some, hlt, ite_true,
                setWidth_extOp op vb (Nat.le_of_lt hw.2)]
            · split at h
              · rename_i hgt
                cases h
                rw [tmVal_node ht (hord t ht), evalNode_ireduce, hv]
                simp only [Option.bind_some, hgt, ite_true,
                  setWidth_extOp op vb (Nat.le_of_lt hw.2), extOp_narrow op vb (Nat.le_of_lt hgt)]
              · cases h
      · cases h
    · cases h
  · cases h

/-! ## The default normaliser -/

theorem ruleSoundT_typedStep {f : Function} : RuleSoundT f (typedStep (atomTy f)) := by
  intro tms i x' h hord fr mem t ht hA
  cases i with
  | select ty c x y => exact ruleSoundT_selTyped tms x' h hord fr mem t ht hA
  | ireduce ty u => exact ruleSoundT_redTyped tms x' h hord fr mem t ht hA
  | _ => simp [typedStep] at h

/-- **The typed rules are sound under typing.** -/
theorem normSoundT_typed {f : Function} : NormSoundT f (Norm.guard (typedStep (atomTy f))) :=
  normSoundT_guard ruleSoundT_typedStep

/-- **The validator's default normaliser is sound under typing.** -/
theorem normSoundT_stdT {f : Function} : NormSoundT f (Norm.stdT f) :=
  normSoundT_orElse normSound_std.toT normSoundT_typed

end Opt.MidVal

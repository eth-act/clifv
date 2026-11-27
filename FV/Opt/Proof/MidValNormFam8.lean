import FV.Opt.Proof.MidValNormDrop
import FV.Opt.Proof.MidValNormAlg2

/-!
# Family 8: comparisons with an offset, saturating differences, products of constants,
differences of sums (#1119, agent MidendNext8)

`fam8Step`, the first step of `Norm.stdD f` (`FV/Opt/MidVal.lean`), the validator's default
normaliser. Each rule of
`fam8Step` gives a node with the value of the node it rewrites wherever the node's operands have
values (`RuleSoundD`, `FV/Opt/Proof/MidValNormDrop.lean`), proved against `Clif.evalInst`:

* `cmpOff` — `icmp cc ty (x + k) c` is `icmp cc' ty x (c' - k)` for `offCmp cc c = (cc', c')`
  (`eq`/`ne` with `c`, and `ugt 0`, `ule 0`, `ult 1`, `uge 1` as `ne`/`eq` with `0`;
  `offCmp_spec`, `add_beq_sub`), and `icmp ugt/ule ty (x + k) x`, `k ≠ 0`, is `icmp cc' ty x c'`
  for `selfOff cc k = (cc', c')` (`x + k >u x` iff `x <u -k`, `ult_add_self`);
* `cmpSub` — `(x - y) >u x` iff `y >u x` (`ult_sub_self`), and its `ule`/`uge`/`ult` forms;
* `mulMul` — `(x * c1) * c2 = x * (c1 * c2)`;
* `subAdds` — `(p + q) - (r + q) = p - r` and the three other positions of the common term; it
  drops the common term, so it holds where the operands have values (`NormSoundD`), not in
  every frame.

Main results: `ruleSoundD_fam8Step` (`normSoundD_stdD`, the default normaliser with families 8
and 9: `FV/Opt/Proof/MidValNormFam9.lean`).
-/

namespace Opt.MidVal

open Clif

/-! ## Arithmetic facts -/

theorem mod_two {a N : Nat} (h : a < N + N) : a % N = if a < N then a else a - N := by
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem nat_add_self {x k N : Nat} (hx : x < N) (hk : k ≠ 0) (hk' : k < N) :
    x < (x + k) % N ↔ x < (N - k) % N := by
  rw [mod_two (by omega), mod_two (by omega)]
  split <;> split <;> omega

/-- `x + k >u x` iff `x <u -k`, for `k ≠ 0`. -/
theorem ult_add_self {w : Nat} (X K : BitVec w) (hK : K ≠ 0) : X.ult (X + K) = X.ult (-K) := by
  have hk : K.toNat ≠ 0 := fun h => hK (BitVec.eq_of_toNat_eq (by simp [h]))
  simp only [BitVec.ult, BitVec.toNat_add, BitVec.toNat_neg, decide_eq_decide]
  exact nat_add_self X.isLt hk K.isLt

theorem nat_sub_self {x y N : Nat} (hx : x < N) (hy : y < N) : x < (N - y + x) % N ↔ x < y := by
  rw [mod_two (by omega)]
  split <;> omega

/-- `x - y >u x` iff `y >u x`. -/
theorem ult_sub_self {w : Nat} (X Y : BitVec w) : X.ult (X - Y) = X.ult Y := by
  simp only [BitVec.ult, BitVec.toNat_sub, decide_eq_decide]
  exact nat_sub_self X.isLt Y.isLt

theorem ule_not_ult {w : Nat} (a b : BitVec w) : a.ule b = !(b.ult a) := by
  simp only [BitVec.ule, BitVec.ult]
  rw [Bool.eq_iff_iff]
  simp [Nat.not_lt]

theorem add_beq_sub {w : Nat} (X K C : BitVec w) : (X + K == C) = (X == C - K) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    rw [← h, BitVec.add_sub_cancel]
  · intro h
    rw [h, BitVec.sub_add_cancel]

theorem add_neg_mid {w : Nat} (A B Z : BitVec w) : A + -B + (Z + -Z) = A - B := by
  rw [← BitVec.sub_eq_add_neg Z Z, BitVec.sub_self, BitVec.add_zero, ← BitVec.sub_eq_add_neg]

theorem sub_add_add_r {w : Nat} (P Q R : BitVec w) : (P + Q) - (R + Q) = P - R := by
  rw [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.sub_eq_add_neg (-R) Q,
    show P + Q + (-R + -Q) = P + -R + (Q + -Q) by ac_rfl, add_neg_mid]

theorem sub_add_add_l {w : Nat} (P Q S : BitVec w) : (P + Q) - (P + S) = Q - S := by
  rw [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.sub_eq_add_neg (-P) S,
    show P + Q + (-P + -S) = Q + -S + (P + -P) by ac_rfl, add_neg_mid]

theorem sub_add_add_lr {w : Nat} (P Q R : BitVec w) : (P + Q) - (R + P) = Q - R := by
  rw [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.sub_eq_add_neg (-R) P,
    show P + Q + (-R + -P) = Q + -R + (P + -P) by ac_rfl, add_neg_mid]

theorem sub_add_add_rl {w : Nat} (P Q S : BitVec w) : (P + Q) - (Q + S) = P - S := by
  rw [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.sub_eq_add_neg (-Q) S,
    show P + Q + (-Q + -S) = P + -S + (Q + -Q) by ac_rfl, add_neg_mid]

/-! ## Values of the nodes involved -/

/-- An `icmp` whose operands hold values of its type. -/
theorem evalNode_icmp_of {F : Frame} {mem : Mem} {cc : IntCC} {ty : Ty} {x y : ValueId}
    {X Y : BitVec ty.width} (hx : F.regs x = some ⟨ty, X⟩) (hy : F.regs y = some ⟨ty, Y⟩) :
    evalNode F mem (.icmp cc ty x y) = some ⟨.i8, Sem.icmp cc X Y⟩ := by
  rw [evalNode_icmp, hx, hy]
  simp only [Option.bind_some, Val.as?_mk, Option.map_some]

/-- A constant term looked up with `findTm`. -/
theorem tmVal_findConst {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {ty : Ty}
    {v : BitVec ty.width} {kc : Nat} (h : findTm tms (.node (.iconst ty v)) = some kc) :
    tmVal f tms fr mem kc = some ⟨ty, v⟩ := by
  obtain ⟨hk1, hk2⟩ := findTm_spec h
  rw [tmVal_node hk1 hk2]
  rfl

/-- Two values of one type that are equal are equal bits. -/
theorem val_bits_eq {ty : Ty} {a b : BitVec ty.width} (h : (some ⟨ty, a⟩ : Option Val) = some ⟨ty, b⟩) :
    a = b := by
  simp only [Option.some.injEq, Val.mk.injEq, heq_eq_eq, true_and] at h
  exact h

/-! ## `cmpOff` -/

theorem offCmp_spec {w : Nat} (hw : 0 < w) {cc cc' : IntCC} {c c' : BitVec w}
    (h : offCmp cc c = some (cc', c')) :
    (cc' = .eq ∨ cc' = .ne) ∧ ∀ Z : BitVec w, Sem.intcc cc Z c = Sem.intcc cc' Z c' := by
  unfold offCmp at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    exact ⟨hc, fun _ => rfl⟩
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨.inr rfl, fun Z => by simp only [Sem.intcc]; exact ugt_zero Z⟩
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨.inl rfl, fun Z => by simp only [Sem.intcc]; exact ule_zero Z⟩
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨.inl rfl, fun Z => by simp only [Sem.intcc]; exact ult_one hw Z⟩
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨.inr rfl, fun Z => by simp only [Sem.intcc]; exact uge_one hw Z⟩
  cases h

theorem selfOff_spec {w : Nat} (hw : 0 < w) {cc cc' : IntCC} {k c' : BitVec w}
    (h : selfOff cc k = some (cc', c')) :
    ∀ X : BitVec w, Sem.intcc cc (X + k) X = Sem.intcc cc' X c' := by
  intro X
  unfold selfOff at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at hc
    obtain ⟨hk, hcc⟩ := hc
    have hult := ult_add_self X k hk
    split at h
    · rename_i h1
      cases h
      have h1' : -k = 1#w := by simpa using h1
      rw [h1', ult_one hw] at hult
      rcases hcc with rfl | rfl
      · simp only [Sem.intcc, if_true]
        exact hult
      · have hne : (IntCC.ule == IntCC.ugt) = false := by decide
        simp only [Sem.intcc, hne, Bool.false_eq_true, if_false, ule_not_ult, hult, bne]
        rfl
    · cases h
      rcases hcc with rfl | rfl
      · simp only [Sem.intcc, if_true]
        exact hult
      · have hne : (IntCC.ule == IntCC.ugt) = false := by decide
        simp only [Sem.intcc, hne, Bool.false_eq_true, if_false, ule_not_ult, hult]
  · cases h

theorem cmpOffPlan_spec {tms : Array Tm} {cc cc' : IntCC} {ty : Ty} {a b x : Nat}
    {v : BitVec ty.width} (h : cmpOffPlan tms cc ty a b = some (cc', x, v)) :
    ∃ k kv, nodeAt tms a = some (.binary .iadd ty x k) ∧ constAt tms ty k = some kv ∧
      ((∃ c, constAt tms ty b = some c ∧
          ∀ X : BitVec ty.width, Sem.intcc cc (X + kv) c = Sem.intcc cc' X v) ∨
        (b = x ∧ ∀ X : BitVec ty.width, Sem.intcc cc (X + kv) X = Sem.intcc cc' X v)) := by
  unfold cmpOffPlan at h
  split at h
  · rename_i ty' x0 k hA
    split at h
    · rename_i hty
      have hty' : ty' = ty := by simpa using hty
      subst hty'
      split at h
      · rename_i kv hkv
        split at h
        · rename_i c hc
          obtain ⟨⟨cc1, c1⟩, ho, he⟩ := Option.map_eq_some_iff.1 h
          cases he
          obtain ⟨hcc, hZ⟩ := offCmp_spec (Ty.width_pos _) ho
          refine ⟨k, kv, hA, hkv, .inl ⟨c, hc, fun X => ?_⟩⟩
          rw [hZ (X + kv)]
          rcases hcc with rfl | rfl
          · simp only [Sem.intcc]
            exact add_beq_sub X kv c1
          · simp only [Sem.intcc, bne, add_beq_sub]
        · split at h
          · rename_i hxb
            have hxb' : x0 = b := by simpa using hxb
            obtain ⟨⟨cc1, c1⟩, ho, he⟩ := Option.map_eq_some_iff.1 h
            cases he
            exact ⟨k, kv, hA, hkv, .inr ⟨hxb'.symm, selfOff_spec (Ty.width_pos _) ho⟩⟩
          · cases h
      · cases h
    · cases h
  · cases h

theorem ruleSoundD_cmpOff {f : Function} {cc : IntCC} {ty : Ty} {a b : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), cmpOff tms cc ty a b = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        (∀ o ∈ operands (.icmp cc ty a b), (tmVal f tms fr mem o).isSome) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.icmp cc ty a b) := by
  intro tms x' h hord fr mem t ht hd
  unfold cmpOff at h
  obtain ⟨⟨cc', x, v⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨kc, hkc, rfl⟩ := Option.map_eq_some_iff.1 h
  have hV : (tmFrame f tms fr mem).regs kc = some ⟨ty, v⟩ := tmVal_findConst hkc
  obtain ⟨k, kv, hA, hkv, hcase⟩ := cmpOffPlan_spec hp
  obtain ⟨X, K, hX, hK, ha⟩ :=
    tmVal_bin_ops (f := f) (fr := fr) (mem := mem) rfl hA (hd a (by simp [operands]))
  have hKv : kv = K := val_bits_eq ((constAt_spec hkv).symm.trans hK)
  subst hKv
  have hX' : (tmFrame f tms fr mem).regs x = some ⟨ty, X⟩ := hX
  have ha' : (tmFrame f tms fr mem).regs a = some ⟨ty, X + kv⟩ := ha
  rw [tmVal_node' ht (hord t ht), evalNode_icmp_of hX' hV]
  rcases hcase with ⟨c, hc, hZ⟩ | ⟨rfl, hZ⟩
  · have hc' : (tmFrame f tms fr mem).regs b = some ⟨ty, c⟩ := constAt_spec hc
    rw [evalNode_icmp_of ha' hc']
    simp only [Sem.icmp, hZ X]
  · rw [evalNode_icmp_of ha' hX']
    simp only [Sem.icmp, hZ X]

/-! ## `cmpSub` -/

theorem ruleSoundD_cmpSub {f : Function} {cc : IntCC} {ty : Ty} {a b : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), cmpSub tms cc ty a b = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        (∀ o ∈ operands (.icmp cc ty a b), (tmVal f tms fr mem o).isSome) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.icmp cc ty a b) := by
  intro tms x' h hord fr mem t ht hd
  unfold cmpSub at h
  split at h
  · rename_i hcc
    simp only [Bool.or_eq_true, beq_iff_eq] at hcc
    split at h
    · rename_i ty' x y hA
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        obtain ⟨X, Y, hX, hY, ha⟩ :=
          tmVal_bin_ops (f := f) (fr := fr) (mem := mem) rfl hA (hd a (by simp [operands]))
        have hX' : (tmFrame f tms fr mem).regs x = some ⟨ty', X⟩ := hX
        have hY' : (tmFrame f tms fr mem).regs y = some ⟨ty', Y⟩ := hY
        have ha' : (tmFrame f tms fr mem).regs a = some ⟨ty', X - Y⟩ := ha
        rw [evalNode_icmp_of ha' hX']
        have hlhs : Sem.intcc cc (X - Y) X = Sem.intcc cc Y X := by
          rcases hcc with rfl | rfl
          · simp only [Sem.intcc]
            exact ult_sub_self X Y
          · simp only [Sem.intcc, ule_not_ult, ult_sub_self]
        split at h
        · cases h
          rw [tmVal_node' ht (hord t ht), evalNode_icmp_of hX' hY']
          simp only [Sem.icmp, hlhs, intcc_swap]
        · cases h
          rw [tmVal_node' ht (hord t ht), evalNode_icmp_of hY' hX']
          simp only [Sem.icmp, hlhs]
      · cases h
    · cases h
  split at h
  · rename_i _ hcc
    simp only [Bool.or_eq_true, beq_iff_eq] at hcc
    split at h
    · rename_i ty' x y hB
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        cases h
        obtain ⟨X, Y, hX, hY, hb⟩ :=
          tmVal_bin_ops (f := f) (fr := fr) (mem := mem) rfl hB (hd b (by simp [operands]))
        have hX' : (tmFrame f tms fr mem).regs x = some ⟨ty', X⟩ := hX
        have hY' : (tmFrame f tms fr mem).regs y = some ⟨ty', Y⟩ := hY
        have hb' : (tmFrame f tms fr mem).regs b = some ⟨ty', X - Y⟩ := hb
        rw [tmVal_node' ht (hord t ht), evalNode_icmp_of hX' hY', evalNode_icmp_of hX' hb']
        rcases hcc with rfl | rfl
        · simp only [Sem.icmp, Sem.intcc, ule_not_ult, ult_sub_self]
        · simp only [Sem.icmp, Sem.intcc, ult_sub_self]
      · cases h
    · cases h
  · cases h

/-! ## `mulMul` -/

theorem mulMulPlan_spec {tms : Array Tm} {ty : Ty} {a b x : Nat} {v : BitVec ty.width}
    (h : mulMulPlan tms ty a b = some (x, v)) :
    ∃ c cv k2, nodeAt tms a = some (.binary .imul ty x c) ∧ constAt tms ty c = some cv ∧
      constAt tms ty b = some k2 ∧ v = cv * k2 := by
  unfold mulMulPlan at h
  split at h
  · rename_i ty' x0 c k2 hA hb
    split at h
    · rename_i hty
      have hty' : ty' = ty := by simpa using hty
      subst hty'
      split at h
      · rename_i cv hcv
        split at h
        · cases h
        · cases h
          exact ⟨c, cv, k2, hA, hcv, hb, rfl⟩
      · cases h
    · cases h
  · cases h

theorem ruleSoundD_mulMul {f : Function} {ty : Ty} {a b : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), mulMul tms ty a b = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        (∀ o ∈ operands (.binary .imul ty a b), (tmVal f tms fr mem o).isSome) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.binary .imul ty a b) := by
  intro tms x' h hord fr mem t ht hd
  unfold mulMul at h
  obtain ⟨⟨x, v⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨kc, hkc, rfl⟩ := Option.map_eq_some_iff.1 h
  have hV : (tmFrame f tms fr mem).regs kc = some ⟨ty, v⟩ := tmVal_findConst hkc
  obtain ⟨c, cv, k2, hA, hcv, hk2, rfl⟩ := mulMulPlan_spec hp
  obtain ⟨X, C, hX, hC, ha⟩ :=
    tmVal_bin_ops (f := f) (fr := fr) (mem := mem) rfl hA (hd a (by simp [operands]))
  have hCv : cv = C := val_bits_eq ((constAt_spec hcv).symm.trans hC)
  subst hCv
  have hX' : (tmFrame f tms fr mem).regs x = some ⟨ty, X⟩ := hX
  have ha' : (tmFrame f tms fr mem).regs a = some ⟨ty, Sem.binary .imul X cv⟩ := ha
  have hb' : (tmFrame f tms fr mem).regs b = some ⟨ty, k2⟩ := constAt_spec hk2
  rw [tmVal_node' ht (hord t ht), evalNode_bin_of rfl hX' hV, evalNode_bin_of rfl ha' hb']
  simp only [Sem.binary, Sem.imul, BitVec.mul_assoc]

/-! ## `subAdds` -/

theorem ruleSoundD_subAdds {f : Function} {ty : Ty} {a b : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), subAdds tms ty a b = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        (∀ o ∈ operands (.binary .isub ty a b), (tmVal f tms fr mem o).isSome) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.binary .isub ty a b) := by
  intro tms x' h hord fr mem t ht hd
  unfold subAdds at h
  split at h
  · rename_i ta p q tb r s hA hB
    split at h
    · rename_i hty
      simp only [Bool.and_eq_true, beq_iff_eq] at hty
      obtain ⟨h1, h2⟩ := hty
      subst ta
      subst tb
      obtain ⟨P, Q, hP, hQ, ha⟩ :=
        tmVal_bin_ops (f := f) (fr := fr) (mem := mem) rfl hA (hd a (by simp [operands]))
      obtain ⟨R, S, hR, hS, hb⟩ :=
        tmVal_bin_ops (f := f) (fr := fr) (mem := mem) rfl hB (hd b (by simp [operands]))
      have hP' : (tmFrame f tms fr mem).regs p = some ⟨ty, P⟩ := hP
      have hQ' : (tmFrame f tms fr mem).regs q = some ⟨ty, Q⟩ := hQ
      have hR' : (tmFrame f tms fr mem).regs r = some ⟨ty, R⟩ := hR
      have hS' : (tmFrame f tms fr mem).regs s = some ⟨ty, S⟩ := hS
      have ha' : (tmFrame f tms fr mem).regs a = some ⟨ty, P + Q⟩ := ha
      have hb' : (tmFrame f tms fr mem).regs b = some ⟨ty, R + S⟩ := hb
      rw [evalNode_bin_of rfl ha' hb']
      split at h
      · rename_i hqs
        have hqs' : q = s := by simpa using hqs
        subst hqs'
        have hQS : Q = S := val_bits_eq (hQ.symm.trans hS)
        subst hQS
        cases h
        rw [tmVal_node' ht (hord t ht), evalNode_bin_of rfl hP' hR']
        simp only [Sem.binary, Sem.isub, sub_add_add_r]
      split at h
      · rename_i hpr
        have hpr' : p = r := by simpa using hpr
        subst hpr'
        have hPR : P = R := val_bits_eq (hP.symm.trans hR)
        subst hPR
        cases h
        rw [tmVal_node' ht (hord t ht), evalNode_bin_of rfl hQ' hS']
        simp only [Sem.binary, Sem.isub, sub_add_add_l]
      split at h
      · rename_i hps
        have hps' : p = s := by simpa using hps
        subst hps'
        have hPS : P = S := val_bits_eq (hP.symm.trans hS)
        subst hPS
        cases h
        rw [tmVal_node' ht (hord t ht), evalNode_bin_of rfl hQ' hR']
        simp only [Sem.binary, Sem.isub, sub_add_add_lr]
      split at h
      · rename_i hqr
        have hqr' : q = r := by simpa using hqr
        subst hqr'
        have hQR : Q = R := val_bits_eq (hQ.symm.trans hR)
        subst hQR
        cases h
        rw [tmVal_node' ht (hord t ht), evalNode_bin_of rfl hP' hS']
        simp only [Sem.binary, Sem.isub, sub_add_add_rl]
      cases h
    · cases h
  · cases h

/-! ## Family 8 and the default normaliser -/

theorem ruleSoundD_fam8Step {f : Function} : RuleSoundD f fam8Step := by
  intro tms i x' h hord fr mem t ht _ hd
  cases i with
  | icmp cc ty a b =>
    simp only [fam8Step] at h
    cases h1 : cmpSub tms cc ty a b with
    | some y =>
      rw [h1] at h
      cases h
      exact ruleSoundD_cmpSub tms _ h1 hord fr mem t ht hd
    | none =>
      rw [h1] at h
      simp only [Option.orElse_none] at h
      exact ruleSoundD_cmpOff tms x' h hord fr mem t ht hd
  | binary op ty a b =>
    cases op
    case isub => exact ruleSoundD_subAdds tms x' h hord fr mem t ht hd
    case imul => exact ruleSoundD_mulMul tms x' h hord fr mem t ht hd
    all_goals simp [fam8Step] at h
  | _ => simp [fam8Step] at h

end Opt.MidVal

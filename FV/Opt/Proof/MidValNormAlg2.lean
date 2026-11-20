import FV.Opt.Proof.MidValNormAlg

/-!
# The second set of single-node algebraic rules is sound (#1119 stage 2, family 2)

`Opt.MidVal.Norm.alg2` (`Norm.guard algStep2`) rewrites a node into a node of the same value
under `Clif.evalInst` in every frame, ill-typed operands included (no typing premise):

* `icmpSwap` — `icmp cc ty a b = icmp (swap cc) ty b a` (`intcc_swap`); both read `a` and `b`
  at `ty`;
* `icmpBool` — with `u` an `icmp` (at `i8`) or its `uextend` to a type wider than `i8`
  (`boolAt_val`: a 0/1 of that type whenever the `icmp` evaluates, nothing otherwise),
  `icmp eq u 1 = icmp ne u 0` is that `icmp` and `icmp eq u 0 = icmp ne u 1` its inversion;
* `icmpUnit` — `icmp ult x 1 = icmp eq x 0`, `icmp uge x 1 = icmp ne x 0` (types have a positive
  width, `Ty.width_pos`), `icmp ugt x 0 = icmp ne x 0`, `icmp ule x 0 = icmp eq x 0`;
* `subNeg` — `isub 0 x = ineg x`; `mulTwo` — `imul x 2 = iadd x x` (either order); `shlOne` —
  `ishl x c = iadd x x` for a constant amount `c` that is `1` modulo the width;
  `xorNot` — `bxor x -1 = bnot x` (either order);
* `bmaskBool` — `bmask.i8 c = ineg.i8 c` for an `icmp` `c` (a 0/1 `i8`).

Main results: **`normSound_alg2 : NormSound Norm.alg2`** and **`normSound_std`** for the
validator's default normaliser (`evalConst`, then `Norm.alg2`, then `Norm.alg`).
-/

namespace Opt.MidVal

open Clif

/-- `RuleSound` of one rule's answer at one node. -/
def NodeSound (tms : Array Tm) (i : Inst) (r : Option Tm) : Prop :=
  ∀ x', r = some x' → (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
    ∀ (f : Function) (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
      tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem i

theorem nodeSound_orElse {tms : Array Tm} {i : Inst} {r s : Option Tm}
    (hr : NodeSound tms i r) (hs : NodeSound tms i s) : NodeSound tms i (r.orElse fun _ => s) := by
  intro x' h
  cases r with
  | some y => exact hr x' h
  | none => exact hs x' h

/-! ## Values -/

theorem evalNode_unary {F : Frame} {mem : Mem} {op : UnaryOp} {ty : Ty} {x : ValueId} :
    evalNode F mem (.unary op ty x) =
      ((F.regs x).bind (·.as? ty)).map fun A => ⟨ty, Sem.unary op A⟩ := by
  simp only [evalNode, evalInst, Frame.getAs, Frame.get]
  rcases ha : F.regs x with _ | va
  · simp [Res.ofOption, bind, Res.bind]
  · cases hA : va.as? ty <;> simp [Res.ofOption, Res.bind, bind, pure, hA]

theorem evalNode_bmask {F : Frame} {mem : Mem} {ty : Ty} {x : ValueId} :
    evalNode F mem (.bmask ty x) = (F.regs x).map fun a => ⟨ty, Sem.bmask a.bits⟩ := by
  rcases hx : F.regs x with _ | a <;>
    simp [evalNode, evalInst, Frame.get, Res.ofOption, hx, bind, Res.bind, pure]

/-- The value of a node term whose operands are earlier (from a `Norm.guard`ed result). -/
theorem tmVal_res {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {t : Nat} {j : Inst}
    (ht : tms[t]? = some (.node j)) (hord : ∀ t, tms[t]? = some (Tm.node j) → ∀ o ∈ (Tm.node j).ops, o < t) :
    tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem j :=
  tmVal_node ht (hord t ht)

/-! ## `icmpSwap` -/

theorem intcc_swap {w : Nat} (cc : IntCC) (x y : BitVec w) :
    Sem.intcc (IntCC.swap cc) y x = Sem.intcc cc x y := by
  cases cc <;> first
    | rfl
    | exact bne_comm
    | exact BEq.comm

theorem ns_icmpSwap {tms : Array Tm} {cc : IntCC} {ty : Ty} {a b : Nat} :
    NodeSound tms (.icmp cc ty a b) (icmpSwap tms cc ty a b) := by
  intro x' h hord f fr mem t ht
  unfold icmpSwap at h
  split at h
  · cases h
    rw [tmVal_res ht hord, evalNode_icmp, evalNode_icmp]
    rcases (tmFrame f tms fr mem).regs a |>.bind (·.as? ty) with _ | A <;>
      rcases (tmFrame f tms fr mem).regs b |>.bind (·.as? ty) with _ | B <;>
      simp [Sem.icmp, intcc_swap]
  · cases h

/-! ## `icmpBool` -/

theorem one_ne_zero_of_pos {w : Nat} (h : 0 < w) : (1#w : BitVec w) ≠ 0#w := by
  intro e
  have h1 : 1 < 2 ^ w :=
    Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide) h)
  have := congrArg BitVec.toNat e
  simp [Nat.mod_eq_of_lt h1] at this

/-- A 0/1 copy of an `icmp` (`boolAt`) has, as term value, the comparison's outcome at its
type. -/
theorem boolAt_val {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {ty : Ty} {u : Nat}
    {j : Inst} (h : boolAt tms ty u = some j) :
    (∃ cc cty a b, j = .icmp cc cty a b) ∧
    tmVal f tms fr mem u = (evalNode (tmFrame f tms fr mem) mem j).map fun v =>
      ⟨ty, if Sem.truthy v.bits then 1 else 0⟩ := by
  unfold boolAt at h
  split at h
  · rename_i cc cty a b hu
    split at h
    · rename_i h8
      simp only [beq_iff_eq] at h8
      subst h8
      cases h
      refine ⟨⟨cc, cty, a, b, rfl⟩, ?_⟩
      rw [tmVal_node (nodeAt_spec hu).1 (nodeAt_spec hu).2]
      rcases hv : evalNode (tmFrame f tms fr mem) mem (.icmp cc cty a b) with _ | v
      · rfl
      · obtain ⟨bb, rfl⟩ := evalNode_icmp_bool hv
        cases bb <;> rfl
    · cases h
  · rename_i ty' c hu
    split at h
    · rename_i hw
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
      obtain ⟨rfl, hw8⟩ := hw
      split at h
      · rename_i cc cty a b hc
        cases h
        refine ⟨⟨cc, cty, a, b, rfl⟩, ?_⟩
        rw [tmVal_node (nodeAt_spec hu).1 (nodeAt_spec hu).2, evalNode_uextend]
        show (tmVal f tms fr mem c).bind _ = _
        rw [tmVal_node (nodeAt_spec hc).1 (nodeAt_spec hc).2]
        rcases hv : evalNode (tmFrame f tms fr mem) mem (.icmp cc cty a b) with _ | v
        · rfl
        · obtain ⟨bb, rfl⟩ := evalNode_icmp_bool hv
          have h8w : (Ty.i8).width < ty'.width := hw8
          simp only [Option.bind_some, Option.map_some, h8w, ite_true, uextend_bool8' _ hw8,
            truthy_bool8']
      · cases h
    · cases h
  · cases h

theorem icmp_bool_keep {w : Nat} (hw : 0 < w) (cc : IntCC) (bb : Bool) (kv : BitVec w)
    (h : (cc == .eq && kv == 1) || (cc == .ne && kv == 0)) :
    Sem.icmp cc (if bb = true then (1 : BitVec w) else 0) kv = Sem.bool8 bb := by
  have h10 := one_ne_zero_of_pos hw
  have e1 : (1#w == 0#w) = false := beq_false_of_ne h10
  have e2 : (0#w == 1#w) = false := beq_false_of_ne (Ne.symm h10)
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases bb <;>
    simp [Sem.icmp, Sem.intcc, e1, e2, bne]

theorem icmp_bool_flip {w : Nat} (hw : 0 < w) (cc : IntCC) (bb : Bool) (kv : BitVec w)
    (h : (cc == .eq && kv == 0) || (cc == .ne && kv == 1)) :
    Sem.icmp cc (if bb = true then (1 : BitVec w) else 0) kv = Sem.bool8 (!bb) := by
  have h10 := one_ne_zero_of_pos hw
  have e1 : (1#w == 0#w) = false := beq_false_of_ne h10
  have e2 : (0#w == 1#w) = false := beq_false_of_ne (Ne.symm h10)
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases bb <;>
    simp [Sem.icmp, Sem.intcc, e1, e2, bne]

theorem ns_icmpBool {tms : Array Tm} {cc : IntCC} {ty : Ty} {u k : Nat} :
    NodeSound tms (.icmp cc ty u k) (icmpBool tms cc ty u k) := by
  intro x' h hord f fr mem t ht
  unfold icmpBool at h
  split at h
  · rename_i cc' cty a b kv hb hk
    obtain ⟨-, hu⟩ := boolAt_val (f := f) (fr := fr) (mem := mem) hb
    have hkv : (tmFrame f tms fr mem).regs k = some ⟨ty, kv⟩ := constAt_spec hk
    have hu' : (tmFrame f tms fr mem).regs u = _ := hu
    rw [evalNode_icmp, hu', hkv]
    split at h
    · rename_i hkeep
      cases h
      rw [tmVal_res ht hord]
      rcases hv : evalNode (tmFrame f tms fr mem) mem (.icmp cc' cty a b) with _ | v
      · rfl
      · obtain ⟨bb, rfl⟩ := evalNode_icmp_bool hv
        simp only [Option.map_some, Option.bind_some, truthy_bool8', Val.as?_mk]
        rw [icmp_bool_keep (Ty.width_pos ty) cc bb kv hkeep]
    · split at h
      · rename_i hflip
        cases h
        rw [tmVal_res ht hord, evalNode_icmp_inv]
        rcases hv : evalNode (tmFrame f tms fr mem) mem (.icmp cc' cty a b) with _ | v
        · rfl
        · obtain ⟨bb, rfl⟩ := evalNode_icmp_bool hv
          simp only [Option.map_some, Option.bind_some, truthy_bool8', Val.as?_mk]
          rw [icmp_bool_flip (Ty.width_pos ty) cc bb kv hflip]
      · cases h
  · cases h

/-! ## `icmpUnit` -/

theorem toNat_one_of_pos {w : Nat} (hw : 0 < w) : (1#w).toNat = 1 := by
  have h1 : 1 < 2 ^ w :=
    Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide) hw)
  simp [Nat.mod_eq_of_lt h1]

theorem ult_one {w : Nat} (hw : 0 < w) (x : BitVec w) : x.ult 1#w = (x == 0#w) := by
  rw [Bool.eq_iff_iff, BitVec.ult, decide_eq_true_eq, toNat_one_of_pos hw, beq_iff_eq,
    ← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.zero_mod]
  omega

theorem uge_one {w : Nat} (hw : 0 < w) (x : BitVec w) : (1#w).ule x = (x != 0#w) := by
  rw [Bool.eq_iff_iff, BitVec.ule, decide_eq_true_eq, toNat_one_of_pos hw, bne_iff_ne, ne_eq,
    ← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.zero_mod]
  omega

theorem ugt_zero {w : Nat} (x : BitVec w) : (0#w).ult x = (x != 0#w) := by
  rw [Bool.eq_iff_iff, BitVec.ult, decide_eq_true_eq, bne_iff_ne, ne_eq, ← BitVec.toNat_inj,
    BitVec.toNat_ofNat, Nat.zero_mod]
  omega

theorem ule_zero {w : Nat} (x : BitVec w) : x.ule 0#w = (x == 0#w) := by
  rw [Bool.eq_iff_iff, BitVec.ule, decide_eq_true_eq, beq_iff_eq, ← BitVec.toNat_inj,
    BitVec.toNat_ofNat, Nat.zero_mod]
  omega

theorem ns_icmpUnit {tms : Array Tm} {cc : IntCC} {ty : Ty} {x k : Nat} :
    NodeSound tms (.icmp cc ty x k) (icmpUnit tms cc ty x k) := by
  intro x' h hord f fr mem t ht
  unfold icmpUnit at h
  split at h
  · rename_i kv hk
    have hkv : (tmFrame f tms fr mem).regs k = some ⟨ty, kv⟩ := constAt_spec hk
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hc
      obtain ⟨rfl, hcc⟩ := hc
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨hz1, hz2⟩ := findTm_spec hz
      have hzv : (tmFrame f tms fr mem).regs z = some ⟨ty, 0⟩ := by
        show tmVal f tms fr mem z = _
        rw [tmVal_node hz1 hz2]; rfl
      rw [tmVal_res ht hord, evalNode_icmp, evalNode_icmp, hzv, hkv]
      rcases (tmFrame f tms fr mem).regs x |>.bind (·.as? ty) with _ | A
      · rfl
      · rcases hcc with rfl | rfl <;>
          simp [Sem.icmp, Sem.intcc, ult_one (Ty.width_pos ty), uge_one (Ty.width_pos ty)]
    · split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hc
        obtain ⟨rfl, hcc⟩ := hc
        cases h
        rw [tmVal_res ht hord, evalNode_icmp, evalNode_icmp, hkv]
        rcases (tmFrame f tms fr mem).regs x |>.bind (·.as? ty) with _ | A
        · rfl
        · rcases hcc with rfl | rfl <;> simp [Sem.icmp, Sem.intcc, ugt_zero, ule_zero]
      · cases h
  · cases h

/-! ## `subNeg`, `mulTwo`, `xorNot`, `bmaskBool` -/

theorem add_self_eq_mul_two {w : Nat} (A : BitVec w) : A + A = A * 2 ∧ A + A = 2 * A :=
  ⟨BitVec.mul_two.symm, by rw [BitVec.mul_comm]; exact BitVec.mul_two.symm⟩

theorem ns_subNeg {tms : Array Tm} {ty : Ty} {z x : Nat} :
    NodeSound tms (.binary .isub ty z x) (subNeg tms ty z x) := by
  intro x' h hord f fr mem t ht
  unfold subNeg at h
  split at h
  · rename_i zv hz
    split at h
    · rename_i h0
      simp only [beq_iff_eq] at h0
      subst h0
      cases h
      have hzv : (tmFrame f tms fr mem).regs z = some ⟨ty, 0⟩ := constAt_spec hz
      rw [tmVal_res ht hord, evalNode_unary, evalNode_binary_nonShift rfl, hzv]
      rcases (tmFrame f tms fr mem).regs x |>.bind (·.as? ty) with _ | A
      · simp
      · simp [Sem.binary, Sem.isub, Sem.unary, Sem.ineg]
    · cases h
  · cases h

theorem ns_mulTwo {tms : Array Tm} {ty : Ty} {x c : Nat} (swap : Bool) :
    NodeSound tms (if swap then .binary .imul ty c x else .binary .imul ty x c)
      (mulTwo tms ty x c) := by
  intro x' h hord f fr mem t ht
  unfold mulTwo at h
  split at h
  · rename_i cv hc
    split at h
    · rename_i h2
      simp only [beq_iff_eq] at h2
      subst h2
      cases h
      have hcv : (tmFrame f tms fr mem).regs c = some ⟨ty, 2⟩ := constAt_spec hc
      rw [tmVal_res ht hord, evalNode_binary_nonShift rfl]
      cases swap
      · simp only [Bool.false_eq_true, ite_false]
        rw [evalNode_binary_nonShift rfl, hcv]
        rcases (tmFrame f tms fr mem).regs x |>.bind (·.as? ty) with _ | A
        · rfl
        · simp only [Option.bind_some, Val.as?_mk, Option.map_some, Sem.binary, Sem.iadd,
            Sem.imul]
          rw [(add_self_eq_mul_two A).1]
      · simp only [ite_true]
        rw [evalNode_binary_nonShift rfl, hcv]
        rcases hA : (tmFrame f tms fr mem).regs x |>.bind (·.as? ty) with _ | A
        · simp [hA]
        · simp only [Option.bind_some, Val.as?_mk, Option.map_some, Sem.binary, Sem.iadd,
            Sem.imul, hA]
          rw [(add_self_eq_mul_two A).2]
    · cases h
  · cases h

theorem shl_one {w : Nat} (A : BitVec w) : A <<< 1 = A + A := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq, Nat.pow_one]
  congr 1
  omega

theorem ns_shlOne {tms : Array Tm} {ty : Ty} {x c : Nat} :
    NodeSound tms (.binary .ishl ty x c) (shlOne tms ty x c) := by
  intro x' h hord f fr mem t ht
  unfold shlOne at h
  split at h
  · rename_i K hK
    split at h
    · rename_i h1
      simp only [beq_iff_eq] at h1
      cases h
      have hKv : (tmFrame f tms fr mem).regs c = some K := tmVal_of_constOf hK
      rw [tmVal_res ht hord, evalNode_binary_nonShift rfl, evalNode_ishl hKv]
      rcases (tmFrame f tms fr mem).regs x |>.bind (·.as? ty) with _ | A
      · rfl
      · simp only [Option.bind_some, Option.map_some, Val.as?_mk, Sem.binary, Sem.iadd, Sem.ishl,
          Sem.shiftAmt, h1, shl_one]
    · cases h
  · cases h

theorem ns_xorNot {tms : Array Tm} {ty : Ty} {x m : Nat} (swap : Bool) :
    NodeSound tms (if swap then .binary .bxor ty m x else .binary .bxor ty x m)
      (xorNot tms ty x m) := by
  intro x' h hord f fr mem t ht
  unfold xorNot at h
  split at h
  · rename_i mv hm
    split at h
    · rename_i h1
      simp only [beq_iff_eq] at h1
      subst h1
      cases h
      have hmv : (tmFrame f tms fr mem).regs m = some ⟨ty, BitVec.allOnes ty.width⟩ :=
        constAt_spec hm
      rw [tmVal_res ht hord, evalNode_unary]
      cases swap
      · simp only [Bool.false_eq_true, ite_false]
        rw [evalNode_binary_nonShift rfl, hmv]
        rcases (tmFrame f tms fr mem).regs x |>.bind (·.as? ty) with _ | A
        · rfl
        · simp [Sem.binary, Sem.bxor, Sem.unary, Sem.bnot]
      · simp only [ite_true]
        rw [evalNode_binary_nonShift rfl, hmv]
        rcases hA : (tmFrame f tms fr mem).regs x |>.bind (·.as? ty) with _ | A
        · simp [hA]
        · simp [Sem.binary, Sem.bxor, Sem.unary, Sem.bnot, hA]
    · cases h
  · cases h

theorem ns_bmaskBool {tms : Array Tm} {ty : Ty} {c : Nat} :
    NodeSound tms (.bmask ty c) (bmaskBool tms ty c) := by
  intro x' h hord f fr mem t ht
  unfold bmaskBool at h
  split at h
  · rename_i cc cty a b hc
    split at h
    · rename_i h8
      simp only [beq_iff_eq] at h8
      subst h8
      cases h
      have hcv : (tmFrame f tms fr mem).regs c = evalNode (tmFrame f tms fr mem) mem
          (.icmp cc cty a b) := tmVal_node (nodeAt_spec hc).1 (nodeAt_spec hc).2
      rw [tmVal_res ht hord, evalNode_unary, evalNode_bmask, hcv]
      rcases hv : evalNode (tmFrame f tms fr mem) mem (.icmp cc cty a b) with _ | v
      · rfl
      · obtain ⟨bb, rfl⟩ := evalNode_icmp_bool hv
        cases bb <;> decide
    · cases h
  · cases h

/-! ## The rule set -/

theorem ruleSound_algStep2 : RuleSound algStep2 := by
  intro tms i x' h hord f fr mem t ht
  cases i with
  | icmp cc ty a b =>
    exact nodeSound_orElse ns_icmpSwap (nodeSound_orElse ns_icmpBool ns_icmpUnit)
      x' h hord f fr mem t ht
  | binary op ty x y =>
    cases op
    case isub => exact ns_subNeg x' h hord f fr mem t ht
    case imul =>
      exact nodeSound_orElse (ns_mulTwo (x := x) (c := y) false)
        (ns_mulTwo (x := y) (c := x) true) x' h hord f fr mem t ht
    case ishl => exact ns_shlOne x' h hord f fr mem t ht
    case bxor =>
      exact nodeSound_orElse (ns_xorNot (x := x) (m := y) false)
        (ns_xorNot (x := y) (m := x) true) x' h hord f fr mem t ht
    all_goals simp [algStep2] at h
  | bmask ty c => exact ns_bmaskBool x' h hord f fr mem t ht
  | _ => simp [algStep2] at h

/-- **The second set of algebraic rules is sound.** -/
theorem normSound_alg2 : NormSound Norm.alg2 :=
  normSound_guard ruleSound_algStep2

/-- **The validator's default normaliser is sound**: constant evaluation, then the algebraic
rules (`Norm.alg2`, then `Norm.alg`). -/
theorem normSound_std : NormSound Norm.std :=
  normSound_orElse normSound_evalConst (normSound_orElse normSound_alg2 normSound_alg)

end Opt.MidVal

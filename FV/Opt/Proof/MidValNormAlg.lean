import FV.Opt.Proof.MidValNormConst

/-!
# Single-node algebraic rules are a sound normaliser (#1119 stage 2, family 2)

`Opt.MidVal.Norm.alg` (`Norm.guard algStep`) rewrites a node into a node of the same value in
every frame, proved here directly against `Clif.evalInst` (Cranelift 0.135.0's rules are not the
proven 0.136.1 `simplify` rules of `FV/Opt`, whose obligation `SimplifySound` is a forward,
typed one; these hold with no typing premise at all):

* `selIcmp` — `select ty c 1 0` with `c` an `icmp` is `c` at `i8` and `uextend ty c` at a wider
  type; `select ty c 0 1` is the same of the inverted `icmp` (`intcc_inv`): the `icmp` is an `i8`
  `0`/`1` whenever it evaluates (`evalNode_icmp_bool`), and both sides read the same operands;
* `mulPow2` — `imul ty x 2^k = ishl ty x k` for `0 < k < width` (`BitVec.shiftLeft_eq_mul_twoPow`;
  the shift amount is `k mod width = k`), either operand order;
* `addStack` — `iadd ty (stack_addr ty slot off) c = stack_addr ty slot (off + c)` with `c` read
  as signed: `ofInt (base + off) + c = ofInt (base + off + c.toInt)` modulo `2^width`
  (`BitVec.ofInt_add`, `BitVec.ofInt_toInt`); a missing slot is `stuck` on both sides;
* `redExt` — `ireduce ty (extend op uty x)` with `x` a node of type `xt` (`nodeTy`, by
  `evalInst_types`), both narrower than `uty`: `x` if `xt = ty`, `extend op ty x` if narrower,
  `ireduce ty x` if wider (low bits of an extension, `setWidth_extOp`, `extOp_narrow`). An atom
  operand is never rewritten: its type is not in the table, and for an operand of another width
  the rewrite is false.

`RuleSound r` is `NormSound` for a rule whose result's operands are earlier than every occurrence
of it (`Norm.guard` checks that); `normSound_guard` turns one into the other. Main results:
**`normSound_alg : NormSound Norm.alg`**, `normSound_orElse`, **`normSound_std`** (the
validator's default normaliser).
-/

namespace Opt.MidVal

open Clif

/-! ## Reading the table -/

/-- `NormSound` for a rule whose result has its operands before each of its occurrences. -/
def RuleSound (r : Norm) : Prop :=
  ∀ (tms : Array Tm) (i : Inst) (x : Tm), r tms i = some x →
    (∀ t, tms[t]? = some x → ∀ o ∈ x.ops, o < t) →
    ∀ (f : Function) (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x →
      tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem i

theorem guard_spec {n : Norm} {tms : Array Tm} {i : Inst} {x : Tm}
    (h : Norm.guard n tms i = some x) :
    n tms i = some x ∧ ∀ t, tms[t]? = some x → ∀ o ∈ x.ops, o < t := by
  simp only [Norm.guard] at h
  cases hn : n tms i with
  | none => rw [hn] at h; cases h
  | some y =>
    rw [hn] at h
    simp only at h
    split at h
    · rename_i ho
      cases h
      refine ⟨rfl, fun t ht o hoo => ?_⟩
      have hlt : t < tms.size := by
        rcases Nat.lt_or_ge t tms.size with h1 | h1
        · exact h1
        · rw [Array.getElem?_eq_none h1] at ht; cases ht
      simp only [ordered, List.all_eq_true, List.mem_range] at ho
      have := ho t hlt
      simp only [ht, bne_self_eq_false, Bool.false_or, List.all_eq_true, decide_eq_true_eq] at this
      exact this o hoo
    · cases h

theorem normSound_guard {r : Norm} (h : RuleSound r) : NormSound (Norm.guard r) := by
  intro tms i x hx
  obtain ⟨hr, ho⟩ := guard_spec hx
  exact h tms i x hr ho

theorem normSound_orElse {a b : Norm} (ha : NormSound a) (hb : NormSound b) :
    NormSound (Norm.orElse a b) := by
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

theorem ruleSound_orElse {a b : Norm} (ha : RuleSound a) (hb : RuleSound b) :
    RuleSound (Norm.orElse a b) := by
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

theorem nodeAt_spec {tms : Array Tm} {c : Nat} {j : Inst} (h : nodeAt tms c = some j) :
    tms[c]? = some (.node j) ∧ ∀ o ∈ operands j, o < c := by
  unfold nodeAt at h
  split at h
  · rename_i j' hj
    split at h
    · rename_i ho
      cases h
      simp only [List.all_eq_true, decide_eq_true_eq] at ho
      exact ⟨hj, ho⟩
    · cases h
  · cases h

theorem findTm_spec {tms : Array Tm} {x : Tm} {a : Nat} (h : findTm tms x = some a) :
    tms[a]? = some x ∧ ∀ o ∈ x.ops, o < a := by
  unfold findTm at h
  cases hf : (List.range tms.size).find? (fun a => tms[a]? == some x) with
  | none => rw [hf] at h; cases h
  | some a' =>
    rw [hf] at h
    simp only [Option.bind_some] at h
    split at h
    · rename_i ho
      cases h
      have := List.find?_some hf
      simp only [beq_iff_eq] at this
      simp only [List.all_eq_true, decide_eq_true_eq] at ho
      exact ⟨this, ho⟩
    · cases h

/-- A node whose operands are earlier has, as term value, its value in the term frame. -/
theorem tmVal_node' {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {t : Nat}
    {j : Inst} (h : tms[t]? = some (.node j)) (ho : ∀ o ∈ (Tm.node j).ops, o < t) :
    tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem j :=
  tmVal_node h ho

theorem constAt_spec {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {ty : Ty}
    {o : Nat} {b : BitVec ty.width} (h : constAt tms ty o = some b) :
    tmVal f tms fr mem o = some ⟨ty, b⟩ := by
  unfold constAt at h
  cases hc : constOf tms o with
  | none => rw [hc] at h; cases h
  | some v =>
    rw [hc] at h
    obtain ⟨vt, vb⟩ := v
    simp only [Option.bind_some, Val.as?] at h
    split at h
    · rename_i he
      subst he
      cases h
      exact tmVal_of_constOf hc
    · cases h

/-! ## Values of the nodes involved -/

theorem evalNode_some_iff {F : Frame} {mem : Mem} {n : Inst} {v : Val} :
    evalNode F mem n = some v ↔ ∃ m', evalInst F mem n = .ok ([v], m') := by
  unfold evalNode
  split
  · rename_i r m' h
    rw [h]
    constructor
    · intro e; cases e; exact ⟨m', rfl⟩
    · rintro ⟨m'', e⟩; cases e; rfl
  · rename_i h
    constructor
    · intro e; cases e
    · rintro ⟨m', e⟩; exact absurd e (h v m')

theorem evalNode_iconst (F : Frame) (mem : Mem) (ty : Ty) (imm : BitVec ty.width) :
    evalNode F mem (.iconst ty imm) = some ⟨ty, imm⟩ := rfl

theorem evalNode_select {F : Frame} {mem : Mem} {ty : Ty} {c x y : ValueId}
    {vx vy : BitVec ty.width} (hx : F.regs x = some ⟨ty, vx⟩) (hy : F.regs y = some ⟨ty, vy⟩) :
    evalNode F mem (.select ty c x y) = (F.regs c).map fun cv => ⟨ty, Sem.select cv.bits vx vy⟩ := by
  rcases hc : F.regs c with _ | cv
  · simp [evalNode, evalInst, Frame.get, Res.ofOption, hc, bind, Res.bind]
  · simp [evalNode, evalInst, Frame.getAs, Frame.get, Res.ofOption, hc, hx, hy, bind, Res.bind, pure]

theorem evalNode_uextend {F : Frame} {mem : Mem} {ty : Ty} {n : ValueId} :
    evalNode F mem (.extend .uextend ty n) =
      (F.regs n).bind fun a => if a.ty.width < ty.width then some ⟨ty, Sem.uextend ty.width a.bits⟩
        else none := by
  rcases hn : F.regs n with _ | a
  · simp [evalNode, evalInst, Frame.get, Res.ofOption, hn, bind, Res.bind]
  · by_cases hw : a.ty.width < ty.width
    · simp [evalNode, evalInst, Frame.get, Res.ofOption, Res.check, hn, hw, bind, Res.bind, pure]
    · simp [evalNode, evalInst, Frame.get, Res.ofOption, Res.check, hn, hw, bind, Res.bind]

/-- An `icmp`: the `i8` `bool8` of the comparison of its operands at its type. -/
theorem evalNode_icmp {F : Frame} {mem : Mem} {cc : IntCC} {cty : Ty} {a b : ValueId} :
    evalNode F mem (.icmp cc cty a b) =
      ((F.regs a).bind (·.as? cty)).bind fun A =>
        ((F.regs b).bind (·.as? cty)).map fun B => ⟨.i8, Sem.icmp cc A B⟩ := by
  simp only [evalNode, evalInst, Frame.getAs, Frame.get]
  rcases ha : F.regs a with _ | va <;> rcases hb : F.regs b with _ | vb
  all_goals simp only [Res.ofOption, Option.bind_none, Option.bind_some, bind, Res.bind]
  all_goals try rfl
  all_goals
    rcases va.as? cty with _ | A <;> try rcases vb.as? cty with _ | B
  all_goals simp [Res.ofOption, Res.bind, pure]

theorem truthy_bool8 (b : Bool) : Sem.truthy (Sem.bool8 b) = b := by
  cases b <;> decide

theorem intcc_inv {w : Nat} (cc : IntCC) (x y : BitVec w) :
    Sem.intcc (IntCC.inv cc) x y = !Sem.intcc cc x y := by
  cases cc <;>
    simp [Sem.intcc, IntCC.inv, BitVec.slt, BitVec.sle, BitVec.ult, BitVec.ule, Int.not_lt,
      Nat.not_lt, bne] <;>
    simp only [← decide_not, Int.not_lt, Int.not_le, Nat.not_lt, Nat.not_le]

theorem truthy_bool8' (b : Bool) : Sem.truthy (w := Ty.i8.width) (Sem.bool8 b) = b :=
  truthy_bool8 b

/-- The inverted comparison of the same operands. -/
theorem evalNode_icmp_inv {F : Frame} {mem : Mem} {cc : IntCC} {cty : Ty} {a b : ValueId} :
    evalNode F mem (.icmp (IntCC.inv cc) cty a b) =
      (evalNode F mem (.icmp cc cty a b)).map fun v => ⟨.i8, Sem.bool8 (!Sem.truthy v.bits)⟩ := by
  rw [evalNode_icmp, evalNode_icmp]
  rcases (F.regs a).bind (·.as? cty) with _ | A
  · rfl
  · rcases (F.regs b).bind (·.as? cty) with _ | B
    · rfl
    · simp [Sem.icmp, truthy_bool8, truthy_bool8', intcc_inv]

/-- Whenever an `icmp` evaluates, it is an `i8` `0`/`1`. -/
theorem evalNode_icmp_bool {F : Frame} {mem : Mem} {cc : IntCC} {cty : Ty} {a b : ValueId}
    {v : Val} (h : evalNode F mem (.icmp cc cty a b) = some v) :
    ∃ bb, v = ⟨.i8, Sem.bool8 bb⟩ := by
  rw [evalNode_icmp] at h
  rcases ha : (F.regs a).bind (·.as? cty) with _ | A <;> rw [ha] at h
  · cases h
  · rcases hb : (F.regs b).bind (·.as? cty) with _ | B <;> rw [hb] at h
    · cases h
    · simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
      exact ⟨_, h.symm⟩

/-! ## `selIcmp` -/

theorem select_bool8 {w : Nat} (bb : Bool) (vx vy : BitVec w) :
    Sem.select (Sem.bool8 bb) vx vy = if bb then vx else vy := by
  simp [Sem.select, truthy_bool8]

theorem uextend_bool8 {w : Nat} (bb : Bool) (h : 8 < w) :
    Sem.uextend w (Sem.bool8 bb) = if bb then (1 : BitVec w) else 0 := by
  apply BitVec.eq_of_toNat_eq
  have h1 : 1 < 2 ^ w :=
    Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega))
  cases bb <;> simp [Sem.uextend, Sem.bool8, BitVec.toNat_setWidth, Nat.mod_eq_of_lt h1]

theorem uextend_bool8' {w : Nat} (bb : Bool) (h : 8 < w) :
    Sem.uextend (w := Ty.i8.width) w (Sem.bool8 bb) = if bb then (1 : BitVec w) else 0 :=
  uextend_bool8 bb h

theorem select_bool8' {w : Nat} (bb : Bool) (vx vy : BitVec w) :
    Sem.select (v := Ty.i8.width) (Sem.bool8 bb) vx vy = if bb then vx else vy :=
  select_bool8 bb vx vy

/-- The value a `select ty c vx vy` takes when `c` is the comparison value `V`. -/
theorem selPick_spec {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {c : Nat}
    {cc : IntCC} {cty : Ty} {a b : Nat} {ty : Ty} {vx vy : BitVec ty.width} {n : Nat}
    (hc : tms[c]? = some (.node (.icmp cc cty a b))) (hco : ∀ o ∈ operands (.icmp cc cty a b), o < c)
    (h : selPick tms c cc cty a b vx vy = some n) :
    ∃ J, tms[n]? = some (.node J) ∧ (∀ o ∈ operands J, o < n) ∧
      ((vx = 1 ∧ vy = 0 ∧ evalNode (tmFrame f tms fr mem) mem J =
          evalNode (tmFrame f tms fr mem) mem (.icmp cc cty a b)) ∨
       (vx = 0 ∧ vy = 1 ∧ evalNode (tmFrame f tms fr mem) mem J =
          (evalNode (tmFrame f tms fr mem) mem (.icmp cc cty a b)).map fun v =>
            ⟨.i8, Sem.bool8 (!Sem.truthy v.bits)⟩)) := by
  unfold selPick at h
  by_cases h10 : (vx == 1 && vy == 0) = true
  · rw [if_pos h10] at h
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at h10
    exact ⟨_, hc, hco, .inl ⟨h10.1, h10.2, rfl⟩⟩
  · rw [if_neg h10] at h
    by_cases h01 : (vx == 0 && vy == 1) = true
    · rw [if_pos h01] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h01
      obtain ⟨hn1, hn2⟩ := findTm_spec h
      exact ⟨_, hn1, hn2, .inr ⟨h01.1, h01.2, evalNode_icmp_inv⟩⟩
    · rw [if_neg h01] at h
      cases h

theorem ruleSound_selIcmp {ty : Ty} {c x y : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), selIcmp tms ty c x y = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (f : Function) (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.select ty c x y) := by
  intro tms x' h hord f fr mem t ht
  unfold selIcmp at h
  split at h
  · rename_i cc cty a b hj
    split at h
    · rename_i vx vy hvx hvy
      obtain ⟨n, hn, hw⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨hc1, hc2⟩ := nodeAt_spec hj
      obtain ⟨J, hnJ, hJo, hJ⟩ := selPick_spec (f := f) (fr := fr) (mem := mem) hc1 hc2 hn
      have hc : tmVal f tms fr mem c = evalNode (tmFrame f tms fr mem) mem (.icmp cc cty a b) :=
        tmVal_node hc1 hc2
      have hx : (tmFrame f tms fr mem).regs x = some ⟨ty, vx⟩ := constAt_spec hvx
      have hy : (tmFrame f tms fr mem).regs y = some ⟨ty, vy⟩ := constAt_spec hvy
      have hn' : tmVal f tms fr mem n = evalNode (tmFrame f tms fr mem) mem J := tmVal_node hnJ hJo
      rw [evalNode_select hx hy]
      show _ = (tmVal f tms fr mem c).map _
      rw [hc]
      unfold selWrap at hw
      by_cases h8 : (ty == .i8) = true
      · rw [if_pos h8] at hw
        simp only [beq_iff_eq] at h8
        subst h8
        rw [hnJ] at hw
        cases hw
        rw [tmVal_node ht (hord t ht)]
        rcases hv : evalNode (tmFrame f tms fr mem) mem (.icmp cc cty a b) with _ | v
        · rcases hJ with ⟨-, -, hJ⟩ | ⟨-, -, hJ⟩ <;> rw [hJ, hv] <;> rfl
        · obtain ⟨bb, rfl⟩ := evalNode_icmp_bool hv
          rcases hJ with ⟨rfl, rfl, hJ⟩ | ⟨rfl, rfl, hJ⟩ <;> rw [hJ, hv] <;> cases bb <;> decide
      · rw [if_neg h8] at hw
        split at hw
        · rename_i hw8
          cases hw
          rw [tmVal_node ht (hord t ht), evalNode_uextend]
          show (tmVal f tms fr mem n).bind _ = _
          rw [hn']
          rcases hv : evalNode (tmFrame f tms fr mem) mem (.icmp cc cty a b) with _ | v
          · rcases hJ with ⟨-, -, hJ⟩ | ⟨-, -, hJ⟩ <;> rw [hJ, hv] <;> rfl
          · obtain ⟨bb, rfl⟩ := evalNode_icmp_bool hv
            have h8w : (Ty.i8).width < ty.width := hw8
            rcases hJ with ⟨rfl, rfl, hJ⟩ | ⟨rfl, rfl, hJ⟩ <;> rw [hJ, hv] <;>
              simp only [Option.map_some, Option.bind_some, h8w, ite_true, truthy_bool8,
                truthy_bool8', select_bool8, select_bool8', uextend_bool8 _ hw8,
                uextend_bool8' _ hw8] <;> cases bb <;> simp
        · cases hw
    · cases h
  · cases h

/-! ## `mulPow2` -/

theorem evalNode_binary_nonShift {F : Frame} {mem : Mem} {op : BinaryOp} {ty : Ty} {x y : ValueId}
    (hop : op.isShift = false) :
    evalNode F mem (.binary op ty x y) =
      ((F.regs x).bind (·.as? ty)).bind fun A =>
        ((F.regs y).bind (·.as? ty)).map fun B => ⟨ty, Sem.binary op A B⟩ := by
  simp only [evalNode, evalInst, Frame.getAs, Frame.get, hop, Bool.false_eq_true, ite_false]
  rcases ha : F.regs x with _ | va <;> rcases hb : F.regs y with _ | vb
  all_goals simp only [Res.ofOption, Option.bind_none, Option.bind_some, bind, Res.bind]
  all_goals try rfl
  all_goals
    rcases va.as? ty with _ | A <;> try rcases vb.as? ty with _ | B
  all_goals simp [Res.ofOption, Res.bind, pure]

theorem evalNode_ishl {F : Frame} {mem : Mem} {ty : Ty} {x kc : ValueId} {K : Val}
    (hk : F.regs kc = some K) :
    evalNode F mem (.binary .ishl ty x kc) =
      ((F.regs x).bind (·.as? ty)).map fun A => ⟨ty, Sem.ishl A K.bits⟩ := by
  simp only [evalNode, evalInst, Frame.getAs, Frame.get, BinaryOp.isShift, ite_true, hk]
  rcases ha : F.regs x with _ | va
  · simp [Res.ofOption, bind, Res.bind]
  · cases hA : va.as? ty <;> simp [Res.ofOption, Res.bind, bind, pure, Sem.shift, hA]

theorem mul_pow2 {w k : Nat} (A B : BitVec w) (hB : 2 ^ k = B.toNat) (hk : k < w) :
    Sem.binary .imul A B = Sem.ishl A (BitVec.ofNat w k) ∧
      Sem.binary .imul B A = Sem.ishl A (BitVec.ofNat w k) := by
  have hkw : k % 2 ^ w = k := Nat.mod_eq_of_lt (Nat.lt_trans hk Nat.lt_two_pow_self)
  have hBt : B = BitVec.twoPow w k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_twoPow, hB, Nat.mod_eq_of_lt B.isLt]
  have hsh : Sem.ishl A (BitVec.ofNat w k) = A * B := by
    simp only [Sem.ishl, Sem.shiftAmt, BitVec.toNat_ofNat, hkw, Nat.mod_eq_of_lt hk]
    rw [BitVec.shiftLeft_eq_mul_twoPow, hBt]
  refine ⟨?_, ?_⟩
  · rw [hsh]; rfl
  · rw [hsh]; exact BitVec.mul_comm B A

theorem pow2Log_spec {v k : Nat} (h : pow2Log v = some k) : 2 ^ k = v := by
  unfold pow2Log at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    exact hc.2
  · cases h

theorem ruleSound_mulPow2 {ty : Ty} {x c : Nat} (swap : Bool) :
    ∀ (tms : Array Tm) (x' : Tm), mulPow2 tms ty x c = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (f : Function) (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem
          (if swap then .binary .imul ty c x else .binary .imul ty x c) := by
  intro tms x' h hord f fr mem t ht
  unfold mulPow2 at h
  split at h
  · rename_i B hb
    split at h
    · rename_i k hk
      split at h
      · rename_i hkw
        obtain ⟨kc, hkc, rfl⟩ := Option.map_eq_some_iff.1 h
        have hcv : (tmFrame f tms fr mem).regs c = some ⟨ty, B⟩ := constAt_spec hb
        obtain ⟨hk1, hk2⟩ := findTm_spec hkc
        have hK : (tmFrame f tms fr mem).regs kc = some ⟨ty, BitVec.ofNat ty.width k⟩ := by
          show tmVal f tms fr mem kc = _
          rw [tmVal_node hk1 hk2]; rfl
        rw [tmVal_node ht (hord t ht), evalNode_ishl hK]
        have e := fun A => mul_pow2 A B (pow2Log_spec hk) hkw
        cases swap
        · simp only [Bool.false_eq_true, ite_false]
          rw [evalNode_binary_nonShift rfl, hcv]
          rcases ((tmFrame f tms fr mem).regs x).bind (·.as? ty) with _ | A
          · rfl
          · simp [(e A).1]
        · simp only [ite_true]
          rw [evalNode_binary_nonShift rfl, hcv]
          simp only [Option.bind_some, Val.as?_mk]
          rcases ((tmFrame f tms fr mem).regs x).bind (·.as? ty) with _ | A
          · rfl
          · simp [(e A).2]
      · cases h
    · cases h
  · cases h

/-! ## `addStack` -/

theorem evalNode_stackAddr {F : Frame} {mem : Mem} {ty : Ty} {slot : SlotId} {off : Int} :
    evalNode F mem (.stackAddr ty slot off) =
      (F.slots.lookup slot).map fun base => Val.ofInt ty (base + off) := by
  rcases hs : F.slots.lookup slot with _ | base <;>
    simp [evalNode, evalInst, Res.ofOption, hs, bind, Res.bind, pure]

theorem add_stack_eq {w : Nat} (X off : Int) (B : BitVec w) :
    BitVec.ofInt w (X + off) + B = BitVec.ofInt w (X + (off + B.toInt)) ∧
      B + BitVec.ofInt w (X + off) = BitVec.ofInt w (X + (off + B.toInt)) := by
  have h : BitVec.ofInt w (X + off) + B = BitVec.ofInt w (X + (off + B.toInt)) := by
    rw [← Int.add_assoc, BitVec.ofInt_add (X + off), BitVec.ofInt_toInt]
  exact ⟨h, by rw [BitVec.add_comm]; exact h⟩

theorem ruleSound_addStack {ty : Ty} {s c : Nat} (swap : Bool) :
    ∀ (tms : Array Tm) (x' : Tm), addStack tms ty s c = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (f : Function) (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem
          (if swap then .binary .iadd ty c s else .binary .iadd ty s c) := by
  intro tms x' h hord f fr mem t ht
  unfold addStack at h
  split at h
  · rename_i ty' slot off B hj hb
    split at h
    · rename_i hty
      simp only [beq_iff_eq] at hty
      subst hty
      cases h
      have hcv : (tmFrame f tms fr mem).regs c = some ⟨ty', B⟩ := constAt_spec hb
      have hsv : (tmFrame f tms fr mem).regs s =
          ((tmFrame f tms fr mem).slots.lookup slot).map fun base => Val.ofInt ty' (base + off) := by
        show tmVal f tms fr mem s = _
        rw [tmVal_node (nodeAt_spec hj).1 (nodeAt_spec hj).2, evalNode_stackAddr]
      rw [tmVal_node ht (hord t ht), evalNode_stackAddr]
      have e := fun X => add_stack_eq (w := ty'.width) X off B
      cases swap
      · simp only [Bool.false_eq_true, ite_false]
        rw [evalNode_binary_nonShift rfl, hsv, hcv]
        rcases (tmFrame f tms fr mem).slots.lookup slot with _ | base
        · rfl
        · simp [Val.ofInt, Sem.binary, Sem.iadd, (e _).1]
      · simp only [ite_true]
        rw [evalNode_binary_nonShift rfl, hsv, hcv]
        rcases (tmFrame f tms fr mem).slots.lookup slot with _ | base
        · simp
        · simp [Val.ofInt, Sem.binary, Sem.iadd, (e _).2]
    · cases h
  · cases h

/-! ## `redExt` -/

/-- The extension `op` to width `v`. -/
def extOp {w : Nat} : ExtendOp → (v : Nat) → BitVec w → BitVec v
  | .uextend, v, x => Sem.uextend v x
  | .sextend, v, x => Sem.sextend v x

theorem evalNode_extend {F : Frame} {mem : Mem} {op : ExtendOp} {ty : Ty} {n : ValueId} :
    evalNode F mem (.extend op ty n) =
      (F.regs n).bind fun a => if a.ty.width < ty.width then some ⟨ty, extOp op ty.width a.bits⟩
        else none := by
  rcases hn : F.regs n with _ | a
  · simp [evalNode, evalInst, Frame.get, Res.ofOption, hn, bind, Res.bind]
  · by_cases hw : a.ty.width < ty.width <;> cases op <;>
      simp [evalNode, evalInst, Frame.get, Res.ofOption, Res.check, hn, hw, bind, Res.bind, pure,
        extOp]

theorem evalNode_ireduce {F : Frame} {mem : Mem} {ty : Ty} {n : ValueId} :
    evalNode F mem (.ireduce ty n) =
      (F.regs n).bind fun a => if ty.width < a.ty.width then
        some ⟨ty, BitVec.setWidth ty.width a.bits⟩ else none := by
  rcases hn : F.regs n with _ | a
  · simp [evalNode, evalInst, Frame.get, Res.ofOption, hn, bind, Res.bind]
  · by_cases hw : ty.width < a.ty.width <;>
      simp [evalNode, evalInst, Frame.get, Res.ofOption, Res.check, hn, hw, bind, Res.bind, pure,
        Sem.ireduce]

/-- A node with a `nodeTy` evaluates to a value of that type. -/
theorem evalNode_ty_of_nodeTy {F : Frame} {mem : Mem} {j : Inst} {xt : Ty} {v : Val}
    (hj : nodeTy j = some xt) (h : evalNode F mem j = some v) : v.ty = xt := by
  obtain ⟨m', he⟩ := evalNode_some_iff.1 h
  have hr : j.resultTypes (fun _ => none) (fun _ => none) = some [xt] := by
    cases j <;> simp_all [nodeTy, Inst.resultTypes]
  simpa using evalInst_types he hr

theorem setWidth_extOp {w m W : Nat} (op : ExtendOp) (x : BitVec w) (hm : m ≤ W) :
    BitVec.setWidth m (extOp op W x) = extOp op m x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hiW : i < W := by omega
  cases op <;>
    simp [extOp, Sem.uextend, Sem.sextend, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend,
      BitVec.getElem_signExtend, BitVec.zeroExtend_eq_setWidth, hi, hiW]

theorem extOp_narrow {w m : Nat} (op : ExtendOp) (x : BitVec w) (hm : m ≤ w) :
    extOp op m x = BitVec.setWidth m x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hiw : i < w := by omega
  cases op <;>
    simp [extOp, Sem.uextend, Sem.sextend, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend,
      BitVec.getElem_signExtend, BitVec.zeroExtend_eq_setWidth, hi, hiw]

theorem extOp_same {w : Nat} (op : ExtendOp) (x : BitVec w) : extOp op w x = x := by
  cases op
  · simp [extOp, Sem.uextend, BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_eq]
  · simp [extOp, Sem.sextend, BitVec.signExtend_eq]

theorem ruleSound_redExt {ty : Ty} {u : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), redExt tms ty u = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (f : Function) (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.ireduce ty u) := by
  intro tms x' h hord f fr mem t ht
  unfold redExt at h
  split at h
  · rename_i op uty x hu
    split at h
    · rename_i j hx
      split at h
      · rename_i xt hxt
        split at h
        · rename_i hw
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
          have hu' : (tmFrame f tms fr mem).regs u =
              evalNode (tmFrame f tms fr mem) mem (.extend op uty x) := by
            show tmVal f tms fr mem u = _
            exact tmVal_node (nodeAt_spec hu).1 (nodeAt_spec hu).2
          have hx' : (tmFrame f tms fr mem).regs x = evalNode (tmFrame f tms fr mem) mem j := by
            show tmVal f tms fr mem x = _
            exact tmVal_node (nodeAt_spec hx).1 (nodeAt_spec hx).2
          rw [evalNode_ireduce, hu', evalNode_extend, hx']
          rcases hv : evalNode (tmFrame f tms fr mem) mem j with _ | v
          · -- `x` does not evaluate: neither side does
            split at h
            · cases h; rw [tmVal_node ht (hord t ht), hv]; rfl
            · split at h
              · cases h; rw [tmVal_node ht (hord t ht), evalNode_extend, hx', hv]; rfl
              · split at h
                · cases h; rw [tmVal_node ht (hord t ht), evalNode_ireduce, hx', hv]; rfl
                · cases h
          · have hvt := evalNode_ty_of_nodeTy hxt hv
            obtain ⟨vt, vb⟩ := v
            simp only at hvt
            subst hvt
            simp only [Option.bind_some, hw.1, hw.2, ite_true]
            split at h
            · rename_i he
              simp only [beq_iff_eq] at he
              subst he
              cases h
              rw [tmVal_node ht (hord t ht), hv, setWidth_extOp op vb (Nat.le_of_lt hw.2),
                extOp_same]
            · split at h
              · rename_i hlt
                cases h
                rw [tmVal_node ht (hord t ht), evalNode_extend, hx', hv]
                simp only [Option.bind_some, hlt, ite_true,
                  setWidth_extOp op vb (Nat.le_of_lt hw.2)]
              · split at h
                · rename_i hgt
                  cases h
                  rw [tmVal_node ht (hord t ht), evalNode_ireduce, hx', hv]
                  simp only [Option.bind_some, hgt, ite_true,
                    setWidth_extOp op vb (Nat.le_of_lt hw.2), extOp_narrow op vb (Nat.le_of_lt hgt)]
                · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-! ## The rule set -/

theorem ruleSound_algStep : RuleSound algStep := by
  intro tms i x' h hord f fr mem t ht
  cases i with
  | select ty c x y => exact ruleSound_selIcmp tms x' h hord f fr mem t ht
  | binary op ty x y =>
    cases op
    case imul =>
      simp only [algStep] at h
      cases h1 : mulPow2 tms ty x y with
      | some z =>
        rw [h1] at h
        cases h
        exact ruleSound_mulPow2 (x := x) (c := y) false tms _ h1 hord f fr mem t ht
      | none =>
        rw [h1] at h
        exact ruleSound_mulPow2 (x := y) (c := x) true tms x' h hord f fr mem t ht
    case iadd =>
      simp only [algStep] at h
      cases h1 : addStack tms ty x y with
      | some z =>
        rw [h1] at h
        cases h
        exact ruleSound_addStack (s := x) (c := y) false tms _ h1 hord f fr mem t ht
      | none =>
        rw [h1] at h
        exact ruleSound_addStack (s := y) (c := x) true tms x' h hord f fr mem t ht
    all_goals simp [algStep] at h
  | ireduce ty u => exact ruleSound_redExt tms x' h hord f fr mem t ht
  | _ => simp [algStep] at h

/-- **The algebraic rules are sound.** -/
theorem normSound_alg : NormSound Norm.alg :=
  normSound_guard ruleSound_algStep

/-- **The validator's default normaliser is sound**: constant evaluation, then the algebraic
rules. -/
theorem normSound_std : NormSound Norm.std :=
  normSound_orElse normSound_evalConst normSound_alg

end Opt.MidVal

import FV.Opt.Proof.MidValNormFam6
import FV.Opt.Proof.RuleNode

/-!
# Family 7: operand-dropping rewrites, sound where the operands have values (#1119, agent MidendNext7)

`Norm.stdD f = Norm.orElse (Norm.stdT f) (Norm.guard (dropStep (atomTy f)))`
(`FV/Opt/MidVal.lean`), the validator's default normaliser. Each rule of `dropStep` drops an
operand of the node, so it is false as a `NormSoundT` rule: in a frame where the dropped operand
has no value the node has none and the result has one. Its obligation is `NormSoundD f`
(`FV/Opt/Proof/MidValTerm.lean`): the node's value in the frames where the atoms below it are
typed and its operands have values, which is where the simulation evaluates a node
(`FV/Opt/Proof/MidValFStep.lean`, `FV/Opt/Proof/MidValPrefix.lean`). Proved against
`Clif.evalInst`:

* `subAdd` — `isub ty (iadd ty x y) x` is `y` and `isub ty (iadd ty x y) y` is `x`: the operand
  `iadd ty x y` has a value only when `x` and `y` hold values of type `ty`, and then the node is
  `(x + y) - x = y` (`(x + y) - y = x`) modulo `2^width`; no typing;
* `addSub` — `iadd ty (isub ty x y) y` and `iadd ty y (isub ty x y)` are `x` (the same, `x - y + y
  = x`); no typing;
* `absTyped` (typed) — `op ty x k` and `op ty k x` with `k` an absorbing constant of type `ty`
  (`x * 0`, `x & 0`, `x | -1`, `rAbsorb_spec`) and `x` of static type `ty` (`tyAt`) are `k`: `x`
  has a value (the operands do), of type `ty` (`tyAt_val`);
* `selfCmp` (typed; #1119 family A, agent StoreFold1) — `icmp cc ty x x` with `x` of static type
  `ty` is the `i8` constant `intcc cc X X` gives (`intcc_self`: 1 for `eq`, `uge`, `ule`, `sge`,
  `sle`, 0 for the others), dropping the operand `x`.

Main results: `ruleSoundD_dropStep`, **`normSoundD_stdD : NormSoundD f (Norm.stdD f)`**.
-/

namespace Opt.MidVal

open Clif

/-! ## Combinators -/

/-- `NormSoundD` for a rule whose result has its operands before each of its occurrences. -/
def RuleSoundD (f : Function) (r : Norm) : Prop :=
  ∀ (tms : Array Tm) (i : Inst) (x : Tm), r tms i = some x →
    (∀ t, tms[t]? = some x → ∀ o ∈ x.ops, o < t) →
    ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x → AtomsTyped f tms fr mem i →
      (∀ o ∈ operands i, (tmVal f tms fr mem o).isSome) →
      tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem i

theorem normSoundD_guard {f : Function} {r : Norm} (h : RuleSoundD f r) :
    NormSoundD f (Norm.guard r) := by
  intro tms i x hx
  obtain ⟨hr, ho⟩ := guard_spec hx
  exact h tms i x hr ho

theorem normSoundD_orElse {f : Function} {a b : Norm} (ha : NormSoundD f a)
    (hb : NormSoundD f b) : NormSoundD f (Norm.orElse a b) := by
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

/-! ## Values of binary nodes -/

/-- A binary non-shift node whose operands hold values of its type. -/
theorem evalNode_bin_of {F : Frame} {mem : Mem} {op : BinaryOp} {ty : Ty} {x y : ValueId}
    {X Y : BitVec ty.width} (hop : op.isShift = false) (hx : F.regs x = some ⟨ty, X⟩)
    (hy : F.regs y = some ⟨ty, Y⟩) :
    evalNode F mem (.binary op ty x y) = some ⟨ty, Sem.binary op X Y⟩ :=
  (Opt.Proof.evalNode_binary F mem hop).2 ⟨X, Y, hx, hy, rfl⟩

/-- A term that is a binary non-shift node with a value: its operands hold values of its type. -/
theorem tmVal_bin_ops {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {a : Nat}
    {op : BinaryOp} {ty : Ty} {x y : Nat} (hop : op.isShift = false)
    (hA : nodeAt tms a = some (.binary op ty x y)) (hd : (tmVal f tms fr mem a).isSome) :
    ∃ X Y : BitVec ty.width, tmVal f tms fr mem x = some ⟨ty, X⟩ ∧
      tmVal f tms fr mem y = some ⟨ty, Y⟩ ∧
      tmVal f tms fr mem a = some ⟨ty, Sem.binary op X Y⟩ := by
  obtain ⟨hta, hoa⟩ := nodeAt_spec hA
  obtain ⟨va, hva⟩ := Option.isSome_iff_exists.1 hd
  have hv := hva
  rw [tmVal_node hta hoa] at hv
  obtain ⟨X, Y, hX, hY, rfl⟩ := (Opt.Proof.evalNode_binary _ mem hop).1 hv
  exact ⟨X, Y, hX, hY, hva⟩

/-! ## `subAdd`, `addSub` -/

theorem add_sub_left {w : Nat} (X Y : BitVec w) :
    Sem.binary .isub (Sem.binary .iadd X Y) X = Y := by
  simp only [Sem.binary, Sem.iadd, Sem.isub]
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem add_sub_right {w : Nat} (X Y : BitVec w) :
    Sem.binary .isub (Sem.binary .iadd X Y) Y = X := by
  simp only [Sem.binary, Sem.iadd, Sem.isub]
  exact BitVec.add_sub_cancel _ _

theorem sub_add_right {w : Nat} (X Y : BitVec w) :
    Sem.binary .iadd (Sem.binary .isub X Y) Y = X := by
  simp only [Sem.binary, Sem.iadd, Sem.isub]
  exact BitVec.sub_add_cancel _ _

theorem sub_add_left {w : Nat} (X Y : BitVec w) :
    Sem.binary .iadd Y (Sem.binary .isub X Y) = X := by
  simp only [Sem.binary, Sem.iadd, Sem.isub]
  rw [BitVec.add_comm]
  exact BitVec.sub_add_cancel _ _

theorem subAdd_spec {tms : Array Tm} {ty : Ty} {a z : Nat} {x' : Tm}
    (h : subAdd tms ty a z = some x') :
    ∃ x y, nodeAt tms a = some (.binary .iadd ty x y) ∧
      ((z = x ∧ tms[y]? = some x') ∨ (z = y ∧ tms[x]? = some x')) := by
  unfold subAdd at h
  split at h
  · rename_i ty' x y hA
    split at h
    · rename_i hty
      have hty' : ty' = ty := by simpa using hty
      subst hty'
      refine ⟨x, y, hA, ?_⟩
      split at h
      · rename_i hzx
        exact .inl ⟨by simpa using hzx, h⟩
      · split at h
        · rename_i hzy
          exact .inr ⟨by simpa using hzy, h⟩
        · cases h
    · cases h
  · cases h

theorem addSubPick_spec {tms : Array Tm} {ty : Ty} {a b : Nat} {x' : Tm}
    (h : addSubPick tms ty a b = some x') :
    ∃ x, nodeAt tms a = some (.binary .isub ty x b) ∧ tms[x]? = some x' := by
  unfold addSubPick at h
  split at h
  · rename_i ty' x y hA
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨x, hA, h⟩
    · cases h
  · cases h

theorem ruleSoundD_subAdd {f : Function} {ty : Ty} {a z : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), subAdd tms ty a z = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        (∀ o ∈ operands (.binary .isub ty a z), (tmVal f tms fr mem o).isSome) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.binary .isub ty a z) := by
  intro tms x' h hord fr mem t ht hd
  obtain ⟨x, y, hA, hc⟩ := subAdd_spec h
  obtain ⟨X, Y, hX, hY, ha⟩ :=
    tmVal_bin_ops (f := f) (fr := fr) (mem := mem) rfl hA (hd a (by simp [operands]))
  rcases hc with ⟨rfl, hy⟩ | ⟨rfl, hx⟩
  · rw [tmVal_same ht hy (hord t ht) (hord y hy), evalNode_bin_of rfl ha hX, add_sub_left]
    exact hY
  · rw [tmVal_same ht hx (hord t ht) (hord x hx), evalNode_bin_of rfl ha hY, add_sub_right]
    exact hX

theorem ruleSoundD_addSub {f : Function} {ty : Ty} {a b : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), addSub tms ty a b = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        (∀ o ∈ operands (.binary .iadd ty a b), (tmVal f tms fr mem o).isSome) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.binary .iadd ty a b) := by
  intro tms x' h hord fr mem t ht hd
  unfold addSub at h
  cases h1 : addSubPick tms ty a b with
  | some y =>
    rw [h1] at h
    cases h
    obtain ⟨x, hA, hx⟩ := addSubPick_spec h1
    obtain ⟨X, Y, hX, hY, ha⟩ :=
      tmVal_bin_ops (f := f) (fr := fr) (mem := mem) rfl hA (hd a (by simp [operands]))
    rw [tmVal_same ht hx (hord t ht) (hord x hx), evalNode_bin_of rfl ha hY, sub_add_right]
    exact hX
  | none =>
    rw [h1] at h
    simp only [Option.orElse_none] at h
    obtain ⟨x, hB, hx⟩ := addSubPick_spec h
    obtain ⟨X, Y, hX, hY, hb⟩ :=
      tmVal_bin_ops (f := f) (fr := fr) (mem := mem) rfl hB (hd b (by simp [operands]))
    rw [tmVal_same ht hx (hord t ht) (hord x hx), evalNode_bin_of rfl hY hb, sub_add_left]
    exact hX

/-! ## `absTyped` -/

theorem rAbsorb_spec {w : Nat} {op : BinaryOp} {k : BitVec w} (h : rAbsorb op k = true)
    (x : BitVec w) : Sem.binary op x k = k := by
  cases op <;> simp only [rAbsorb, beq_iff_eq, Bool.false_eq_true] at h <;> subst h <;>
    simp [Sem.binary, Sem.imul, Sem.band, Sem.bor]

theorem rAbsorb_comm {w : Nat} {op : BinaryOp} {k : BitVec w} (h : rAbsorb op k = true) :
    commOp op = true := by
  cases op <;> simp_all [rAbsorb, commOp]

theorem rAbsorb_nonShift {w : Nat} {op : BinaryOp} {k : BitVec w} (h : rAbsorb op k = true) :
    op.isShift = false := by
  cases op <;> simp_all [rAbsorb, BinaryOp.isShift]

theorem absPick_spec {aty : Tm → Option Ty} {tms : Array Tm} {op : BinaryOp} {ty : Ty}
    {x k : Nat} {x' : Tm} (h : absPick aty tms op ty x k = some x') :
    ∃ kv, constAt tms ty k = some kv ∧ rAbsorb op kv = true ∧ tyAt aty tms x = some ty ∧
      tms[k]? = some x' := by
  unfold absPick at h
  split at h
  · rename_i kv hkv
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨kv, hkv, hc.1, hc.2, h⟩
    · cases h
  · cases h

theorem ruleSoundD_absTyped {f : Function} {op : BinaryOp} {ty : Ty} {a b : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), absTyped (atomTy f) tms op ty a b = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        AtomsTyped f tms fr mem (.binary op ty a b) →
        (∀ o ∈ operands (.binary op ty a b), (tmVal f tms fr mem o).isSome) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.binary op ty a b) := by
  intro tms x' h hord fr mem t ht hA hd
  -- the typed operand `x` has a value of type `ty`
  have hval : ∀ x, x ∈ operands (.binary op ty a b) → tyAt (atomTy f) tms x = some ty →
      ∃ X : BitVec ty.width, tmVal f tms fr mem x = some ⟨ty, X⟩ := by
    intro x hxo htx
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hd x hxo)
    have hvt : v.ty = ty := tyAt_val hA (.op hxo) htx hv
    obtain ⟨vt, vb⟩ := v
    simp only at hvt
    subst hvt
    exact ⟨vb, hv⟩
  unfold absTyped at h
  cases h1 : absPick (atomTy f) tms op ty a b with
  | some y =>
    rw [h1] at h
    cases h
    obtain ⟨kv, hkv, hn, htx, hk⟩ := absPick_spec h1
    obtain ⟨X, hX⟩ := hval a (by simp [operands]) htx
    have hK : tmVal f tms fr mem b = some ⟨ty, kv⟩ := constAt_spec hkv
    rw [tmVal_same ht hk (hord t ht) (hord b hk), evalNode_bin_of (rAbsorb_nonShift hn) hX hK,
      rAbsorb_spec hn]
    exact hK
  | none =>
    rw [h1] at h
    simp only [Option.orElse_none] at h
    obtain ⟨kv, hkv, hn, htx, hk⟩ := absPick_spec h
    obtain ⟨X, hX⟩ := hval b (by simp [operands]) htx
    have hK : tmVal f tms fr mem a = some ⟨ty, kv⟩ := constAt_spec hkv
    rw [tmVal_same ht hk (hord t ht) (hord a hk), evalNode_bin_of (rAbsorb_nonShift hn) hK hX,
      commOp_spec (rAbsorb_comm hn), rAbsorb_spec hn]
    exact hK

/-! ## `selfCmp` -/

/-- A comparison of a value with itself. -/
theorem intcc_self {w : Nat} (cc : IntCC) (x : BitVec w) :
    Sem.intcc cc x x = (cc == .eq || cc == .uge || cc == .ule || cc == .sge || cc == .sle) := by
  cases cc <;> simp [Sem.intcc, BitVec.slt, BitVec.sle, BitVec.ult, BitVec.ule]

theorem ruleSoundD_selfCmp {f : Function} {cc : IntCC} {ty : Ty} {a b : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), selfCmp (atomTy f) tms cc ty a b = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        AtomsTyped f tms fr mem (.icmp cc ty a b) →
        (∀ o ∈ operands (.icmp cc ty a b), (tmVal f tms fr mem o).isSome) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.icmp cc ty a b) := by
  intro tms x' h hord fr mem t ht hA hd
  unfold selfCmp at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, htx⟩ := hc
    have hao : a ∈ operands (.icmp cc ty a a) := by simp [operands]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hd a hao)
    have hvt : v.ty = ty := tyAt_val hA (.op hao) htx hv
    obtain ⟨vt, X⟩ := v
    simp only at hvt
    subst hvt
    have hr : (tmFrame f tms fr mem).regs a = tmVal f tms fr mem a := rfl
    rw [tmVal_node' ht (by simp [Tm.ops, operands]), evalNode_iconst, evalNode_icmp, hr, hv]
    simp only [Option.bind_some, Val.as?_mk, Option.map_some, Sem.icmp, intcc_self]
    cases cc <;> rfl
  · cases h

/-! ## Family 7 and the default normaliser -/

theorem ruleSoundD_dropStep {f : Function} : RuleSoundD f (dropStep (atomTy f)) := by
  intro tms i x' h hord fr mem t ht hA hd
  cases i with
  | binary op ty a b =>
    simp only [dropStep] at h
    split at h
    · rename_i hop
      have hop' : op = .isub := by simpa using hop
      subst hop'
      exact ruleSoundD_subAdd tms x' h hord fr mem t ht hd
    · split at h
      · rename_i _ hop
        have hop' : op = .iadd := by simpa using hop
        subst hop'
        exact ruleSoundD_addSub tms x' h hord fr mem t ht hd
      · exact ruleSoundD_absTyped tms x' h hord fr mem t ht hA hd
  | icmp cc ty a b =>
    simp only [dropStep] at h
    exact ruleSoundD_selfCmp tms x' h hord fr mem t ht hA hd
  | _ => simp [dropStep] at h

/-- **The validator's default normaliser is sound where the operands have values.** -/
theorem normSoundD_stdD {f : Function} : NormSoundD f (Norm.stdD f) :=
  normSoundD_orElse normSoundT_stdT.toD (normSoundD_guard ruleSoundD_dropStep)

end Opt.MidVal

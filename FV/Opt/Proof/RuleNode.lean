import FV.Opt.Proof.Sem

/-!
# `evalNode` of each pure node form

Inversion/computation lemmas for `Opt.evalNode` (the single result of `Clif.evalInst`) of the
pure nodes the rules see and build: `evalNode fr mem n = some a` in terms of the operands'
registers. Used by the rule proofs to read the value of a matched node off the model
(`GraphModel.nodes`) and to compute the value of a made node (`MakeSound`).
-/

namespace Opt.Proof

open Clif

theorem Val.as?_eq_some {v : Val} {t : Ty} {b : BitVec t.width} :
    v.as? t = some b ↔ v = ⟨t, b⟩ := by
  obtain ⟨vt, vb⟩ := v
  simp only [Val.as?]
  constructor
  · intro h
    split at h
    · rename_i hh
      simp only [Option.some.injEq] at h
      subst hh
      cases h
      rfl
    · cases h
  · intro h
    cases h
    simp

section
variable (fr : Frame) (mem : Mem)

theorem getAs_ok {x : ValueId} {t : Ty} {b : BitVec t.width} :
    fr.getAs x t = .ok b ↔ fr.regs x = some ⟨t, b⟩ := by
  simp only [Frame.getAs, Frame.get, Res.ofOption]
  cases h : fr.regs x with
  | none => simp [bind, Res.bind]
  | some v =>
    simp only [bind, Res.bind, Option.some.injEq]
    cases h2 : v.as? t with
    | none =>
      simp only
      constructor
      · intro h; cases h
      · intro h; subst h; simp at h2
    | some b' =>
      simp only [Res.ok.injEq]
      rw [Val.as?_eq_some] at h2
      subst h2
      constructor
      · intro h; subst h; rfl
      · intro h; cases h; rfl

theorem getAs_bind_ok {β : Type} {x : ValueId} {t : Ty} {k : BitVec t.width → Res β} {r : β} :
    (fr.getAs x t >>= k) = .ok r ↔ ∃ b, fr.regs x = some ⟨t, b⟩ ∧ k b = .ok r := by
  cases h : fr.getAs x t with
  | ok b =>
    rw [getAs_ok] at h
    simp only [Res.ok_bind]
    constructor
    · intro e; exact ⟨b, h, e⟩
    · rintro ⟨b', h', e⟩
      rw [h] at h'
      cases h'
      exact e
  | trap c =>
    simp only [Res.trap_bind, reduceCtorEq, false_iff, not_exists, not_and]
    intro b hb
    have : fr.getAs x t = .ok b := (getAs_ok fr).2 hb
    rw [h] at this; cases this
  | stuck m =>
    simp only [Res.stuck_bind, reduceCtorEq, false_iff, not_exists, not_and]
    intro b hb
    have : fr.getAs x t = .ok b := (getAs_ok fr).2 hb
    rw [h] at this; cases this

theorem get_bind_ok {β : Type} {x : ValueId} {k : Val → Res β} {r : β} :
    (fr.get x >>= k) = .ok r ↔ ∃ v, fr.regs x = some v ∧ k v = .ok r := by
  simp only [Frame.get, Res.ofOption]
  cases fr.regs x <;> simp

theorem evalNode_eq_some {n : Inst} {a : Val} :
    evalNode fr mem n = some a ↔ ∃ m, evalInst fr mem n = .ok ([a], m) := by
  simp only [evalNode]
  split
  · rename_i r m h
    rw [h]
    constructor
    · intro e; cases e; exact ⟨m, rfl⟩
    · rintro ⟨m', e⟩; cases e; rfl
  · rename_i h
    simp only [reduceCtorEq, false_iff, not_exists]
    intro m e
    exact h _ _ e

theorem evalNode_iconst (t : Ty) (imm : BitVec t.width) :
    evalNode fr mem (.iconst t imm) = some ⟨t, imm⟩ := rfl

theorem evalNode_unary {op : UnaryOp} {t : Ty} {x : ValueId} {a : Val} :
    evalNode fr mem (.unary op t x) = some a ↔
      ∃ b : BitVec t.width, fr.regs x = some ⟨t, b⟩ ∧ a = ⟨t, Sem.unary op b⟩ := by
  simp only [evalNode_eq_some, evalInst, getAs_bind_ok, pure, Res.ok.injEq, Prod.mk.injEq,
    List.cons.injEq, and_true]
  constructor
  · rintro ⟨m, b, h, rfl, -⟩; exact ⟨b, h, rfl⟩
  · rintro ⟨b, h, rfl⟩; exact ⟨mem, b, h, rfl, rfl⟩

theorem evalNode_binary {op : BinaryOp} {t : Ty} {x y : ValueId} {a : Val} (hs : op.isShift = false) :
    evalNode fr mem (.binary op t x y) = some a ↔
      ∃ b c : BitVec t.width, fr.regs x = some ⟨t, b⟩ ∧ fr.regs y = some ⟨t, c⟩ ∧
        a = ⟨t, Sem.binary op b c⟩ := by
  simp only [evalNode_eq_some, evalInst, getAs_bind_ok, hs, Bool.false_eq_true, ite_false,
    pure, Res.ok.injEq, Prod.mk.injEq, List.cons.injEq, and_true]
  constructor
  · rintro ⟨m, b, h, c, h', rfl, -⟩; exact ⟨b, c, h, h', rfl⟩
  · rintro ⟨b, c, h, h', rfl⟩; exact ⟨mem, b, h, c, h', rfl, rfl⟩

theorem evalNode_icmp {cc : IntCC} {t : Ty} {x y : ValueId} {a : Val} :
    evalNode fr mem (.icmp cc t x y) = some a ↔
      ∃ b c : BitVec t.width, fr.regs x = some ⟨t, b⟩ ∧ fr.regs y = some ⟨t, c⟩ ∧
        a = ⟨.i8, Sem.icmp cc b c⟩ := by
  simp only [evalNode_eq_some, evalInst, getAs_bind_ok, pure, Res.ok.injEq, Prod.mk.injEq,
    List.cons.injEq, and_true]
  constructor
  · rintro ⟨m, b, h, c, h', rfl, -⟩; exact ⟨b, c, h, h', rfl⟩
  · rintro ⟨b, c, h, h', rfl⟩; exact ⟨mem, b, h, c, h', rfl, rfl⟩


/-- `evalNode` of a binary node, shifts and non-shifts at once (for `simp`: the `if` on the
concrete opcode reduces). -/
theorem evalNode_binary_iff {op : BinaryOp} {t : Ty} {x y : ValueId} {a : Val} :
    evalNode fr mem (.binary op t x y) = some a ↔
      if op.isShift then
        ∃ b : BitVec t.width, fr.regs x = some ⟨t, b⟩ ∧ ∃ c : Val, fr.regs y = some c ∧
          ∃ r, Sem.shift op b c.bits = some r ∧ a = ⟨t, r⟩
      else
        ∃ b c : BitVec t.width, fr.regs x = some ⟨t, b⟩ ∧ fr.regs y = some ⟨t, c⟩ ∧
          a = ⟨t, Sem.binary op b c⟩ := by
  cases hs : op.isShift
  · simp only [Bool.false_eq_true, ite_false]
    exact evalNode_binary fr mem hs
  · simp only [ite_true, evalNode_eq_some, evalInst, getAs_bind_ok, hs, get_bind_ok, pure,
      Res.ofOption]
    constructor
    · rintro ⟨m, b, h, c, h', e⟩
      cases hsh : Sem.shift op b c.bits with
      | none => simp [hsh] at e
      | some r =>
        simp only [hsh, Res.ok_bind, Res.ok.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at e
        exact ⟨b, h, c, h', r, hsh, e.1.symm⟩
    · rintro ⟨b, h, c, h', r, hsh, rfl⟩
      exact ⟨mem, b, h, c, h', by simp [hsh]⟩

end

end Opt.Proof

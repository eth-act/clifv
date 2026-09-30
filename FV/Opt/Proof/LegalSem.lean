import FV.Opt.Proof.LegalBase

/-!
# `Clif.evalInst` facts for the legalisation simulation

* `evalInst_same`: an instruction evaluates identically in two frames that agree on its
  operands, stack slots and global declarations (the `same` plan);
* `evalInst_types`: the results have the instruction's result types (the source invariant);
* `evalInst_allocs`: memory allocations are unchanged.
-/

namespace Opt.Legal

open Clif

theorem evalInst_same {fr fr' : Frame} {m : Mem} {i : Inst}
    (hops : ∀ x ∈ instOps i, fr'.regs x = fr.regs x) (hsl : fr'.slots = fr.slots)
    (hgl : fr'.func.globals = fr.func.globals) (hfa : ∀ t fn, i ≠ .funcAddr t fn) :
    evalInst fr' m i = evalInst fr m i := by
  cases i <;> simp only [instOps, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, List.mem_singleton] at hops <;>
    simp [evalInst, Frame.getAs, Frame.get, Frame.getMany, hops, hsl, hgl]
  exact absurd rfl (hfa _ _)

theorem Mem.store_allocs {w : Nat} {m : Mem} {fl a n} {x : BitVec w} {m'}
    (h : m.store fl a n x = .ok m') : m'.allocs = m.allocs := by
  simp only [Mem.store, Res.bind_eq_ok, Res.pure_eq_ok] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  rfl

theorem evalInst_allocs {fr : Frame} {m : Mem} {i : Inst} {vals : List Val} {m' : Mem}
    (h : evalInst fr m i = .ok (vals, m')) : m'.allocs = m.allocs := by
  cases i <;> simp only [evalInst, Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at h
  all_goals (repeat' (first | obtain ⟨_, _, h⟩ := h | split at h)) <;>
    (try simp only [Res.pure_eq_ok, Prod.mk.injEq, Res.bind_eq_ok] at h) <;>
    (repeat' (first | obtain ⟨_, _, h⟩ := h | split at h))
  all_goals first | (obtain ⟨-, rfl⟩ := h; rfl) | rfl | exact Mem.store_allocs ‹_› | skip

theorem evalInst_types {fr : Frame} {m : Mem} {i : Inst} {vals : List Val} {m' : Mem}
    (h : evalInst fr m i = .ok (vals, m')) {sigOf : FnRef → Option Signature}
    {declOf : Nat → Option Signature} {tys : List Ty}
    (ht : i.resultTypes sigOf declOf = some tys) : vals.map (·.ty) = tys := by
  cases i <;> simp only [Inst.resultTypes] at ht <;>
    simp only [evalInst, Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq, Frame.getAs,
      Res.ofOption_eq_ok] at h
  case call => cases h
  case callIndirect => cases h
  case iconcat t _ _ =>
    obtain ⟨t2, ht2, _, _, _, _, h3, -⟩ := h
    rw [ht2] at ht; simp only [Option.map_some, Option.some.injEq] at ht
    subst ht; subst h3; rfl
  case isplit t _ =>
    obtain ⟨th, hth, h3⟩ := h
    rw [hth] at ht; simp only [Option.map_some, Option.some.injEq] at ht
    subst ht
    grind
  case atomicCas =>
    simp only [Option.some.injEq] at ht; subst ht
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := h
    split at h <;> simp only [Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at h
    · obtain ⟨_, _, h, -⟩ := h; subst h; rfl
    · grind
  case symbolValue =>
    simp only [Option.some.injEq] at ht; subst ht
    obtain ⟨g, _, h⟩ := h
    split at h
    · simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨_, _, h, -⟩ := h; subst h; rfl
    · cases h
  case tlsValue =>
    simp only [Option.some.injEq] at ht; subst ht
    obtain ⟨g, _, h⟩ := h
    split at h
    · simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨_, _, h, -⟩ := h; subst h; rfl
    · cases h
  all_goals
    simp only [Option.some.injEq] at ht; subst ht
    (repeat' split at h) <;>
      (try simp only [Res.pure_eq_ok, Prod.mk.injEq, Res.bind_eq_ok, Res.ofOption_eq_ok,
        Res.check_eq_ok, pure] at h) <;>
      grind [Val.ofInt, Val.ofBool]

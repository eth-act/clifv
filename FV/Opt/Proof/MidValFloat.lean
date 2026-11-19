import FV.Opt.MidVal
import FV.Opt.Proof.SemFacts

/-!
# The `Opt.MidVal` pure nodes evaluate, without touching memory (#1119)

* `evalInst_float_total`: a float node typed by `floatTyped` (other than the trapping
  `fcvt_to_{u,s}int`) over typed operands evaluates to one value.
* `evalInst_pureK_total`: so does every non-partial `pureK` node (the `isPure` ones by
  `Opt.evalInst_total`).
* `pureK_not_call`, `pureK_mem`: a `pureK` node is not a call and keeps memory.
* `evalInst_pureK_mem`: a non-partial `pureK` node does not read memory: its evaluation in
  another memory differs only in the memory component of the result (`evalNode_pureK_mem`,
  `evalInst_pureK_ok_mem`). The literal `evalInst fr m i = evalInst fr m' i` is false whenever
  `m ≠ m'` and the node evaluates: `evalInst` returns the memory it ran in.
-/

namespace Opt.MidVal

open Clif

/-- Typed operands are all defined, and `tm` gives their types. -/
theorem getMany_typed {fr : Frame} {tm : ValueId → Option Ty} {args : List ValueId}
    (hops : ∀ x ∈ args, ∃ a, fr.regs x = some a ∧ tm x = some a.ty) :
    ∃ vs, fr.getMany args = .ok vs ∧ args.map tm = vs.map (fun v => some v.ty) := by
  induction args with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons x xs ih =>
    obtain ⟨a, ha, hta⟩ := hops x (by simp)
    obtain ⟨vs, hvs, hm⟩ := ih (fun y hy => hops y (by simp [hy]))
    refine ⟨a :: vs, ?_, by simp [hta, hm]⟩
    simp only [Frame.getMany, Frame.get, ha, Res.ofOption_some, Res.ok_bind, hvs]
    rfl

/-- `evalFloat` on values whose types `floatTyped` accepts. -/
theorem evalFloat_total {op : FOp} {ty : Ty} {vs : List Val} {tm : ValueId → Option Ty}
    {args : List ValueId} (hk : op ≠ .fcvtToUint ∧ op ≠ .fcvtToSint)
    (ht : floatTyped tm (.float op ty args) = true)
    (hm : args.map tm = vs.map (fun v => some v.ty)) :
    ∃ r, evalFloat op ty vs = .ok r := by
  simp only [floatTyped, hm] at ht
  clear hm
  obtain ⟨hk1, hk2⟩ := hk
  cases op <;> (try exact absurd rfl hk1) <;> (try exact absurd rfl hk2) <;>
    rcases vs with _ | ⟨⟨ta, xa⟩, _ | ⟨⟨tb, xb⟩, _ | ⟨⟨tc, xc⟩, _ | ⟨d, vs⟩⟩⟩⟩ <;>
    simp [FOp.arity, FSem.unary, FSem.binary, and_assoc] at ht
  all_goals first
    | (rcases ht with ⟨rfl | rfl, rfl, rfl, rfl⟩)
    | (rcases ht with ⟨rfl | rfl, rfl, rfl⟩)
    | (rcases ht with ⟨rfl | rfl, rfl⟩)
    | (rcases ht with ⟨rfl, rfl⟩)
    | (rcases ht with ⟨_, rfl | rfl⟩)
  all_goals (try cases ty) <;>
    (try simp_all [evalFloat, Val.at, FSem.lift1, FSem.lift2, FSem.lift3, FSem.fcmp,
      FSem.toIntSat, FSem.fromInt, FSem.unary, FSem.binary])
  all_goals exact ⟨_, _, rfl, rfl⟩

theorem evalInst_float_total {tm : ValueId → Option Ty} {fr : Frame} {mem : Mem} {op : FOp}
    {ty : Ty} {args : List ValueId}
    (hk : op ≠ .fcvtToUint ∧ op ≠ .fcvtToSint)
    (ht : floatTyped tm (.float op ty args) = true)
    (hops : ∀ x ∈ args, ∃ a, fr.regs x = some a ∧ tm x = some a.ty) :
    ∃ v, evalInst fr mem (.float op ty args) = .ok ([v], mem) := by
  obtain ⟨vs, hvs, hm⟩ := getMany_typed hops
  obtain ⟨r, hr⟩ := evalFloat_total hk ht hm
  exact ⟨r, by simp [evalInst, hvs, hr]⟩

/-- Every non-partial `pureK` node, typed by `Opt.pureTyped` and `floatTyped`, evaluates to one
value and keeps memory. -/
theorem evalInst_pureK_total {f : Function} {tm : ValueId → Option Ty} {fr : Frame} {mem : Mem}
    {i : Inst} (hp : pureK i = true) (hpart : partialK i = false)
    (hpt : isPure i = true → pureTyped tm f i = true) (hft : floatTyped tm i = true)
    (hf : fr.func.globals = f.globals)
    (hops : ∀ x ∈ operands i, ∃ a, fr.regs x = some a ∧ tm x = some a.ty)
    (hsl : ∀ s, (f.slots.lookup s).isSome → (fr.slots.lookup s).isSome) :
    ∃ v, evalInst fr mem i = .ok ([v], mem) := by
  by_cases hi : isPure i = true
  · exact Opt.evalInst_total hi (hpt hi) hf hops hsl
      (fun _ _ _ _ _ h _ => by subst h; simp [partialK] at hpart)
  · cases i
    case float op ty args =>
      simp [pureK, isPure] at hp
      exact evalInst_float_total hp hft hops
    all_goals simp [pureK, isPure, partialK] at hp hi hpart

theorem pureK_not_call {i : Inst} (hp : pureK i = true) : ∀ fn args, i ≠ .call fn args := by
  rintro fn args rfl
  simp [pureK, isPure] at hp

/-- A `pureK` node keeps memory. -/
theorem pureK_mem {fr : Frame} {m m' : Mem} {i : Inst} {vs : List Val} (hp : pureK i = true)
    (h : evalInst fr m i = .ok (vs, m')) : m' = m := by
  by_cases hi : isPure i = true
  · exact (evalInst_pure hi h).1
  · cases i
    case float op ty args =>
      simp only [evalInst, Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨_, _, _, _, _, h⟩ := h
      exact h.symm
    case funcAddr ty fn =>
      simp only [evalInst, Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨_, _, _, _, _, h⟩ := h
      exact h.symm
    case tlsValue ty gv =>
      simp only [evalInst, Res.bind_eq_ok] at h
      obtain ⟨_, _, h⟩ := h
      split at h
      · simp only [Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at h
        obtain ⟨_, _, _, h⟩ := h
        exact h.symm
      · cases h
    all_goals simp [pureK, isPure] at hp hi

/-- A non-partial `pureK` node does not read memory: in memory `m'` it evaluates as in `m`,
with `m'` as the result memory. -/
theorem evalInst_pureK_mem {fr : Frame} {m m' : Mem} {i : Inst} (hp : pureK i = true)
    (hpart : partialK i = false) :
    evalInst fr m' i = (fun r => (r.1, m')) <$> evalInst fr m i := by
  cases i <;> simp [pureK, isPure, partialK] at hp hpart
  case bitcast ty fl x =>
    simp only [evalInst]
    cases fr.get x with
    | ok a => simp only [Res.ok_bind]; split <;> rfl
    | trap c => rfl
    | stuck s => rfl
  all_goals simp only [evalInst, map_bind, map_pure]
  all_goals (repeat' split) <;> (try simp only [map_bind, map_pure])

theorem evalNode_pureK_mem {fr : Frame} {m m' : Mem} {i : Inst} (hp : pureK i = true)
    (hpart : partialK i = false) : evalNode fr m' i = evalNode fr m i := by
  rw [evalNode_eq_val1, evalNode_eq_val1, evalInst_pureK_mem (m := m) (m' := m') hp hpart]
  rcases evalInst fr m i with ⟨vs, mm⟩ | c | msg
  · rcases vs with _ | ⟨v, _ | ⟨w, vs⟩⟩ <;> rfl
  all_goals rfl

theorem evalInst_pureK_ok_mem {fr : Frame} {m m' mm : Mem} {i : Inst} {vs : List Val}
    (hp : pureK i = true) (hpart : partialK i = false) (h : evalInst fr m i = .ok (vs, mm)) :
    evalInst fr m' i = .ok (vs, m') := by
  rw [evalInst_pureK_mem (m := m) (m' := m') hp hpart, h]
  rfl

end Opt.MidVal

module

import FV.Backend.Proof.DriverCheckSound
public import FV.Backend.Proof.IselContract
public import FV.Backend.Proof.DriverCheck
import FV.Arm.MinTheory

public section

/-!
# The float-capable context check (S11e4)

`ctxOkT f ctx` decides `CtxInvT f ctx` (the invariant of a float-capable lowering context, the
premise of `LowerRulesCorrectT`/`MemRulesCorrectRT`): `ctxOk`'s checks without E's
instruction subset (`Compile.instE`), with class-aware value registers (`valClassOf`), the
types `i8..i64`, `f32`, `f64` (`mCTys`) and the integer typing of the operands in integer
positions (`intArgs`, `IntPos`). `ctxOkT_sound`: a context it accepts satisfies `CtxInvT`.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- `t ∈ l`, decided (`CTy`'s derived `BEq` is not lawful, so not through `List.Mem`'s instance). -/
def tyIn (l : List CTy) (t : CTy) : Bool := l.any fun u => decide (t = u)

theorem tyIn_sound {l : List CTy} {t : CTy} (h : tyIn l t = true) : t ∈ l := by
  obtain ⟨u, hu, he⟩ := List.any_eq_true.mp h
  rw [of_decide_eq_true he]; exact hu

/-- `IntPos ctx x`, decided. -/
@[expose] def intPosOk (ctx : Ctx) (x : Nat) : Bool :=
  match ctx.valueType? x with
  | some t => tyIn eCTys t
  | none => true

/-- **`CtxInvT f ctx`, decided.** -/
@[expose] def ctxOkT (f : Clif.Function) (ctx : Ctx) : Bool :=
  decide (ctx.func = f) &&
  ctx.insts.toList.all (fun info => match info.clif with
    | some i =>
      (match instData f i with
        | .ok d => d == info.data
        | .error _ => false) &&
      ctxResTysOk f info i && (intArgs i).all (intPosOk ctx)
    | none => true) &&
  (List.range ctx.valReg.size).all (fun x => match ctx.valueReg? x with
    | some r => decide (r = .vreg x (valClassOf ctx x))
    | none => true) &&
  (List.range ctx.valTy.size).all (fun x => match ctx.valueType? x with
    | some t => decide (ctx.valueReg? x = some (.vreg x t.valClass)) && tyIn mCTys t
    | none => true) &&
  (List.range ctx.valDef.size).all (fun x => match ctx.defInst? x with
    | some d => match ctx.insts[d]? with
      | some info => decide (x ∈ info.results) && info.clif.isSome
      | none => false
    | none => true) &&
  decide (ctx.slotOff = (slotLayout f.slots).1) &&
  ctx.insts.toList.all (fun info => info.resTys.all (tyIn mCTys)) &&
  ctx.insts.toList.all (fun info => match info.clif with
    | some i => match memAddr? i with
      | some x => decide (ctx.valueType? x = some (.int 64))
      | none => true
    | none => true)

theorem intPosOk_sound {ctx : Ctx} {x : Nat} (h : intPosOk ctx x = true) : IntPos ctx x := by
  intro t ht
  simp only [intPosOk, ht] at h
  exact tyIn_sound h

theorem lt_valReg {ctx : Ctx} {x : Nat} {r : Reg} (h : ctx.valueReg? x = some r) :
    x < ctx.valReg.size := by
  simp only [Ctx.valueReg?] at h
  cases h' : ctx.valReg[x]? with
  | none => rw [h'] at h; cases h
  | some _ => exact (Array.getElem?_eq_some_iff.mp h').1

theorem lt_valTy {ctx : Ctx} {x : Nat} {t : CTy} (h : ctx.valueType? x = some t) :
    x < ctx.valTy.size := by
  simp only [Ctx.valueType?] at h
  cases h' : ctx.valTy[x]? with
  | none => rw [h'] at h; cases h
  | some _ => exact (Array.getElem?_eq_some_iff.mp h').1

theorem lt_valDef {ctx : Ctx} {x d : Nat} (h : ctx.defInst? x = some d) :
    x < ctx.valDef.size := by
  simp only [Ctx.defInst?] at h
  cases h' : ctx.valDef[x]? with
  | none => rw [h'] at h; cases h
  | some _ => exact (Array.getElem?_eq_some_iff.mp h').1

/-- **`ctxOkT` is sound**: a context it accepts is a float-capable lowering context. -/
theorem ctxOkT_sound {f : Clif.Function} {ctx : Ctx}
    (h : ctxOkT f ctx = true) : CtxInvT f ctx := by
  simp only [ctxOkT, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hfunc, hinsts⟩, hreg⟩, hty⟩, hdef⟩, hslot⟩, hres⟩, haddr⟩ := h
  have hmem : ∀ {ii : Nat} {info : IInfo}, ctx.insts[ii]? = some info → info ∈ ctx.insts.toList :=
    fun hi => by rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hi
  have hinst : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
      info.clif = some inst →
      (instData f inst = .ok info.data) ∧
      (∃ tys, inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) =
          some tys ∧
        info.resTys = tys.map CTy.ofClif ∧ info.results.length = tys.length) ∧
      ∀ x ∈ intArgs inst, IntPos ctx x := by
    intro ii info inst hi hc
    have := List.all_eq_true.mp hinsts info (hmem hi)
    rw [hc] at this
    simp only [Bool.and_eq_true] at this
    obtain ⟨⟨h1, h2⟩, h3⟩ := this
    refine ⟨?_, ?_, fun x hx => intPosOk_sound (List.all_eq_true.mp h3 x hx)⟩
    · cases hd : instData f inst with
      | ok d => rw [hd] at h1; simpa using h1
      | error e => rw [hd] at h1; simp at h1
    · have h2' : ctxResTysOk f info inst = true := h2
      unfold ctxResTysOk at h2'
      cases hty : inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) with
      | none => rw [hty] at h2'; simp at h2'
      | some tys =>
        have h2'' : (decide (info.resTys = tys.map CTy.ofClif) &&
            decide (info.results.length = tys.length)) = true := by
          rw [hty] at h2'; exact h2'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2''
        exact ⟨tys, rfl, h2''.1, h2''.2⟩
  have htyx : ∀ (x : Nat) (t : CTy), ctx.valueType? x = some t →
      ctx.valueReg? x = some (.vreg x t.valClass) ∧ t ∈ mCTys := by
    intro x t hx
    have := all_range hty (lt_valTy hx)
    rw [hx] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1, tyIn_sound this.2⟩
  refine ⟨hfunc, fun ii info inst hi hc => (hinst ii info inst hi hc).1,
    fun ii info inst hi hc => (hinst ii info inst hi hc).2.1, ?_,
    fun x t hx => (htyx x t hx).1, ?_, ?_, hslot, ?_, fun x t hx => (htyx x t hx).2, ?_,
    fun ii info inst hi hc => (hinst ii info inst hi hc).2.2⟩
  · intro x r hx
    have := all_range hreg (lt_valReg hx)
    rw [hx] at this
    simpa using this
  · intro x d hx
    have := all_range hdef (lt_valDef hx)
    rw [hx] at this
    simp only at this
    split at this
    · rename_i info hi
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨info, hi, this.1⟩
    · cases this
  · intro x d info hx hi
    have := all_range hdef (lt_valDef hx)
    rw [hx] at this
    simp only [hi, Bool.and_eq_true] at this
    exact this.2
  · intro ii info hi t ht
    exact tyIn_sound (List.all_eq_true.mp (List.all_eq_true.mp hres info (hmem hi)) t ht)
  · intro ii info inst x hi hc hx
    have := List.all_eq_true.mp haddr info (hmem hi)
    rw [hc] at this
    simp only [hx, decide_eq_true_eq] at this
    exact this

end Backend.Proof.Driver

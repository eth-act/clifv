import FV.Backend.Proof.TryRegs
import FV.Backend.Proof.AbiClass
import FV.Compile.SubsetT

/-!
# The typed `try_call` of the lowering on integer signatures (S11e6)

`lowerFunction` lowers a direct `try_call` with the typed operand, data and vregs
(`exnTableOpndC`, `tryCallDataC`, `tryRegsOfC`: `f32`/`f64` parameters and returns allowed, the
returns' vregs of their classes in `retRegsC`'s registers). On integer signatures they are the
integer ones:

* `exnTableOpnd_iff_C`: `exnTableOpnd` is `exnTableOpndC` with `sigIntB`;
* `tryCallDataC_of`, `tryCallData_of_C` (integer externs, `Compile.sigE`): the typed data is the
  integer data;
* `tryRegsOfC_eq` (integer returns): the typed vregs are `tryRegsOf`'s;
* `exnTableOpndC_cc`, `exnTableOpndC_sig`: `exnTableOpnd_cc`/`exnTableOpnd_sig` for the typed
  operand.
-/

namespace Backend

open Backend.Proof

/-- **`exnTableOpnd` is the typed operand with integer signatures.** -/
theorem exnTableOpnd_iff_C {f : Clif.Function} {et : Clif.ExnTable} {sig : Clif.Signature}
    {items : List (Option Nat)} :
    exnTableOpnd f et = .ok (sig, items) ↔ exnTableOpndC f et = .ok (sig, items) ∧ sigIntB sig = true := by
  unfold exnTableOpnd exnTableOpndC
  cases hs : f.sigDecls.lookup et.sig with
  | none => simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  | some sig' =>
    simp only []
    by_cases hcc : (sig'.callConv.isNone || sig'.callConv == some .systemV) = true
    · simp only [hcc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure,
        Except.pure]
      by_cases hi : sigIntB sig' = true
      · simp only [hi, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        constructor
        · intro h
          refine ⟨h, ?_⟩
          split at h
          · cases h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.1]; exact hi
        · exact fun h => h.1
      · simp only [Bool.not_eq_true] at hi
        simp only [hi, Bool.not_false, ↓reduceIte, throw, throwThe, MonadExceptOf.throw,
          reduceCtorEq, false_iff, not_and]
        intro h
        split at h
        · cases h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.1, hi]; simp
    · simp [hcc, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

theorem exnTableOpndC_of {f : Clif.Function} {et : Clif.ExnTable} {sig : Clif.Signature}
    {items : List (Option Nat)} (h : exnTableOpnd f et = .ok (sig, items)) :
    exnTableOpndC f et = .ok (sig, items) :=
  (exnTableOpnd_iff_C.mp h).1

theorem exnTableOpnd_of_C {f : Clif.Function} {et : Clif.ExnTable} {sig : Clif.Signature}
    {items : List (Option Nat)} (h : exnTableOpndC f et = .ok (sig, items)) (hi : sigIntB sig = true) :
    exnTableOpnd f et = .ok (sig, items) :=
  exnTableOpnd_iff_C.mpr ⟨h, hi⟩

/-- The typed operand's signature is its `sigN` declaration. -/
theorem exnTableOpndC_sig {f : Clif.Function} {et : Clif.ExnTable} {sig : Clif.Signature}
    {items : List (Option Nat)} (h : exnTableOpndC f et = .ok (sig, items)) :
    f.sigDecls.lookup et.sig = some sig := by
  unfold exnTableOpndC at h
  cases hs : f.sigDecls.lookup et.sig with
  | none => simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | some sig' =>
    simp only [hs] at h
    split at h
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    · simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [h.1]

/-- The typed operand's convention passes the exception payloads in x0 and x1. -/
theorem exnTableOpndC_cc {f : Clif.Function} {et : Clif.ExnTable} {sig : Clif.Signature}
    {items : List (Option Nat)} (h : exnTableOpndC f et = .ok (sig, items)) :
    payloadRegs sig.callConv = [.x 0, .x 1] := by
  unfold exnTableOpndC at h
  cases hs : f.sigDecls.lookup et.sig with
  | none => simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | some sig' =>
    simp only [hs] at h
    split at h
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    · rename_i hcc
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.or_eq_true, Option.isNone_iff_eq_none,
          beq_iff_eq] at hcc
        rcases hcc with h | h <;> simp [payloadRegs, h]

set_option maxRecDepth 20000 in
/-- **The integer data is the typed data.** -/
theorem tryCallDataC_of {f : Clif.Function} {t : Clif.Terminator} {d : V}
    (h : tryCallData f t = .ok d) : tryCallDataC f t = .ok d := by
  cases t with
  | tryCall fn args et =>
    obtain ⟨sig, items, ext, he, hx, hs⟩ := tryCallData_spec h
    rw [tryCallData_eq he hx hs] at h
    cases h
    simp only [tryCallDataC, exnTableOpndC_of he, hx, hs, bind, Except.bind, bne_self_eq_false,
      Bool.false_eq_true, ite_false, pure, Except.pure]
    rfl
  | _ => exact h

/-- An extern of a function whose externs have integer signatures (`Compile.sigE`) has an integer
signature (`sigIntB`). -/
theorem sigIntB_of_externs {f : Clif.Function} (hx : f.externs.all (Compile.sigE ·.2.sig) = true)
    {fn : Clif.FnRef} {e : Clif.ExtFunc} (he : f.extern? fn = some e) : sigIntB e.sig = true := by
  have hs := List.all_eq_true.mp hx _ (Compile.lookup_mem he)
  simp only [Compile.sigE, Compile.tyE, Bool.and_eq_true, List.all_eq_true] at hs
  simp only [sigIntB, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun p hp => (hs.1 p hp).1, fun p hp => (hs.2 p hp).1⟩

set_option maxRecDepth 20000 in
/-- **The typed data is the integer data** for a function whose externs have integer signatures
(a direct `try_call`'s signature is its callee's). -/
theorem tryCallData_of_C {f : Clif.Function} (hx : f.externs.all (Compile.sigE ·.2.sig) = true)
    {t : Clif.Terminator} {d : V} (h : tryCallDataC f t = .ok d) : tryCallData f t = .ok d := by
  cases t with
  | tryCall fn args et =>
    simp only [tryCallDataC] at h
    cases he : exnTableOpndC f et with
    | error e => simp [he, bind, Except.bind] at h
    | ok q =>
      obtain ⟨sig, items⟩ := q
      cases hxf : f.extern? fn with
      | none => simp [he, hxf, bind, Except.bind] at h
      | some ext =>
        by_cases hs : ext.sig = sig
        · have hi : sigIntB sig = true := hs ▸ sigIntB_of_externs hx hxf
          simp only [he, hxf, hs, bind, Except.bind, bne_self_eq_false, Bool.false_eq_true,
            ite_false, pure, Except.pure] at h
          rw [tryCallData_eq (exnTableOpnd_of_C he hi) hxf hs]
          exact h
        · simp [he, hxf, hs, bind, Except.bind] at h
  | _ => exact h

/-- Folds agreeing on the list's elements agree. -/
theorem foldl_congr_mem {α γ : Type} {g h : γ → α → γ} :
    ∀ (L : List α) (i : γ), (∀ a ∈ L, ∀ x, g x a = h x a) → L.foldl g i = L.foldl h i
  | [], _, _ => rfl
  | a :: L, i, hg => by
    simp only [List.foldl_cons]
    rw [hg a List.mem_cons_self i]
    exact foldl_congr_mem L _ fun b hb x => hg b (List.mem_cons_of_mem _ hb) x

/-- A fold that ignores the list's elements depends only on its length. -/
theorem foldl_len {α β γ : Type} (g : γ → γ) :
    ∀ (L1 : List α) (L2 : List β) (i : γ), L1.length = L2.length →
      L1.foldl (fun a _ => g a) i = L2.foldl (fun a _ => g a) i
  | [], [], _, _ => rfl
  | _ :: L1, _ :: L2, i, h => by
    simp only [List.foldl_cons]
    exact foldl_len g L1 L2 _ (by simpa using h)
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- **The typed vregs are `tryRegsOf`'s on integer returns.** (Both allocate over the declared
returns, #587; integer ABI returns, `sigRets`, make integer declared returns.) -/
theorem tryRegsOfC_eq {sig : Clif.Signature}
    (h : (sigRets sig).map retClass = List.replicate (sigRets sig).length .int) (st : LState) :
    tryRegsOfC sig st = tryRegsOf sig st := by
  have h' : sig.returns.map retClass = List.replicate sig.returns.length .int := by
    unfold sigRets at h
    split at h
    · split at h
      · rename_i hr; rw [List.isEmpty_iff.mp hr]; rfl
      · exact h
    · exact h
  unfold tryRegsOfC tryRegsOf
  rw [h', retRegsC_int]
  cases hr : retRegs sig.returns.length with
  | none => rfl
  | some ps =>
    simp only [bind, Option.bind]
    have hcls : ∀ q ∈ sig.returns, retClass q = .int := fun q hq => by
      have hm : retClass q ∈ sig.returns.map retClass := List.mem_map_of_mem hq
      rw [h'] at hm
      exact List.eq_of_mem_replicate hm
    have hps : ps.length = sig.returns.length := by
      unfold retRegs at hr; split at hr
      · cases hr; simp
      · cases hr
    have e1 : sig.returns.foldl (init := ((#[] : Array Reg), st)) (fun (x : Array Reg × LState) q =>
        ((x.1.push (x.2.fresh (retClass q)).1), (x.2.fresh (retClass q)).2)) =
        sig.returns.foldl (init := ((#[] : Array Reg), st)) (fun (x : Array Reg × LState) _ =>
        ((x.1.push (x.2.fresh .int).1), (x.2.fresh .int).2)) := by
      exact foldl_congr_mem _ _ fun q hq x => by rw [hcls q hq]
    have e2 := foldl_len (fun (x : Array Reg × LState) =>
        ((x.1.push (x.2.fresh .int).1), (x.2.fresh .int).2)) sig.returns ps
      ((#[] : Array Reg), st) hps.symm
    rw [e1, e2]

/-- `tryRegsOfC` allocates fresh vregs only. -/
theorem tryRegsOfC_mono {sig : Clif.Signature} {st st' : LState} {r : List Reg × List Reg}
    (h : tryRegsOfC sig st = some (r, st')) : st.nextVreg ≤ st'.nextVreg ∧ st'.emitted = st.emitted := by
  have hf : ∀ (c : RegClass) (s : LState), s.nextVreg ≤ (s.fresh c).2.nextVreg ∧
      (s.fresh c).2.emitted = s.emitted := fun c s => by simp [LState.fresh]
  unfold tryRegsOfC at h
  cases hr : retRegsC (sig.returns.map retClass) 0 0 with
  | none => rw [hr] at h; cases h
  | some ps =>
    rw [hr] at h
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have g1 : ∀ (L : List Clif.AbiParam) (acc : Array Reg) (s : LState),
        s.nextVreg ≤ (L.foldl (fun (x : Array Reg × LState) q =>
          ((x.1.push (x.2.fresh (retClass q)).1), (x.2.fresh (retClass q)).2)) (acc, s)).2.nextVreg ∧
        (L.foldl (fun (x : Array Reg × LState) q =>
          ((x.1.push (x.2.fresh (retClass q)).1), (x.2.fresh (retClass q)).2)) (acc, s)).2.emitted =
          s.emitted := by
      intro L
      induction L with
      | nil => intro acc s; simp
      | cons q L ih =>
        intro acc s
        simp only [List.foldl_cons]
        obtain ⟨a1, a2⟩ := ih (acc.push (s.fresh (retClass q)).1) (s.fresh (retClass q)).2
        obtain ⟨b1, b2⟩ := hf (retClass q) s
        exact ⟨Nat.le_trans b1 a1, a2.trans b2⟩
    have g2 : ∀ (L : List Reg) (rets : Array Reg) (acc : Array Reg) (s : LState),
        s.nextVreg ≤ (L.foldl (fun (x : Array Reg × LState) p => match ps.idxOf? p with
          | some i => (x.1.push rets[i]!, x.2)
          | none => (x.1.push (x.2.fresh .int).1, (x.2.fresh .int).2)) (acc, s)).2.nextVreg ∧
        (L.foldl (fun (x : Array Reg × LState) p => match ps.idxOf? p with
          | some i => (x.1.push rets[i]!, x.2)
          | none => (x.1.push (x.2.fresh .int).1, (x.2.fresh .int).2)) (acc, s)).2.emitted =
          s.emitted := by
      intro L rets
      induction L with
      | nil => intro acc s; simp
      | cons p L ih =>
        intro acc s
        simp only [List.foldl_cons]
        split
        · exact ih _ _
        · obtain ⟨a1, a2⟩ := ih (acc.push (s.fresh .int).1) (s.fresh .int).2
          obtain ⟨b1, b2⟩ := hf .int s
          exact ⟨Nat.le_trans b1 a1, a2.trans b2⟩
    obtain ⟨c1, c2⟩ := g1 sig.returns #[] st
    generalize hR : sig.returns.foldl (fun (x : Array Reg × LState) q =>
      ((x.1.push (x.2.fresh (retClass q)).1), (x.2.fresh (retClass q)).2)) (#[], st) = R at c1 c2
    obtain ⟨d1, d2⟩ := g2 (payloadRegs sig.callConv) R.1 #[] R.2
    exact ⟨Nat.le_trans c1 d1, d2.trans c2⟩

end Backend

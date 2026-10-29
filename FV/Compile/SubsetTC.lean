module

public import FV.Compile.SubsetT

@[expose] public section

/-!
# The typed movement scope with typed direct `try_call`s (S11e6, #419)

`Compile.functionETC f`: the typed movement scope `functionET` where a direct `try_call`'s callee
may take and return `f32`/`f64`: the externs have signatures of the typed scope (`sigET`), the
callees of the `call` statements keep integer signatures (`callsE`), and a direct `try_call`'s
arguments are not integer positions (`termIntOperandsC`: they are passed in their values'
classes, `Backend.Proof.IselCtlTryF`). `functionET_iff`-style: `functionETC_of_functionET`
(every function of the typed movement scope is in it). `functionET` is unchanged.
-/

namespace Compile

open Clif

/-- The callee of every `call` statement of `f` has an integer signature. -/
def callsE (f : Function) : Bool :=
  f.blocks.all fun b => b.body.all fun s => match s.inst with
    | .call fn _ => match f.extern? fn with
      | some e => sigE e.sig
      | none => true
    | _ => true

/-- The operands of a terminator in integer positions, with typed direct `try_call`s: a branch
condition, a `br_table` index, the callee and arguments of a `try_call_indirect` (integer-only);
a direct `try_call`'s arguments are passed in their classes' registers. -/
def termIntOperandsC : Terminator → List Nat
  | .tryCall _ _ _ => []
  | t => termIntOperands t

/-- `opsTypedT` with `termIntOperandsC`. -/
def opsTypedTC (f : Function) : Bool :=
  let fd := floatDefs f
  f.blocks.all fun b =>
    b.body.all (fun s => (intOperands s.inst).all fun x => !fd.contains x) &&
      (termIntOperandsC b.term).all fun x => !fd.contains x

/-- **The typed movement scope with typed direct `try_call`s.** -/
def functionETC (f : Function) : Bool :=
  sigET f.sig && f.globals.all (globalE ·.2) && f.externs.all (sigET ·.2.sig) && callsE f &&
    f.blocks.all (fun b =>
      b.params.all (tyM ·.2) && b.body.all (instET ·.inst) && termE b.term) &&
    opsTypedTC f && edgeClassOk f

theorem termIntOperandsC_sub (t : Terminator) : ∀ x ∈ termIntOperandsC t, x ∈ termIntOperands t := by
  intro x hx
  cases t <;> simp_all [termIntOperandsC]

theorem termIntOperandsC_eq {t : Terminator} (h : t.isTry = false) :
    termIntOperandsC t = termIntOperands t := by
  cases t <;> simp_all [termIntOperandsC, Terminator.isTry]

/-- Integer externs: every `call` statement's callee has an integer signature. -/
theorem callsE_of_externs {f : Function} (hx : f.externs.all (sigE ·.2.sig) = true) :
    callsE f = true := by
  simp only [callsE, List.all_eq_true]
  intro b _ s _
  split
  · rename_i fn _ _
    split
    · rename_i e he
      exact List.all_eq_true.mp hx _ (lookup_mem he)
    · rfl
  · rfl

/-- **The typed movement scope is in the scope with typed `try_call`s.** -/
theorem functionETC_of_functionET {f : Function} (h : functionET f = true) :
    functionETC f = true := by
  simp only [functionET, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hs, hg⟩, hx⟩, hb⟩, ho⟩, he⟩ := h
  simp only [functionETC, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨hs, hg⟩, ?_⟩, callsE_of_externs hx⟩, hb⟩, ?_⟩, he⟩
  · exact List.all_eq_true.mpr fun p hp => sigET_of_sigE (List.all_eq_true.mp hx p hp)
  · simp only [opsTypedT, opsTypedTC, Bool.and_eq_true, List.all_eq_true] at ho ⊢
    exact fun b hb' => ⟨(ho b hb').1, fun x hx => (ho b hb').2 x (termIntOperandsC_sub _ x hx)⟩

end Compile

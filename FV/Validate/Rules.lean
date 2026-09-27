/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.

# CLIF-side proof rules for the generated simulation proofs

The validated function runs as the only frame (`callers = []`) of a CLIF state
`⟨⟨F, regs, slots, body, term⟩, [], mem⟩`. The program `p` passed to `Clif.step` is the empty
program `Validate.noFuncs`, so every `call` (including a recursive one) is an extern call
through `Clif.Env`: callees are abstract, governed by their contracts.

Each rule turns `GoodF` of a CLIF state into a goal about what the next CLIF step computes.
The goals are phrased with `ResK`, which `simp` evaluates once the operands are known.
-/
import FV.Validate.Basic

namespace Validate

open Arm

/-- The empty CLIF program: every call goes to the environment. -/
def noFuncs : Clif.Program := { header := [], funcs := [] }

/-- The top-level CLIF state of the validated function. -/
abbrev cst (F : Clif.Function) (regs : Clif.Regs) (slots : List (Clif.SlotId × Nat))
    (body : List Clif.Stmt) (term : Clif.Terminator) (mem : Clif.Mem) : Clif.State :=
  ⟨⟨F, regs, slots, body, term⟩, [], mem⟩

/-- Continuation on a CLIF result: `ok` continues, a trap must be matched by an Arm trap
site, `stuck` constrains nothing. -/
def ResK {α : Type} (A : Act) (res : Clif.Res α) (k : α → Prop) (a : ArmState) : Prop :=
  match res with
  | .ok x => k x
  | .trap c => Reach (fun a' => TrapOK A c a' ∨ StackOut A a') a
  | .stuck _ => True

@[simp] theorem ResK_ok {α : Type} (A : Act) (x : α) (k : α → Prop) (a : ArmState) :
    ResK A (.ok x) k a = k x := rfl
@[simp] theorem ResK_stuck {α : Type} (A : Act) (m : String) (k : α → Prop) (a : ArmState) :
    ResK A (.stuck m) k a = True := rfl
@[simp] theorem ResK_trap {α : Type} (A : Act) (c : Clif.TrapCode) (k : α → Prop) (a : ArmState) :
    ResK A (.trap c) k a = Reach (fun a' => TrapOK A c a' ∨ StackOut A a') a := rfl

@[simp] theorem ResK_pure {α : Type} (A : Act) (x : α) (k : α → Prop) (a : ArmState) :
    ResK A (pure x) k a = k x := rfl

theorem ResK_mono {α : Type} {A : Act} {r : Clif.Res α} {k k' : α → Prop} {a : ArmState}
    (h : ResK A r k a) (hk : ∀ x, k x → k' x) : ResK A r k' a := by
  revert h; cases r <;> simp_all [ResK]

theorem ResK_ite {α : Type} (A : Act) (c : Prop) [Decidable c] (r1 r2 : Clif.Res α)
    (k : α → Prop) (a : ArmState) :
    ResK A (if c then r1 else r2) k a = ((c → ResK A r1 k a) ∧ (¬c → ResK A r2 k a)) := by
  by_cases h : c <;> simp [h]

theorem ofExcept_ite {α : Type} (c : Prop) [Decidable c] (x y : Except Clif.TrapCode α) :
    Clif.Res.ofExcept (if c then x else y) = if c then Clif.Res.ofExcept x else Clif.Res.ofExcept y := by
  by_cases h : c <;> simp [h]

theorem ResK_bind {α β : Type} (A : Act) (r : Clif.Res α) (f : α → Clif.Res β) (k : β → Prop)
    (a : ArmState) : ResK A (r >>= f) k a = ResK A r (fun x => ResK A (f x) k a) a := by
  cases r <;> rfl

/-- Is the instruction a `call`? -/
def isCall : Clif.Inst → Bool
  | .call .. => true
  | _ => false

/-- What must hold after one CLIF step with result `sr`. -/
def StepGood (A : Act) (p : Clif.Program) (n : Nat) (sr : Clif.StepResult) (a : ArmState) : Prop :=
  match sr with
  | .next s' => GoodF A p n s' a
  | .done vals mem => Reach (fun a' => RetOK A vals mem a' ∨ StackOut A a') a
  | .trapped c => Reach (fun a' => TrapOK A c a' ∨ StackOut A a') a
  | .stuck _ => True

/-- A CLIF step, consuming one unit of the fuel bound. -/
theorem GoodF.ofStepDec {A : Act} {p : Clif.Program} {n : Nat} {c : Clif.State} {a : ArmState}
    (h : StepGood A p n (Clif.step A.W.env p c) a) : GoodF A p (n + 1) c a := by
  intro fuel hf
  cases fuel with
  | zero => trivial
  | succ f =>
    rw [Clif.runLoop_succ]
    revert h
    cases Clif.step A.W.env p c with
    | next s' => intro h; exact h f (by omega)
    | done vals mem => intro h; exact h
    | trapped c => intro h; exact h
    | stuck m => intro _; trivial

/-- A CLIF step, not consuming the fuel bound. -/
theorem GoodF.ofStep {A : Act} {p : Clif.Program} {n : Nat} {c : Clif.State} {a : ArmState}
    (h : StepGood A p n (Clif.step A.W.env p c) a) : GoodF A p n c a := by
  intro fuel hf
  cases fuel with
  | zero => trivial
  | succ f =>
    rw [Clif.runLoop_succ]
    revert h
    cases Clif.step A.W.env p c with
    | next s' => intro h; exact h f (by omega)
    | done vals mem => intro h; exact h
    | trapped c => intro h; exact h
    | stuck m => intro _; trivial

theorem StepGood.ofRes {A : Act} {p : Clif.Program} {n : Nat} {a : ArmState} {α : Type}
    {r : Clif.Res α} {k : α → Clif.StepResult}
    (h : ResK A r (fun x => StepGood A p n (k x) a) a) :
    StepGood A p n (Clif.StepResult.ofRes r k) a := by
  revert h
  cases r with
  | ok x => intro h; exact h
  | trap c => intro h; exact h
  | stuck m => intro _; trivial

/-- A non-`call` statement. -/
theorem GoodF.stmt {A : Act} {p : Clif.Program} {n : Nat} {F : Clif.Function} {regs : Clif.Regs}
    {slots : List (Clif.SlotId × Nat)} {st : Clif.Stmt} {rest : List Clif.Stmt}
    {term : Clif.Terminator} {mem : Clif.Mem} {a : ArmState}
    (hnc : isCall st.inst = false)
    (k : ResK A (Clif.evalInst ⟨F, regs, slots, st :: rest, term⟩ mem st.inst)
      (fun r => (regs.setMany st.results r.1).elim True
        (fun regs' => GoodF A p n (cst F regs' slots rest term r.2) a)) a) :
    GoodF A p n (cst F regs slots (st :: rest) term mem) a := by
  have hc : ∀ fn args, st.inst ≠ .call fn args := by
    intro fn args h; rw [h] at hnc; simp [isCall] at hnc
  apply GoodF.ofStep
  rw [Clif.step_inst _ _ _ st rest rfl hc]
  apply StepGood.ofRes
  revert k
  cases Clif.evalInst ⟨F, regs, slots, st :: rest, term⟩ mem st.inst with
  | ok x =>
    intro k
    obtain ⟨vals, mem'⟩ := x
    simp only [ResK] at k ⊢
    simp only [Clif.continueWith]
    cases hs : regs.setMany st.results vals with
    | none => trivial
    | some regs' =>
      simp only [hs, Option.elim] at k
      exact k
  | trap c => intro k; exact k
  | stuck m => intro _; trivial

/-- `jump`: the edge of a cut-point path (consumes one unit of the fuel bound). -/
theorem GoodF.jump {A : Act} {p : Clif.Program} {n m : Nat} {F : Clif.Function} {regs : Clif.Regs}
    {slots : List (Clif.SlotId × Nat)} {dest : Clif.BlockCall} {mem : Clif.Mem} {a : ArmState}
    (k : ResK A (Clif.enterBlock ⟨F, regs, slots, [], .jump dest⟩ dest)
      (fun fr => GoodF A p n ⟨fr, [], mem⟩ a) a) (hm : m ≤ n + 1 := by omega) :
    GoodF A p m (cst F regs slots [] (.jump dest) mem) a := by
  refine GoodF.mono ?_ hm
  apply GoodF.ofStepDec
  rw [Clif.step_term _ _ _ rfl]
  exact StepGood.ofRes k

/-- `brif`: one premise per direction. -/
theorem GoodF.brif {A : Act} {p : Clif.Program} {n m : Nat} {F : Clif.Function}
    {regs : Clif.Regs} {slots : List (Clif.SlotId × Nat)} {c : Clif.ValueId}
    {t e : Clif.BlockCall} {mem : Clif.Mem} {a : ArmState}
    (k : ResK A (Clif.Frame.get ⟨F, regs, slots, [], .brif c t e⟩ c) (fun cv =>
      (Clif.Sem.truthy cv.bits = true →
        ResK A (Clif.enterBlock ⟨F, regs, slots, [], .brif c t e⟩ t)
          (fun fr => GoodF A p n ⟨fr, [], mem⟩ a) a) ∧
      (Clif.Sem.truthy cv.bits = false →
        ResK A (Clif.enterBlock ⟨F, regs, slots, [], .brif c t e⟩ e)
          (fun fr => GoodF A p n ⟨fr, [], mem⟩ a) a)) a)
    (hm : m ≤ n + 1 := by omega) :
    GoodF A p m (cst F regs slots [] (.brif c t e) mem) a := by
  refine GoodF.mono ?_ hm
  apply GoodF.ofStepDec
  rw [Clif.step_term _ _ _ rfl]
  refine StepGood.ofRes (Validate.ResK_mono k fun cv h => StepGood.ofRes ?_)
  cases hc : Clif.Sem.truthy cv.bits
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact h.2 hc
  · simp only [hc, ↓reduceIte]; exact h.1 hc

/-- `br_table`. -/
theorem GoodF.brTable {A : Act} {p : Clif.Program} {n m : Nat} {F : Clif.Function}
    {regs : Clif.Regs} {slots : List (Clif.SlotId × Nat)} {x : Clif.ValueId}
    {dflt : Clif.BlockCall} {table : List Clif.BlockCall} {mem : Clif.Mem} {a : ArmState}
    (k : ResK A (Clif.Frame.get ⟨F, regs, slots, [], .brTable x dflt table⟩ x) (fun xv =>
      ResK A (Clif.enterBlock ⟨F, regs, slots, [], .brTable x dflt table⟩
          (table[xv.toNat]?.getD dflt))
        (fun fr => GoodF A p n ⟨fr, [], mem⟩ a) a) a) (hm : m ≤ n + 1 := by omega) :
    GoodF A p m (cst F regs slots [] (.brTable x dflt table) mem) a := by
  refine GoodF.mono ?_ hm
  apply GoodF.ofStepDec
  rw [Clif.step_term _ _ _ rfl]
  exact StepGood.ofRes (Validate.ResK_mono k fun _ h => StepGood.ofRes h)

/-- `return`: the Arm side must reach the return point. -/
theorem GoodF.ret {A : Act} {p : Clif.Program} {n : Nat} {F : Clif.Function} {regs : Clif.Regs}
    {slots : List (Clif.SlotId × Nat)} {xs : List Clif.ValueId} {mem : Clif.Mem} {a : ArmState}
    (k : ResK A (Clif.Frame.getMany ⟨F, regs, slots, [], .ret xs⟩ xs) (fun vals =>
      ResK A (Clif.checkTys s!"return values of %{F.name}" vals
          (Clif.AbiParam.tys F.sig.returns))
        (fun _ => Reach (fun a' => RetOK A vals (mem.free (slots.map (·.2))) a' ∨
          StackOut A a') a) a) a) :
    GoodF A p n (cst F regs slots [] (.ret xs) mem) a := by
  apply GoodF.ofStep
  rw [Clif.step_term _ _ _ rfl]
  simp only [Clif.stepTerm]
  refine StepGood.ofRes (Validate.ResK_mono k fun vals h => ?_)
  simp only [Clif.returnValues]
  exact StepGood.ofRes h

/-- `trap code`: the Arm side must reach a trap site with that code. -/
theorem GoodF.trapTerm {A : Act} {p : Clif.Program} {n : Nat} {F : Clif.Function}
    {regs : Clif.Regs} {slots : List (Clif.SlotId × Nat)} {code : Clif.TrapCode}
    {mem : Clif.Mem} {a : ArmState}
    (k : Reach (fun a' => TrapOK A code a' ∨ StackOut A a') a) :
    GoodF A p n (cst F regs slots [] (.trap code) mem) a :=
  GoodF.trapped (Clif.step_term _ _ _ rfl) k

end Validate

/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.

# Translation validation: the simulation statement (M3)

Definitions shared by every generated per-function proof (`docs/contracts/validator.md`).

* `World` — the linked program: the Arm code map, the global trap table, the stack region
  `[lim, top)`, the GOT entries, and the semantics of extern callees (`Clif.Env`).
* `Act` — one activation of the validated function: the Arm entry state `a0`, the CLIF entry
  memory `m0`, and the function's own stack-slot allocations.
* `RetOK` / `TrapOK` / `StackOut` — the Arm-side outcomes; `Matches` relates a CLIF outcome to
  an Arm state (every Arm outcome is "reaches, within finitely many steps").
* `GoodF A p n c a` — every CLIF run of at most `n` steps from `c` is matched by the Arm run
  from `a`. The rules `GoodF.arm`, `GoodF.clif`, `GoodF.reach`, … and the fuel induction
  `GoodF.induct` are what the generated proofs are built from.
-/
import FV.Clif
import FV.Arm

namespace Validate

open Arm

/-! ## Reachability on the Arm side -/

/-- The Arm run from `a` reaches a state satisfying `Q` after finitely many steps. -/
def Reach (Q : ArmState → Prop) (a : ArmState) : Prop := ∃ n, Q (run n a)

theorem Reach.here {Q : ArmState → Prop} {a : ArmState} (h : Q a) : Reach Q a := ⟨0, h⟩

theorem Reach.step {Q : ArmState → Prop} {a : ArmState} (h : Reach Q (stepi a)) : Reach Q a := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by simpa [run] using hn⟩

theorem Reach.run {Q : ArmState → Prop} {a : ArmState} (k : Nat) (h : Reach Q (Arm.run k a)) :
    Reach Q a := by
  obtain ⟨n, hn⟩ := h
  exact ⟨k + n, by rw [run_plus]; exact hn⟩

theorem Reach.bind {Q R : ArmState → Prop} {a : ArmState} (h : Reach Q a)
    (k : ∀ a', Q a' → Reach R a') : Reach R a := by
  obtain ⟨n, hn⟩ := h
  exact Reach.run n (k _ hn)

theorem Reach.mono {Q R : ArmState → Prop} {a : ArmState} (h : Reach Q a)
    (k : ∀ a', Q a' → R a') : Reach R a := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, k _ hn⟩

/-! ## Byte addresses and allocations -/

/-- `x` lies in allocation `al`. -/
def Has (al : Clif.Alloc) (x : Nat) : Prop := al.base ≤ x ∧ x < al.base + al.size

/-- `x` lies in a live allocation of `m`. -/
def MemHas (m : Clif.Mem) (x : Nat) : Prop := ∃ al ∈ m.allocs, Has al x

/-- CLIF memory `m` agrees with the Arm memory of `a` on every initialised byte of every live
allocation. -/
def MemRel (m : Clif.Mem) (a : ArmState) : Prop :=
  ∀ x b, MemHas m x → m.bytes x = some b → read_mem (BitVec.ofNat 64 x) a = b

/-- `al` lies below `2^64` (addresses do not wrap inside it). -/
def Bounded (al : Clif.Alloc) : Prop := al.base + al.size ≤ 2 ^ 64

/-- `[x, x + n)` and allocation `al` are disjoint. -/
def Disjoint (al : Clif.Alloc) (x n : Nat) : Prop := al.base + al.size ≤ x ∨ x + n ≤ al.base

/-! ## The linked program -/

/-- The linked program and the environment of the validated function. -/
structure World where
  /-- Code of the whole linked image. -/
  prog : Program
  /-- Trap table of the whole image: trap code of each trap site. -/
  traps : BitVec 64 → Option Clif.TrapCode
  /-- The stack region is `[lim, top)`. -/
  lim : BitVec 64
  top : BitVec 64
  /-- GOT entries: (slot address, callee address). -/
  got : List (BitVec 64 × BitVec 64)
  /-- Semantics of extern callees. -/
  env : Clif.Env

/-- `al` avoids the stack region and every GOT slot. -/
def World.Avoid (W : World) (al : Clif.Alloc) : Prop :=
  Disjoint al W.lim.toNat (W.top.toNat - W.lim.toNat) ∧ ∀ g ∈ W.got, Disjoint al g.1.toNat 8

/-- The GOT entries hold the callee addresses. -/
def GotOK (W : World) (a : ArmState) : Prop := ∀ g ∈ W.got, read_mem_bytes 8 g.1 a = g.2

/-- Well-formedness of a world: the stack region does not wrap, GOT slots lie outside it and
do not wrap. -/
def World.WF (W : World) : Prop :=
  W.lim.toNat ≤ W.top.toNat ∧
  ∀ g ∈ W.got, g.1.toNat + 8 ≤ 2 ^ 64 ∧
    (g.1.toNat + 8 ≤ W.lim.toNat ∨ W.top.toNat ≤ g.1.toNat)

/-! ## An activation -/

/-- One activation of a validated function. -/
structure Act where
  W : World
  /-- Arm state at function entry. -/
  a0 : ArmState
  /-- CLIF memory at function entry (before the function's own stack slots exist). -/
  m0 : Clif.Mem
  /-- The function's own stack-slot allocations (placed in its Arm frame). -/
  slots : List Clif.Alloc
  /-- Bytes of stack arguments above the entry SP. -/
  argBytes : Nat

/-- Entry stack pointer. -/
abbrev Act.sp0 (A : Act) : BitVec 64 := r (StateField.GPR 31#5) A.a0

/-- Callee-saved general-purpose registers (x19–x29), SP, and the low 64 bits of v8–v15
(AAPCS64) hold their entry values. -/
def CSaved (a0 a : ArmState) : Prop :=
  r (StateField.GPR 19#5) a = r (StateField.GPR 19#5) a0 ∧
  r (StateField.GPR 20#5) a = r (StateField.GPR 20#5) a0 ∧
  r (StateField.GPR 21#5) a = r (StateField.GPR 21#5) a0 ∧
  r (StateField.GPR 22#5) a = r (StateField.GPR 22#5) a0 ∧
  r (StateField.GPR 23#5) a = r (StateField.GPR 23#5) a0 ∧
  r (StateField.GPR 24#5) a = r (StateField.GPR 24#5) a0 ∧
  r (StateField.GPR 25#5) a = r (StateField.GPR 25#5) a0 ∧
  r (StateField.GPR 26#5) a = r (StateField.GPR 26#5) a0 ∧
  r (StateField.GPR 27#5) a = r (StateField.GPR 27#5) a0 ∧
  r (StateField.GPR 28#5) a = r (StateField.GPR 28#5) a0 ∧
  r (StateField.GPR 29#5) a = r (StateField.GPR 29#5) a0 ∧
  r (StateField.GPR 31#5) a = r (StateField.GPR 31#5) a0 ∧
  VSaved a0 a
where
  /-- Low 64 bits of v8–v15. -/
  VSaved (a0 a : ArmState) : Prop :=
    ∀ i : BitVec 5, 8 ≤ i.toNat → i.toNat < 16 →
      (r (StateField.SFP i) a).setWidth 64 = (r (StateField.SFP i) a0).setWidth 64

/-- AAPCS64 location of argument/result `i` (integer types up to 64 bits): `x0`–`x7`, then
8-byte stack slots at `SP + 8 * (i - 8)`. -/
def ValAt (a : ArmState) (sp : BitVec 64) (i : Nat) (v : Clif.Val) : Prop :=
  if i < 8 then (r (StateField.GPR (BitVec.ofNat 5 i)) a).setWidth v.ty.width = v.bits
  else (read_mem_bytes 8 (sp + BitVec.ofNat 64 (8 * (i - 8))) a).setWidth v.ty.width = v.bits

/-- Integer types that fit a general-purpose register. -/
def ScalarTy (t : Clif.Ty) : Prop := t.width ≤ 64

/-- The arguments `vals` are in their AAPCS64 locations. -/
def ArgsAt (a : ArmState) (vals : List Clif.Val) : Prop :=
  ∀ i (h : i < vals.length), ValAt a (r (StateField.GPR 31#5) a) i vals[i]

/-- The results `vals` are in `x0`, `x1`, … (at most eight). -/
def ResultsAt (a : ArmState) (vals : List Clif.Val) : Prop :=
  vals.length ≤ 8 ∧ ∀ i (h : i < vals.length), ValAt a 0 i vals[i]

/-- Allocation discipline during the activation: every live allocation is bounded and is an
entry allocation, an own stack slot, or avoids the stack region and the GOT. -/
def AllocsOK (A : Act) (m : Clif.Mem) : Prop :=
  ∀ al ∈ m.allocs, Bounded al ∧ (al ∈ A.m0.allocs ∨ al ∈ A.slots ∨ A.W.Avoid al)

/-- Allocation discipline at return: the own stack slots are gone. -/
def AllocsRet (A : Act) (m : Clif.Mem) : Prop :=
  ∀ al ∈ m.allocs, Bounded al ∧ (al ∈ A.m0.allocs ∨ A.W.Avoid al)

/-- The stack above the entry SP (the callers' frames), outside the entry allocations, is
unchanged. -/
def Pres (A : Act) (a : ArmState) : Prop :=
  ∀ x : Nat, A.sp0.toNat ≤ x → x < A.W.top.toNat → ¬ MemHas A.m0 x →
    read_mem (BitVec.ofNat 64 x) a = read_mem (BitVec.ofNat 64 x) A.a0

/-- Arm state at the return point, matching CLIF result `vals` with memory `m`. -/
def RetOK (A : Act) (vals : List Clif.Val) (m : Clif.Mem) (a : ArmState) : Prop :=
  read_pc a = r (StateField.GPR 30#5) A.a0 ∧ read_err a = .None ∧ a.program = A.W.prog ∧
  CSaved A.a0 a ∧ ResultsAt a vals ∧ MemRel m a ∧ AllocsRet A m ∧ Pres A a ∧ GotOK A.W a

/-- Arm state at a trap site whose trap code is `c`. -/
def TrapOK (A : Act) (c : Clif.TrapCode) (a : ArmState) : Prop :=
  A.W.traps (read_pc a) = some c

/-- Stack exhaustion: SP is below the stack limit. -/
def StackOut (A : Act) (a : ArmState) : Prop :=
  (r (StateField.GPR 31#5) a).toNat < A.W.lim.toNat

/-- A CLIF outcome matched by the Arm run from `a`: a returned result by an Arm return with the
same results, a trap by an Arm trap site with the same code, unless the stack is exhausted
first. `stuck` (a violated CLIF precondition) and `outOfFuel` constrain nothing. -/
def Matches (A : Act) : Clif.Outcome → ArmState → Prop
  | .returned vals m, a => Reach (fun a' => RetOK A vals m a' ∨ StackOut A a') a
  | .trapped c, a => Reach (fun a' => TrapOK A c a' ∨ StackOut A a') a
  | .stuck _, _ => True
  | .outOfFuel, _ => True

/-- Every CLIF run of at most `n` steps from `c` (program `p`, environment `A.W.env`) is
matched by the Arm run from `a`. -/
def GoodF (A : Act) (p : Clif.Program) (n : Nat) (c : Clif.State) (a : ArmState) : Prop :=
  ∀ fuel ≤ n, Matches A (Clif.runLoop A.W.env p fuel c) a

/-! ## Rules -/

theorem Matches.reach {A : Act} {o : Clif.Outcome} {a : ArmState} {Q : ArmState → Prop}
    (h : Reach Q a) (k : ∀ a', Q a' → Matches A o a') : Matches A o a := by
  cases o with
  | returned vals m =>
    exact Reach.bind h fun a' h' => by have := k a' h'; simpa only [Matches] using this
  | trapped c =>
    exact Reach.bind h fun a' h' => by have := k a' h'; simpa only [Matches] using this
  | stuck _ => trivial
  | outOfFuel => trivial

/-- Arm-side progress: the Arm state may be advanced along any finite run. -/
theorem GoodF.reach {A : Act} {p : Clif.Program} {n : Nat} {c : Clif.State} {a : ArmState}
    {Q : ArmState → Prop} (h : Reach Q a) (k : ∀ a', Q a' → GoodF A p n c a') :
    GoodF A p n c a :=
  fun fuel hf => Matches.reach h fun a' h' => k a' h' fuel hf

/-- One Arm step. -/
theorem GoodF.arm {A : Act} {p : Clif.Program} {n : Nat} {c : Clif.State} {a : ArmState}
    (h : GoodF A p n c (stepi a)) : GoodF A p n c a :=
  GoodF.reach (Reach.step (Reach.here rfl)) fun _ h' => h' ▸ h

theorem GoodF.zero (A : Act) (p : Clif.Program) (c : Clif.State) (a : ArmState) :
    GoodF A p 0 c a := by
  intro fuel hf
  have : fuel = 0 := by omega
  subst this
  trivial

theorem GoodF.mono {A : Act} {p : Clif.Program} {n m : Nat} {c : Clif.State} {a : ArmState}
    (h : GoodF A p n c a) (hm : m ≤ n) : GoodF A p m c a :=
  fun fuel hf => h fuel (by omega)

/-- Stack exhaustion reached: nothing else to show. -/
theorem GoodF.stackOut {A : Act} {p : Clif.Program} {n : Nat} {c : Clif.State} {a : ArmState}
    (h : Reach (StackOut A) a) : GoodF A p n c a := by
  intro fuel _
  cases Clif.runLoop A.W.env p fuel c with
  | returned vals m => exact Reach.mono h fun _ h' => Or.inr h'
  | trapped c => exact Reach.mono h fun _ h' => Or.inr h'
  | stuck _ => trivial
  | outOfFuel => trivial

/-- One CLIF step that does not finish (fuel is not consumed from `n`). -/
theorem GoodF.clif {A : Act} {p : Clif.Program} {n : Nat} {c c' : Clif.State} {a : ArmState}
    (h : Clif.step A.W.env p c = .next c') (k : GoodF A p n c' a) : GoodF A p n c a := by
  intro fuel hf
  cases fuel with
  | zero => trivial
  | succ f => rw [Clif.runLoop_succ, h]; exact k f (by omega)

/-- One CLIF step that consumes one unit of the fuel bound (used once per cut-point path). -/
theorem GoodF.clifDec {A : Act} {p : Clif.Program} {n : Nat} {c c' : Clif.State}
    {a : ArmState} (h : Clif.step A.W.env p c = .next c') (k : GoodF A p n c' a) :
    GoodF A p (n + 1) c a := by
  intro fuel hf
  cases fuel with
  | zero => trivial
  | succ f => rw [Clif.runLoop_succ, h]; exact k f (by omega)

theorem GoodF.done {A : Act} {p : Clif.Program} {n : Nat} {c : Clif.State} {a : ArmState}
    {vals : List Clif.Val} {m : Clif.Mem} (h : Clif.step A.W.env p c = .done vals m)
    (k : Reach (fun a' => RetOK A vals m a' ∨ StackOut A a') a) : GoodF A p n c a := by
  intro fuel hf
  cases fuel with
  | zero => trivial
  | succ f => rw [Clif.runLoop_succ, h]; exact k

theorem GoodF.trapped {A : Act} {p : Clif.Program} {n : Nat} {c : Clif.State} {a : ArmState}
    {code : Clif.TrapCode} (h : Clif.step A.W.env p c = .trapped code)
    (k : Reach (fun a' => TrapOK A code a' ∨ StackOut A a') a) : GoodF A p n c a := by
  intro fuel hf
  cases fuel with
  | zero => trivial
  | succ f => rw [Clif.runLoop_succ, h]; exact k

theorem GoodF.stuck {A : Act} {p : Clif.Program} {n : Nat} {c : Clif.State} {a : ArmState}
    {msg : String} (h : Clif.step A.W.env p c = .stuck msg) : GoodF A p n c a := by
  intro fuel hf
  cases fuel with
  | zero => trivial
  | succ f => rw [Clif.runLoop_succ, h]; trivial

/-- Fuel induction over cut points: if from every cut point, with the hypothesis that every
cut point is good for `n`, the state is good for `n + 1`, then every cut point is good. -/
theorem GoodF.induct {A : Act} {p : Clif.Program} (Cut : Clif.State → ArmState → Prop)
    (step : ∀ n c a, Cut c a → (∀ c' a', Cut c' a' → GoodF A p n c' a') →
      GoodF A p (n + 1) c a) :
    ∀ n c a, Cut c a → GoodF A p n c a := by
  intro n
  induction n with
  | zero => intro c a _; exact GoodF.zero A p c a
  | succ n ih => intro c a h; exact step n c a h ih

end Validate

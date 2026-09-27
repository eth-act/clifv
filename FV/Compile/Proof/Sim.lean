import FV.Compile.Proof.Gen
import FV.Compile.Proof.Heap
import FV.Compile.Proof.Check

/-!
# Simulation context and single-instruction steps

`Ctx`: the constants of one activation of a compiled function (program, function, emitter
context, frame slot bases, callers, result buffer). `Inv c H s`: the machine state `s` runs
this activation and its memory models the heap `H` with the frame's own allocations intact.
`Exh`: the resource-exhaustion outcomes (`stk_ovf`, `oomTrap`), the only way a run of
compiled code may end early.
-/

set_option autoImplicit false

namespace Compile.Proof

open Compile Clif
open DSL (Ty IntW)

/-- The resource-exhaustion outcomes. -/
def Exh (o : Outcome) : Prop := ∃ c, o = .trapped c ∧ (c = .stkOvf ∨ c = oomTrap)

/-- One activation of a compiled function. -/
structure Ctx where
  P : Program
  F : Function
  fc : FnCtx
  sl : List (SlotId × Nat)
  K : List (Frame × List ValueId)
  /-- base address of the result buffer (buffer mode) -/
  buf : Option Nat
  /-- the parameter ids (`ctx`, `retBuf`) are below `n0` -/
  n0 : Nat

namespace Ctx

variable (c : Ctx)

def SlotsOK (m : Mem) (H : Heap) : Prop :=
  ∀ k ss, c.F.slots.lookup k = some ss → ∃ b, c.sl.lookup k = some b ∧
    (⟨b, ss.size⟩ : Alloc) ∈ m.allocs ∧ b % 16 = 0 ∧ ObjFree H b

def BufOK (m : Mem) (H : Heap) : Prop :=
  ∀ b, c.buf = some b → (⟨b, 8 * (flat c.fc.abi.result).length⟩ : Alloc) ∈ m.allocs ∧ ObjFree H b

def RegsOK (r : Regs) : Prop :=
  (∀ x, c.fc.ctx = some x → x < c.n0 ∧ ∃ v : BitVec 64, r x = some ⟨.i64, v⟩) ∧
  (∀ p, c.fc.retBuf = some p → p < c.n0 ∧ ∃ b, c.buf = some b ∧ r p = some (Val.ofNat .i64 b))

/-- The state invariant of running `c.F`. -/
structure Inv (H : Heap) (s : State) : Prop where
  func : s.frame.func = c.F
  slots : s.frame.slots = c.sl
  callers : s.callers = c.K
  mem : MemModels s.mem H
  slotsOK : c.SlotsOK s.mem H
  bufOK : c.BufOK s.mem H
  regs : c.RegsOK s.frame.regs

theorem RegsOK.agree {c : Ctx} {r r' : Regs} {n : Nat} (h : c.RegsOK r) (ha : Agree r r' n)
    (hn : c.n0 ≤ n) : c.RegsOK r' := by
  refine ⟨fun x hx => ?_, fun p hp => ?_⟩
  · obtain ⟨hlt, v, hv⟩ := h.1 x hx
    exact ⟨hlt, v, by rw [ha x (Nat.lt_of_lt_of_le hlt hn)]; exact hv⟩
  · obtain ⟨hlt, b, hb, hv⟩ := h.2 p hp
    exact ⟨hlt, b, hb, by rw [ha p (Nat.lt_of_lt_of_le hlt hn)]; exact hv⟩

end Ctx

/-! ## Heap growth keeps the frame's allocations free of objects -/

/-- `H'` only adds objects, or moves arrays to addresses `≥ n`, relative to `H`. -/
def Grows (H H' : Heap) (n : Nat) : Prop :=
  ∀ h d es, H' h = some (d, es) → H h = some (d, es) ∨ (n ≤ d ∧ (H h = none → n ≤ h))

theorem Grows.refl (H : Heap) (n : Nat) : Grows H H n := fun _ _ _ h => .inl h

theorem Grows.trans {H₁ H₂ H₃ : Heap} {n₁ n₂ : Nat} (h₁ : Grows H₁ H₂ n₁) (h₂ : Grows H₂ H₃ n₂)
    (hn : n₁ ≤ n₂) : Grows H₁ H₃ n₁ := fun h d es hH => by
  rcases h₂ h d es hH with h' | ⟨hd, hh⟩
  · exact h₁ h d es h'
  · right; refine ⟨by omega, fun hn₁ => ?_⟩
    cases hH₂ : H₂ h with
    | none => have := hh hH₂; omega
    | some p =>
      obtain ⟨d', es'⟩ := p
      rcases h₁ h d' es' hH₂ with h'' | ⟨_, hh'⟩
      · rw [hn₁] at h''; cases h''
      · exact hh' hn₁

theorem ObjFree.grows {H H' : Heap} {n b : Nat} (hf : ObjFree H b) (hg : Grows H H' n)
    (hb : b < n) : ObjFree H' b := fun h d es hH => by
  rcases hg h d es hH with h' | ⟨hd, hh⟩
  · exact hf h d es h'
  · refine ⟨fun he => ?_, by omega⟩
    subst he
    cases hH₀ : H b with
    | none => have := hh hH₀; omega
    | some p => exact (hf b p.1 p.2 hH₀).1 rfl

theorem Grows.set_new {H : Heap} {h d n : Nat} {es : List (Word × Word)} (hh : n ≤ h)
    (hd : n ≤ d) : Grows H (H.set h (d, es)) n := fun x d' es' hx => by
  by_cases e : x = h
  · subst e; simp at hx; obtain ⟨rfl, rfl⟩ := hx; exact .inr ⟨hd, fun _ => hh⟩
  · rw [Heap.set_other _ _ e] at hx; exact .inl hx

theorem Grows.set_old {H : Heap} {h d n : Nat} {es : List (Word × Word)} (hd : n ≤ d)
    (hH : H h ≠ none) : Grows H (H.set h (d, es)) n := fun x d' es' hx => by
  by_cases e : x = h
  · subst e; simp at hx; obtain ⟨rfl, rfl⟩ := hx
    exact .inr ⟨hd, fun hn => absurd hn hH⟩
  · rw [Heap.set_other _ _ e] at hx; exact .inl hx

/-! ## Single instructions and branches -/

section
variable {E : Env} {P : Program}

theorem reach_inst1 {F : Function} {cg : CG} {s : State} {i : Inst} {v : Val} {m' : Mem}
    {Q : State → Prop} {X : Outcome → Prop}
    (hG : Good F ((inst1 i).run cg).2) (hAt : At F cg s.frame)
    (hnc : ∀ fn args, i ≠ .call fn args)
    (hev : evalInst s.frame s.mem i = .ok ([v], m'))
    (k : ∀ fr' : Frame, At F ((inst1 i).run cg).2 fr' → fr'.regs = s.frame.regs.set cg.nextVal v →
      fr'.func = s.frame.func → fr'.slots = s.frame.slots →
      Reach E P Q X { s with frame := fr', mem := m' }) :
    Reach E P Q X s := by
  obtain ⟨rest, hb, hA'⟩ := At.emit (cg := cg) (cg' := ((inst1 i).run cg).2)
    (st := ⟨[cg.nextVal], i⟩) rfl rfl hG hAt
  exact .next (step_inst1 (regs' := s.frame.regs.set cg.nextVal v) hb
    (fun fn args => hnc fn args) hev (by simp)) (k _ (hA'.congr rfl rfl rfl) rfl rfl rfl)

theorem reach_iconst {F : Function} {cg : CG} {s : State} {ty : Clif.Ty} {n : Nat}
    {Q : State → Prop} {X : Outcome → Prop}
    (hG : Good F ((iconstN ty n).run cg).2) (hAt : At F cg s.frame)
    (k : ∀ fr' : Frame, At F ((iconstN ty n).run cg).2 fr' →
      fr'.regs = s.frame.regs.set cg.nextVal ⟨ty, BitVec.ofNat ty.width n⟩ →
      fr'.func = s.frame.func → fr'.slots = s.frame.slots →
      Reach E P Q X { s with frame := fr' }) :
    Reach E P Q X s :=
  reach_inst1 (i := .iconst ty (BitVec.ofNat ty.width n)) hG hAt (fun _ _ h => by cases h) rfl k

end

theorem getAs_of {fr : Frame} {x : ValueId} {ty : Clif.Ty} {a : BitVec ty.width}
    (h : fr.regs x = some ⟨ty, a⟩) : fr.getAs x ty = .ok a := by
  simp [Frame.getAs, Frame.get, h]

theorem get_of {fr : Frame} {x : ValueId} {v : Val} (h : fr.regs x = some v) :
    fr.get x = .ok v := by
  simp [Frame.get, h]

/-- Entering a block with parameters `ps` (distinct) from arguments holding `vals`. -/
theorem enterBlock_of {fr : Frame} {b : BlockId} {args : List ValueId} {blk : Block}
    {vals : List Val} (hb : fr.func.block? b = some blk) (hv : RegsHas fr.regs args vals)
    (ht : vals.map (·.ty) = blk.params.map (·.2)) (hnd : (blk.params.map (·.1)).Nodup) :
    ∃ regs', enterBlock fr ⟨b, args⟩ =
        .ok { fr with regs := regs', body := blk.body, term := blk.term } ∧
      RegsHas regs' (blk.params.map (·.1)) vals ∧
      ∀ y, y ∉ blk.params.map (·.1) → regs' y = fr.regs y := by
  have hl : (blk.params.map (·.1)).length = vals.length := by
    have := congrArg List.length ht; simp at this ⊢; omega
  obtain ⟨regs', hr⟩ := setMany_some fr.regs _ _ hl
  exact ⟨regs', enterBlock_ok hb hv ht hr, setMany_has hnd hr, fun y hy => setMany_other hr hy⟩

end Compile.Proof

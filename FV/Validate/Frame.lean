/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.

# Frame lemmas: what register/PC/flag writes and frame stores leave unchanged
-/
import FV.Validate.Basic
import FV.Validate.Attr

namespace Validate

open Arm

theorem read_mem_w (fld : StateField) (v : state_value fld) (s : ArmState) (x : BitVec 64) :
    read_mem x (w fld v s) = read_mem x s := read_mem_of_w

@[simp, vsimp] theorem MemRel_w {m : Clif.Mem} {fld : StateField} {v : state_value fld} {s : ArmState} :
    MemRel m (w fld v s) ↔ MemRel m s := by
  simp only [MemRel, read_mem_w]

@[simp, vsimp] theorem Pres_w {A : Act} {fld : StateField} {v : state_value fld} {s : ArmState} :
    Pres A (w fld v s) ↔ Pres A s := by
  simp only [Pres, read_mem_w]

@[simp, vsimp] theorem GotOK_w {W : World} {fld : StateField} {v : state_value fld} {s : ArmState} :
    GotOK W (w fld v s) ↔ GotOK W s := by
  simp only [GotOK, read_mem_bytes_of_w]

theorem VSaved_w_of {a0 s : ArmState} {fld : StateField} {v : state_value fld}
    (h : ∀ i : BitVec 5, 8 ≤ i.toNat → i.toNat < 16 → fld ≠ StateField.SFP i) :
    VSaved a0 (w fld v s) ↔ VSaved a0 s := by
  unfold VSaved
  constructor
  · intro hv i h1 h2
    have := hv i h1 h2
    rwa [r_of_w_different (fun e => h i h1 h2 e.symm)] at this
  · intro hv i h1 h2
    rw [r_of_w_different (fun e => h i h1 h2 e.symm)]
    exact hv i h1 h2

@[simp, vsimp] theorem VSaved_w_gpr {a0 s : ArmState} {j : BitVec 5} {v : BitVec 64} :
    VSaved a0 (w (StateField.GPR j) v s) ↔ VSaved a0 s :=
  VSaved_w_of (by intro i _ _ h; cases h)
@[simp, vsimp] theorem VSaved_w_pc {a0 s : ArmState} {v : BitVec 64} :
    VSaved a0 (w StateField.PC v s) ↔ VSaved a0 s :=
  VSaved_w_of (by intro i _ _ h; cases h)
@[simp, vsimp] theorem VSaved_w_flag {a0 s : ArmState} {f : PFlag} {v : BitVec 1} :
    VSaved a0 (w (StateField.FLAG f) v s) ↔ VSaved a0 s :=
  VSaved_w_of (by intro i _ _ h; cases h)
@[simp, vsimp] theorem VSaved_w_err {a0 s : ArmState} {v : StateError} :
    VSaved a0 (w StateField.ERR v s) ↔ VSaved a0 s :=
  VSaved_w_of (by intro i _ _ h; cases h)
theorem VSaved_w_sfp {a0 s : ArmState} {j : BitVec 5} {v : BitVec 128}
    (hj : j.toNat < 8 ∨ 16 ≤ j.toNat) :
    VSaved a0 (w (StateField.SFP j) v s) ↔ VSaved a0 s :=
  VSaved_w_of (by intro i h1 h2 h; cases h; omega)

@[simp, vsimp] theorem VSaved_write_mem_bytes {a0 s : ArmState} {n : Nat} {x : BitVec 64}
    {v : BitVec (n * 8)} : VSaved a0 (write_mem_bytes n x v s) ↔ VSaved a0 s := by
  simp only [VSaved, r_of_write_mem_bytes]

@[simp, vsimp] theorem RegsHold_nil (a : ArmState) (i : Nat) : RegsHold a i [] = True := rfl
@[simp, vsimp] theorem RegsHold_cons (a : ArmState) (i : Nat) (v : Clif.Val) (vs : List Clif.Val) :
    RegsHold a i (v :: vs) =
      ((r (StateField.GPR (BitVec.ofNat 5 i)) a).setWidth v.ty.width = v.bits ∧
        RegsHold a (i + 1) vs) := rfl

end Validate

namespace Validate

theorem MemHas_free {m : Clif.Mem} {bases : List Nat} {x : Nat} (h : MemHas (m.free bases) x) :
    MemHas m x := by
  obtain ⟨al, hal, hx⟩ := h
  simp only [Clif.Mem.free, List.mem_filter] at hal
  exact ⟨al, hal.1, hx⟩

@[vsimp] theorem Ty.width_i8 : Clif.Ty.i8.width = 8 := rfl
@[vsimp] theorem Ty.width_i16 : Clif.Ty.i16.width = 16 := rfl
@[vsimp] theorem Ty.width_i32 : Clif.Ty.i32.width = 32 := rfl
@[vsimp] theorem Ty.width_i64 : Clif.Ty.i64.width = 64 := rfl
@[vsimp] theorem Ty.width_i128 : Clif.Ty.i128.width = 128 := rfl

@[vsimp] theorem as?_i8 (x : BitVec 8) : (Clif.Val.mk .i8 x).as? .i8 = some x := rfl
@[vsimp] theorem as?_i16 (x : BitVec 16) : (Clif.Val.mk .i16 x).as? .i16 = some x := rfl
@[vsimp] theorem as?_i32 (x : BitVec 32) : (Clif.Val.mk .i32 x).as? .i32 = some x := rfl
@[vsimp] theorem as?_i64 (x : BitVec 64) : (Clif.Val.mk .i64 x).as? .i64 = some x := rfl
@[vsimp] theorem as?_i128 (x : BitVec 128) : (Clif.Val.mk .i128 x).as? .i128 = some x := rfl

theorem MemRel_free {m : Clif.Mem} {a : Arm.ArmState} (bases : List Nat) (h : MemRel m a) :
    MemRel (m.free bases) a := fun x b hx hb => h x b (MemHas_free hx) hb

theorem AllocsRet_free {A : Act} {m : Clif.Mem} {bases : List Nat} (h : AllocsOK A m)
    (hb : ∀ al ∈ A.slots, al.base ∈ bases) : AllocsRet A (m.free bases) := by
  intro al hal
  simp only [Clif.Mem.free, List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hal
  obtain ⟨hal, hnb⟩ := hal
  obtain ⟨hbd, h1 | h2 | h3⟩ := h al hal
  · exact ⟨hbd, Or.inl h1⟩
  · exact absurd (hb al h2) hnb
  · exact ⟨hbd, Or.inr h3⟩

end Validate

namespace Validate

theorem retOK_of {A : Act} {a : Arm.ArmState} {vals : List Clif.Val} {mem : Clif.Mem}
    {bases : List Nat}
    (hpc : Arm.r Arm.StateField.PC a = Arm.r (Arm.StateField.GPR 30#5) A.a0)
    (hcom : Common A mem a) (hcs : CSGpr A.a0 a) (hres : ResultsAt a vals)
    (hb : ∀ al ∈ A.slots, al.base ∈ bases) : RetOK A vals (mem.free bases) a := by
  obtain ⟨hprog, herr, _, hmem, hal, hpres, hgot, hvs⟩ := hcom
  exact ⟨hpc, herr, hprog, ⟨hcs, hvs⟩, hres, MemRel_free _ hmem, AllocsRet_free hal hb, hpres, hgot⟩

end Validate

namespace Validate

theorem trapOK_of {A : Act} {a : Arm.ArmState} {base : BitVec 64}
    {sites : List (Nat × Clif.TrapCode)} (ht : TrapsAt A.W.traps base sites) (i : Nat)
    {off : Nat} {c : Clif.TrapCode} (hi : sites[i]? = some (off, c))
    (hpc : Arm.r Arm.StateField.PC a = base + BitVec.ofNat 64 off) : TrapOK A c a := by
  have hlt : i < sites.length := by
    rcases Nat.lt_or_ge i sites.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at hi
  have := ht i hlt
  rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hi
  rw [hi] at this
  simpa [TrapOK, Arm.read_pc, hpc] using this

end Validate

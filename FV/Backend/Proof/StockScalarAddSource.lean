import FV.Backend.Lowering.StockScalarAdd
import FV.Clif.Run

/-! Complete reference execution for the two-parameter scalar-add class. -/
set_option autoImplicit false
namespace Backend.Stock.ScalarAdd.Source
open D0

def argument (c : Configuration) (word : BitVec (valueType c).width) : Clif.Val := ⟨valueType c,word⟩
def frame (name : String) (c : Configuration) (runs : List Clif.RunCommand)
    (u v : BitVec (valueType c).width) : Clif.Frame := {
  func := source name c runs
  regs := (Clif.Regs.empty.set 0 (argument c u)).set 1 (argument c v)
  slots := []
  body := [⟨[2],.binary .iadd (valueType c) 0 1⟩]
  term := .ret [2] }

private theorem slots_empty (name : String) (c : Configuration) (runs : List Clif.RunCommand)
    (mem : Clif.Mem) : (Clif.enterSlots (source name c runs) mem).1 = [] := by
  unfold Clif.enterSlots
  cases h : mem.place with
  | none => rfl
  | some pl =>
    dsimp only
    cases h' : pl.frame (source name c runs).name with
    | none => rfl
    | some pair => rcases pair with ⟨d,off⟩; exact (Clif.initSlots_fst _ _ _ _ _).trans rfl

theorem source_entry (name : String) (c : Configuration) (runs : List Clif.RunCommand)
    (u v : BitVec (valueType c).width) (mem : Clif.Mem) :
    Clif.enterFunc (source name c runs) [argument c u,argument c v] mem =
      .ok (frame name c runs u v,(Clif.enterSlots (source name c runs) mem).2) := by
  simp [Clif.enterFunc,Clif.checkTys,Clif.AbiParam.tys,Clif.Function.entry?,
    source,D0.source,argument,frame,Clif.Regs.setMany,Clif.Res.ofOption,Clif.Res.check]
  exact slots_empty name c runs mem

theorem source_return (name : String) (c : Configuration) (runs : List Clif.RunCommand)
    (u v : BitVec (valueType c).width) (mem : Clif.Mem) (env : Clif.Env) (p : Clif.Program) :
    Clif.runLoop env p 2 ⟨frame name c runs u v,[],mem⟩ =
      .returned [argument c (u+v)] (mem.free []).leave := by
  cases c <;> rfl

theorem source_memory_roundtrip (name : String) (c : Configuration)
    (runs : List Clif.RunCommand) (mem : Clif.Mem) :
    (((Clif.enterSlots (source name c runs) mem).2).free []).leave = mem := by
  cases mem with
  | mk allocs bytes next symbols place =>
    cases place with
    | none => simp [Clif.enterSlots,source,D0.source,Clif.bumpSlots,Clif.Mem.free,Clif.Mem.leave]
    | some pl =>
      cases h : pl.frame name with
      | none => simp [Clif.enterSlots,source,D0.source,h,Clif.bumpSlots,Clif.Mem.free,Clif.Mem.leave]
      | some pair =>
        rcases pair with ⟨d,off⟩
        simp [Clif.enterSlots,source,D0.source,h,Clif.placeSlots,Clif.Mem.free,Clif.Mem.leave]

theorem complete_source_witness (name : String) (c : Configuration)
    (runs : List Clif.RunCommand) (u v : BitVec (valueType c).width) (mem : Clif.Mem) :
    ∃ (fr : Clif.Frame) (entered : Clif.Mem),
      Clif.enterFunc (source name c runs) [argument c u,argument c v] mem = .ok (fr,entered) ∧
      Clif.runLoop Clif.Env.empty {funcs := [source name c runs]} 2 ⟨fr,[],entered⟩ =
        .returned [argument c (u+v)] mem := by
  refine ⟨frame name c runs u v,(Clif.enterSlots (source name c runs) mem).2,
    source_entry name c runs u v mem,?_⟩
  rw [source_return,source_memory_roundtrip]

/-- Every high-bit pattern is admitted for narrow ABI arguments. -/
theorem dirty_machine_bits (c : Configuration) (word : BitVec (valueType c).width) (upper : Nat) :
    (BitVec.ofNat 64 (upper * 2^(valueType c).width + word.toNat)).setWidth
      (valueType c).width = word := by
  have bound : (valueType c).width ≤ 64 := by cases c <;> decide
  rw [BitVec.setWidth_ofNat_of_le bound]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,
    Nat.zero_mod,Nat.zero_add,Nat.mod_mod]
  exact Nat.mod_eq_of_lt word.isLt
end Backend.Stock.ScalarAdd.Source

import FV.Backend.Lowering.StockD0
import FV.Clif.Run

namespace Backend.Stock.D0

private def argument (c : Configuration) (word : BitVec (valueType c).width) : Clif.Val :=
  ⟨valueType c, word⟩

private def sourceFrame (name : String) (c : Configuration) (runs : List Clif.RunCommand)
    (word : BitVec (valueType c).width) : Clif.Frame := {
  func := source name c runs
  slots := [], body := [], term := .ret [0]
  regs := Clif.Regs.empty.set 0 (argument c word) }

private theorem slots_empty (name : String) (c : Configuration) (runs : List Clif.RunCommand)
    (mem : Clif.Mem) : (Clif.enterSlots (source name c runs) mem).1 = [] := by
  unfold Clif.enterSlots
  cases h : mem.place with
  | none => rfl
  | some pl =>
    dsimp only
    cases h' : pl.frame (source name c runs).name with
    | none => rfl
    | some pair => rcases pair with ⟨d, off⟩; rfl

/-- Genuine source entry for every input word, name, run metadata and memory,
including the actual placement-oracle stack update. -/
theorem source_entry (name : String) (c : Configuration) (runs : List Clif.RunCommand)
    (word : BitVec (valueType c).width) (mem : Clif.Mem) :
    Clif.enterFunc (source name c runs) [argument c word] mem =
      .ok (sourceFrame name c runs word, (Clif.enterSlots (source name c runs) mem).2) := by
  simp [Clif.enterFunc, Clif.checkTys, Clif.AbiParam.tys, Clif.Function.entry?,
    source, argument, sourceFrame,
    Clif.Regs.setMany, Clif.Res.ofOption, Clif.Res.check]
  exact slots_empty name c runs mem

/-- The complete source body returns that word with exactly the source memory
release/placement-oracle effects; no empty-oracle premise is added. -/
theorem source_return (name : String) (c : Configuration) (runs : List Clif.RunCommand)
    (word : BitVec (valueType c).width) (mem : Clif.Mem) :
    Clif.stepTerm Clif.Env.empty {funcs := []}
      ⟨sourceFrame name c runs word, [], mem⟩ (.ret [0]) =
        .done [argument c word] (mem.free []).leave := by
  simp [Clif.stepTerm, Clif.StepResult.ofRes, Clif.returnValues, Clif.checkTys,
    Clif.AbiParam.tys, Clif.Frame.getMany, Clif.Frame.get, Clif.Regs.set,
    source, argument, sourceFrame, Clif.Res.ofOption, Clif.Res.check]

/-- Every dirty high-bit pattern preserves the source word; there is no
zero-extension or clean-register premise. -/
theorem dirty_machine_bits (c : Configuration) (word : BitVec (valueType c).width)
    (upper : Nat) :
    (BitVec.ofNat 128 (upper * 2^(valueType c).width + word.toNat)).setWidth
      (valueType c).width = word := by
  have bound : (valueType c).width ≤ 128 := by cases c <;> decide
  rw [BitVec.setWidth_ofNat_of_le bound]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero,
    Nat.zero_mod, Nat.zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt word.isLt

/-- Entry and return balance the actual placement-oracle stack on arbitrary
memory, without assuming that the oracle is absent or the stack is nonempty. -/
theorem source_memory_roundtrip (name : String) (c : Configuration)
    (runs : List Clif.RunCommand) (mem : Clif.Mem) :
    (((Clif.enterSlots (source name c runs) mem).2).free []).leave = mem := by
  cases mem with
  | mk allocs bytes next symbols place =>
    cases place with
    | none => simp [Clif.enterSlots, source, Clif.bumpSlots, Clif.Mem.free, Clif.Mem.leave]
    | some pl =>
      cases h : pl.frame name with
      | none => simp [Clif.enterSlots, source, h, Clif.bumpSlots, Clif.Mem.free, Clif.Mem.leave]
      | some pair =>
        rcases pair with ⟨d, off⟩
        simp [Clif.enterSlots, source, h, Clif.placeSlots, Clif.Mem.free, Clif.Mem.leave]

/-- Complete source execution is inhabited for all words and arbitrary dirty
machine upper bits, including arbitrary initial memory and placement oracles. -/
theorem source_complete_witness (name : String) (c : Configuration)
    (runs : List Clif.RunCommand) (word : BitVec (valueType c).width)
    (upper : Nat) (mem : Clif.Mem) :
    ∃ (fr : Clif.Frame) (entered : Clif.Mem),
      Clif.enterFunc (source name c runs) [argument c word] mem = .ok (fr, entered) ∧
      Clif.stepTerm Clif.Env.empty {funcs := []} ⟨fr, [], entered⟩ (.ret [0]) =
        .done [argument c word] mem ∧
      (BitVec.ofNat 128 (upper * 2^(valueType c).width + word.toNat)).setWidth
        (valueType c).width = word := by
  refine ⟨sourceFrame name c runs word, (Clif.enterSlots (source name c runs) mem).2,
    source_entry name c runs word mem, ?_, dirty_machine_bits c word upper⟩
  rw [source_return, source_memory_roundtrip]

#print axioms source_entry
#print axioms source_return
#print axioms dirty_machine_bits
#print axioms source_memory_roundtrip
#print axioms source_complete_witness
end Backend.Stock.D0

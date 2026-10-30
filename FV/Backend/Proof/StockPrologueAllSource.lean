import FV.Clif.Run
import FV.Backend.Lowering.StockPrologue

namespace Backend.Stock.Prologue.AllConfigurations.Source
open D0

def argument (c : Configuration) (word : BitVec (valueType c).width) : Clif.Val :=
  ⟨valueType c, word⟩

def sourceFrame (name : String) (c : Configuration) (runs : List Clif.RunCommand)
    (word : BitVec (valueType c).width) : Clif.Frame := {
  func := source name c runs
  slots := [], body := [{inst := .nop}], term := .jump {block := 1, args := []}
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
    | some pair => rcases pair with ⟨d, off⟩; exact (Clif.initSlots_fst _ _ _ _ _).trans rfl

/-- Genuine source entry for every input word, name, run metadata and memory,
including the actual placement-oracle stack update. -/
theorem source_entry (name : String) (c : Configuration) (runs : List Clif.RunCommand)
    (word : BitVec (valueType c).width) (mem : Clif.Mem) :
    Clif.enterFunc (source name c runs) [argument c word] mem =
      .ok (sourceFrame name c runs word, (Clif.enterSlots (source name c runs) mem).2) := by
  simp [Clif.enterFunc, Clif.checkTys, Clif.AbiParam.tys, Clif.Function.entry?,
    Prologue.source, D0.source, argument, sourceFrame,
    Clif.Regs.setMany, Clif.Res.ofOption, Clif.Res.check]
  exact slots_empty name c runs mem

/-- The complete four-step prologue execution, with all original values and memory. -/
theorem source_return (name : String) (c : Configuration) (runs : List Clif.RunCommand)
    (word : BitVec (valueType c).width) (mem : Clif.Mem)
    (env : Clif.Env) (p : Clif.Program) :
    Clif.runLoop env p 4 ⟨sourceFrame name c runs word, [], mem⟩ =
      .returned [argument c word] (mem.free []).leave := by
  cases c <;> rfl

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
    | none => simp [Clif.enterSlots, Prologue.source, D0.source, Clif.bumpSlots, Clif.Mem.free, Clif.Mem.leave]
    | some pl =>
      cases h : pl.frame name with
      | none => simp [Clif.enterSlots, Prologue.source, D0.source, h, Clif.bumpSlots, Clif.Mem.free, Clif.Mem.leave]
      | some pair =>
        rcases pair with ⟨d, off⟩
        simp [Clif.enterSlots, Prologue.source, D0.source, h, Clif.placeSlots, Clif.Mem.free, Clif.Mem.leave]

/-- Complete source execution is inhabited for all words and arbitrary dirty
machine upper bits, including arbitrary initial memory and placement oracles. -/
theorem source_complete_witness (name : String) (c : Configuration)
    (runs : List Clif.RunCommand) (word : BitVec (valueType c).width)
    (upper : Nat) (mem : Clif.Mem) :
    ∃ (fr : Clif.Frame) (entered : Clif.Mem),
      Clif.enterFunc (source name c runs) [argument c word] mem = .ok (fr, entered) ∧
      Clif.runLoop Clif.Env.empty {funcs := [source name c runs]} 4 ⟨fr, [], entered⟩ =
        .returned [argument c word] mem ∧
      (BitVec.ofNat 128 (upper * 2^(valueType c).width + word.toNat)).setWidth
        (valueType c).width = word := by
  refine ⟨sourceFrame name c runs word, (Clif.enterSlots (source name c runs) mem).2,
    source_entry name c runs word mem, ?_, dirty_machine_bits c word upper⟩
  rw [source_return, source_memory_roundtrip]

end Backend.Stock.Prologue.AllConfigurations.Source

import FV.Backend.Proof.StockFenceWitness
import FV.Backend.Proof.StockMemoryAccessReach
import FV.Backend.Proof.StockSourceEntry

namespace Backend.Stock.Proof.FenceFixture
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

def faultArguments (pointer addend : BitVec 64) : List Clif.Val :=
  [⟨.i64,pointer⟩,⟨.i64,addend⟩]

def faultEntry (pointer addend : BitVec 64) : Clif.Frame :=
  ⟨function,(Clif.Regs.empty.set 7 ⟨.i64,pointer⟩).set 31 ⟨.i64,addend⟩,
    [],function.blocks[0]!.body,.ret [128]⟩

/-- The unchanged complete function admits arbitrary source arguments and an empty heap. -/
theorem fault_source_entry (pointer addend : BitVec 64) :
    SourceEntry function (faultArguments pointer addend) (faultEntry pointer addend) := by
  exact ⟨function.blocks[0]!,_,rfl,rfl,rfl,rfl,rfl⟩

/-- The unchanged mixed function faults at its first load without a heap guard. -/
theorem unallocated_first_access_traps (pointer addend : BitVec 64)
    (env : Clif.Env) (cp : Clif.Program) :
    Clif.runLoop env cp 1 ⟨faultEntry pointer addend,[],Clif.Mem.empty⟩ = .trapped .heapOob := by
  rfl

/-- The fault is a real source memory event at the actual initial address. -/
theorem unallocated_first_access_event (pointer addend : BitVec 64)
    (env : Clif.Env) (cp : Clif.Program) :
    Clif.MemTrapAt env cp ⟨faultEntry pointer addend,[],Clif.Mem.empty⟩ .heapOob
      (Clif.effAddr ⟨.i64,pointer⟩ 0) 8 := by
  refine ⟨rfl,rfl,⟨⟨[63],.load .load .i64 {} 7 0⟩,(faultEntry pointer addend).body.tail,rfl,?_⟩⟩
  exact .load rfl

end Backend.Stock.Proof.FenceFixture

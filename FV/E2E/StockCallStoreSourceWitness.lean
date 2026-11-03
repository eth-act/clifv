import FV.E2E.StockCallStoreFixture
import FV.Clif.MemTrap

namespace E2E.CallStoreSourceWitness
open Backend Backend.Proof Backend.Proof.Driver CallStoreFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def value (word : BitVec 64) : Clif.Val := ⟨.i64,word⟩
def program : Clif.Program := {funcs := [caller,callee]}
def frame (pointer word : BitVec 64) : Clif.Frame := {
  func := caller
  regs := (Clif.Regs.empty.set 7 (value pointer)).set 11 (value word)
  slots := []
  body := [⟨[31],.call 0 [11]⟩,⟨[],.store .store .i64 {} 31 7 8⟩]
  term := .ret [31] }
def storeFrame (pointer word : BitVec 64) : Clif.Frame :=
  {frame pointer word with regs := (frame pointer word).regs.set 31 (value (word+13)),body := [⟨[],.store .store .i64 {} 31 7 8⟩]}
def initial (pointer word : BitVec 64) : Clif.State := ⟨frame pointer word,[],Clif.Mem.empty⟩
def atStore (pointer word : BitVec 64) : Clif.State := ⟨storeFrame pointer word,[],Clif.Mem.empty⟩

/-- The unchanged source keeps every pointer and word and reaches its first store fault. -/
theorem default_store_fault (pointer word : BitVec 64) :
    Clif.enterFunc caller [value pointer,value word] Clif.Mem.empty =
      .ok (frame pointer word,Clif.Mem.empty) ∧
    Clif.runLoop Clif.Env.empty program 5 (initial pointer word) = .trapped .heapOob := by
  exact ⟨rfl,rfl⟩

/-- The original source call and complete callee run reach the caller's actual store. -/
theorem store_reached (pointer word : BitVec 64) :
    Reach Clif.Env.empty program (initial pointer word) (atStore pointer word) := by
  exact .step rfl (.step rfl (.step rfl (.step rfl (.refl _))))

/-- The reached instruction is the original default-flag heap store, with its original pointer. -/
theorem store_fault_at (pointer word : BitVec 64) :
    Clif.MemTrapAt Clif.Env.empty program (atStore pointer word) .heapOob
      (Clif.effAddr (value pointer) 8) 8 := by
  refine ⟨rfl,rfl,⟨⟨[],.store .store .i64 {} 31 7 8⟩,[],rfl,?_⟩⟩
  exact .store rfl

def heapBase : Nat := 0x300000
def sourceHeap : Clif.Mem := Clif.Mem.empty.allocAt heapBase 16
def storedHeap (word : BitVec 64) : Clif.Mem :=
  sourceHeap.writeBits false (heapBase+8) 8 (word+13)

/-- The same default-flag source stores the arbitrary callee result and returns it. -/
theorem default_store_return (word : BitVec 64) :
    Clif.enterFunc caller [value (BitVec.ofNat 64 heapBase),value word] sourceHeap =
      .ok (frame (BitVec.ofNat 64 heapBase) word,sourceHeap) ∧
    Clif.runLoop Clif.Env.empty program 6 ⟨frame (BitVec.ofNat 64 heapBase) word,[],sourceHeap⟩ =
      .returned [value (word+13)] (storedHeap word) := by
  exact ⟨rfl,rfl⟩

end E2E.CallStoreSourceWitness

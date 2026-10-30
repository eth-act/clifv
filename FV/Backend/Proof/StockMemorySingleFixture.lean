import FV.Backend.Proof.StockMemoryLoadWitness
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Memory.SingleFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def function : Clif.Function := { LoadFixture.function with
  name := "stock_memory_single_load_return"
  blocks := [{id := 0,params := [(0,.i64)],body := [⟨[2],.load .load .i32 LoadFixture.flags 0 0⟩],term := .ret [2]}] }

theorem scope : LowerScope function := lowerScope_of rfl

theorem dominated : Dominated function := by
  constructor
  · change ([0,2] : List Nat).Nodup; decide
  · intro ctx ranges st build bi b found
    have bound : bi < 1 := by have h := lt_of_getElem? found; simpa [function] using h
    have zero : bi = 0 := by omega
    subst bi
    simp [function] at found
    subst b
    constructor
    · intro j stm present
      cases j with
      | zero =>
        simp [function] at present
        subst stm
        intro x member
        have zero : x = 0 := by simpa [Driver.instArgs] using member
        subst x
        simp [availOf,function,defsBefore,defsFrom]
      | succ j => simp [function] at present
    · intro x member
      have two : x = 2 := by simpa [abiTerm,Driver.termArgs,sretRet,sigRets,function,LoadFixture.function] using member
      subst x
      simp [availOf,function,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have length : function.blocks.length = 1 := rfl
    omega

section Kernel
/-- Complete actual Stock lowering succeeds for the positive memory-domain input. -/
theorem lowered : (Stock.lower function).isOk = true := by decide +kernel
end Kernel

end Backend.Stock.Memory.SingleFixture

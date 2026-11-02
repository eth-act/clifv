import FV.Backend.Proof.StockCallStoreSource
import FV.Backend.Proof.StockMemoryStoreAccessTrap

namespace Backend.Stock.Proof.CallStoreResult
open Backend Backend.Proof Backend.Proof.Driver E2E MemoryFaults
set_option autoImplicit false
set_option Elab.async false

/-- The call reaches the actual default-flag store without executing its failed access. -/
theorem call_then_store_access {sb : Nat} {isem : Sem}
    {name : String} {pairs : List (Nat × Reg)} {destination pointer : Nat}
    (separate : pointer ≠ destination) {values : Nat → CV} {output : CV}
    {before after : Arm.ArmState}
    (called : isem (.call ⟨.sym name,retPairs pairs,callDefs [(.x 0,destination)]⟩)
      (pairs.map (values ·.1)) before = some ([output],after,.next))
    {flags : Clif.MemFlags} {code : Clif.TrapCode} {address : BitVec 64}
    {property : BitVec 64 → Nat → Prop} (flag : flags.trapCode = some code)
    (access : amodeAddr sb (.unsignedOffset (.vreg pointer .int) 8) 8 [values pointer] after = some address)
    (holds : property address 8) :
    AccessTrapRun sb isem
      [.call ⟨.sym name,retPairs pairs,callDefs [(.x 0,destination)]⟩,
       .store .store64 (.vreg destination .int) (.unsignedOffset (.vreg pointer .int) 8) flags]
      values before code property := by
  have callRun := seqRun_call_sym called (show [output].length = [(.x 0,destination)].length from rfl)
  have update := DirectCallResult.virtual_result pairs destination output values
  rw [vdefUpd_call] at update
  rw [update] at callRun
  apply AccessTrapRun.prefix callRun
  apply AccessTrapRun.store (by intro reg member; exact ⟨_,List.mem_singleton.mp member⟩) flag
  · simpa only [amUses,amVregs,AMode.regs,List.filterMap_cons,List.filterMap_nil,
      List.map_cons,List.map_nil,separate,↓reduceIte,StoreOp.bytes] using access
  · simpa only [StoreOp.bytes] using holds

/-- A trapped source run exposes either the callee trap or the actual invalid post-call store.
The callee-trap alternative stays explicit and does not restrict source admission. -/
theorem source_fault_decomposition {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame}
    {cm : Clif.Mem} {fuel source pointer : Nat} {code : Clif.TrapCode} {flags : Clif.MemFlags}
    {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc} {result : Clif.AbiParam}
    (separate : pointer ≠ source)
    (body : fr.body = [⟨[source],.call fn args⟩,⟨[],.store .store .i64 flags source pointer 8⟩])
    (term : fr.term = .ret [source]) (little : flags.endianness ≠ some .big)
    (lookup : fr.func.extern? fn = some ext) (external : cp.func? ext.name = none)
    (returns : ext.sig.returns = [result])
    (trapped : Clif.runLoop env cp (fuel+1) ⟨fr,[],cm⟩ = .trapped code) :
    instOutcome env cp fr cm (.call fn args) = .trap code ∨
      ∃ (after : Clif.Mem) (value : Clif.Val) (bits : BitVec 64) (address : Clif.Val),
        instOutcome env cp fr cm (.call fn args) = .ok ([value],after) ∧ value.ty = result.ty ∧
        ({fr with regs := fr.regs.set source value,body := [⟨[],.store .store .i64 flags source pointer 8⟩]} : Clif.Frame).getAs source .i64 = .ok bits ∧
        fr.get pointer = .ok address ∧ after.valid (Clif.effAddr address 8) 8 = false ∧
        flags.trapCode = some code := by
  rcases source_call_fault_or_continues body lookup external returns trapped with failed |
      ⟨after,value,called,typed,remaining⟩
  · exact .inl failed
  · have failed := source_store_faults
      (fr := {fr with regs := fr.regs.set source value,body := [⟨[],.store .store .i64 flags source pointer 8⟩]})
      rfl term little remaining
    obtain ⟨bits,address,readValue,readPointer,invalid,flag⟩ := source_store_trap failed
    have originalPointer : fr.get pointer = .ok address := by
      simpa only [Clif.Frame.get,Clif.Regs.set,separate,↓reduceIte] using readPointer
    refine .inr ⟨after,value,bits,address,called,typed,readValue,originalPointer,?_,flag⟩
    simpa only [Clif.StoreOp.size,Clif.Ty.bytes,Clif.Ty.width] using invalid

end Backend.Stock.Proof.CallStoreResult

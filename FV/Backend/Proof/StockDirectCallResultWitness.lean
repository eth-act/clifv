import FV.Backend.Proof.StockDirectCallResultFixture
import FV.Backend.Proof.StockSourceCallWitness
namespace Backend.Stock.Proof.DirectCallResultWitness
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.DirectCallResult
open Backend.Stock.Proof.DirectCallResultFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower SourceDefinedAt
/-- Sparse source result31 resolves to virtual194, whose actual call definition and return use x0. -/
-- witness: native_decide (only fixed Stock metadata; every argument word remains arbitrary)
theorem original_call_binding (word : BitVec 64) : ∃ c d : Stock.Result,
    Stock.lower caller = .ok c ∧ Stock.lower callee = .ok d ∧
    Nonempty (Binding c.ctx c.final 31) ∧
    (∃ block,c.code.blocks[0]? = some block ∧ callData block.insts[1]? = some (actualInfo.dest,actualInfo.uses,actualInfo.defs) ∧
      retData block.insts.toList.getLast? = some [(.vreg 194 .int,.x 0)]) ∧
    Clif.enterFunc caller [value word] Clif.Mem.empty = .ok (before word,Clif.Mem.empty) ∧
    Clif.step environment {funcs := []} ⟨before word,[],Clif.Mem.empty⟩ =
      .next ⟨after word,[],Clif.Mem.empty⟩ ∧
    Clif.step Clif.Env.empty program ⟨before word,[],Clif.Mem.empty⟩ = .next (active word) ∧
    Clif.step Clif.Env.empty program (active word) = .next ⟨after word,[],Clif.Mem.empty⟩ ∧
    SourceDefinedAt caller c.ctx 0 1 (after word) ∧
    VHolds (value word)
      (vdefUpd (retOps [(192,.x 0)] ++ callDefOps [(.x 0,194)]).toArray [ofX word]
        (fun _ => 0) 194) := by
  obtain ⟨c,d,crun,drun,scope,scopeD,dominated,one,oneD,entered,external,internal,
    returned,done,definedBefore,definedAfter,kept,bound,restored⟩ :=
    SourceCallWitness.stock_source_call_result_witness word
  have crun' : Stock.lower caller = .ok c := crun
  have observed := binding_of_run crun'
  refine ⟨c,d,crun',drun,observed.1,observed.2,entered,external,internal,returned,definedAfter,?_⟩
  rw [virtual_result]
  simp [VHolds,value,ofX,Clif.Ty.width]

/-- The source binder keeps arbitrary returned memory; it preserves inherited source values. -/
theorem memory_effect (word : BitVec 64) (cm resultMemory : Clif.Mem) :
    let initial : Clif.State := ⟨before word,[],cm⟩
    let next : Clif.State := ⟨after word,[],resultMemory⟩
    Clif.continueWith initial [] [31] [value word] resultMemory = .next next ∧
      next.frame.regs 31 = some (value word) ∧ next.frame.regs 7 = some (value word) ∧
      next.mem = resultMemory := by
  exact ⟨rfl,rfl,rfl,rfl⟩

end Backend.Stock.Proof.DirectCallResultWitness

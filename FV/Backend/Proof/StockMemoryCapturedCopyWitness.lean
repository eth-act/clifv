import FV.Backend.Proof.StockMemoryCapturedCopyDomain
import FV.Backend.Proof.StockMemoryLoadedPointerStoreWitness

namespace Backend.Stock.Memory.CapturedCopy.Fixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open IntegerRoots.LoadedPointerFixture (function)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def flags : Clif.MemFlags := {trapCode := none}
def entry : Clif.Block := {
  id := 0,params := [(0,.i64)],body := [⟨[],.nop⟩],term := .jump ⟨1,[]⟩ }
def target : Clif.Block := {
  id := 1,body := [⟨[],.nop⟩,⟨[2],.load .load .i64 flags 0 8⟩,
    ⟨[3],.load .load .i64 flags 0 0⟩,⟨[],.store .store .i64 flags 2 3 0⟩],term := .ret [] }
/-- The parsed capture equals this exact original function, including its name and ABI. -/
theorem captured_source_shape_witness : function = {
    name := "_RNxC7fv_demo12HezxnGHZarII",
    sig := {params := [⟨.i64,.none,.normal⟩],callConv := some .systemV},blocks := [entry,target] } := by native_decide
private theorem original_shape : function.blocks = [entry,target] ∧
    sigAbiOk function.sig = true ∧ (sigRets function.sig).any (·.purpose == .sret) = false := by
  rw [captured_source_shape_witness]
  exact ⟨rfl,rfl,rfl⟩

/-- The unchanged captured source satisfies the complete memory-capable contract. -/
theorem captured_domain_witness : Domain function := by
  obtain ⟨ctx,ranges,st,info,build,scope,dominated,rest⟩ :=
    IntegerRoots.LoadedPointerFixture.captured_loaded_pointer_context_witness
  apply domain_of_two_block_captured_copy scope dominated original_shape.2.1 original_shape.2.2
    original_shape.1 ?_ rfl (iv := 1) (ip := 2) (is := 3) rfl rfl rfl (by decide) (by decide)
    ?_ rfl (by simp [entry]) rfl rfl rfl
  · intro stm member
    have same : stm = ⟨[],.nop⟩ := by simpa [entry] using member
    subst stm
    rfl
  · intro j stm found
    have bound := lt_of_getElem? found
    have indices : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp only [target,List.length_cons,List.length_nil] at bound; omega
    rcases indices with rfl | rfl | rfl | rfl
    all_goals simp [target] at found; subst stm; simp

/-- The complete original contract has a successful actual Stock lowering. -/
theorem captured_domain_and_lower_witness :
    Domain function ∧ ∃ result : Result,Stock.lower function = .ok result := by
  refine ⟨captured_domain_witness,?_⟩
  obtain ⟨result,event,b,record,step,valueReg,pointerReg,run,rest⟩ :=
    StoreRoots.LoadedPointerWitness.captured_loaded_pointer_store_record_witness
  exact ⟨result,run⟩

end Backend.Stock.Memory.CapturedCopy.Fixture

import FV.Backend.Proof.StockMemorySretCopyBodySpec
import FV.Backend.Proof.StockMemoryComputedStoreRecordWitness

namespace Backend.Stock.Memory.SretCopy.Fixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open StoreRoots.ComputedFixture (function)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def flags : Clif.MemFlags := {trapCode := none}
def entry : Clif.Block := {
  id := 0,params := [(0,.i64),(1,.i64)],body := [⟨[],.nop⟩],term := .jump ⟨1,[]⟩ }
def middle : Clif.Block := {
  id := 1,body := [⟨[],.nop⟩,⟨[2],.load .load .i64 flags 1 0⟩,
    ⟨[3],.load .load .i64 flags 1 8⟩,⟨[],.store .store .i64 flags 2 0 0⟩,
    ⟨[],.store .store .i64 flags 3 0 8⟩],term := .jump ⟨2,[]⟩ }
def exit : Clif.Block := { id := 2,body := [⟨[],.nop⟩],term := .ret [] }

/-- The original capture retains its source name, sret purpose, blocks, offsets and ABI. -/
theorem captured_sret_source_shape_witness : function = {
    name := "_RNxC7fv_demo11HawPMC3YC2b",
    sig := {params := [⟨.i64,.none,.sret⟩,⟨.i64,.none,.normal⟩],callConv := some .systemV},
    blocks := [entry,middle,exit] } := by native_decide

/-- The unchanged original sret capture inhabits all four retained source records.
The body specification derives both load emissions from the actual stores. -/
theorem captured_sret_copy_body_witness :
    ∃ (result : Result) (event : BlockScanEvent),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      sigAbiOk function.sig = true ∧ event ∈ result.blockScans.toList ∧ event.block = 1 ∧
      function.blocks[event.block]? = some middle ∧
      Nonempty (BodySpec function result event middle 1 2 3 4 1 0 2 3 flags flags flags flags) := by
  have blocks : function.blocks = [entry,middle,exit] := by rw [captured_sret_source_shape_witness]
  have scope : LowerScope function := lowerScope_of (by rw [captured_sret_source_shape_witness]; decide +kernel)
  have dominated : Dominated function := dominated_of (by native_decide)
  have abi : sigAbiOk function.sig = true := by rw [captured_sret_source_shape_witness]; rfl
  obtain ⟨f,result,event,b,sameFunction,_,_,run,events,block,loadStatement,_,_,_,_⟩ :=
    StoreRoots.ComputedFixture.captured_computed_store_record_witness
  subst f
  have bound := lt_of_getElem? block
  have indices : event.block = 0 ∨ event.block = 1 ∨ event.block = 2 := by
    rw [blocks] at bound
    simp only [List.length_cons,List.length_nil] at bound
    omega
  have actual : event.block = 1 ∧ b = middle := by
    rcases indices with atEntry | atMiddle | atExit
    · have same : entry = b := by simpa [blocks,atEntry] using block
      subst b
      simp [entry] at loadStatement
    · exact ⟨atMiddle,by simpa [blocks,atMiddle] using block.symm⟩
    · have same : exit = b := by simpa [blocks,atExit] using block
      subst b
      simp [exit] at loadStatement
  obtain ⟨atMiddle,rfl⟩ := actual
  have spec := captured_sret_copy_body_spec run scope dominated events block
    (i0 := 1) (i8 := 2) (j0 := 3) (j8 := 4) (base := 1) (destination := 0)
    (low := 2) (high := 3) rfl rfl rfl rfl (by decide) (by decide) ?_
    (pi := 0) (pb := entry) (by rw [blocks]; rfl) (by simp [entry]) (by simp [entry])
  · exact ⟨result,event,run,scope,dominated,abi,events,atMiddle,block,spec⟩
  · intro j stm found
    have bound := lt_of_getElem? found
    have indices : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
      simp only [middle,List.length_cons,List.length_nil] at bound
      omega
    rcases indices with rfl | rfl | rfl | rfl | rfl
    all_goals simp [middle] at found; subst stm; simp

end Backend.Stock.Memory.SretCopy.Fixture

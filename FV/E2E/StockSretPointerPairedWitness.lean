import FV.E2E.StockSretPointerPaired
import FV.E2E.StockMemorySretCopyCompiledWitness

namespace E2E.StockMemorySretCopyCompiledWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Memory.StoreRoots.ComputedFixture (function)
set_option autoImplicit false
set_option Elab.async false

theorem compiled_sret_original_x8_paired_witness (cleanup : Bool) :
    ∃ (result : Stock.Result) (prepared : VCode) (allocated : RFunc) (frame : AFunc)
      (assembly : FnAsm) (binary : FnBin),
      Stock.lower function = .ok result ∧
      Stock.MemorySretCopy.lowerValidated function = .ok result.code ∧
      Stock.MemorySretCopy.check function result.code = true ∧
      CompiledStockArithmeticStage function cleanup 0 result prepared allocated frame assembly binary ∧
      FormsCovered ⟨assembly.k,frame.slotBase⟩ prepared ∧
      SretOriginalPointerPaired function 0 result prepared allocated frame assembly binary := by
  obtain ⟨result,prepared,allocated,frame,assembly,binary,lowered,provider,checked,stage,covered⟩ :=
    compiled_sret_stage_witness cleanup
  obtain ⟨actual,family,run,equal,effects⟩ := Stock.MemorySretCopy.check_sound checked
  have same : actual = result := Except.ok.inj (run.symm.trans lowered)
  subst actual
  have sret : (sigRets function.sig).any (·.purpose == .sret) = true := by
    rw [Backend.Stock.Memory.SretCopy.Fixture.captured_sret_source_shape_witness]
    rfl
  exact ⟨result,prepared,allocated,frame,assembly,binary,lowered,provider,checked,stage,covered,
    sret_original_pointer_paired_of_stage family sret (by rwa [equal]) stage⟩
end E2E.StockMemorySretCopyCompiledWitness


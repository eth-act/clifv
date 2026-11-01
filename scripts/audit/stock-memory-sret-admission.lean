import FV.Backend.Proof.StockMemorySretCopyCheckWitness
import FV.E2E.StockMemorySretCopyNI

#print axioms Backend.Stock.Memory.Domain.toABI
#print axioms Backend.Stock.MemorySretCopy.sourceOk_sound
#print axioms Backend.Stock.MemorySretCopy.check_sound
#print axioms Backend.Stock.Memory.SretCopy.CfgClass.domainABI
#print axioms Backend.Stock.MemorySretCopy.Fixture.captured_sret_sourceOk_witness -- witness: native_decide
#print axioms Backend.Stock.MemorySretCopy.Fixture.captured_sret_check_witness -- witness: native_decide

#print axioms Backend.Stock.Memory.SretCopy.sret_copy_return_frame_canonical
#print axioms E2E.StockMemory.SretCopy.sret_copy_paired_return_frame_canonical

#print axioms E2E.StockMemory.SretCopy.sret_copy_paired_return_function_canonical
#print axioms E2E.backend_correct_world_niX_stock_sret_copy_memory

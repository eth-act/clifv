import FV.Backend.Proof.StockMemoryCfgCompatibility
import FV.E2E.SemanticNIBoundary
import FV.Backend.Proof.StockMemoryCfgNotrap
import FV.E2E.StockMemoryCfgTls
import FV.E2E.StockMemoryCfgWorldX
import FV.Backend.Proof.StockMemoryCfgSourceWitness
import FV.Backend.Proof.StockMemoryCfgClass
import FV.E2E.StockMemoryCfgValue
import FV.E2E.StockMemoryCfgMachine
import FV.E2E.StockMemoryCfgPairedFunction
import FV.E2E.StockMemoryCfgNI

#print axioms Backend.Stock.MemoryCfg.sourceOk_sound
#print axioms Backend.Stock.MemoryCfg.check_sound
#print axioms Backend.Stock.MemoryCfg.effectsOnly_noTls
#print axioms E2E.StockMemoryCfg.effectsOnly_instruction
#print axioms E2E.StockMemoryCfg.return_value
#print axioms E2E.StockMemoryCfg.machine_return
#print axioms E2E.StockMemoryCfg.paired_returns
#print axioms E2E.backend_correct_world_niX_stock_memory_cfg

#print axioms Backend.Stock.MemoryCfg.captured_source_class

#print axioms Backend.Stock.Proof.OrdinaryCfg.ordinary_jump_return_notrap
#print axioms Backend.Stock.MemoryCfg.TwoBlockClass.source_notrap
#print axioms E2E.StockMemoryCfg.fixedTlsFlags_ok
#print axioms E2E.StockMemoryCfg.return_original_tls
#print axioms E2E.backend_correct_worldX_stock_memory_cfg

#print axioms Backend.Stock.MemoryCfg.previous_file_exact
#print axioms Backend.Stock.MemoryCfg.previous_file_exact_witness
#print axioms E2E.CompiledSemanticNI.of_checks
#print axioms E2E.backend_correct_world_niX_semantic

-- Executable checks add no axioms to the generic proofs above.
#guard Backend.Stock.MemoryCfg.lowerRoutes.length == 14
#guard match Backend.Stock.MemoryCfg.lowerValidated Backend.Stock.Memory.CapturedFixture.function,
    Backend.Stock.lower Backend.Stock.Memory.CapturedFixture.function with
  | .ok code, .ok result => decide (code = result.code)
  | _, _ => false
#guard (Backend.Stock.lower Backend.Stock.Memory.CapturedFixture.function).toOption.any
  (fun result => Backend.SemanticNI.check Backend.Stock.Memory.CapturedFixture.function result.code)
#guard (Backend.Stock.lower Backend.Stock.Memory.CapturedFixture.function).toOption.any
  (fun result => Backend.Stock.MemoryCfg.check Backend.Stock.Memory.CapturedFixture.function result.code)

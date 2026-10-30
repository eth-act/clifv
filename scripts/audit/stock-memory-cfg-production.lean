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

import FV.Backend.SemanticNICheck
import FV.Backend.StockVoidCallCheck
import FV.Backend.Proof.StockSourceCallWitness
open Backend Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
private def text := "function %stock_source_call_result(i64) -> i64 system_v {\n fn0 = colocated %stock_source_identity(i64) -> i64 system_v\nblock0(v7: i64):\n v31 = call fn0(v7)\n return v31\n}\n"
#eval match (Clif.parseFile text).funcs[0]?.bind (·.func.toOption) with
 | none => "parse failed"
 | some f => match Stock.lower f with
   | .error e => e
   | .ok r => s!"lowerCheck={lowerCheck f r.code}, semNI={SemanticNI.check f r.code}; source31={repr (r.ctx.valueReg? 31)}; code={repr (r.code.blocks.toList.map (fun b => b.insts.toList.map (fun i => match i with | .call c => (c.uses,c.defs) | .rets us => (us,[]) | _ => ([],[]))))}"

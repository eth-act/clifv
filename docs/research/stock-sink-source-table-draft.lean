import FV.Backend.Proof.StockNoOpportunityTable
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
attribute [local irreducible] Isle.Aarch64.program
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
def sinkSourcePre (t : TermId) (args : List AW) : Bool :=
  noOpportunityPre t args && (if t == TId.sink_inst then args == [.xv .inst] else true)
private def sinkEntryOk (e : TermId × List AW × AW) : Bool :=
  (program.rulesOf e.1).all (aRule program covTab aext actor sinkSourcePre aOracle e.2.1 e.2.2)
private theorem checked0 : covTab0.all sinkEntryOk = true := by decide +kernel
private theorem checked1 : covTab1.all sinkEntryOk = true := by decide +kernel
private theorem checked2 : covTab2.all sinkEntryOk = true := by decide +kernel
private theorem checked3 : covTab3.all sinkEntryOk = true := by decide +kernel
private theorem checked4 : covTab4.all sinkEntryOk = true := by decide +kernel
private theorem checked5 : covTab5.all sinkEntryOk = true := by decide +kernel
private theorem checked6 : covTab6.all sinkEntryOk = true := by decide +kernel
private theorem checked7 : covTab7.all sinkEntryOk = true := by decide +kernel
end Backend.Stock.Proof

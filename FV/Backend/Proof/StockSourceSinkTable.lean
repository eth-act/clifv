import FV.Backend.Proof.StockNoOpportunityPre
import FV.Backend.Proof.IselCovTab
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
attribute [local irreducible] Isle.Aarch64.program
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
def sourceSinkPre (t : TermId) (args : List AW) : Bool :=
  noOpportunityPre t args && (if t == TId.sink_inst then (match args with | [.xv .inst] => true | _ => false) else true)
def sourceSinkEntry (e : TermId × List AW × AW) : TermId × List AW × AW :=
  if e.1 == 564 then (e.1,[.xv .inst],e.2.2) else e
def sourceSinkTab : Tab := covTab.map sourceSinkEntry
def sourceSinkActor (t : TermId) (args : List AW) : AW :=
  if t == TId.is_sinkable_inst then .xv .inst else actor t args
private def sourceSinkEntryOk (e : TermId × List AW × AW) : Bool :=
  let e := sourceSinkEntry e
  (program.rulesOf e.1).all (aRule program sourceSinkTab aext sourceSinkActor sourceSinkPre aOracle e.2.1 e.2.2)
private theorem checked0 : covTab0.all sourceSinkEntryOk = true := by decide +kernel
private theorem checked1 : covTab1.all sourceSinkEntryOk = true := by decide +kernel
private theorem checked2 : covTab2.all sourceSinkEntryOk = true := by decide +kernel
private theorem checked3 : covTab3.all sourceSinkEntryOk = true := by decide +kernel
private theorem checked4 : covTab4.all sourceSinkEntryOk = true := by decide +kernel
private theorem checked5 : covTab5.all sourceSinkEntryOk = true := by decide +kernel
private theorem checked6 : covTab6.all sourceSinkEntryOk = true := by decide +kernel
private theorem checked7 : covTab7.all sourceSinkEntryOk = true := by decide +kernel
/-- All704 reused summaries are kernel checked with typed source sink targets.
Only the atomic-load input summary is strengthened; no source acceptance rule changes. -/
theorem stock_sourceSink_table_checked :
    chkTab program sourceSinkTab aext sourceSinkActor sourceSinkPre aOracle = true := by
  unfold chkTab sourceSinkTab
  change covTab.all sourceSinkEntryOk = true
  simp only [covTab,List.all_append,checked0,checked1,checked2,checked3,checked4,checked5,checked6,checked7,Bool.and_self]
/-- Every original statement/return/trap/branch root passes the refined analysis
under the same existing exclusions and root argument descriptions. -/
theorem stock_sourceSink_roots_checked :
    (program.rulesOf TId.lower).all (fun r => !closureRootIds.contains r.id ||
      aRule program sourceSinkTab aext sourceSinkActor sourceSinkPre aOracle [.xv .inst] AW.top r) = true ∧
    (program.rulesOf TId.lower).all (fun r => !(r.id == 964 || r.id == 1037) ||
      aRule program sourceSinkTab aext sourceSinkActor sourceSinkPre aOracle [.c0] AW.top r) = true ∧
    (program.rulesOf TId.lower_branch).all
      (aRule program sourceSinkTab aext sourceSinkActor sourceSinkPre aOracle [.c0,.c0] AW.top) = true := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩
end Backend.Stock.Proof

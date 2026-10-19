import FV.Backend.Proof.StockReturnContract
import FV.Backend.Proof.StockBlockCode

/-! Actual whole-driver assembly discharges return segment placement.
No helper, emitted-decision, operand, or placement certificate is supplied
by the caller. The original guarded simulation invariant remains. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver

/-- Original retained source returns reach an ABI-correct return in the actual
returned VCode, with all block/record placement derived from Stock.lower. -/
theorem stock_lower_return_runOk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {xs : List Nat} (ret : b.term = .ret xs)
    {record : ScanRecord} (records : record ∈ event.output.records) (terminal : record.inst = event.termInst)
    {env : Clif.Env} {cp : Clif.Program} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (func : s.frame.func = f) (callers : s.callers = [])
    (done : Clif.stepTerm env cp s (.ret xs) = .done vals cm)
    (defined : SourceDefinedAt f result.ctx event.block b.body.length s.frame)
    {ρ : Nat → CV} (held : ValuesHeld (fun x => Demanded record.output.state x ∧
      x ∈ availOf f (availIn f result.ctx) event.block b.body.length) event.ctx s.frame
      (fun key => ρ (aliasNum result.final.alias key)))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR)
    (world : Arm.ArmState) (memory : MR s.frame.slots s.mem world) :
    ∃ label k, RunOkABI f result.code isem MR s.frame.slots ⟨label,k,ρ,world⟩ (.returned vals cm) := by
  obtain ⟨label,blockCode,k,placed,segment⟩ := stock_lower_record_segment run events records
  exact ⟨label,k,stock_lower_return_record_runOk run scope dominated abi events block ret records terminal
    func callers done defined held refines stable placed segment world memory⟩
end Backend.Stock.Proof

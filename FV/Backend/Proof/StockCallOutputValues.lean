import FV.Backend.Proof.StockCallOutputStatic
namespace Backend.Stock.Proof.CallOutputValuesDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.CallOutputStaticDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem write_before {ρ : Nat → CV} {base count n : Nat} (below : n < base) (values : List CV) :
    writeV ρ ((callDefOps (outDefs base count)).zip values) n = ρ n := by
  apply writeV_other
  intro pair member
  have operand := (List.of_mem_zip member).1
  simp only [callDefOps,List.mem_map] at operand
  obtain ⟨q,present,same⟩ := operand
  rw [← same]
  obtain ⟨j,inside,rfl⟩ := mem_outDefs present
  dsimp only
  omega

/-- Real call output/pin helpers identify the actual fresh definitions. Writing
results into those definitions preserves EVERY earlier virtual register and
establishes ResultsHeld for matching source/ABI result values. The callee's
AllHold/length obligations remain explicit for source-call composition. -/
theorem stock_call_output_values {ctx : Ctx} {sig : Clif.Signature}
    {before after final : State} {outs rets : V}
    (output : Stock.externCtor ctx T.gen_call_output [.op (.sig sig)] before = .ok (outs,after))
    (pinned : Stock.externCtor ctx T.gen_call_rets [.op (.sig sig),outs] after = .ok (rets,final)) :
    rets = .op (.callRets (callDefs (outDefs before.base.nextVreg sig.returns.length))) ∧
      (∀ (ρ : Nat → CV) (values : List CV) (n : Nat),n < before.base.nextVreg →
        writeV ρ ((callDefOps (outDefs before.base.nextVreg sig.returns.length)).zip values) n = ρ n) ∧
      ∀ (fr : Clif.Frame) (ρ : Nat → CV) (values : List Clif.Val) (results : List CV),
        AllHold values results → values.length = sig.returns.length →
        ResultsHeld before.base.nextVreg fr (outRegs before.base sig.returns.length) values
          (writeV ρ ((callDefOps (outDefs before.base.nextVreg sig.returns.length)).zip results)) := by
  obtain ⟨shape,state,unchanged,bound,returned,defs,fresh,emitted⟩ := stock_gen_call_rets_fresh_defs output pinned
  refine ⟨returned,fun ρ values n below => write_before below values,?_⟩
  intro fr ρ values results held count
  simpa only [outRegs_eq,count] using (resultsHeld_call (fr := fr) (ρ := ρ) (b := before.base.nextVreg) held)
end Backend.Stock.Proof.CallOutputValuesDraft

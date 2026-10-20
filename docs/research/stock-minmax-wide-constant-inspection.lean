import FV.Backend.Proof.StockMinMaxWideDriverRuns
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open MinMaxRegisterFixture
set_option maxRecDepth 20000
def wideConstantFunction (unsigned maximum wide left large : Bool) : Clif.Function := {
  name := "stock_minmax_wide_constant_original"
  sig := {params := [⟨wideMinmaxTy wide,.none,.normal⟩],returns := [⟨wideMinmaxTy wide,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(31,wideMinmaxTy wide)],body := [
    ⟨[7],.iconst (wideMinmaxTy wide) (BitVec.ofNat (wideMinmaxTy wide).width (if large then 65537 else 3))⟩,
    ⟨[100],.binary (minmaxOperation unsigned maximum) (wideMinmaxTy wide) (if left then 7 else 31) (if left then 31 else 7)⟩],term := .ret [100]}] }
def wideConstantBuilt (unsigned maximum wide left large : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (wideConstantFunction unsigned maximum wide left large)).toOption.getD (sinkCtx,#[],sinkState)
#eval do
  for wide in [false,true] do
    for left in [false,true] do
      for large in [false,true] do
        let result := Stock.lower (wideConstantFunction false false wide left large)
        let details := result.toOption.map fun (r : Result) =>
          let blocks := r.blockScans.toList.map fun (e : BlockScanEvent) =>
            e.output.records.map fun (rec : ScanRecord) =>
              (rec.inst,rec.output.emitted.size,rec.output.step.map fun (s : Step) => (s.rules.getLast?,s.results))
          (aliasNum r.final.alias 192,aliasNum r.final.alias 193,blocks)
        IO.println (reprStr (wide,left,large,details))
end Backend.Stock.Proof.ScalarSelect

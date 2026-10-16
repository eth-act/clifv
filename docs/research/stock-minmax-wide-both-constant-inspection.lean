import FV.Backend.Proof.StockMinMaxWideDriverRuns
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open MinMaxRegisterFixture
set_option maxRecDepth 20000
def wideBothConstantFunction (unsigned maximum wide : Bool) : Clif.Function := {
  name := "stock_minmax_wide_both_constant_original"
  sig := {returns := [⟨wideMinmaxTy wide,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [],body := [
    ⟨[7],.iconst (wideMinmaxTy wide) (BitVec.ofNat (wideMinmaxTy wide).width 3)⟩,
    ⟨[31],.iconst (wideMinmaxTy wide) (BitVec.ofNat (wideMinmaxTy wide).width 65537)⟩,
    ⟨[100],.binary (minmaxOperation unsigned maximum) (wideMinmaxTy wide) 7 31⟩],term := .ret [100]}] }
#eval do
  for wide in [false,true] do
    for unsigned in [false,true] do
      for maximum in [false,true] do
        let result := Stock.lower (wideBothConstantFunction unsigned maximum wide)
        let details := result.toOption.map fun (r : Result) =>
          let blocks := r.blockScans.toList.map fun (e : BlockScanEvent) =>
            e.output.records.map fun (rec : ScanRecord) =>
              (rec.inst,rec.output.emitted.size,rec.output.step.map fun (s : Step) => (s.rules.getLast?,s.results))
          (aliasNum r.final.alias 192,aliasNum r.final.alias 193,blocks)
        IO.println (reprStr (wide,unsigned,maximum,details))
end Backend.Stock.Proof.ScalarSelect

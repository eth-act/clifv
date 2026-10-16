import FV.Backend.Proof.StockTryAliasSource
namespace Backend.Stock.Proof.TryAliasFixture
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
theorem try_term : termOf program 300 = .ok T.gen_try_call_rets := by
  unfold termOf Isle.Aarch64.program
  rfl
theorem try_lookup : program.termByName? "gen_try_call_rets" = some T.gen_try_call_rets := by
  decide +kernel


end Backend.Stock.Proof.TryAliasFixture

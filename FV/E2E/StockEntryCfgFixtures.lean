import FV.E2E.StockCfgFixtures

namespace E2E.StockEntryCfgNIWitness
open Backend.Stock.D0
set_option autoImplicit false

/-- Actual dividing entry bodies with inherited values, nonempty copies,
nine ABI parameters and the original placed source slot. Mode3 distinguishes
an early zero-divisor trap from a later signed-overflow trap. -/
def function (config : Configuration) (ty : Clif.Ty) (mode : Nat) : Clif.Function :=
  let old := StockCfgNIWitness.function config ty 0
  let target : List Clif.Stmt :=
    if mode == 0 then
      [⟨[102],.binary .iadd ty 1 101⟩,⟨[103],.binary .rotl ty 102 8⟩,⟨[104],.bmask ty 103⟩]
    else if mode == 1 then [⟨[102],.binary .iadd ty 1 101⟩]
    else if mode == 2 then [⟨[102],.iconst ty 0⟩,⟨[103],.div .udiv ty 101 102⟩]
    else [⟨[102],.iconst ty (BitVec.ofNat ty.width (2^(ty.width-1)))⟩,
      ⟨[103],.iconst ty (BitVec.ofNat ty.width (2^ty.width-1))⟩,⟨[104],.div .sdiv ty 102 103⟩]
  {old with blocks := [
    {old.blocks[0]! with body := [⟨[100],.div (if mode == 1 then .sdiv else .udiv) ty 1 8⟩,⟨[],.nop⟩]},
    {old.blocks[1]! with body := target,term := .ret [if mode == 1 then 102 else if mode == 2 then 103 else 104]}]}

def functions (config : Configuration) : List (Clif.Function × Clif.Ty) :=
  let all := ([.i8,.i16,.i32,.i64] : List Clif.Ty).flatMap fun ty =>
    (List.range 4).map fun mode => (function config ty mode,ty)
  all.zipIdx.map fun ((f,ty),i) => ({f with name := s!"stock_cfgentry_{i}"},ty)

end E2E.StockEntryCfgNIWitness

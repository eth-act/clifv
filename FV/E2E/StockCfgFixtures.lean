import FV.E2E.StockNarrowFixtures

namespace E2E.StockCfgNIWitness
open Backend.Stock.D0
set_option autoImplicit false

/-- Four widths, inherited entry/stack values and a forwarded constant.
The source slot and all nine ABI parameters remain present. -/
def function (config : Configuration) (ty : Clif.Ty) (mode : Nat) : Clif.Function :=
  let old := StockNarrowNIWitness.function config ⟨"cfg",ty,.binary .iadd ty 1 8⟩
  let body : List Clif.Stmt :=
    if mode == 0 then
      [⟨[102],.binary .iadd ty 1 101⟩,⟨[103],.binary .rotl ty 102 8⟩,⟨[104],.bmask ty 103⟩]
    else if mode == 1 then
      [⟨[102],.div .sdiv ty 1 8⟩,⟨[],.nop⟩,⟨[103],.div .urem ty 102 101⟩,⟨[104],.bmask ty 103⟩]
    else
      [⟨[102],.iconst ty 0⟩,⟨[103],.div .udiv ty 1 102⟩]
  {old with blocks := [
    {old.blocks[0]! with body := [⟨[100],.iconst ty (BitVec.ofNat ty.width 3)⟩,⟨[],.nop⟩],term := .jump ⟨10,[100]⟩},
    {id := 10,params := [(101,ty)],body,
      term := .ret [if mode == 0 then 104 else if mode == 1 then 102 else 103]}]}

def functions (config : Configuration) : List (Clif.Function × Clif.Ty) :=
  let all := ([.i8,.i16,.i32,.i64] : List Clif.Ty).flatMap fun ty =>
    (List.range 3).map fun mode => (function config ty mode,ty)
  all.zipIdx.map fun ((f,ty),i) => ({f with name := s!"stock_cfg_{i}"},ty)

end E2E.StockCfgNIWitness

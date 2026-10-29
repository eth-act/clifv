module

public import FV.E2E.StockNarrowFixtures

@[expose] public section

namespace E2E.StockConditionalCfgNIWitness
open Backend.Stock.D0
set_option autoImplicit false

/-- Original scalar operations, before or after the branch, include returning
and trapping paths. Distinct false-edge results detect an inverted choice;
duplicate destinations exercise actual synthetic critical-edge blocks. -/
def functions (config : Configuration) : List (Clif.Function × Clif.Ty) :=
  let cases := ([.i32,.i64] : List Clif.Ty).flatMap fun ty =>
    (StockNarrowNIWitness.cases ty).filter fun c => match c.inst with
      | .iconst .. | .select .. | .unary .. | .binary .. | .div .. => true
      | _ => false
  (List.range 100).map fun i =>
    let c := cases[i % cases.length]?.getD ⟨"default",.i64,.iconst .i64 0⟩
    let original := StockNarrowNIWitness.function config c
    let b := original.blocks[0]!
    let early := i % 2 == 0
    let critical := i % 5 == 4
    let condition := ([0,1,8] : List Nat)[i % 3]!
    let result := match b.term with | .ret (x :: _) => x | _ => 100
    let output := StockNarrowNIWitness.resultType c
    let falseBody := if early && !critical then [⟨[500],.unary .bnot output result⟩]
      else [⟨[500],.iconst output (BitVec.ofNat output.width 42)⟩]
    ({original with name := s!"stock_cfgconditional_{i}",blocks := [
      {b with body := if early then b.body else [],term := .brif condition ⟨10,[]⟩ ⟨if critical then 10 else 20,[]⟩},
      {id := 10,params := [],body := if early then [] else b.body,term := b.term},
      {id := 20,params := [],body := falseBody,term := .ret [500]}]},c.inputTy)

end E2E.StockConditionalCfgNIWitness

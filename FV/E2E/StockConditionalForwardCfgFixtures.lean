import FV.E2E.StockConditionalCfgFixtures

namespace E2E.StockConditionalForwardCfgNIWitness
open Backend.Stock.D0
set_option autoImplicit false

/-- Preserve the source operation and branch outcomes while adding real
inherited-value, parameter-copy and optional shared-return continuations. -/
private def tail (b : Clif.Block) (ty : Clif.Ty) (leaf sample : Nat) (shared : Bool) :
    Clif.Block × List Clif.Block := Id.run do
  let result := match b.term with | .ret (x :: _) => x | _ => 500
  let delayed := sample % 3 != 0
  let count := 2 + sample % 3
  let firstCopy := !delayed && (sample + leaf) % 2 == 0
  let base := 1000 + leaf * 20
  let mut current := if firstCopy then 600 + leaf * 20 else result
  let mut incoming := firstCopy
  let mut blocks := []
  for j in List.range count do
    let copying := (sample + leaf + j + 1) % 2 == 0
    let next := 600 + leaf * 20 + j + 1
    let term := if j + 1 == count then
        if shared then Clif.Terminator.jump ⟨2000,[current]⟩ else .ret [current]
      else .jump ⟨base+j+1,if copying then [current] else []⟩
    blocks := blocks ++ [{
      id := base+j
      params := if incoming then [(current,ty)] else []
      body := if delayed && j == 0 then b.body else [⟨[],.nop⟩]
      term := term }]
    current := if copying then next else current
    incoming := copying
  return ({b with
    body := if delayed then [] else b.body
    term := .jump ⟨base,if firstCopy then [result] else []⟩},blocks)

/-- Seven to twelve original blocks, both widths, real stack arguments/slots,
first and later traps, critical duplicates, inherited values and shared joins. -/
def functions (config : Configuration) : List (Clif.Function × Clif.Ty) :=
  (StockConditionalCfgNIWitness.functions config).zipIdx.map fun ((f,ty),i) =>
    let output := match f.sig.returns with | p :: _ => p.ty | _ => .i64
    let shared := i % 4 < 2
    let (yes,yesTail) := tail f.blocks[1]! output 0 i shared
    let (no,noTail) := tail f.blocks[2]! output 1 i shared
    let common := if shared then [{id := 2000,params := [(900,output)],term := .ret [900]}] else []
    ({f with
      name := s!"stock_cfgconditionalforward_{i}"
      blocks := [f.blocks[0]!,yes,no] ++ yesTail ++ noTail ++ common},ty)

end E2E.StockConditionalForwardCfgNIWitness

import FV.E2E.StockNarrowFixtures

namespace E2E.StockMaskNIWitness
open Backend.Stock.D0
set_option autoImplicit false

def widths : List Clif.Ty := [.i8,.i16,.i32,.i64]
abbrev conventions := StockNarrowNIWitness.conventions

/-- Independent original widths, nine arguments, an actual stack argument and
the original explicit source slot are retained. -/
def function (config : Configuration) (input output : Clif.Ty) : Clif.Function :=
  StockNarrowNIWitness.function config ⟨s!"bmask_{output.width}",input,.bmask output 1⟩

/-- Nop before, between and after computations; retained consumed and unused
divisions surround both emitted and omitted bmask results. -/
def mixedFunction (config : Configuration) (input output : Clif.Ty) : Clif.Function :=
  let f := function config input output
  let b := f.blocks[0]!
  let body : List Clif.Stmt :=
    [⟨[],.nop⟩,⟨[100],.div .sdiv input 1 8⟩,⟨[],.nop⟩,
     ⟨[106],.binary .bor input 100 1⟩,⟨[101],.bmask output 106⟩,⟨[102],.iconst output (BitVec.ofNat output.width 3)⟩,
     ⟨[103],.div .urem output 101 102⟩,⟨[104],.bmask input 103⟩,
     ⟨[105],.unary .bnot input 104⟩,⟨[],.nop⟩]
  {f with name := f.name ++ "_mixed",blocks := [{b with body,term := .ret [101]}]}

def nopFunction (config : Configuration) (ty : Clif.Ty) : Clif.Function :=
  let f := function config ty ty
  {f with name := f.name ++ "_nop",blocks := [{f.blocks[0]! with body := [⟨[],.nop⟩,⟨[],.nop⟩],term := .ret [1]}]}

/-- The same fixture cohort is used by fixed proofs, native execution and
ordinary compiler/consumer validation. -/
def functions (config : Configuration) : List (Clif.Function × Clif.Ty) :=
  let masks := widths.flatMap fun input => widths.flatMap fun output =>
    [(function config input output,input),(mixedFunction config input output,input)]
  let all := masks ++ widths.map (fun ty => (nopFunction config ty,ty))
  all.zipIdx.map fun ((f,ty),i) => ({f with name := s!"stock_mask_{i}"},ty)

end E2E.StockMaskNIWitness

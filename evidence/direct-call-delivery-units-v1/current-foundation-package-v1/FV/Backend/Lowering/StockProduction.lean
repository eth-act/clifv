import FV.Backend.Lowering.StockPrologue

/-! Additive rollout selector. Existing production entrypoints remain compatible
until their actual-output consumers migrate to this selector. -/
set_option autoImplicit false
namespace Backend.Stock.Production

def lowerWith (stock : Clif.Function → Except String Result) (f : Clif.Function) :
    Except String VCode :=
  let fallback := fun (_ : Unit) => D0.defaultLower f
  if Prologue.eligible f then
    match stock f with
    | .ok r =>
      if r.edgeArgs.all (fun row => row.all (·.isEmpty)) then .ok (D0.compact f.name r)
      else fallback ()
    | .error _ => fallback ()
  else fallback ()

def lower (f : Clif.Function) : Except String VCode := lowerWith Stock.lower f
end Backend.Stock.Production

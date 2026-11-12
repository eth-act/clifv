import FV.Backend
import FV.Backend.Proof.StockD0Dispatch

namespace Backend.Stock.D0.Compiler

def legacyLowerChecked (f : Clif.Function) (verify : Bool) : Except String VCode := do
  let vc ← lowerFunction f
  if verify && !Backend.lowerCheckFor f vc then
    throw "lowering rejected by the M7 lowering validator (lowerCheck)"
  pure vc

def legacyLowerForAllocation (f : Clif.Function) (verify deadCleanup : Bool) : Except String VCode :=
  (legacyLowerChecked f verify).map fun vc =>
    if deadCleanup then Backend.cleanupStageChecked verify f vc else vc

theorem lowerChecked_eq_legacy (f : Clif.Function) (verify : Bool) :
    Backend.lowerChecked f verify = legacyLowerChecked f verify := by
  simp only [Backend.lowerChecked, defaultLower_eq_legacy, legacyLowerChecked]

theorem lowerForAllocation_eq_legacy (f : Clif.Function) (verify cleanup : Bool) :
    Backend.lowerForAllocation f verify cleanup = legacyLowerForAllocation f verify cleanup := by
  simp only [Backend.lowerForAllocation, lowerChecked_eq_legacy, legacyLowerForAllocation]

/-- Equality for every allocator monad, including its effects, errors, all metadata,
verification settings, cleanup and mixed files. No allocator answer is constrained. -/
theorem compileFileWith_eq_legacy {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String)) (cleanup : Bool) :
    compileFileWith alloc pf preUnverified cleanup =
      compileFileWithLowering legacyLowerForAllocation VCode.rulesFired alloc pf preUnverified cleanup := by
  have lowering : Backend.lowerForAllocation = legacyLowerForAllocation := by
    funext f verify cleanup
    exact lowerForAllocation_eq_legacy f verify cleanup
  simp only [compileFileWith, lowering]

/-- An inhabited complete D0 source witnesses both validator/cleanup settings
and arbitrary allocator effects, including the old failure behavior. -/
theorem compiler_compatibility_witness {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc)))
    (name : String) (c : Configuration) (runs : List Clif.RunCommand)
    (verify cleanup : Bool) :
    Backend.lowerChecked (source name c runs) verify = legacyLowerChecked (source name c runs) verify ∧
    Backend.lowerForAllocation (source name c runs) verify cleanup =
      legacyLowerForAllocation (source name c runs) verify cleanup ∧
    compileFileWith alloc { header := [], funcs := [⟨name, .ok (source name c runs), 0⟩] } [] cleanup =
      compileFileWithLowering legacyLowerForAllocation VCode.rulesFired alloc
        { header := [], funcs := [⟨name, .ok (source name c runs), 0⟩] } [] cleanup := by
  exact ⟨lowerChecked_eq_legacy .., lowerForAllocation_eq_legacy .., compileFileWith_eq_legacy ..⟩

#print axioms lowerChecked_eq_legacy
#print axioms lowerForAllocation_eq_legacy
#print axioms compileFileWith_eq_legacy
#print axioms compiler_compatibility_witness
end Backend.Stock.D0.Compiler

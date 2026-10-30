import FV.Link.ProductionExe
import FV.Link.ProductionExeWith
import FV.Backend.Production
import FV.Backend.ProductionWith

/-! Exact compatibility with the published production functions. These equations
keep the old interfaces useful while new classes select the generic consumers. -/
set_option autoImplicit false
namespace Link.ProductionCompilerWith
open Backend E2E.LinkCheck

theorem input_original (S : LinkSpec) (cleanup : Bool) :
    input Stock.Production.lower S cleanup = ProductionCompiler.input S cleanup := rfl

theorem attempt_original (S : LinkSpec) (file0 : ByteArray) (cleanup : Bool) :
    attempt Stock.Production.lower S file0 cleanup = ProductionCompiler.attempt S file0 cleanup := rfl

theorem compile_original (S : LinkSpec) (file0 : ByteArray) (cleanup : Bool) :
    (compile Stock.Production.lower S file0 cleanup).map
      (fun o => (⟨o.file, o.stock⟩ : ProductionCompiler.Output)) =
      ProductionCompiler.compile S file0 cleanup := by
  unfold compile ProductionCompiler.compile
  rw [LinkSpec.placedProductionWith_original, attempt_original]
  cases h : ProductionCompiler.attempt (S.placedProduction cleanup) file0 cleanup with
  | ok file => rfl
  | error e =>
    change ((ProductionCompiler.legacyCompile (ProductionCompiler.legacySpec S cleanup) file0 cleanup).map
      (fun file => (⟨file,false⟩ : Output))).map
        (fun o => (⟨o.file,o.stock⟩ : ProductionCompiler.Output)) =
      (ProductionCompiler.legacyCompile (ProductionCompiler.legacySpec S cleanup) file0 cleanup).map
        (fun file => (⟨file,false⟩ : ProductionCompiler.Output))
    cases hl : ProductionCompiler.legacyCompile (ProductionCompiler.legacySpec S cleanup) file0 cleanup <;> rfl

end Link.ProductionCompilerWith

namespace Backend

theorem lowerCheckedProductionWith_original (f : Clif.Function) (verify : Bool) :
    lowerCheckedProductionWith Stock.Production.lower f verify = lowerCheckedProduction f verify := rfl

theorem lowerForAllocationProductionWith_original (f : Clif.Function) (verify cleanup : Bool) :
    lowerForAllocationProductionWith Stock.Production.lower f verify cleanup =
      lowerForAllocationProduction f verify cleanup := rfl

theorem hasStockPrologue_option (pf : Clif.ParsedFile) :
    pf.funcs.any (fun p => p.func.toOption.any Stock.Prologue.eligible) = hasStockPrologue pf := by
  unfold hasStockPrologue
  congr 1
  funext p
  cases p.func <;> rfl

theorem compileFileProductionWith_original {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String)) (cleanup : Bool) :
    compileFileProductionWith Stock.Production.lower Stock.Prologue.eligible
      alloc pf preUnverified cleanup = compileFileProduction alloc pf preUnverified cleanup := by
  unfold compileFileProductionWith compileFileProduction
  rw [hasStockPrologue_option]
  rfl

end Backend

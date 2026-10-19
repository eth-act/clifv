import FV.Backend.Proof.StockD0Code
import FV.Backend.Proof.IselPrgDriver

namespace Backend.Stock.D0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

private theorem legacy_succeeds (name : String) (c : Configuration) (runs : List Clif.RunCommand) :
    (lowerFunction (source name c runs)).isOk = true := by
  have hE : Compile.functionE (source name c runs) = true := by cases c <;> d0_open_kernel_decide
  have hs : sigAbiOk (source name c runs).sig = true := by cases c <;> d0_open_kernel_decide
  have hd : Backend.Proof.Driver.dominatedB (source name c runs) = true := by cases c <;> d0_open_kernel_decide
  have hl : Backend.Proof.Driver.lowerScopeB (source name c runs) = true := by cases c <;> d0_open_kernel_decide
  have ha : Backend.Proof.Spill.arityOkB (source name c runs) = true := by cases c <;> d0_open_kernel_decide
  have he : Backend.Proof.Spill.entryParamsB (source name c runs) = true := by cases c <;> d0_open_kernel_decide
  have hw : Backend.Proof.Driver.extendsWidenB (source name c runs) = true := by cases c <;> d0_open_kernel_decide
  have hdrv : Backend.Proof.Driver.driverInB (source name c runs) = true := by cases c <;> d0_open_kernel_decide
  have hi : Backend.Proof.Prg.iselInB (source name c runs) = true := by cases c <;> d0_open_kernel_decide
  obtain ⟨vc, hv⟩ := Backend.Proof.Prg.lowerFunction_ok_input hE hs hd hl ha he hw hdrv hi
  rw [hv]
  rfl

/-- The selected class is inhabited for arbitrary names and run metadata. -/
theorem source_eligible (name : String) (c : Configuration) (runs : List Clif.RunCommand) :
    eligible (source name c runs) = true := by
  have member : c ∈ configurations := by cases c <;> simp [configurations]
  apply List.any_eq_true.mpr
  refine ⟨c, member, ?_⟩
  exact decide_eq_true rfl

/-- Actual Stock success, ruling out equality through joint rejection. -/
theorem stock_succeeds (name : String) (c : Configuration) (runs : List Clif.RunCommand) :
    ∃ result, Stock.lower (source name c runs) = .ok result := by
  have hn := normalized_eq_legacy name c runs
  cases hs : Stock.lower (source name c runs) with
  | error e =>
    have hi := legacy_succeeds name c runs
    rw [← hn, hs] at hi
    cases hi
  | ok result => exact ⟨result, rfl⟩

#print axioms source_eligible
#print axioms stock_succeeds
end Backend.Stock.D0

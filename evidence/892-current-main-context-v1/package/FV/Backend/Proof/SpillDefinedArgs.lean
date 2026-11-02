import FV.Backend.Proof.KillAssemble
import FV.Backend.Proof.SpillDefinedPaths

/-!
# Branch arguments of `lowerFunction`'s VCode (`ParamArgs`)

`paramArgs_of_lowOk`: in a VCode meeting `LowOk` (`lowerFunction`'s, `lowOk_of`), every edge
into a block with parameters passes a branch argument for each: a block without branch arguments
targets parameterless blocks (`LowOk.noArgs`), and a block with branch arguments ends in a `jump`
to a block with as many parameters (`LowOk.args`).
-/

namespace Backend.Proof.Spill

open Backend

theorem paramArgs_of_lowOk {vc : VCode} (hv : LowOk vc) : ParamArgs vc := by
  intro succs preds hc b vb ss s sb hb hss hs hsb k p hp
  obtain ⟨t0, ts, ht0, -⟩ := (Prep.cfg_spec hc).blk b vb hb
  have hst := Kill.asm_succs hv hc hb ht0 hss
  have hst' : s ∈ t0.targets := by rw [← hst]; exact hs
  by_cases hba : vb.branchArgs = #[]
  · have := hv.noArgs b vb t0 s sb hb hba ht0 hst' hsb
    rw [this] at hp
    simp at hp
  · obtain ⟨l, tb, hj, htb, hsz, -, -⟩ := hv.args b vb hb hba
    rw [hj] at ht0
    cases ht0
    have hsl : s = l := by simpa [MInst.targets] using hst'
    subst hsl
    rw [hsb] at htb
    cases htb
    have hk : k < sb.params.size := (Array.getElem?_eq_some_iff.mp hp).1
    exact ⟨_, Array.getElem?_eq_getElem (by omega)⟩

/-- `defined_of_paths` without the CFG premise (`DefAvail` holds vacuously without a CFG). -/
theorem defined_of_paths' {vc : VCode} (hU : UsesDefined vc) (hP : ParamArgs vc) :
    ∃ M, DefAvail vc M ∧ ∀ v, M 0 v = false := by
  cases hc : vc.cfg with
  | ok r => exact defined_of_paths ⟨r.1, r.2, hc⟩ hU hP
  | error e =>
    refine ⟨fun _ _ => false, ⟨?_, ?_⟩, fun _ => rfl⟩
    · intro _ _ h; rw [hc] at h; cases h
    · intro _ _ h; rw [hc] at h; cases h

end Backend.Proof.Spill

import FV.Front.Bundle
import FV.Link.DeadCleanupImage

/-! # When `lean-link` names the frontend theorems on the typed route (#1088)

`Front.bundle_correct_rawT` and `Front.bundle_correct_raw_peakT` (`FV/Front/ExeT.lean`) are about
the `LinkSpec` `S` of a bundle `b` (`hb : buildSpec b = .ok S`), compiled by
`Link.DeadCleanup.compileExeT S file0 = .ok file`, in the source domain
(`hsrc : SrcScopeB S.inputCleanup`). `lean-link` compiles the Lean compiler's placement of the
constant-phi-removed spec (`DeadCleanup.placedPar S0.cp`, #1036), which is `buildSpec` of no
bundle when constant-phi removal changes a function (`S0.cpChanged ≠ []`: `FnInput.cp` changes
that function's CLIF text, `buildSpec` keeps the bundle's). So `lean-link` names the two theorems
only where both premises are decided of the spec it compiled (`rawTNamed`, `rawTNamed_premises`),
with `b` the bundle it read with the placed sizes; otherwise its coverage line says that no Front
theorem is named and why (`rawTClause`).
-/

deriving instance DecidableEq for E2E.LinkCheck.FnInput
deriving instance DecidableEq for Link.LinkSpec

namespace Front

open E2E.LinkCheck Link

/-- `buildSpec b = .ok S`, decided. -/
def buildsB (b : Bundle) (S : LinkSpec) : Bool :=
  match buildSpec b with
  | .ok S' => decide (S' = S)
  | .error _ => false

theorem buildsB_eq {b : Bundle} {S : LinkSpec} (h : buildsB b S = true) : buildSpec b = .ok S := by
  unfold buildsB at h
  split at h
  · rename_i S' hS
    rw [hS, of_decide_eq_true h]
  · cases h

/-- `SrcScopeB` reads the functions only, which `inputCleanup` keeps. -/
theorem srcScopeB_inputCleanup (S : LinkSpec) : SrcScopeB S.inputCleanup = SrcScopeB S.input0 := rfl

/-- **The premises `hb` and `hsrc` of `bundle_correct_rawT{,_peak}`, decided**, skipped (`false`)
when constant-phi removal changed `cpN ≠ 0` functions (then `S`'s functions are not the bundle's). -/
def rawTNamed (cpN : Nat) (b : Bundle) (S : LinkSpec) : Bool :=
  cpN == 0 && buildsB b S && SrcScopeB S.input0

theorem rawTNamed_premises {cpN : Nat} {b : Bundle} {S : LinkSpec} (h : rawTNamed cpN b S = true) :
    buildSpec b = .ok S ∧ SrcScopeB S.inputCleanup = true := by
  simp only [rawTNamed, Bool.and_eq_true] at h
  exact ⟨buildsB_eq h.1.2, by rw [srcScopeB_inputCleanup]; exact h.2⟩

/-- The theorems named when `rawTNamed` holds. -/
def rawTNames : String := "Front.bundle_correct_rawT, Front.bundle_correct_raw_peakT"

/-- **The frontend clause of `lean-link`'s `compileExeT` coverage line**: `rawTNames` exactly
when `rawTNamed cpN b S` (`b`: the bundle read, with the placed sizes; `S`: the spec compiled),
otherwise the reason no Front theorem is named. -/
def rawTClause (cpN : Nat) (b : Bundle) (S : LinkSpec) : String :=
  if rawTNamed cpN b S then s!"cg_clif's program: {rawTNames}"
  else if cpN != 0 then
    s!"cg_clif's program: no Front theorem is named (constant-phi removal changed {cpN} function(s), so the compiled spec is not the bundle's, the premise of Front.bundle_correct_rawT; #1088)"
  else
    "cg_clif's program: no Front theorem is named (the compiled spec is not buildSpec of the bundle with the placed sizes, or not in SrcScopeB; #1088)"

end Front

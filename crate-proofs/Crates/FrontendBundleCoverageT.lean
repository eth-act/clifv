import Crates.FrontendBundleWitness
import FV.Front.CoverageT
import FV.Link.Placed
import FV.Link.CpSourceWitness

/-! # `lean-link`'s frontend clause on the typed route (#1088), on a real bundle

`lean-link --verified` prints, on the `Link.DeadCleanup.compileExeT` route, `Front.rawTClause`
of the number of functions constant-phi removal changed, the bundle it read with the placed
sizes, and the spec it compiled (`DeadCleanup.placedPar S0.cp`). Its three cases, evaluated as
`lean-link` evaluates them (`native_decide`, test only):
* `named`: the bundle `bw` of `Crates.FrontendBundleWitness` (cg_clif's `wmul_u128` and the local
  `wrapping_mul` of the survey crate `g_u128`), where constant-phi removal changes nothing: the
  compiled spec is `buildSpec` of the bundle with the placed sizes and in `SrcScopeB`, so the
  clause names `Front.bundle_correct_rawT{,_peak}`, and their premises `hb`, `hsrc` hold
  (`named_premises`, from `Front.rawTNamed_premises`);
* `cpChanged`: `Link.CpSourceWitness.S0`, where constant-phi removal changes `f`: no Front
  theorem is named, with the reason;
* `notBuilt`: a spec that is not the bundle's (the region moved by a word): no Front theorem is
  named, with the reason.
-/

namespace Crates.FrontendBundleCoverageT

open Crates.FrontendBundleWitness (bw S)

/-- What `lean-link` compiles for `bw`: the cleanup placement of the constant-phi-removed spec. -/
def SC : Link.LinkSpec := Link.DeadCleanup.placedPar S.cp

/-- The bundle with the placed sizes (`lean-link`'s `{ b0 with sizes := SC.names.zip SC.sizes }`). -/
def bP : Front.Bundle := { bw with sizes := SC.names.zip SC.sizes }

theorem cp_none : S.cpChanged = [] := by native_decide -- test: native_decide

theorem named : Front.rawTClause S.cpChanged.length bP SC =
    "cg_clif's program: Front.bundle_correct_rawT, Front.bundle_correct_raw_peakT" := by
  native_decide -- test: native_decide

theorem named_premises : Front.buildSpec bP = .ok SC ∧ E2E.LinkCheck.SrcScopeB SC.inputCleanup = true :=
  Front.rawTNamed_premises (cpN := S.cpChanged.length) (by native_decide) -- test: native_decide

theorem cpChanged : Front.rawTClause Link.CpSourceWitness.S0.cpChanged.length bP SC =
    "cg_clif's program: no Front theorem is named (constant-phi removal changed 1 function(s), so the compiled spec is not the bundle's, the premise of Front.bundle_correct_rawT; #1088)" := by
  native_decide -- test: native_decide

theorem notBuilt : Front.rawTClause 0 bP { SC with R := SC.R + 4 } =
    "cg_clif's program: no Front theorem is named (the compiled spec is not buildSpec of the bundle with the placed sizes, or not in SrcScopeB; #1088)" := by
  native_decide -- test: native_decide

end Crates.FrontendBundleCoverageT

import FV.Concurrency.Armv8Full
import FVTest.Concurrency.Litmus
import FV.Concurrency.Witness

/-!
# Litmus tests of the full Armv8 model (`aarch64.cat`, T2g #305)

* `mp_full`: MP (plain) with no dependencies is consistent for the full model, and so
  (`Armv8Full.consistent_frag`) for the fragment (non-vacuity of the monotonicity theorem);
* `mp_dmb_addr`: MP+dmb+addr (`str x; dmb; str y ‖ ldr y; ldr x` with an address dependency
  between the loads), outcome y=1, x=0: **forbidden** by herd7, forbidden by the full model (the
  `dob` edge closes an `ob` cycle), **allowed** by the fragment (which ignores dependencies): the
  fragment is strictly weaker.
-/

namespace Concurrency.Litmus

open Rel

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-- The full-model kinds of a litmus test. -/
abbrev Lit.fk {n : Nat} (t : Lit n) (e : Fin n) : FKind := .frag (t.ak e)

/-- Dependencies: only address dependencies, as a list. -/
abbrev addrDeps {n : Nat} (addr : List (Nat × Nat)) : Armv8Full.Deps (Fin n) :=
  ⟨fun a b => (a.val, b.val) ∈ addr, fun _ _ => False, fun _ _ => False⟩

/-- **MP: allowed by the full model** (no dependencies), and so by the fragment. -/
theorem mp_full : Armv8Full.Consistent (mpT .plainW .plainR).exec (mpT .plainW .plainR).fk
      (addrDeps []) ∧
    Armv8.Consistent (mpT .plainW .plainR).exec (mpT .plainW .plainR).ak := by
  have h : Armv8Full.Consistent (mpT .plainW .plainR).exec (mpT .plainW .plainR).fk
      (addrDeps []) :=
    { internal := acyclic_of_rank mpRank (by
        simp only [union, Exec.poLoc, Exec.com, Exec.fr]; decide)
      atomic := by simp only [Exec.ext, Exec.fr]; decide
      external := acyclic_of_rank mpRank (by
        simp only [Armv8Full.ob, Armv8.obs, Armv8Full.dob, Armv8Full.aob, Armv8Full.bob,
          Armv8Full.A, Armv8Full.Q, Armv8Full.L, Armv8Full.rfi, Armv8Full.coi, Exec.ext, Exec.fr]
        decide) }
  exact ⟨h, Armv8Full.consistent_frag h⟩

/-- MP+dmb+addr. Events: 0 init x, 1 init y; thread 0: 2 `str x`, 3 `dmb`, 4 `str y`; thread 1:
5 `ldr y` (reads 4), 6 `ldr x` (reads 0; its address depends on 5). -/
def mpDmbAddr : Lit 7 where
  tid := [10, 11, 0, 0, 0, 1, 1]
  kind := [.plainW, .plainW, .plainW, .dmb, .plainW, .plainR, .plainR]
  loc := [0, 1, 0, 9, 1, 1, 0]
  po := [(2, 3), (2, 4), (3, 4), (5, 6)]
  rf := [(4, 5), (0, 6)]
  co := [(0, 2), (1, 4)]

/-- **MP+dmb+addr: allowed by the fragment** (it ignores the dependency). -/
theorem mp_dmb_addr_frag : mpDmbAddr.exec.Wf ∧ Armv8.Consistent mpDmbAddr.exec mpDmbAddr.ak := by
  refine ⟨by constructor <;> decide, ?_⟩
  consistent_by (fun e : Fin 7 => ([0, 0, 2, 2, 3, 4, 1] : List Nat).getD e.val 0)

/-- **MP+dmb+addr: forbidden by the full model** (herd7's verdict): `bob` (the `dmb`), `rfe`,
`dob` (the address dependency), `fre`. -/
theorem mp_dmb_addr_full :
    ¬ Armv8Full.Consistent mpDmbAddr.exec mpDmbAddr.fk (addrDeps [(5, 6)]) := fun hc =>
  hc.external 2 (PathTo.plus (l := [4, 5, 6]) (by
    simp only [PathTo, Armv8Full.ob, Armv8.obs, Armv8Full.dob, Armv8Full.aob, Armv8Full.bob,
      Armv8Full.A, Armv8Full.Q, Armv8Full.L, Armv8Full.rfi, Armv8Full.coi, Exec.ext, Exec.fr]
    decide))

end Concurrency.Litmus

namespace Concurrency.Witness

open Rel

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-- **Non-vacuity of `Mapping.armv8full_to_clif`/`armv8full_to_clifF`**: the two LL/SC increments
`incX` (with a failed iteration) are consistent for the full model (no dependencies). -/
theorem incX_full :
    Armv8Full.Consistent incX (fun e => .frag (incAK e)) (Litmus.addrDeps []) ∧
      ClifMM.Consistent (incX.restrict incS) (Mapping.srcKind incSK incS) ∧
      ClifMM.ConsistentF (incX.restrict incS) (Mapping.srcKind incSK incS) := by
  have h : Armv8Full.Consistent incX (fun e => .frag (incAK e)) (Litmus.addrDeps []) :=
    { internal := incX_consistent.internal
      atomic := incX_consistent.atomic
      external := acyclic_of_rank incRank (by
        simp only [Armv8Full.ob, Armv8.obs, Armv8Full.dob, Armv8Full.aob, Armv8Full.bob,
          Armv8Full.A, Armv8Full.Q, Armv8Full.L, Armv8Full.rfi, Armv8Full.coi, Exec.ext, Exec.fr]
        decide) }
  refine ⟨h, Mapping.armv8full_to_clif _ incX_wf h incX_compiled,
    Mapping.armv8full_to_clifF _ incX_wf incX_compiled incX_kind h ?_⟩
  intro a b _ _ hr
  revert hr; revert a b; decide

end Concurrency.Witness

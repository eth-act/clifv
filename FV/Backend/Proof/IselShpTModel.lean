module

public import FV.Backend.Proof.IselShpTCtor
public import FV.Backend.Proof.IselShpOracle
public import FV.Backend.Proof.IselCovTModel
public import FV.Backend.Proof.IselShpTotal

@[expose] public section

/-!
# Control shapes of the typed ISLE lowering: the oracles and the model

* `oracle_ctlT`: the control-form oracles (`load_ext_name_got/near`, `elf_tls_get_addr`,
  `atomic_rmw_loop`, `atomic_cas_loop`) keep `ShpIsT` and return an int vreg. Their runs do not
  depend on the context, so the integer proofs (`Cov.got_ok`, …) give them from the run's own
  start state (`ShpIsT.of_shpIs`); the int-vreg operands come from the typed `isV_sound`.
* `oracleST_sound`: the typed `operand_size` oracle (`oracle_sound`, state unchanged) and the
  control-form oracles.
* `shpModelT`: the typed control-shape model (`apreST`/`aOracleST`, invariant `ShpIsT N s0`).
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Spill Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
open Backend.Proof.Cov (Totality IntAt got_ok near_ok tls_ok rmw_ok cas_ok os_run CovSince
  LogicImmComplete Clean ShpIs)

variable {f : Clif.Function} {ctx : Ctx}

/-- An integer `γ (.reg m)` is a typed one. -/
theorem γ_reg_of_cov {m : Nat} {v : V} (h : Cov.γ f ctx (.reg m) v) : γ f ctx (.reg m) v := by
  obtain ⟨r, rfl, hk⟩ := h
  exact ⟨r, rfl, hk⟩

theorem intAtT_of {as : List AT} {vs : List V} (hvs : Holds2 f ctx as vs) {k : Nat} {a : AT}
    (ha : as[k]? = some a) (hv : a.isV = true) : IntAt vs k :=
  fun _ hr => isV_sound hv (γL_get hvs k a _ ha hr)

/-- **The control-form oracles are sound at every fuel** (typed domain). -/
theorem oracle_ctlT (htot : Totality) {N : Nat} {s0 : LState} {cfg : Config}
    (hc : cfg.checkOverlap = false) {n : Nat} {ty : TypeId} {t : TermId} {as : List AT}
    {vs : List V} {s : LState} {tr : Array RuleId} {r : Option V} {s' : LState}
    {tr' : Array RuleId} (ha : ctlOracleT t as = true) (hvs : Holds2 f ctx as vs)
    (hIs : ShpIsT N s0 s)
    (h : (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    ShpIsT N s0 s' ∧ ∀ v, r = some v → γ f ctx (.reg 1) v := by
  have fin : ShpIs N s s' ∧ (∀ v, r = some v → Cov.γ f ctx (.reg 1) v) →
      ShpIsT N s0 s' ∧ ∀ v, r = some v → γ f ctx (.reg 1) v :=
    fun h' => ⟨hIs.of_shpIs h'.1, fun v hv => γ_reg_of_cov (h'.2 v hv)⟩
  have hs := hIs.shpIs_self
  unfold ctlOracleT at ha
  split at ha
  · rename_i ht
    simp only [Bool.or_eq_true, beq_iff_eq] at ht
    rcases ht with (rfl | rfl) | rfl
    · exact fin (got_ok htot hc hs h)
    · exact fin (near_ok htot hc hs h)
    · exact fin (tls_ok htot hc hs h)
  split at ha
  · rename_i ht
    obtain rfl : t = 612 := eq_of_beq ht
    split at ha
    · simp only [Bool.and_eq_true] at ha
      exact fin (rmw_ok htot hc hs (intAtT_of hvs (k := 1) rfl ha.1)
        (intAtT_of hvs (k := 2) rfl ha.2) h)
    · cases ha
  split at ha
  · rename_i ht
    obtain rfl : t = 613 := eq_of_beq ht
    split at ha
    · simp only [Bool.and_eq_true] at ha
      exact fin (cas_ok htot hc hs (intAtT_of hvs (k := 0) rfl ha.1.1)
        (intAtT_of hvs (k := 1) rfl ha.1.2) (intAtT_of hvs (k := 2) rfl ha.2) h)
    · cases ha
  cases ha

/-- The typed oracles are sound: `operand_size` (state unchanged) and the control helpers. -/
theorem oracleST_sound (N : Nat) (s0 : LState) (cfg : Config)
    (hc : cfg.checkOverlap = false) (n : Nat) (ty : TypeId) (t : TermId) (as : List AT) (vs : List V)
    (a : AT) (s : LState) (tr : Array RuleId) (r : Option V) (s' : LState) (tr' : Array RuleId)
    (ha : aOracleST t as = some a) (hvs : Holds2 f ctx as vs) (hIs : ShpIsT N s0 s)
    (h : (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    ShpIsT N s0 s' ∧ ∀ v, r = some v → γ f ctx a v := by
  unfold aOracleST at ha
  cases hos : aOracle t as with
  | some a' =>
    rw [hos] at ha
    cases ha
    have hγ := (oracle_sound s cfg hc n ty t as vs a s tr r s' tr' hos hvs ⟨[], by simp, by simp⟩ h).2
    have ht : t = 305 := by
      unfold aOracle at hos
      split at hos
      · exact eq_of_beq ‹_›
      · cases hos
    subst ht
    have hs := (os_run hc h).1
    simp only at hs
    subst hs
    exact ⟨hIs, hγ⟩
  | none =>
    rw [hos] at ha
    simp only at ha
    split at ha
    · cases ha
      exact oracle_ctlT Cov.totality hc ‹_› hvs hIs h
    · cases ha

/-- **The typed control-shape model**: state invariant `ShpIsT N s0`. -/
def shpModelT (hLI : LogicImmComplete) (hctx : CtxInvT f ctx) (hcl : Clean ctx)
    (hfam : FamCover ctx) (N : Nat) (s0 : LState) :
    CovModel aext actor apreST aOracleST program f ctx where
  Is := ShpIsT N s0
  ext := fun a term v st fs hv h => ext_sound hctx hcl hfam a term v st fs hv h
  ctor := fun as vs term v st st' hvs hIs hpre h =>
    ctorST_sound hLI hctx N s0 as vs term v st st' hvs hIs hpre h
  oracle := oracleST_sound N s0

@[simp] theorem shpModelT_Is (hLI : LogicImmComplete) (hctx : CtxInvT f ctx) (hcl : Clean ctx)
    (hfam : FamCover ctx) (N : Nat) (s0 : LState) :
    (shpModelT hLI hctx hcl hfam N s0).Is = ShpIsT N s0 := rfl

end Backend.Proof.CovT

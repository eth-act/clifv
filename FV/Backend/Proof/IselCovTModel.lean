import FV.Backend.Proof.IselCovTCtor
import FV.Backend.Proof.IselCovModel

/-!
# Form coverage over float-capable contexts (typed V3): the model

`covModelT`: `IselCovModel`'s `covModel` over a float-capable context (`CtxInvT`) whose
statements belong to the instruction families (`FamCover`): state invariant `CovSince s0`, the
typed `ext_sound`/`ctor_sound`, and the `operand_size` oracle (`Cov.os_run`, at every fuel).
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
open Backend.Proof.Cov (Clean LogicImmComplete os_run)

set_option maxRecDepth 20000

variable {f : Clif.Function} {ctx : Ctx}

theorem γ_os {k : Nat} : γ f ctx .c0 (.data 93 k []) :=
  ⟨fun r hr => by simp [V.regsIn, regsInL] at hr, fun _ => rfl⟩

/-- **The `operand_size` oracle is sound at every fuel** (typed domain). -/
theorem oracle_sound (s0 : LState) (cfg : Config) (hc : cfg.checkOverlap = false) (n : Nat)
    (ty : TypeId) (t : TermId) (as : List AT) (vs : List V) (a : AT) (s : LState)
    (tr : Array RuleId) (r : Option V) (s' : LState) (tr' : Array RuleId)
    (ha : aOracle t as = some a) (hvs : Holds2 f ctx as vs) (hIs : CovSince s0 s)
    (h : (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    CovSince s0 s' ∧ ∀ v, r = some v → γ f ctx a v := by
  unfold aOracle at ha
  split at ha
  case isFalse => cases ha
  rename_i ht
  have ht : t = 305 := eq_of_beq ht
  subst ht
  obtain ⟨hs, v0, rfl, hv0⟩ := os_run hc h
  cases hs
  refine ⟨hIs, fun v hv => ?_⟩
  cases hv
  split at ha
  · rename_i t1
    cases ha
    rcases vs with _ | ⟨w, ws⟩
    · exact absurd hvs id
    have hw : γ f ctx (.ty [t1]) w ∧ γL f ctx [] ws := hvs
    obtain rfl : ws = [] := by
      cases ws with
      | nil => rfl
      | cons _ _ => exact absurd hw.2 id
    obtain ⟨t', ht', rfl⟩ := hw.1
    obtain rfl := List.mem_singleton.mp ht'
    rcases hv0 with ⟨rfl, h32⟩ | ⟨rfl, h64⟩
    · simp only [h32 _ rfl, ↓reduceIte]
      exact ⟨[], rfl, trivial⟩
    · obtain ⟨hn, hb⟩ := h64 _ rfl
      simp only [hn, hb, ↓reduceIte]
      exact ⟨[], rfl, trivial⟩
  · cases ha
    rcases hv0 with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact γ_os

/-- **The typed coverage model**: state invariant `CovSince s0`. -/
def covModelT (hLI : LogicImmComplete) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hcl : Clean ctx) (hfam : FamCover ctx) (s0 : LState) :
    CovModel aext actor apre aOracle program f ctx where
  Is := CovSince s0
  ext := fun a term v st fs hv h => ext_sound hctx hcl hfam a term v st fs hv h
  ctor := fun as vs term v st st' hvs hIs hpre h =>
    ctor_sound hLI hctx s0 as vs term v st st' hvs hIs hpre h
  oracle := oracle_sound s0

@[simp] theorem covModelT_Is (hLI : LogicImmComplete) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInvT f ctx) (hcl : Clean ctx) (hfam : FamCover ctx) (s0 : LState) :
    (covModelT hLI hctx hcl hfam s0).Is = CovSince s0 := rfl

end Backend.Proof.CovT

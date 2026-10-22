import FV.Backend.Proof.IselCovModel
import FV.Backend.Proof.IselCovSoundT
import FV.Backend.Proof.IselCovExtT
import FV.Backend.Proof.IselCovCtorT

/-!
# Form coverage over float-capable contexts: the model

`oracle_soundT`: the `operand_size` oracle at every fuel, over `γT`. `covModelT`: the
`CovModelT` of the driver's semantics at the typed scope (`Compile.instET`, opcode split
`opsT`/`floatOps`), with state invariant `CovSince s0`, from `ext_soundT` (`IselCovExtT`) and
`ctor_soundT` (`IselCovCtorT`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx}

theorem oracle_soundT (s0 : LState) (cfg : Config) (hc : cfg.checkOverlap = false) (n : Nat)
    (ty : TypeId) (t : TermId) (as : List AW) (vs : List V) (a : AW) (s : LState)
    (tr : Array RuleId) (r : Option V) (s' : LState) (tr' : Array RuleId)
    (ha : aOracle t as = some a) (hvs : Holds2T S iOps fOps f ctx as vs) (hIs : CovSince s0 s)
    (h : (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    CovSince s0 s' ∧ ∀ v, r = some v → γT S iOps fOps f ctx a v := by
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
    have hw : γT S iOps fOps f ctx (.ty [t1]) w ∧ γLT S iOps fOps f ctx [] ws := hvs
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
    rcases hv0 with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact γ_osT

/-- **The coverage model** over float-capable contexts: state invariant `CovSince s0`. -/
def covModelT (hLI : LogicImmComplete) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInvT f ctx) (hsp : InstSplit Compile.instET f ctx opsT floatOps)
    (hsc : InstScopeT ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true)
    (hcl : Clean ctx) (s0 : LState) :
    CovModelT aextT actorC apre aOracle Compile.instET opsT floatOps program f ctx where
  Is := CovSince s0
  ext := fun a term v st fs hv h => ext_soundT hctx hsp hsc hx hcl a term v st fs hv h
  ctor := fun as vs term v st st' hvs hIs hpre h =>
    ctor_soundT hLI hctx s0 as vs term v st st' hvs hIs hpre h
  oracle := oracle_soundT s0

@[simp] theorem covModelT_Is (hLI : LogicImmComplete) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInvT f ctx) (hsp : InstSplit Compile.instET f ctx opsT floatOps)
    (hsc : InstScopeT ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true)
    (hcl : Clean ctx) (s0 : LState) :
    (covModelT hLI hctx hsp hsc hx hcl s0).Is = CovSince s0 := rfl

end Backend.Proof.Cov

import FV.Backend.Proof.IselSzExt
import FV.Backend.Proof.IselSzDefsT
import FV.Backend.Proof.IselCovSemT

/-!
# The size of the ISLE lowering's output over float-capable contexts: the extern weights

The typed counterpart of `IselSzExt`: `extWT_wt`/`extWT_tg` (an extern constructor call grows the
weight `wtA` of the emitted instructions by at most `actorW`, their branch targets `tgA` by at
most `actorT`) and `oracleWT_wt`/`oracleWT_tg`, over `γLT`.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64


theorem γL_single {as : List AW} {i : V} (h : γLT S iOps fOps f ctx as [i]) : ∃ a, as = [a] ∧ γT S iOps fOps f ctx a i :=
  holds2_oneT h


/-- **`emitW`**: an instruction `emit` builds from a value `a` describes weighs at most
`emitW a`. -/
theorem emitW_soundT {a : AW} {c : Nat} (ha : emitW a = some c) {v : V} (hv : γT S iOps fOps f ctx a v)
    {m : MInst} (hm : MInst.ofV v = some m) : szInstW m ≤ c := by
  cases a with
  | data t k fs =>
    simp only [emitW] at ha
    split at ha
    · cases ha
      obtain ⟨vs, rfl, -⟩ := hv
      exact emitW_data ‹_› hm
    · cases ha
  | alts as =>
    simp only [emitW] at ha
    split at ha
    · cases ha
      rename_i hall
      obtain ⟨b, hb, hbv⟩ := γAnyT_iff.mp hv
      have hp := List.all_eq_true.mp hall b hb
      cases b with
      | data t k fs =>
        obtain ⟨vs, rfl, -⟩ := hbv
        exact emitW_data hp hm
      | _ => cases hp
    · cases ha
  | _ => cases ha


/-- **`emitT`**: an instruction `emit` builds from a value `a` describes has at most `emitT a`
branch targets. -/
theorem emitT_soundT {a : AW} {n : Nat} (ha : emitT a = some n) {v : V} (hv : γT S iOps fOps f ctx a v)
    {m : MInst} (hm : MInst.ofV v = some m) : m.targets.length ≤ n := by
  cases a with
  | data t k fs =>
    simp only [emitT] at ha
    split at ha
    · rename_i ht
      obtain rfl : t = tyMInst := eq_of_beq ht
      obtain ⟨vs, rfl, -⟩ := hv
      exact varT_sound ha hm
    · cases ha
  | alts as =>
    simp only [emitT, Option.map_eq_some_iff] at ha
    obtain ⟨ns, hns, rfl⟩ := ha
    obtain ⟨b, hb, hbv⟩ := γAnyT_iff.mp hv
    obtain ⟨nb, hnb, hg⟩ := mapM_some_mem hns b hb
    refine Nat.le_trans ?_ (mem_le_foldl_max ns 0 nb hnb)
    cases b with
    | data t k fs =>
      simp only at hg
      split at hg
      · rename_i ht
        obtain rfl : t = tyMInst := eq_of_beq ht
        obtain ⟨vs, rfl, -⟩ := hbv
        exact varT_sound hg hm
      · cases hg
    | _ => cases hg
  | _ => cases ha

/-! ## `load_constant_full` -/


/-- **Extern constructors** grow the weight of the emitted instructions by at most `actorW`. -/
theorem extWT_wt : ExtWT S iOps fOps f ctx apre actorW (fun s => wtA s.emitted) := by
  intro as vs term v st st' c hvs _ hc h
  rcases externCtor_sz ctx term vs st v st' h with
    he | ⟨hid, i, m, rfl, hm, he⟩ | ⟨hid, hw, -⟩ | ⟨hid, l, hl, he⟩ | ⟨hid, -⟩
  · simp only [he]; omega
  · obtain ⟨a, rfl, ha⟩ := γL_single hvs
    rw [hid] at hc
    simp only [actorW, beq_self_eq_true, ↓reduceIte] at hc
    simp only [he, wtA_push]
    have := emitW_soundT hc ha hm
    omega
  · rw [hid] at hc
    simp only [actorW] at hc
    cases hc
    exact hw
  · rw [hid] at hc
    simp only [actorW] at hc
    cases hc
    simp only [he, wtA_push]
    have : szInstW (.rets l) ≤ retsW := by
      simp only [szInstW, szWords, regCount, MInst.targets, retsW, List.length_nil]
      omega
    omega
  · rw [hid] at hc
    simp only [actorW] at hc
    cases hc


/-- **Extern constructors** grow the branch targets of the emitted instructions by at most
`actorT`. -/
theorem extWT_tg : ExtWT S iOps fOps f ctx apre actorT (fun s => tgA s.emitted) := by
  intro as vs term v st st' c hvs _ hc h
  rcases externCtor_sz ctx term vs st v st' h with
    he | ⟨hid, i, m, rfl, hm, he⟩ | ⟨-, -, ht⟩ | ⟨-, l, -, he⟩ | ⟨-, ht⟩
  · simp only [he]; omega
  · obtain ⟨a, rfl, ha⟩ := γL_single hvs
    rw [hid] at hc
    simp only [actorT, beq_self_eq_true, ↓reduceIte] at hc
    simp only [he, tgA_push]
    have := emitT_soundT hc ha hm
    omega
  · simp only [ht]; omega
  · simp only [he, tgA_push, MInst.targets, List.length_nil]; omega
  · simp only [ht]; omega


/-- **The oracle's runs** do not grow the weight of the emitted instructions. -/
theorem oracleWT_wt : OracleWT S iOps fOps program f ctx aOracle (fun s => wtA s.emitted) := by
  intro cfg hc n ty t as vs a s tr r s' tr' ha _ h
  rw [oracle_keeps hc ha h]
  exact Nat.le_refl _


/-- **The oracle's runs** do not grow the branch targets of the emitted instructions. -/
theorem oracleWT_tg : OracleWT S iOps fOps program f ctx aOracle (fun s => tgA s.emitted) := by
  intro cfg hc n ty t as vs a s tr r s' tr' ha _ h
  rw [oracle_keeps hc ha h]
  exact Nat.le_refl _


end Backend.Proof.Cov

import FV.Backend.Proof.IselSzTDefs
import FV.Backend.Proof.IselSzExt
import FV.Backend.Proof.IselCovTCtor

/-!
# The size of the ISLE lowering's output over float-capable contexts (typed V6c): the extern
helpers and the oracle

`IselSzExt`'s facts for the typed transfer functions (`Backend.Proof.CovT`): `extW_wt`/`extW_tg`
(`ExtW`: an extern constructor call grows `wtA` by at most `actorW`, `tgA` by at most `actorT`;
what a call emits is `IselSzExt.externCtor_sz`, which does not depend on the abstract domain) and
`oracleW_wt`/`oracleW_tg` (`OracleW`: the `operand_size` oracle keeps the lowering state).
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Proof.Cov (szInstW wtA tgA wtA_push tgA_push emitK varT loadConstW retsW ofV_sz
  varT_sound mem_le_foldl_max externCtor_sz os_run szWords regCount restW)

variable {f : Clif.Function} {ctx : Ctx}

theorem emitW_data {t k : Nat} {vs : List V} {m : MInst}
    (h : (t == tyMInst && (k != VIdx.MInst.Call && k != VIdx.MInst.CallInd &&
      k != VIdx.MInst.JTSequence)) = true) (hm : MInst.ofV (.data t k vs) = some m) :
    szInstW m ≤ emitK := by
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨rfl, ⟨h1, h2⟩, h3⟩ := h
  exact (ofV_sz hm).1 h1 h2 h3

/-- **`emitW`**: an instruction `emit` builds from a value `a` describes weighs at most
`emitW a`. -/
theorem emitW_sound {a : AT} {c : Nat} (ha : emitW a = some c) {v : V} (hv : γ f ctx a v)
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
      obtain ⟨b, hb, hbv⟩ := γAny_iff.mp hv
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
theorem emitT_sound {a : AT} {n : Nat} (ha : emitT a = some n) {v : V} (hv : γ f ctx a v)
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
    obtain ⟨b, hb, hbv⟩ := γAny_iff.mp hv
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

/-! ## The facts `ExtW` and `OracleW` -/

/-- **Extern constructors** grow the weight of the emitted instructions by at most `actorW`. -/
theorem extW_wt : ExtW f ctx apre actorW (fun s => wtA s.emitted) := by
  intro as vs term v st st' c hvs _ hc h
  rcases externCtor_sz ctx term vs st v st' h with
    he | ⟨hid, i, m, rfl, hm, he⟩ | ⟨hid, hw, -⟩ | ⟨hid, l, hl, he⟩ | ⟨hid, -⟩
  · simp only [he]; omega
  · obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    rw [hid] at hc
    simp only [actorW, beq_self_eq_true, ↓reduceIte] at hc
    simp only [he, wtA_push]
    have := emitW_sound hc ha hm
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
theorem extW_tg : ExtW f ctx apre actorT (fun s => tgA s.emitted) := by
  intro as vs term v st st' c hvs _ hc h
  rcases externCtor_sz ctx term vs st v st' h with
    he | ⟨hid, i, m, rfl, hm, he⟩ | ⟨-, -, ht⟩ | ⟨-, l, -, he⟩ | ⟨-, ht⟩
  · simp only [he]; omega
  · obtain ⟨a, rfl, ha⟩ := holds2_one hvs
    rw [hid] at hc
    simp only [actorT, beq_self_eq_true, ↓reduceIte] at hc
    simp only [he, tgA_push]
    have := emitT_sound hc ha hm
    omega
  · simp only [ht]; omega
  · simp only [he, tgA_push, MInst.targets, List.length_nil]; omega
  · simp only [ht]; omega

/-- The oracle's runs keep the lowering state. -/
theorem oracle_keeps {cfg : Config} (hc : cfg.checkOverlap = false) {n : Nat} {ty : TypeId}
    {t : TermId} {as : List AT} {vs : List V} {a : AT} {s : LState} {tr : Array RuleId}
    {r : Option V} {s' : LState} {tr' : Array RuleId} (ha : aOracle t as = some a)
    (h : (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr'))) : s' = s := by
  unfold aOracle at ha
  split at ha
  · rename_i ht
    obtain rfl : t = 305 := eq_of_beq ht
    exact (os_run hc h).1
  · cases ha

/-- **The oracle's runs** do not grow the weight of the emitted instructions. -/
theorem oracleW_wt : OracleW program f ctx aOracle (fun s => wtA s.emitted) := by
  intro cfg hc n ty t as vs a s tr r s' tr' ha _ h
  rw [oracle_keeps hc ha h]
  exact Nat.le_refl _

/-- **The oracle's runs** do not grow the branch targets of the emitted instructions. -/
theorem oracleW_tg : OracleW program f ctx aOracle (fun s => tgA s.emitted) := by
  intro cfg hc n ty t as vs a s tr r s' tr' ha _ h
  rw [oracle_keeps hc ha h]
  exact Nat.le_refl _


end Backend.Proof.CovT

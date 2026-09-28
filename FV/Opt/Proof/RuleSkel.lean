import FV.Opt.Proof.RuleBase

/-!
# Rule obligations for `simplify_skeleton`, and their lifting to `Isle.Opt.simplifySkeleton`

`SkelRuleOk p r`: whenever the `simplify_skeleton` rule `r` of the program `p` fires on a
skeleton instruction `i` (in a model `den` of the e-graph with a sound `make`, and a
`trapBlock` that is `tb`), every result of its right-hand side that the driver reads
(`skelSimp? w = some c`) refines `i` (`Opt.SkelRefines tb`) in *every* later model state:
the driver evaluates the refinement in the final valuation, which only grows after the rule
ran, and `SkelRefines` is not monotone in the valuation (an undefined operand of `i` may become
defined), so the obligation quantifies over later states.

`skeletonSound`: if every rule of `p.rulesOf simplify_skeleton` accepted by `allow` is
`SkelRuleOk`, `Isle.Opt.simplifySkeleton` with the allow-list is `Opt.SkeletonSound`. The proof
is `applyMulti_gen` (`FV/Opt/Proof/RuleBase.lean`) with no invariant and the result property
"refines `i` from here on".
-/

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

/-- The result property of `simplify_skeleton` on `i`: every simplification read off `w`
refines `i` in every later model state. -/
def SkelGood {σ : Type} (P : σ → Prop) (den : σ → Valuation) (fr : Frame) (mem : Mem)
    (tb : BlockId → Option TrapCode) (i : SkelInst) (w : V) (s : St σ) : Prop :=
  ∀ c, skelSimp? w = some c → ∀ st, P st → Valuation.Le (den s.inner) (den st) →
    SkelRefines tb { fr with regs := den st } mem i c

/-- **Obligation of one `simplify_skeleton` rule.** -/
def SkelRuleOk (p : Isle.Program) (r : Rule) : Prop :=
  ∀ (σ : Type) (G : EGraph σ) (P : σ → Prop) (den : σ → Valuation) (fr : Frame) (mem : Mem)
    (tb : BlockId → Option TrapCode),
  GraphOk G P den fr mem → (∀ st, P st → G.trapBlock st = tb) →
  ∀ i, RuleSpec p G P den (.inst (some i)) (fun _ => True)
    (fun _ w s => SkelGood P den fr mem tb i w s) r

/-- The `simplify_skeleton` rules accepted by `allow` are all `SkelRuleOk`. -/
def SkeletonRulesCorrect (p : Isle.Program) (allow : RuleId → Bool) : Prop :=
  ∀ r ∈ p.rulesOf T.«simplify_skeleton».id, allow r.id = true → SkelRuleOk p r

theorem simplify_skeleton_kind :
    T.«simplify_skeleton».kind = .decl ⟨false, true, false, false⟩ (some .internal) none := rfl

/-- **Lifting**: the `simplify_skeleton` rules accepted by `allow` being `SkelRuleOk`,
`Isle.Opt.simplifySkeleton` with the allow-list is a sound skeleton rule set. -/
theorem skeletonSound (allow : RuleId → Bool) (hc : SkeletonRulesCorrect program allow)
    (hlen : fuelMin + (program.rulesOf T.«simplify_skeleton».id).length ≤ cfg.fuel) :
    SkeletonSound (fun enodes typeOf make trapBlock st i =>
      Isle.Opt.simplifySkeleton enodes typeOf make trapBlock st i allow) := by
  intro σ enodes typeOf make trapBlock P den fr mem tb hM hMk htb st i cands names st' hP h
  let G : EGraph σ := ⟨enodes, typeOf, make, trapBlock⟩
  have hG : GraphOk G P den fr mem := ⟨hM, hMk⟩
  unfold Isle.Opt.simplifySkeleton at h
  dsimp only at h
  split at h
  · cases h
  · rename_i r hr
    simp only [Interp.runMultiTerm, simplify_skeleton_kind] at hr
    simp only [TermFlags.isMulti, Bool.not_true, Bool.false_eq_true, ite_false, bind,
      Except.bind] at hr
    split at hr
    · cases hr
    · rename_i x hx
      obtain ⟨vals, s1, tr1⟩ := x
      simp only [pure, Except.pure, Except.ok.injEq] at hr
      subst hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      obtain ⟨h1, h2, h3⟩ := applyMulti_gen program hG allow (.inst (some i)) (fun _ => True)
        (fun _ w s => SkelGood P den fr mem tb i w s) (fun _ _ _ _ => trivial)
        (fun _ _ _ _ h hle c hc st hst hle' => h c hc st hst (Valuation.le_trans hle hle'))
        T.«simplify_skeleton» _ (fun r hr ha => hc r hr ha σ G P den fr mem tb hG htb i)
        cfg.fuel hlen { inner := st } #[] vals s1 tr1 hP trivial hx
      refine ⟨h1, h2, ?_⟩
      intro c hcm
      simp only [List.mem_map, List.mem_filterMap] at hcm
      obtain ⟨⟨c', nm⟩, ⟨⟨rid, w⟩, hmem, hw⟩, rfl⟩ := hcm
      simp only at hw
      split at hw
      · rename_i hal
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hw
        obtain ⟨c'', hc'', rfl, -⟩ := hw
        exact h3 rid w hmem hal c'' hc'' _ h1 (Valuation.le_refl _)
      · cases hw

end Opt.Proof

import FV.Backend.Proof.SpillEdgesLow

/-!
# The spill allocator's CFG facts on the pipeline's output (V4, `EdgesHyp`)

`edgesHyp_of`: for `Dominated`, `LowerScope`, `ArityOk` input, `prepare (lowerFunction f)` meets
`EdgesOk` — `lowOk_of` (the lowered VCode's CFG facts, `SpillEdgesLow`) carried through `prepare`
by `edgesOk_prepare` (`SpillEdgesPrep`). `ArityOk` is needed: an argument-less `brif` edge goes
straight to its target, which may have parameters otherwise.

`edgesOk_witness`: `EdgesOk` is satisfiable with branch arguments (a two-block VCode, a `jump`
passing one argument to a block with one parameter).
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Driver

/-- **The CFG facts of the pipeline's output** (`EdgesHyp` with `ArityOk`). -/
theorem edgesHyp_of {f : Clif.Function} {vc vcp : VCode} (hd : Dominated f) (hs : LowerScope f)
    (ha : ArityOk f) (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp) :
    ∀ succs preds, vcp.cfg = .ok (succs, preds) → EdgesOk vcp succs preds :=
  edgesOk_prepare (lowOk_of hd hs ha hl) hp

/-- A `jump` passing `v5` to a block with parameter `v7`, which returns. -/
def edgesEx : VCode where
  name := "ex"
  blocks := #[⟨0, #[.jump 1], #[], #[.vreg 5 .int]⟩, ⟨1, #[.rets []], #[.vreg 7 .int], #[]⟩]
  classes := #[]
  slotBytes := 0
  outgoing := 0
  rulesFired := #[]

/-- `edgesEx`'s CFG, checked by the kernel. -/
def edgesExCfgB : Bool := match edgesEx.cfg with
  | .ok (s, p) => s == #[#[1], #[]] && p == #[#[], #[0]]
  | .error _ => false

theorem edgesEx_cfg : edgesEx.cfg = .ok (#[#[1], #[]], #[#[], #[0]]) := by
  have : edgesExCfgB = true := by decide +kernel
  unfold edgesExCfgB at this
  split at this
  · rename_i s p h
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    rw [h, this.1, this.2]
  · cases this

/-- **Non-vacuity**: `EdgesOk` holds of a VCode with branch arguments. -/
theorem edgesOk_witness : ∃ vc succs preds, vc.cfg = .ok (succs, preds) ∧ EdgesOk vc succs preds ∧
    ∃ vb ∈ vc.blocks.toList, vb.branchArgs ≠ #[] := by
  refine ⟨edgesEx, _, _, edgesEx_cfg, ⟨⟨by decide, rfl, rfl⟩, ?_, ?_, ?_⟩,
    ⟨_, List.mem_cons_self, by decide⟩⟩
  · intro b vb hb hne
    match b, hb with
    | 0, hb =>
      cases hb
      refine ⟨⟨.jump 1, rfl, rfl⟩, 1, _, rfl, rfl, rfl, fun k a p ha hp => ?_, by decide⟩
      match k, ha, hp with
      | 0, ha, hp => cases ha; cases hp; exact ⟨5, 7, .int, rfl, rfl⟩
    | 1, hb => cases hb; exact absurd rfl hne
  · intro b vb ss s sb hb hba hss hs hsb
    match b, hb, hss with
    | 0, hb, _ => cases hb; cases hba
    | 1, _, hss => cases hss; simp at hs
  · intro b vb info ti ss s hb hback
    match b, hb with
    | 0, hb => cases hb; cases hback
    | 1, hb => cases hb; cases hback

end Backend.Proof.Spill

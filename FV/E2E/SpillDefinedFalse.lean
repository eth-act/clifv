import FV.E2E.SpillDefined

/-!
# `SpillDefinedHyp` is false: entry-block parameters beyond the signature

`lowerFunction` defines the entry block's parameters from the signature's parameter locations
(`entryParams`: `B0.params` zipped with `locsOf f.sig`), so a parameter of the entry block beyond
the signature's is never defined. Cranelift's verifier rejects such a function ("entry block
parameters must match the function signature"), but none of `InSubset`, `Dominated`,
`LowerScope`, `ArityOk` — nor the crate theorem's per-function input condition `fnScopeB` —
does. `entryWitness` (`function %f() -> i64 { block0(v0: i64): return v0 }`) passes `fnScopeB`,
and its prepared VCode's `return` reads the never-defined `v0`: `not_spillDefinedHyp`. Hence
`crate_correct_inScope` is vacuous as stated. The variants with the input condition
`Spill.entryParamsB` (`SpillDefinedHypE`, `crate_correct_inScopeE`) exclude it
(`entryWitness_entryParams`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill E2E.LinkCheck

def entryWitnessSrc : String := "function %f() -> i64 system_v {
block0(v0: i64):
    return v0
}"

def entryWitness : Clif.Function :=
  match (Clif.parseFile entryWitnessSrc).funcs[0]? with
  | some p => match p.func with
    | .ok f => f
    | .error _ => default
  | none => default

theorem entryWitness_checks :
    fnScopeB entryWitness = true ∧ Spill.entryParamsB entryWitness = false ∧
      ((lowerFunction entryWitness).toOption.bind fun vc => (prepare vc).toOption.map fun vcp =>
        (vcp.cfg.toOption, vcp.blocks[0]?.map (·.insts))) =
        some (some (#[#[]], #[#[]]), some #[.args [], .rets [(.vreg 0 .int, .x 0)]]) := by
  native_decide

/-- The entry block of `entryWitness`'s prepared VCode reads `v0`, defined nowhere. -/
theorem entryWitness_pipe : ∃ (p : Clif.Program) (vc vcp : VCode) (vb : VBlock),
    InSubset p entryWitness ∧ Spill.ArityOk entryWitness ∧ Dominated entryWitness ∧
    LowerScope entryWitness ∧ lowerFunction entryWitness = .ok vc ∧ prepare vc = .ok vcp ∧
    vcp.cfg = .ok (#[#[]], #[#[]]) ∧ vcp.blocks[0]? = some vb ∧
    vb.insts = #[.args [], .rets [(.vreg 0 .int, .x 0)]] := by
  obtain ⟨hsc, -, hpipe⟩ := entryWitness_checks
  obtain ⟨-, -, -, -, -, -, -, -, hd, hs, har, hlw⟩ := fnScope_parts hsc
  obtain ⟨-, vc, vcp, hl, hp, -⟩ := lowersB_spec hlw
  simp only [hl, hp, Except.toOption, Option.bind_some, Option.map_some, Option.some.injEq,
    Prod.mk.injEq] at hpipe
  obtain ⟨hcfg, hb⟩ := hpipe
  cases hc : vcp.cfg with
  | error e => rw [hc] at hcfg; cases hcfg
  | ok r =>
    rw [hc] at hcfg
    cases hcfg
    cases hb0 : vcp.blocks[0]? with
    | none => rw [hb0] at hb; cases hb
    | some vb =>
      rw [hb0] at hb
      simp only [Option.map_some, Option.some.injEq] at hb
      exact ⟨_, vc, vcp, vb, inSubset_of_fnScope hsc { funcs := [] }, arityOk_of har,
        dominated_of hd, lowerScope_of hs, hl, hp, hc, hb0, hb⟩

/-- No definedness or availability sets with nothing on entry exist for `entryWitness`. -/
theorem entryWitness_no_sets {vcp : VCode} {vb : VBlock} (hc : vcp.cfg = .ok (#[#[]], #[#[]]))
    (hb : vcp.blocks[0]? = some vb) (hi : vb.insts = #[.args [], .rets [(.vreg 0 .int, .x 0)]])
    {D : Nat → Nat → Bool} (hD0 : ∀ v, D 0 v = false) :
    ¬ SpillAvail vcp D ∧ ¬ DefAvail vcp D := by
  have hk : vb.insts[1]? = some (.rets [(.vreg 0 .int, .x 0)]) := by rw [hi]; rfl
  have hes : entryStored vcp #[#[]] #[#[]] 0 = [] := rfl
  have hops : (MInst.rets [(.vreg 0 .int, .x 0)]).operands =
      .ok #[⟨0, .int, .use, .early, .fixed (.x 0)⟩] := rfl
  have hargs : (MInst.args []).operands = .ok #[] := rfl
  have hmem : (⟨0, .int, .use, .early, .fixed (.x 0)⟩ : Operand) ∈
      (#[⟨0, .int, .use, .early, .fixed (.x 0)⟩] : Array Operand).toList := by simp
  refine ⟨fun hav => ?_, fun hav => ?_⟩
  · have h := hav.uses _ _ hc 0 vb 1 _ _ hb hk hops _ hmem rfl
    rw [hi] at h
    simp [availAt, availInst, availStart, hes, hD0, hargs] at h
  · have h := hav.uses _ _ hc 0 vb 1 _ _ hb hk hops _ hmem rfl
    rw [hi] at h
    simp [defAt, defInst, defStart, hes, hD0, hargs] at h

/-- **`SpillDefinedHyp` is false** (`entryWitness`: an entry-block parameter beyond the
signature's, read by the `return`). -/
theorem not_spillDefinedHyp : ¬ SpillDefinedHyp := by
  intro h
  obtain ⟨p, vc, vcp, vb, hsub, har, hd, hs, hl, hp, hc, hb, hi⟩ := entryWitness_pipe
  obtain ⟨D, hav, hD0⟩ := h p entryWitness vc vcp hsub har hd hs hl hp
  exact (entryWitness_no_sets hc hb hi hD0).1 hav

/-- `entryWitness` fails the input condition of `SpillDefinedHypE`. -/
theorem entryWitness_entryParams : Spill.entryParamsB entryWitness = false :=
  entryWitness_checks.2.1

end E2E

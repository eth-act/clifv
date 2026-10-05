import FV.E2E.AllocDirect
import FV.Backend.Proof.SpillAvail

/-!
# The availability sets of the pipeline's output (V4 step 4, `SpillAvailable`)

`spillAvailable_of_killFree`: `SpillAvailable` (`FV/E2E/AllocDirect.lean`) follows from
`SpillKillFree` — the prepared VCode of in-scope input passes `Spill.killFreeB` (no instruction
reads a vreg some instruction kills without storing it: the scratch defs past
`MInst.keptDefs` of the LL/SC loops, the defs of a terminator — `JTSequence`'s temporaries, a
`try_call`'s results; a killed branch argument, i.e. a `try_call` result passed by its edge block,
is stored by the edge block's entry stores) — with the sets `Spill.killD` and the CFG facts of
step 3 (`Spill.edgesHyp_of`).

`SpillKillFree` is open (an explicit hypothesis, not an axiom): it is the SSA discipline of the
ISLE lowering (a statement's lowering reads only vregs of available values and its own earlier
kept defs, and returns no scratch vreg). `lean-e2e-check` decides `killFreeB` on every in-scope
function of the corpus and the runtests ("killFreeB" line).

`spillKillFree_witness`: on a function with an LL/SC loop (`rmwWitness`, so `killedOf` is
non-empty and `killD` excludes the loop's scratch vregs outside the entry block), the input
conditions hold and `killFreeB` accepts its prepared VCode, so `SpillAvail` holds for it.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **The syntactic availability facts of the pipeline's output** (V4 step 4; open, an explicit
hypothesis, not an axiom): for every prepared VCode `vcp` the pipeline produces from in-scope
input, `Spill.killFreeB vcp` holds. -/
def SpillKillFree : Prop :=
  ∀ (p : Clif.Program) (f : Clif.Function) (vc vcp : VCode), InSubset p f → Spill.ArityOk f →
    Dominated f → LowerScope f → lowerFunction f = .ok vc → Backend.prepare vc = .ok vcp →
      Spill.killFreeB vcp = true

/-- **`SpillAvailable` from `SpillKillFree`**: the sets `Spill.killD vcp` are availability sets of
the pipeline's output (`Spill.spillAvail_of_killFree`, with the CFG facts `Spill.edgesHyp_of`). -/
theorem spillAvailable_of_killFree (hk : SpillKillFree) : SpillAvailable :=
  fun p f vc vcp hsub har hd hs hl hp =>
    ⟨Spill.killD vcp, Spill.spillAvail_of_killFree (hk p f vc vcp hsub har hd hs hl hp)
      (Spill.edgesHyp_of hd hs har hl hp)⟩

/-- **`SpillAccepted` from the step-4 invariant proof and `SpillKillFree`**. -/
theorem spillAccepted_of_killFree (h4 : Spill.SpillStep4) (hk : SpillKillFree) : SpillAccepted :=
  spillAccepted_of_step4 h4 (spillAvailable_of_killFree hk)

/-! ## Non-vacuity -/

/-- The witness's source: an LL/SC loop (`atomic_rmw`, whose scratch defs are killed), its result
passed to a block parameter. -/
def rmwWitnessSrc : String := "function %rmw(i64, i64) -> i64 {
block0(v0: i64, v1: i64):
    v2 = atomic_rmw.i64 add v0, v1
    jump block1(v2)
block1(v3: i64):
    return v3
}"

/-- The witness function. -/
def rmwWitness : Clif.Function :=
  match (Clif.parseFile rmwWitnessSrc).funcs[0]? with
  | some p => match p.func with
    | .ok f => f
    | .error _ => default
  | none => default

/-- The decided facts of the witness: the input conditions, and the prepared VCode has killed
vregs, passes `killFreeB`, and `killD` excludes a killed vreg outside the entry block. -/
theorem rmwWitness_checks :
    dominatedB rmwWitness = true ∧ lowerScopeB rmwWitness = true ∧
      Spill.arityOkB rmwWitness = true ∧
      (match lowerFunction rmwWitness with
        | .ok vc => match Backend.prepare vc with
          | .ok vcp => Spill.killFreeB vcp && !(Spill.killedOf vcp).isEmpty &&
              (Spill.killedOf vcp).all (fun v => !Spill.killD vcp 1 v) && decide (1 < vcp.blocks.size)
          | .error _ => false
        | .error _ => false) = true := by
  native_decide

/-- **Non-vacuity of `spillAvailable_of_killFree`**: on `rmwWitness` (an LL/SC loop), the input
conditions hold, `killFreeB` accepts the prepared VCode — so `SpillAvail` holds with `killD` —
and `killD` is not trivial: some vreg is unavailable on entry to block 1. -/
theorem spillKillFree_witness :
    Dominated rmwWitness ∧ LowerScope rmwWitness ∧ Spill.ArityOk rmwWitness ∧
      ∃ vc vcp, lowerFunction rmwWitness = .ok vc ∧ Backend.prepare vc = .ok vcp ∧
        Spill.killFreeB vcp = true ∧ Spill.SpillAvail vcp (Spill.killD vcp) ∧
        ∃ v, Spill.killD vcp 1 v = false := by
  obtain ⟨hd, hs, ha, h⟩ := rmwWitness_checks
  have hd := dominated_of hd
  have hs := lowerScope_of hs
  have ha := Spill.arityOk_of ha
  refine ⟨hd, hs, ha, ?_⟩
  cases hl : lowerFunction rmwWitness with
  | error e => rw [hl] at h; cases h
  | ok vc =>
    rw [hl] at h
    simp only at h
    cases hp : Backend.prepare vc with
    | error e => rw [hp] at h; cases h
    | ok vcp =>
      rw [hp] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨hk, hne⟩, hall⟩, -⟩ := h
      cases hK : Spill.killedOf vcp with
      | nil => rw [hK] at hne; cases hne
      | cons v vs =>
        rw [hK] at hall
        have hv := List.all_eq_true.mp hall v List.mem_cons_self
        exact ⟨vc, vcp, rfl, hp, hk,
          Spill.spillAvail_of_killFree hk (Spill.edgesHyp_of hd hs ha hl hp), v, by simpa using hv⟩

end E2E

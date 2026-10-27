import FV.Concurrency.CStepSConv
import FV.Concurrency.CallLoadWitness
import FV.Concurrency.ProgramWitness

/-!
# Witnesses for `CStepSConv` (#473)

* `cstepS_C`, `crunS_C`: the compiled caller's CLIF call step (`cstepC`) is a `CStepS` step and a
  one-step `CRunS` run between the states encoding the mask `{0}`;
* `fresh0_WR`: in the trace "write byte 0, then read byte 0" with byte 0 masked at the start, the
  read follows the write;
* `toTD_nil`: the empty refinement is a `RefinesT` from the start-dirty set of all bytes.
-/

namespace Concurrency.CallSeg.WitnessC

open Prog ClifThread Concurrency.CallComposeT ThreadRefine ArmAllocThread PrepThread ClifThreadI

theorem cstepS_C (env : Clif.Env) :
    CStepS env pCL (encT (fun a => a = 0) (.run csC)) []
      (encT (fun a => a = 0 ∧ ¬ writes [] a) (.run (ClifLift.pushC extC RealizeCompiled.WitnessL.csL))) :=
  cstepS_of_cstep (cstepC env) (fun _ h => nomatch h)

theorem crunS_C (env : Clif.Env) :
    CRunS env pCL (encT (fun a => a = 0) (.run csC)) [[]]
      (encT (maskAfter (fun a => a = 0) [[]]) (.run (ClifLift.pushC extC RealizeCompiled.WitnessL.csL))) :=
  crunS_of_crun (.cons (cstepC env) .nil) rfl (by simp [ReadsAvoid])

/-- The trace "write byte 0, then read byte 0". -/
def trWR : List (List (Ev SKind BVal)) :=
  [[⟨.naW, .W, 0, 1, [some 0]⟩], [⟨.naR, .R, 0, 1, [some 0]⟩]]

theorem fresh0_WR : ∃ q x', evAt trWR q = some x' ∧ x'.dir = .W ∧ x'.loc = 0 ∧
    Lt (id q) (id (1, 0)) := by
  have hra : ReadsAvoid (fun a => a = 0) trWR := by
    simp only [ReadsAvoid, trWR]
    refine ⟨fun e he => ?_, fun e he => ?_, trivial⟩
    · simp at he; subst he; intro h; cases h
    · simp at he; subst he; intro _ k hk; simp [writes]
  have h := fresh0_of_mask (ψ := id) (trS := trWR) (U := fun a => a = 0) hra
    (by
      intro p x q y hp hq hR hW hle hlt
      obtain ⟨_ | _ | _, _ | _⟩ := p <;> obtain ⟨_ | _ | _, _ | _⟩ := q <;>
        simp [evAt, trWR] at hp hq <;> subst hp hq <;> try simp_all)
    (by
      intro p x hp
      obtain ⟨_ | _ | _, _ | _⟩ := p <;> simp [evAt, trWR] at hp <;> subst hp <;> decide)
    (fun _ _ _ _ h => h)
    (1, 0) ⟨.naR, .R, 0, 1, [some 0]⟩ (by simp [evAt, trWR]) rfl rfl
  simpa using h

theorem toTD_nil :
    PrivCohT.RefinesT (K := SKind) (V := BVal) (MK := Maps) (fun _ => True) (fun _ => fun _ => False)
      (MonPair []) [] (conv []) id :=
  Refines.toTD CallCompose.refines_nil (fun _ x hx => by rw [evAt_nil] at hx; cases hx)

/-- The bottom frame `sR` returns as a `CStepS` step from the empty mask, and not from the mask
`{0}`. -/
theorem ret_sR : CStepS ProgWitness.env0 ProgWitness.p0 (encT (fun _ => False) (.run ProgWitness.sR))
      [] (.ret []) ∧
    ¬ CStepS ProgWitness.env0 ProgWitness.p0 (encT (fun a => a = 0) (.run ProgWitness.sR)) []
      (.ret []) := by
  have hc : CStep ProgWitness.env0 ProgWitness.p0 (.run ProgWitness.sR) [] (.ret []) :=
    ⟨⟨by simp [evShape, ProgWitness.sR], fun e he => absurd he List.not_mem_nil⟩,
      ⟨fun _ => none, trivial⟩, fun B _ => ⟨.ret [], ProgWitness.step_sR B, rfl⟩⟩
  exact ⟨(cstepS_ret_iff hc ProgWitness.step_sR _).2 fun _ h => h,
    fun h => (cstepS_ret_iff hc ProgWitness.step_sR _).1 h 0 rfl⟩

/-- Byte locations form a partition, and `trWR` accesses them: its accesses are uniform. -/
theorem uniform_WR : Uniform trWR :=
  uniform_of_parts (Loc := fun _ n => n = 1) (fun a n b m _ hm h1 h2 => by omega)
    (fun p x hx _ => by
      obtain ⟨_ | _ | _, _ | _⟩ := p <;> simp [evAt, trWR] at hx <;> subst hx <;> rfl)

/-- The empty refinement from the start-dirty set of the 8-byte partition. -/
theorem toT_parts_nil :
    PrivCohT.RefinesT (K := SKind) (V := BVal) (MK := Maps)
      (fun a => False ∨ (a = 0) ∨ ¬ ∃ n, (fun a n => n = 8 ∧ a % 8 = 0) a n)
      (fun _ => fun _ => False) (MonPair []) [] (conv []) id :=
  Refines.toT_parts CallCompose.refines_nil (by simp [ReadsAvoid])
    (fun a n b m ha hb h1 h2 => by omega) (fun _ x hx => by rw [evAt_nil] at hx; cases hx)
    (fun _ x hx => by rw [evAt_nil] at hx; cases hx)

/-- A returned state stops, whatever mask it is encoded with. -/
theorem stop_ret : IselThread.Stop ProgWitness.env0 ProgWitness.p0 (encT (fun a => a = 0) (.ret [])) :=
  (stop_encT _ _).2 (.inl fun ⟨_, _, h⟩ => h)

end Concurrency.CallSeg.WitnessC

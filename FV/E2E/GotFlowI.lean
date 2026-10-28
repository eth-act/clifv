import FV.E2E.GotFlow
import FV.E2E.RegLevelCorrectI

/-!
# Calls through the GOT in the counted VCode run (SEM1, `docs/plans/uninit.md` §5.9)

`vReturns_gotV`/`vTraps_gotV` (`FV/E2E/GotFlow.lean`) for the counted semantics: a run of
`csemI F ctx XI` is one of `csemVI (GotV vc) F ctx XI` (each step at counter `m` is a step of
`csem F ctx (XI.at m)`, which the GOT invariant turns into one of `csemV (GotV vc) F ctx
(XI.at m)`; the invariant reads only `XI.sym`, the same at every index).

* `GotInvI`, `gotInvI_step`, `gotInvI_star`, **`vRetFrom_gotVI`**, **`vTrapFrom_gotVI`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

variable {vc : VCode} {F : BitVec 64 → Prop} {ctx : FnCtx} {XI : ExtSemI}

/-- The GOT invariant of a counted state (on its Arm world; `XI.sym` is every index's). -/
def GotInvI (vc : VCode) (XI : ExtSemI) (s : VState CV (Arm.ArmState × Nat)) : Prop :=
  GotInv vc (XI.at 0) ⟨s.b, s.k, s.ρ, s.w.1⟩

/-- **One counted step** keeps the invariant and is a step of `csemVI (GotV vc)`. -/
theorem gotInvI_step {s : VState CV (Arm.ArmState × Nat)} {c' : VConf CV (Arm.ArmState × Nat)}
    (hI : GotInvI vc XI s) (h : VStep vc (csemI F ctx XI) (.run s) c') :
    VStep vc (csemVI (GotV vc) F ctx XI) (.run s) c' ∧ ∀ s', c' = .run s' → GotInvI vc XI s' := by
  obtain ⟨b, k, ρ, ⟨w, m⟩⟩ := s
  cases h with
  | @step _ _ _ _ vb i ops outs w' ctl _ hvb hi hops hsem hlen hnext =>
  obtain ⟨hs1, hs2⟩ := ISem.counted_some (sem := fun n => csem F ctx (XI.at n)) hsem
  have hst1 : VStep vc (csem F ctx (XI.at m)) (.run ⟨b, k, ρ, w⟩) (c'.mapW Prod.fst) :=
    VStep.step hvb hi hops hs1 hlen (VNext_mapW hnext)
  have hI' : GotInv vc (XI.at m) ⟨b, k, ρ, w⟩ := hI
  obtain ⟨hst2, hinv⟩ := gotInv_step hI' hst1
  refine ⟨?_, fun s' hc => ?_⟩
  · cases hst2 with
    | step hvb2 hi2 hops2 hsem2 hlen2 hnext2 =>
      rw [hvb] at hvb2; cases hvb2
      rw [hi] at hi2; cases hi2
      rw [hops] at hops2; cases hops2
      have e := csemV_sub hsem2
      rw [show csem F ctx (XI.at m) _ _ w = some (outs, w'.1, ctl) from hs1] at e
      cases e
      refine VStep.step hvb hi hops ?_ hlen hnext
      show (csemV (GotV vc) F ctx (XI.at m) i _ w).map _ = _
      rw [hsem2]
      simp only [Option.map_some]
      rw [← hs2]
  · subst hc
    exact hinv _ rfl

theorem gotInvI_star {s s' : VState CV (Arm.ArmState × Nat)} (hI : GotInvI vc XI s)
    (h : Star (VStep vc (csemI F ctx XI)) (.run s) (.run s')) :
    Star (VStep vc (csemVI (GotV vc) F ctx XI)) (.run s) (.run s') ∧ GotInvI vc XI s' := by
  generalize ha : (VConf.run s : VConf CV (Arm.ArmState × Nat)) = a at h
  generalize hb : (VConf.run s' : VConf CV (Arm.ArmState × Nat)) = b at h
  induction h generalizing s with
  | refl => subst ha; cases hb; exact ⟨.refl _, hI⟩
  | @step a1 a2 a3 h1 h2 ih =>
    subst ha
    cases a2 with
    | run s2 =>
      obtain ⟨h1', hI2⟩ := gotInvI_step hI h1
      obtain ⟨h2', hI'⟩ := ih (hI2 s2 rfl) rfl hb
      exact ⟨.step h1' h2', hI'⟩
    | ret vals w => subst hb; cases h2 with | step h _ => cases h
    | halt w => subst hb; cases h2 with | step h _ => cases h

/-- **A returning counted run of `csemI` is one of `csemVI (GotV vc)`.** -/
theorem vRetFrom_gotVI {ρ₀ : Nat → CV} {w₀ : Arm.ArmState × Nat} {us : List (Reg × Reg)}
    {vals : List CV} {w : Arm.ArmState × Nat}
    (h : VRetFrom vc (csemI F ctx XI) ⟨0, 0, ρ₀, w₀⟩ us vals w) :
    VRetFrom vc (csemVI (GotV vc) F ctx XI) ⟨0, 0, ρ₀, w₀⟩ us vals w := by
  obtain ⟨b, k, ρ, w₁, vb, ops, outs, hs, hvb, hk, hops, hvals, hsem⟩ := h
  obtain ⟨hs', -⟩ := gotInvI_star
    (show GotInvI vc XI ⟨0, 0, ρ₀, w₀⟩ from gotInv_entry vc (XI.at 0) ρ₀ w₀.1) hs
  refine ⟨b, k, ρ, w₁, vb, ops, outs, hs', hvb, hk, hops, hvals, ?_⟩
  obtain ⟨hs1, hs2⟩ := ISem.counted_some (sem := fun n => csem F ctx (XI.at n)) hsem
  have hv : csemV (GotV vc) F ctx (XI.at w₁.2) (.rets us) vals w₁.1 = some (outs, w.1, .ret) := by
    rw [csemV_eq fun info h => by rcases h with h | ⟨_, h⟩ <;> cases h]
    exact hs1
  simp only [csemVI, ISem.counted, hv, Option.map_some]
  rw [← hs2]

/-- **A trapping counted run of `csemI` is one of `csemVI (GotV vc)`.** -/
theorem vTrapFrom_gotVI {ρ₀ : Nat → CV} {w₀ : Arm.ArmState × Nat} {c : Clif.TrapCode}
    (h : VTrapFrom vc (csemI F ctx XI) ⟨0, 0, ρ₀, w₀⟩ c) :
    VTrapFrom vc (csemVI (GotV vc) F ctx XI) ⟨0, 0, ρ₀, w₀⟩ c := by
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, hvb, hi, hops, hsem, htc⟩ := h
  obtain ⟨hs', -⟩ := gotInvI_star
    (show GotInvI vc XI ⟨0, 0, ρ₀, w₀⟩ from gotInv_entry vc (XI.at 0) ρ₀ w₀.1) hs
  refine ⟨b, k, ρ, w, vb, i, ops, outs, w', hs', hvb, hi, hops, ?_, htc⟩
  obtain ⟨hs1, hs2⟩ := ISem.counted_some (sem := fun n => csem F ctx (XI.at n)) hsem
  obtain ⟨-, hform⟩ := csem_halt hs1
  have hnc : ∀ info, (i = .call info ∨ ∃ ti, i = .tryCall info ti) →
      gotGuard (GotV vc) (XI.at w.2) info (vuses ops ρ) := by
    intro info h
    exfalso
    rcases hform with ⟨_, e⟩ | ⟨_, _, e, _⟩ <;> rcases h with e' | ⟨_, e'⟩ <;>
      rw [e] at e' <;> cases e'
  have hv : csemV (GotV vc) F ctx (XI.at w.2) i (vuses ops ρ) w.1 = some (outs, w'.1, .halt) := by
    rw [csemV_eq hnc]
    exact hs1
  simp only [csemVI, ISem.counted, hv, Option.map_some]
  rw [← hs2]

end E2E

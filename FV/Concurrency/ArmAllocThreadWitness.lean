import FV.Concurrency.ArmAllocThread
import FV.Concurrency.ThreadLayerWitness

/-!
# Non-vacuity of the run level of layer 4b (T2h, #311)

`refines_ldaxr`: `ArmAllocThread.refines_of_itemSim` for the `ldaxr x27, [x25]` of
`ArmThread.Witness` against a one-step source reading the 8 bytes at `0x8000` with any value:
the per-item obligation `ItemSim` holds for every precise run (`itemSim`: a precise label of the
`ldaxr` is the read at `0x8000` of the environment's bytes, `stepEvs_setMem_st0`), and the run
whose `ldaxr` reads the environment's `5` (its own memory holds `0`) is realized.
-/

namespace Concurrency.ArmAllocThread.Witness

open Arm ArmFoot ArmThread ArmInstFoot ArmPrecise ThreadRefine ProgE2E PrepThread

/-- The `ldaxr` state of `ArmThread.Witness`. -/
abbrev st0 : ArmState := ArmThread.Witness.st 0x1000#64 0#64

/-- The source: one step reading 8 bytes at `0x8000` (any value), then done. -/
def S (b : Bool) (evs : List Ev) (b' : Bool) : Prop :=
  b = false ∧ b' = true ∧ ∃ v, evs = [⟨.acqXR, 0x8000#64, 8, v⟩]

/-- The `ldaxr` state before the step; anything after it. -/
def Rel (t : ArmState × Mon) (b : Bool) : Prop := (b = false ∧ t = (st0, none)) ∨ b = true

theorem stepEvs_st0 : stepEvs st0 = [⟨.acqXR, 0x8000#64, 8, readM 8 0x8000#64 st0.mem⟩] :=
  VCodeThread.Witness.evs_ext (by decide +kernel)

/-- A precise label of the `ldaxr` reads the environment's bytes at `0x8000`. -/
theorem stepEvs_setMem_st0 (m : Memory) :
    stepEvs (setMem m st0) = [⟨.acqXR, 0x8000#64, 8, readM 8 0x8000#64 m⟩] := by
  rw [stepEvs_setMem, stepEvs_st0, reread_R rfl]

theorem cls_st0 : cls st0 = .ldx true 25#5 3#2 := by
  unfold cls; rw [ArmThread.Witness.decode_ldaxr]; decide

/-- **The per-item obligation holds** for the `ldaxr` against the one-step source. -/
theorem itemSim : ItemSim Policy.arm stepi (fun _ _ => True) S Rel (· = true) (fun _ => 0)
    (fun _ => False) := by
  intro t c hR ls t' hr
  rcases hR with ⟨rfl, rfl⟩ | rfl
  · cases hr with
    | nil => exact .inr (.inr (.inr fun p y hy => by simp [evTr, evAt_nil] at hy))
    | @cons _ t1 _ l ls' hs hp _ _ =>
      have hx : l.xfail = false := by
        cases hs with
        | exec => rfl
        | xfail hc => rw [cls_st0] at hc; cases hc
      rcases hp with hp | ⟨m, hm⟩
      · rw [hx] at hp; cases hp
      · have he : l.evs = [⟨.acqXR, 0x8000#64, 8, readM 8 0x8000#64 m⟩] := by
          rw [hm, stepEvs_setMem_st0]
        have htr : evTr ((l :: ls').take 1) = [l.evs] := by simp [evTr]
        refine .inr (.inl ⟨1, l.evs, true, t1, fun _ => (0, 0), by simp, .inl Nat.one_pos,
          ⟨rfl, rfl, _, he⟩, by simpa using PRun.cons hs (.inr ⟨m, hm⟩) trivial .nil, .inr rfl,
          ?_⟩)
        rw [htr, he]
        refine ⟨fun k hk => ?_, fun k k' h1 h2 => ?_, fun p y hy hW _ => ?_, fun _ _ h => h,
          .inl ⟨by simp, fun e he' => ?_⟩, fun h => ?_⟩
        · obtain rfl : k = 0 := by simpa using hk
          rfl
        · simp at h2; omega
        · obtain ⟨j, k⟩ := p
          cases j with
          | zero =>
            rw [evAt_single] at hy
            obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp hy
            obtain rfl : k = 0 := by simpa using hk
            cases hW
          | succ j => simp [evAt] at hy
        · simp only [List.mem_singleton] at he'; subst he'; simp
        · simp at h
  · exact .inl rfl

/-- **Non-vacuity of `refines_of_itemSim`**: the precise run in which the `ldaxr` reads the
environment's `5` (`ThreadLayerWitness.precise_ldaxr`) is realized by a run of the source. -/
theorem refines_ldaxr : ∃ t' n trS cE ψ,
    PRun Policy.arm stepi (fun _ _ => True) (st0, none) [⟨[ArmThread.Witness.evRead], false⟩] t' ∧
    n ≤ 1 ∧ SRun S false trS cE ∧
    Refines (· = ·) (fun _ => False)
      (MonPair (evTr (([⟨[ArmThread.Witness.evRead], false⟩] : List Lab).take n))) (conv trS)
      (conv (evTr (([⟨[ArmThread.Witness.evRead], false⟩] : List Lab).take n))) ψ ∧
    (n = 1 ∨ cE = true) := by
  obtain ⟨t', h1, h2⟩ := ThreadLayerWitness.precise_ldaxr
  have hr : PRun Policy.arm stepi (fun _ _ => True) (st0, none)
      [⟨[ArmThread.Witness.evRead], false⟩] t' := .cons h1 h2 trivial .nil
  obtain ⟨n, trS, cE, ψ, hn, hs, href, hend⟩ := refines_of_itemSim itemSim hr (.inl ⟨rfl, rfl⟩)
  exact ⟨t', n, trS, cE, ψ, hr, hn, hs, href, hend⟩

end Concurrency.ArmAllocThread.Witness

import FV.Backend.Proof.VCodeSemISeq
import FV.Backend.Proof.LowerContract

/-!
# The driver facts and terminator lowerings under the counted semantics (SEM1 step 2, `docs/plans/uninit.md` §5.3)

The instruction-selection driver (`Driver.DriverHyp`) is generic in the world type. Its
world-independent semantics facts (`Driver.DriverSemG`) and its terminator lowerings
(`LowerTermOk`, call-free) carry over from `csem` (at every call index) to `csemI`:

* `MInst.isCallI_mapRegs`, `MInst.isCallI_setTargets`: renaming and retargeting keep the calls;
* `DriverSemG.csemI`: `DriverSemG` of `csem` at every index gives it for `csemI`;
* `LowerTermOk.csemI`: a call-free terminator lowering correct for `csem` is correct for
  `csemI`, with the memory relation on the Arm world and any counter invariant (terminators
  other than calls leave the CLIF memory unchanged).
-/

namespace Backend.Proof

open Backend Backend.Proof.Driver

theorem _root_.Backend.MInst.isCallI_mapRegs (g : Reg → Reg) (i : MInst) :
    (i.mapRegs g).isCallI = i.isCallI := by
  cases i <;> rfl

theorem _root_.Backend.MInst.isCallI_setTargets {i i' : MInst} {ls : List Label}
    (h : i.setTargets ls = some i') : i'.isCallI = i.isCallI := by
  unfold MInst.setTargets at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

/-- **`DriverSemG` for `csemI`** from `DriverSemG` of `csem` at every call index. -/
theorem DriverSemG.csemI {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSemI}
    (h : ∀ n, DriverSemG (csem F ctx (X.at n))) : DriverSemG (Backend.Proof.csemI F ctx X) where
  jump := fun l w => by
    obtain ⟨w, n⟩ := w
    rw [csemI_eq, (h n).jump l w]
    rfl
  rename := fun g gn hg i => by
    funext uses w
    obtain ⟨w, n⟩ := w
    rw [csemI_eq, csemI_eq, (h n).rename g gn hg i, MInst.isCallI_mapRegs]
  retarget := fun i ls i' hs => by
    funext uses w
    obtain ⟨w, n⟩ := w
    rw [csemI_eq, csemI_eq, (h n).retarget i ls i' hs, MInst.isCallI_setTargets hs]

/-- **A call-free terminator lowering correct for `csem` is correct for `csemI`**, with the
memory relation `MR` on the Arm world and any counter invariant `Q`. -/
theorem LowerTermOk.csemI {F : BitVec 64 → Prop} {fctx : FnCtx} {X : ExtSemI} {m : Nat}
    {MR : MemRelT} {Q : Clif.Mem → Nat → Prop} {ctx : Ctx} {t : Clif.Terminator}
    {targets : List Label} {st st' : LState} {ms : List MInst}
    (h : LowerTermOk (csem F fctx (X.at m)) MR ctx t targets st st' ms)
    (hnc : ∀ i ∈ ms, i.isCallI = false) :
    LowerTermOk (Backend.Proof.csemI F fctx X) (fun sl cm w => MR sl cm w.1 ∧ Q cm w.2) ctx t
      targets st st' ms := by
  refine ⟨h.mono, h.defs, fun fr cm ρ ⟨w, n⟩ hf hv hd ⟨hmr, hq⟩ => ?_⟩
  have hr := h.run fr cm ρ w hf hv hd hmr
  have hseq := seqRun_csemI_noCall F fctx X m hnc ρ w n
  cases t with
  | ret xs =>
    intro vals hvals
    obtain ⟨hu, k, us, ops, ρ₁, w₁, outs, w₂, hs, hus, hlen, hall, hmr'⟩ := hr vals hvals
    exact ⟨hu, k, us, ops, ρ₁, (w₁, n), outs, (w₂, n), by rw [hseq, hs]; rfl, hus, hlen, hall,
      hmr', hq⟩
  | trap c =>
    obtain ⟨hu, k, i, ops, ρ₁, w₁, outs, w₂, hs, htc⟩ := hr
    exact ⟨hu, k, i, ops, ρ₁, (w₁, n), outs, (w₂, n), by rw [hseq, hs]; rfl, htc⟩
  | _ =>
    obtain ⟨hl, hj⟩ := hr
    refine ⟨hl, fun j hb => ?_⟩
    obtain ⟨hu, k, i, ops, ρ₁, w₁, outs, w₂, hs, hk, hmr'⟩ := hj j hb
    exact ⟨hu, k, i, ops, ρ₁, (w₁, n), outs, (w₂, n), by rw [hseq, hs]; rfl, hk, hmr', hq⟩

end Backend.Proof

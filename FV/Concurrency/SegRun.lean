import FV.Concurrency.PrepThread
import FV.Concurrency.VCodeThreadWitness

/-!
# A statement's segment as a forward run (T2h, #311, layer 2b)

A VCode thread run (`PrepThread.VTRun`) reads the environment's bytes at each memory instruction
(`VCodeThread.VTStep` steps on its world patched with the read events). The single-threaded
simulation (`LowerSim.stmt_step`) is a forward run of `VStep` from one world. This file connects
the two for a run whose steps have at most one event list (a statement's segment: one memory
instruction, `docs/plans/atomics.md` §3e layer 2):

* `vtstep_nil`: a thread step without events is a `VStep`;
* `vstep_setMem`: a step whose instruction has no events (`IFoot sem i uses w []`) is the same
  step on any memory, which it leaves unchanged (`ifoot_nil_mem`);
* **`vtrun_patch`**: a thread run of steps without events, one step with events `evs`, and steps
  without events is the forward `VStep` run from the start configuration patched once with the
  read bytes of `evs` (`patchC`). Witness: `ldar_patch`.
-/

namespace Concurrency.SegRun

open Arm ArmFoot ArmThread Backend Backend.Proof VCodeThread PrepThread

/-- The configuration's world with memory `m`. -/
def confMem (m : Memory) : VConf CV ArmState → VConf CV ArmState
  | .run s => .run { s with w := setMem m s.w }
  | .ret v w => .ret v (setMem m w)
  | .halt w => .halt (setMem m w)

/-- The world of a configuration. -/
def confW : VConf CV ArmState → ArmState
  | .run s => s.w
  | .ret _ w => w
  | .halt w => w

/-- The configuration with its world patched with the read events' bytes. -/
def patchC (evs : List Ev) (c : VConf CV ArmState) : VConf CV ArmState :=
  confMem (applyR evs (confW c).mem) c

theorem confMem_self (c : VConf CV ArmState) : confMem (confW c).mem c = c := by
  cases c <;> rfl

theorem patch_nil (w : ArmState) : patch [] w = w := rfl

/-- **A thread step without events is a `VStep`.** -/
theorem vtstep_nil {vc : VCode} {sem : ISem CV ArmState} {ev : MInst → List CV → ArmState → List Ev}
    {s : VState CV ArmState} {c' : VConf CV ArmState} (h : VTStep vc sem ev (.run s) [] c') :
    VStep vc sem (.run s) c' := by
  cases h with
  | mk _ _ _ _ _ hst => exact hst

/-- The instruction of a thread step has its events as footprint. -/
theorem vtstep_foot {vc : VCode} {sem : ISem CV ArmState} {ev : MInst → List CV → ArmState → List Ev}
    {b k : Nat} {ρ : Nat → CV} {w : ArmState} {evs : List Ev} {c' : VConf CV ArmState}
    (h : VTStep vc sem ev (.run ⟨b, k, ρ, w⟩) evs c') :
    ∃ vb i ops, vc.blocks[b]? = some vb ∧ vb.insts[k]? = some i ∧ i.operands = .ok ops ∧
      IFoot sem i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) (patch evs w) evs ∧
      VStep vc sem (.run ⟨b, k, ρ, patch evs w⟩) c' := by
  cases h with
  | mk hb hi hops _ hf hst => exact ⟨_, _, _, hb, hi, hops, hf, hst⟩

theorem vnext_setMem {vc : VCode} {b k n : Nat} {i : MInst} {uses : List CV} {ρ : Nat → CV}
    {w : ArmState} {ctl : Ctl} {c : VConf CV ArmState} (m : Memory)
    (h : VNext vc b k n i uses ρ w ctl c) : VNext vc b k n i uses ρ (setMem m w) ctl (confMem m c) := by
  cases h with
  | next h => exact .next h
  | goto h1 h2 h3 => exact .goto h1 h2 h3
  | ret h => exact .ret h
  | halt => exact .halt

/-- An instruction without events leaves the memory unchanged. -/
theorem ifoot_nil_mem {sem : ISem CV ArmState} {i : MInst} {uses : List CV} {w : ArmState}
    {r : List CV × ArmState × Ctl} (hf : IFoot sem i uses w []) (h : sem i uses w = some r) :
    r.2.1.mem = w.mem := by
  have e := hf.2 w.mem trivial
  rw [setMem_self, h] at e
  simp only [Option.map_some, Option.some.injEq] at e
  rw [e]; rfl

/-- **A step whose instruction has no events is the same step on any memory**, and leaves the
memory unchanged. -/
theorem vstep_setMem {vc : VCode} {sem : ISem CV ArmState} {b k : Nat} {ρ : Nat → CV}
    {w : ArmState} {c' : VConf CV ArmState}
    (hf : ∀ vb i ops, vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
      IFoot sem i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w [])
    (h : VStep vc sem (.run ⟨b, k, ρ, w⟩) c') (m : Memory) :
    VStep vc sem (.run ⟨b, k, ρ, setMem m w⟩) (confMem m c') ∧ (confW c').mem = w.mem := by
  cases h with
  | step hb hi hops hsem hlen hnx =>
    have hfi := hf _ _ _ hb hi hops
    have e := hfi.2 m trivial
    rw [hsem] at e
    simp only [Option.map_some] at e
    refine ⟨.step hb hi hops e hlen ?_, ?_⟩
    · have := vnext_setMem m hnx
      simpa [applyW] using this
    · have hm := ifoot_nil_mem hfi hsem
      cases hnx <;> simpa [confW] using hm

/-- A thread run of steps without events from a running configuration, forward. -/
theorem vtrun_nil_star {vc : VCode} {sem : ISem CV ArmState}
    {ev : MInst → List CV → ArmState → List Ev} :
    ∀ {c c' : VConf CV ArmState} {tr : List (List Ev)}, VTRun vc sem ev c tr c' →
      (∀ e ∈ tr, e = []) → ∀ m, Star (VStep vc sem) (confMem m c) (confMem m c') ∧
        ((confW c').mem = (confW c).mem)
  | _, _, _, .nil, _, m => ⟨.refl _, rfl⟩
  | _, _, _, .cons (c := c) hs hr, he, m => by
    have h0 := he _ List.mem_cons_self
    subst h0
    obtain ⟨ih, ihm⟩ := vtrun_nil_star hr (fun e h => he e (List.mem_cons_of_mem _ h)) m
    cases c with
    | run s =>
      obtain ⟨b, k, ρ, w⟩ := s
      obtain ⟨vb, i, ops, hb, hi, hops, hf, hst⟩ := vtstep_foot hs
      rw [patch_nil] at hf hst
      have hf' : ∀ vb' i' ops', vc.blocks[b]? = some vb' → vb'.insts[k]? = some i' →
          i'.operands = .ok ops' →
          IFoot sem i' ((ops'.toList.filter Operand.isUse).map (ρ ·.vreg)) w [] := by
        intro vb' i' ops' hb' hi' hops'
        rw [hb] at hb'; cases hb'
        rw [hi] at hi'; cases hi'
        rw [hops] at hops'; cases hops'
        exact hf
      obtain ⟨h1, h2⟩ := vstep_setMem hf' hst m
      exact ⟨.step h1 ih, ihm.trans h2⟩
    | ret v w => cases hs
    | halt w => cases hs

/-- **A segment run is a forward run from the patched start**: steps without events, one step
with events `evs` (reading the environment's bytes), steps without events, from a running
configuration, are the forward `VStep` run from the start patched once with `evs`' read bytes. -/
theorem vtrun_patch {vc : VCode} {sem : ISem CV ArmState}
    {ev : MInst → List CV → ArmState → List Ev} {c0 c1 c2 c3 : VConf CV ArmState}
    {pre post : List (List Ev)} {evs : List Ev}
    (h1 : VTRun vc sem ev c0 pre c1) (hpre : ∀ e ∈ pre, e = [])
    (h2 : VTStep vc sem ev c1 evs c2)
    (h3 : VTRun vc sem ev c2 post c3) (hpost : ∀ e ∈ post, e = []) :
    Star (VStep vc sem) (patchC evs c0) c3 := by
  have hpre' := vtrun_nil_star h1 hpre (applyR evs (confW c0).mem)
  have hpost' := vtrun_nil_star h3 hpost (confW c2).mem
  have e3 : confMem (confW c2).mem c3 = c3 := by rw [← hpost'.2]; exact confMem_self c3
  rw [confMem_self, e3] at hpost'
  refine Star.trans hpre'.1 (.step ?_ hpost'.1)
  cases c1 with
  | run s =>
    obtain ⟨b, k, ρ, w⟩ := s
    obtain ⟨-, -, -, -, -, -, -, hst⟩ := vtstep_foot h2
    have hm : (confW c0).mem = w.mem := hpre'.2.symm
    simpa [confMem, patch, hm] using hst
  | ret v w => cases h2
  | halt w => cases h2

/-- **Non-vacuity of `vtrun_patch`**: the `ldar` thread step of `VCodeThread.Witness` (reading the
environment's `5` at `0x8000` while its own memory holds `0`) is a forward step from its start
patched with that read. -/
theorem ldar_patch : ∃ c', Star (VStep Witness.vc0 (csem (fun _ => False) Witness.ctx0 Witness.X0))
    (patchC [Witness.ev5] (.run ⟨0, 0, Witness.ρ0, Witness.w0⟩)) c' := by
  obtain ⟨c', h⟩ := Witness.ldar_vtstep
  exact ⟨c', vtrun_patch .nil (fun _ h => nomatch h) h .nil (fun _ h => nomatch h)⟩

end Concurrency.SegRun

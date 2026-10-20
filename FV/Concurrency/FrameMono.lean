import FV.Concurrency.PrepThread

/-!
# Larger frame sets give sub-semantics (T2h, #311, layer 2: finding 3)

The M7 driver's statement step (`Backend.Proof.Driver.stmt_step`) does not reveal which
addresses the VCode of a statement accesses. The plan of `docs/plans/atomics.md` §3e: run each
statement's simulation under `csem F_t` with a **per-statement frame set** `F_t` (every address
outside the CLIF event's bytes), so that every successful access avoids `F_t`, and use the result
in the thread semantics under the function's frame set `F`. This file proves the step from `F_t`
to `F`:

* `csem_mono`: for `F ⊆ F'`, `csem F'` is a sub-semantics of `csem F` (where `csem F'` is
  defined, `csem F` is defined with the same result: `F` enters only through the guards
  `AccessOk`/`Avoids`);
* `cEvs_mono`: there the precise footprints agree too;
* `vtstep_mono`, `vtrun_mono`: **a VCode thread step (run) under `csem F'` with its footprint is
  one under `csem F`**.
-/

namespace Concurrency.FrameMono

open Arm ArmFoot ArmThread Backend Backend.Proof VCodeThread PrepThread

variable {F F' : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}

theorem avoids_mono (hF : ∀ a, F a → F' a) {n : Nat} {a : BitVec 64} (h : Avoids F' n a) :
    Avoids F n a := fun k hk hf => h k hk (hF _ hf)

theorem accessOk_mono (hF : ∀ a, F a → F' a) {i : MInst} {s : ArmState} (h : AccessOk F' ctx i s) :
    AccessOk F ctx i s := fun p hp => avoids_mono hF (h p hp)

theorem straightSem_mono (hF : ∀ a, F a → F' a) {i : MInst} {u : List CV} {w : ArmState}
    {r : List CV × ArmState × Ctl} (h : straightSem F' ctx i u w = some r) :
    straightSem F ctx i u w = some r := by
  unfold straightSem at h ⊢
  split at h
  · cases h
  · rename_i ops _
    split at h
    · cases h
    · rename_i ic _
      by_cases ha : AccessOk F' ctx ic (placeUses ops (canonRegs ops) u w)
      · rw [ite_eq_left ha] at h
        rw [ite_eq_left (accessOk_mono hF ha)]
        exact h
      · rw [ite_eq_right ha] at h; cases h

theorem loopSem_mono (hF : ∀ a, F a → F' a) {ty : CTy} {a : CV} {body : List Line}
    {regs : List Reg} {uses : List CV} {defs : List Reg} {w : ArmState}
    {r : List CV × ArmState × Ctl} (h : loopSem F' ty a body regs uses defs w = some r) :
    loopSem F ty a body regs uses defs w = some r := by
  unfold loopSem at h ⊢
  by_cases hc : AtomTy ty ∧ Avoids F' ty.bytes (lo64 a) ∧ Arm.r .ERR w = .None
  · rw [ite_eq_left hc] at h
    rw [ite_eq_left ⟨hc.1, avoids_mono hF hc.2.1, hc.2.2⟩]
    exact h
  · rw [ite_eq_right hc] at h; cases h

theorem ite_straight_mono (hF : ∀ a, F a → F' a) {c : Prop} {_ : Decidable c} {i : MInst}
    {u : List CV} {w : ArmState} {sb : Nat} {r : List CV × ArmState × Ctl}
    (h : (if c then straightSem F' ctx i u w else mspec sb i u w) = some r) :
    (if c then straightSem F ctx i u w else mspec sb i u w) = some r := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h ⊢; exact straightSem_mono hF h
  · rw [ite_eq_right hc] at h ⊢; exact h

theorem rmw_mono (hF : ∀ a, F a → F' a) {ty : CTy} {op : AtomicRmwLoopOp} {fl : Clif.MemFlags}
    {a b c d e : Reg} {u : List CV} {w : ArmState} {r : List CV × ArmState × Ctl}
    (h : csem F' ctx X (.atomicRmwLoop ty op fl a b c d e) u w = some r) :
    csem F ctx X (.atomicRmwLoop ty op fl a b c d e) u w = some r := by
  simp only [csem] at h ⊢
  rcases u with _ | ⟨u0, _ | ⟨x0, _ | ⟨y, t⟩⟩⟩
  · exact h
  · exact h
  · simp only at h ⊢
    by_cases he : Arm.r .ERR w = .None
    · rw [ite_eq_left he] at h ⊢
      exact loopSem_mono hF h
    · rw [ite_eq_right he] at h ⊢
      by_cases hc : AtomTy ty ∧ Avoids F' ty.bytes (lo64 u0)
      · rw [ite_eq_left hc] at h
        rw [ite_eq_left ⟨hc.1, avoids_mono hF hc.2⟩]
        exact h
      · rw [ite_eq_right hc] at h; cases h
  · exact h

theorem cas_mono (hF : ∀ a, F a → F' a) {ty : CTy} {fl : Clif.MemFlags}
    {a b c d e : Reg} {u : List CV} {w : ArmState} {r : List CV × ArmState × Ctl}
    (h : csem F' ctx X (.atomicCasLoop ty fl a b c d e) u w = some r) :
    csem F ctx X (.atomicCasLoop ty fl a b c d e) u w = some r := by
  simp only [csem] at h ⊢
  rcases u with _ | ⟨u0, _ | ⟨e0, _ | ⟨x0, _ | ⟨y, t⟩⟩⟩⟩
  · exact h
  · exact h
  · exact h
  · simp only at h ⊢
    by_cases he : Arm.r .ERR w = .None
    · rw [ite_eq_left he] at h ⊢
      cases hL : loopSem F' ty u0 (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28] [u0, e0, x0]
          [.x 27, .x 24] w with
      | none => rw [hL] at h; cases h
      | some r1 =>
        obtain ⟨outs, t1, c0⟩ := r1
        rw [hL] at h
        rw [loopSem_mono hF hL]
        simp only at h ⊢
        by_cases hne : Arm.ConditionHolds Cond.ne.bits t1
        · rw [ite_eq_left hne] at h ⊢; exact h
        · rw [ite_eq_right hne] at h ⊢; exact loopSem_mono hF h
    · rw [ite_eq_right he] at h ⊢
      by_cases hc : AtomTy ty ∧ Avoids F' ty.bytes (lo64 u0)
      · rw [ite_eq_left hc] at h
        rw [ite_eq_left ⟨hc.1, avoids_mono hF hc.2⟩]
        exact h
      · rw [ite_eq_right hc] at h; cases h
  · exact h

/-- **A larger frame set gives a sub-semantics.** -/
theorem csem_mono (hF : ∀ a, F a → F' a) {i : MInst} {u : List CV} {w : ArmState}
    {r : List CV × ArmState × Ctl} (h : csem F' ctx X i u w = some r) : csem F ctx X i u w = some r := by
  cases i
  case atomicRmwLoop => exact rmw_mono hF h
  case atomicCasLoop => exact cas_mono hF h
  all_goals
    simp only [csem] at h ⊢
    first | exact h | exact ite_straight_mono hF h

theorem casEvs_mono (hF : ∀ a, F a → F' a) {ty : CTy} {fl : Clif.MemFlags} {a b c d e : Reg}
    {u0 e0 x0 : CV} {w : ArmState} {r : List CV × ArmState × Ctl}
    (h : csem F' ctx X (.atomicCasLoop ty fl a b c d e) [u0, e0, x0] w = some r) :
    casEvs F ty fl u0 e0 x0 w = casEvs F' ty fl u0 e0 x0 w := by
  unfold casEvs
  by_cases he : Arm.r .ERR w = .None
  · simp only [csem, ite_eq_left he] at h
    cases hL : loopSem F' ty u0 (casLoopHead ty.bits fl) [.x 25, .x 26, .x 28] [u0, e0, x0]
        [.x 27, .x 24] w with
    | none => rw [hL] at h; cases h
    | some r1 => rw [loopSem_mono hF hL]
  · have h1 : ∀ G : BitVec 64 → Prop, loopSem G ty u0 (casLoopHead ty.bits fl)
        [.x 25, .x 26, .x 28] [u0, e0, x0] [.x 27, .x 24] w = none := fun G => by
      unfold loopSem
      rw [ite_eq_right (fun hc => he hc.2.2)]
    rw [h1, h1]

/-- Where `csem F'` is defined, the precise footprints under `F` and `F'` agree. -/
theorem cEvs_mono (hF : ∀ a, F a → F' a) {i : MInst} {u : List CV} {w : ArmState}
    {r : List CV × ArmState × Ctl} (h : csem F' ctx X i u w = some r) :
    cEvs F ctx i u w = cEvs F' ctx i u w := by
  cases i
  case atomicCasLoop ty fl a b c d e =>
    rcases u with _ | ⟨u0, _ | ⟨e0, _ | ⟨x0, _ | ⟨y, t⟩⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · simp only [cEvs, MInst.isCtl, ite_true]; exact casEvs_mono hF h
    · rfl
  case atomicRmwLoop =>
    rcases u with _ | ⟨u0, _ | ⟨x0, _ | ⟨y, t⟩⟩⟩ <;> rfl
  all_goals rfl

/-- **A VCode thread step under a larger frame set is one under the smaller.** -/
theorem vtstep_mono (hF : ∀ a, F a → F' a) {vc : VCode} {c c' : VConf CV ArmState} {evs : List Ev}
    (h : VTStep vc (csem F' ctx X) (cEvs F' ctx) c evs c') :
    VTStep vc (csem F ctx X) (cEvs F ctx) c evs c' := by
  cases h with
  | @mk b k ρ w vb i ops _ _ hvb hi hops hevs hfoot hst =>
    cases hst with
    | step hvb1 hi1 hops1 hsem hlen hnext =>
      rename_i vb1 i1 ops1 outs w' ctl
      rw [hvb] at hvb1; cases hvb1
      rw [hi] at hi1; cases hi1
      rw [hops] at hops1; cases hops1
      refine .mk hvb hi hops (by rw [cEvs_mono hF hsem]; exact hevs) ⟨hfoot.1, fun m hm => ?_⟩
        (.step hvb hi hops (csem_mono hF hsem) hlen hnext)
      have e := hfoot.2 m hm
      rw [hsem, Option.map_some] at e
      rw [csem_mono hF e, csem_mono hF hsem, Option.map_some]

/-- Runs. -/
theorem vtrun_mono (hF : ∀ a, F a → F' a) {vc : VCode} {c c' : VConf CV ArmState}
    {tr : List (List Ev)} (h : VTRun vc (csem F' ctx X) (cEvs F' ctx) c tr c') :
    VTRun vc (csem F ctx X) (cEvs F ctx) c tr c' := by
  induction h with
  | nil => exact .nil
  | cons hs _ ih => exact .cons (vtstep_mono hF hs) ih

end Concurrency.FrameMono

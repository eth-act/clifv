module

public import FV.Concurrency.IselFoot

@[expose] public section

/-!
# From "touched" to "covered by an event" (T2h, #311, layer 2d)

`IselClif.access_in_events` says that no byte of a memory statement's CLIF access stays
outside every event of its code's run (`¬ RunOut`). This file turns that into the event that
covers each byte, and pins the event's address:

* `RunAt`: the run of `ms` reaches instruction `j` in a given state; `RunFoot sem ev`: every
  instruction the run reaches steps with the footprint `ev` (`IFoot`);
* **`cover_of_not_runOut`**: under `RunFoot`, a byte that is not outside every event (`¬ RunOut`)
  lies in an event `ev i uses wj` of an instruction `i = ms[j]` the run reaches (`RunAt`);
* **`addr_eq_of_cover`**: an event of `n` bytes (`n ≤ 2^63`) covering every byte of
  `[a, a + n)` (without wrap-around, `a + n ≤ 2^64`, as `MemRelOk.valid` gives for valid CLIF
  accesses) starts at `a`.
-/

namespace Concurrency.IselCover

open Arm ArmFoot ArmThread VCodeThread Backend Backend.Proof IselVary IselFoot

/-- **The run of `ms` from `ρ, w` reaches instruction `j` in state `ρj, wj`.** -/
def RunAt (sem : Sem) : List MInst → (Nat → CV) → ArmState → Nat → (Nat → CV) → ArmState → Prop
  | _, ρ, w, 0, ρj, wj => ρj = ρ ∧ wj = w
  | [], _, _, _ + 1, _, _ => False
  | i :: ms, ρ, w, j + 1, ρj, wj => ∃ ops outs w', i.operands = .ok ops ∧
      sem i (vuses ops ρ) w = some (outs, w', .next) ∧ RunAt sem ms (vdefUpd ops outs ρ) w' j ρj wj

/-- **Every instruction the run of `ms` reaches steps with the footprint `ev`.** -/
def RunFoot (sem : Sem) (ev : MInst → List CV → ArmState → List Ev) :
    List MInst → (Nat → CV) → ArmState → Prop
  | [], _, _ => True
  | i :: ms, ρ, w => ∀ ops, i.operands = .ok ops →
      IFoot sem i (vuses ops ρ) w (ev i (vuses ops ρ) w) ∧
        ∀ outs w', sem i (vuses ops ρ) w = some (outs, w', .next) →
          RunFoot sem ev ms (vdefUpd ops outs ρ) w'

open Classical in
/-- **A byte not outside every event of the run lies in an event of an instruction it reaches.** -/
theorem cover_of_not_runOut {sem : Sem} {ev : MInst → List CV → ArmState → List Ev}
    {x : BitVec 64} :
    ∀ {ms : List MInst} {ρ : Nat → CV} {w : ArmState}, RunFoot sem ev ms ρ w →
      ¬ RunOut sem x ms ρ w →
      ∃ j ρj wj i ops, RunAt sem ms ρ w j ρj wj ∧ ms[j]? = some i ∧ i.operands = .ok ops ∧
        ∃ e ∈ ev i (vuses ops ρj) wj, ∃ k < e.n, e.addr + BitVec.ofNat 64 k = x
  | [], _, _, _, hn => absurd trivial hn
  | i :: ms, ρ, w, hf, hn => by
    simp only [RunOut, not_forall] at hn
    obtain ⟨ops, hops, hn⟩ := hn
    obtain ⟨hif, hnext⟩ := hf ops hops
    by_cases hout : Out x (ev i (vuses ops ρ) w)
    · have hn' : ¬ ∀ outs w', sem i (vuses ops ρ) w = some (outs, w', .next) →
          RunOut sem x ms (vdefUpd ops outs ρ) w' := fun hall => hn ⟨_, hif, hout, hall⟩
      simp only [not_forall] at hn'
      obtain ⟨outs, w', hs, hr⟩ := hn'
      obtain ⟨j, ρj, wj, i', ops', hat, hj, hops', hc⟩ := cover_of_not_runOut (hnext outs w' hs) hr
      exact ⟨j + 1, ρj, wj, i', ops', ⟨ops, outs, w', hops, hs, hat⟩, hj, hops', hc⟩
    · simp only [Out, not_forall, Decidable.not_not] at hout
      obtain ⟨e, he, k, hk, hx⟩ := hout
      exact ⟨0, ρ, w, i, ops, ⟨rfl, rfl⟩, rfl, hops, e, he, k, hk, hx⟩

/-- **An event of `n` bytes covering every byte of `[a, a + n)` starts at `a`.** -/
theorem addr_eq_of_cover {A : BitVec 64} {a n : Nat} (hn : 0 < n) (hn2 : n ≤ 2 ^ 63)
    (ha : a + n ≤ 2 ^ 64)
    (h : ∀ k < n, ∃ j < n, A + BitVec.ofNat 64 j = BitVec.ofNat 64 (a + k)) :
    A = BitVec.ofNat 64 a := by
  obtain ⟨j0, hj0, e0⟩ := h 0 hn
  obtain ⟨j1, hj1, e1⟩ := h (n - 1) (by omega)
  have t0 := congrArg BitVec.toNat e0
  have t1 := congrArg BitVec.toNat e1
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_zero] at t0 t1
  have hA := A.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

end Concurrency.IselCover

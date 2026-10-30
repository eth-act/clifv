import FV.E2E.LinkArmXNIF
import FV.E2E.LinkArmHCall
import FV.E2E.LinkArmLockedCalleeWitness

/-!
# Witnesses: `XNIF` of the guarded semantics, the lock to the return and the call hook's lock
(SEM1 #537, #713; `LinkArmXNIF.lean`, `LinkArmLockRet.lean`, `LinkArmHCall.lean`)

* `guardR_eps_*`: a guard whose underlying semantics answers nothing answers its ε-chosen result
  at two distinct worlds, and `guardR_rel` makes the two answers equal;
* `mem_eq_of_saved_w`: two distinct states (they differ in `x0`) with the same saved record;
* `r_canon_congr_Lsl`: the canonical states of two worlds that differ in the pc have the same
  registers (`Lsl`);
* on the slotted system `Lsl` (`Ok`, budget discharged; the induction hypotheses remain):
  `progXBT_rel_Lsl`, `xnifXPBTGY_Lsl`, `callLock_of_Lsl`, `hooks_lock_tls_Lsl`,
  `hooks_lock_base_Lsl`.
-/

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- The semantics that answers no call. -/
noncomputable def XNone : ExtSem := { Lsl.Xb with call := fun _ _ _ => none }

/-- A satisfiable, not vacuous guard predicate (independent of the world). -/
def QOne : Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop :=
  fun _ _ _ r => r.1 = []

noncomputable def wA : Arm.ArmState := Arm.w (.GPR 0#5) 0#64 Arm.ArmState.default
noncomputable def wB : Arm.ArmState := Arm.w (.GPR 0#5) 1#64 Arm.ArmState.default

theorem wA_ne_wB : wA ≠ wB := by
  intro e
  have := congrArg (Arm.r (.GPR 0#5)) e
  simp only [wA, wB, Arm.r_of_w_same] at this
  exact absurd this (by decide)

/-- **The guard answers at both worlds** (its ε branch: `XNone` answers nothing). -/
theorem guardR_eps_exists (w : Arm.ArmState) :
    ∃ r, (XNone.guardR QOne).call none [] w = some r ∧ QOne none [] w r :=
  ExtSem.guardR_spec ⟨([], w), rfl⟩ fun h => by
    have := h ([ofX 0#64], w)
    simp [QOne] at this

/-- **`guardR_rel`: the ε-chosen answers at two distinct worlds are equal.** -/
theorem guardR_eps_eq {r r' : List CV × Arm.ArmState}
    (h : (XNone.guardR QOne).call none [] wA = some r)
    (h' : (XNone.guardR QOne).call none [] wB = some r') : r = r' :=
  guardR_rel (X := XNone) (Q := QOne) (fun r r' => r = r') (fun _ => rfl)
    (fun r r' e => by subst e; exact Iff.rfl) ⟨fun _ => rfl, fun _ => rfl⟩
    (fun _ _ h => by cases h) h h'

/-- **`mem_eq_of_saved` on two distinct states** (same memory, different `x0`). -/
theorem mem_eq_of_saved_w {a : BitVec 64}
    (ha : StackBelow 8 (BitVec.ofNat 64 0x100) a) : wA.mem a = wB.mem a :=
  mem_eq_of_saved (by decide) (read_mem_bytes_congr _ _ fun k _ => by
    simp only [wA, wB, Arm.ArmState.mem_w_eq_mem]) ha

/-- **`r_canon_congr` on two worlds that differ in the pc.** -/
theorem r_canon_congr_Lsl (g : Clif.Function) (uses : List CV) (f : Arm.StateField) :
    Arm.r f (Lsl.canon g uses wA) = Arm.r f (Lsl.canon g uses (Arm.w .PC 4#64 wA)) :=
  Lsl.r_canon_congr g uses (fun _ hf => (Arm.r_of_w_different hf).symm) f

theorem progXBT_rel_Lsl {M : Nat}
    (ih : 0 < M → Lsl.ThmPRBRL (fun M _ => Lsl.K M) (M - 1))
    (hdet : 0 < M → Lsl.DetPRBRU (fun M _ => Lsl.K M) (M - 1))
    (htw : 0 < M → Lsl.CallTwinCET (fun M _ => Lsl.K M) M) {h : Clif.Function}
    (hh : h ∈ Lsl.P.funcs) (hcal : ∃ g ∈ Lsl.P.funcs, Lsl.Callee g h) {F : BitVec 64 → Prop}
    (himgF : ∀ a, Lsl.Img a → F a) {uses : List CV} {W W' : Arm.ArmState}
    (hr : ∀ f, f ≠ .PC → Arm.r f W = Arm.r f W') (hp : W.program = W'.program)
    (hm : ∀ a, ¬ F a → W.mem a = W'.mem a)
    (hrgn : ∀ a, StackBelow (frameDrop (Lsl.A h).af + (fun M _ => Lsl.K M) (M - 1) h) (spv W) a →
      W.mem a = W'.mem a)
    {o : List CV} {x : Arm.ArmState}
    (hx : Lsl.progXBT (fun M _ => Lsl.K M) M F h uses W = some (o, x)) :
    ∃ x', Lsl.progXBT (fun M _ => Lsl.K M) M F h uses W' = some (o, x') ∧ SameWorld F x x' :=
  Lsl.progXBT_rel Lsl_ok (Lsl.budget_K Lsl_ok) ih hdet htw hh hcal himgF hr hp hm hrgn hx

theorem xnifXPBTGY_Lsl (hN : Lsl.NeedNI) {M : Nat}
    (ih : 0 < M → Lsl.ThmPRBRL (fun M _ => Lsl.K M) (M - 1))
    (hdet : 0 < M → Lsl.DetPRBRU (fun M _ => Lsl.K M) (M - 1))
    (htw : 0 < M → Lsl.CallTwinCET (fun M _ => Lsl.K M) M) {g : Clif.Function}
    (hg : g ∈ Lsl.P.funcs) {F : BitVec 64 → Prop} (himgF : ∀ a, Lsl.Img a → F a)
    (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) {c : BitVec 64} {cs : Clif.State}
    (hnrc : NoRetCall (Lsl.envOfB M g c) Lsl.P.bare cs) {s : Clif.State} {n : Nat}
    (hs : ReachN (Lsl.envOfB M g c) Lsl.P.bare cs s n) :
    XNIF F Lsl.syms (g.externs.map (·.2)) (indSigs g) c
      (CallLg ((Lsl.envOfB M g c).only (Clif.Invoked (Lsl.envOfB M g c) Lsl.P.bare s))
        (g.externs.map (·.2)) (indSigs g))
      ((Lsl.XPBTGY (fun M _ => Lsl.K M) M g F P R (Lsl.envOfB M g c) cs c).at n) :=
  Lsl.xnifXPBTGY Lsl_ok (Lsl.budget_K Lsl_ok) hN ih hdet htw hg himgF P R hnrc hs

theorem callLock_of_Lsl {M : Nat} (hM : 0 < M)
    (ih : Lsl.ThmPRBRLE (fun M _ => Lsl.K M) (M - 1))
    (hlock : Lsl.LockRet (fun M _ => Lsl.K M) (M - 1)) : Lsl.CallLock (fun M _ => Lsl.K M) M :=
  Lsl.callLock_of Lsl_ok (Lsl.budget_K Lsl_ok) hM ih hlock

/-- **`hooks_lock_tls` on two distinct states** (they differ in `x30`, `Z = ∅`). -/
theorem hooks_lock_tls_Lsl {F : BitVec 64 → Prop} (hN : HookNIX Lsl.Hb Lsl.BaseDest F) (M : Nat)
    (m : String) (r : Reg) (u : Arm.ArmState) (v : BitVec 64) :
    StEqOutX (fun _ => False) ((Lsl.hooks M).tls m r u)
      ((Lsl.hooks M).tls m r (Arm.w (.GPR 30#5) v u)) :=
  Lsl.hooks_lock_tls hN M m r ⟨fun _ hf => (Arm.r_of_w_different hf).symm,
    (Arm.w_program).symm, fun a _ => (congrFun (Arm.ArmState.mem_w_eq_mem _ _ _) a).symm⟩
    (fun _ h => h.elim)

/-- **`hooks_lock_base` for a base extern, two distinct states** (differ in `x30`). -/
theorem hooks_lock_base_Lsl {F : BitVec 64 → Prop} (hN : HookNIX Lsl.Hb Lsl.BaseDest F)
    (M : Nat) {nm : String} (hpf : Lsl.P.func? nm = none) (u : Arm.ArmState) (v : BitVec 64) :
    StEqOutX (fun _ => False) ((Lsl.hooks M).call (some nm) u)
      ((Lsl.hooks M).call (some nm) (Arm.w (.GPR 30#5) v u)) :=
  Lsl.hooks_lock_base hN (.inr ⟨nm, rfl, hpf⟩) (fun h => by cases h) (fun h => by cases h)
    ⟨fun _ hf => (Arm.r_of_w_different hf).symm, (Arm.w_program).symm,
      fun a _ => (congrFun (Arm.ArmState.mem_w_eq_mem _ _ _) a).symm⟩ (fun _ h => h.elim)

end E2E.LinkSlotSysWitness

import FV.E2E.RegLevelCallN
import FV.E2E.RegLevelTryN
import FV.E2E.LinkArmProphThmWitness

/-!
# Witnesses for the call-state variants, part B (SEM1 #537, step 2k)

* `CalleeOkGP`/`CalleeTryOkGP` (the contracts of `realizes_callN`, `realizes_tryCallN`) hold for a
  concrete callee hook and external semantics when they are required at no state
  (`calleeOkGP_none`, `calleeTryOkGP_none`), which `CalleeOkG` itself does not allow; from
  `CalleeOkG`/`CalleeTryOkG` at any `P` (`CalleeOkG.p`, `CalleeTryOkG.p`).
* `RL.CallSt`/`RL.NoCallAt` of `realizes_*N` on the one-line `bl f` function `faC`
  (`LinkArmProphThmWitness`) loaded at `0x1000`: its state at `0x1000` is a call state
  (`callSt_faC`), a state at `0x1004` is none (`noCallAt_faC`).
* `RunsAsS` with any segment fact for an execution that never runs (`runsAsS_none`).

The lemmas `realizes_callN` … `ret_machineN` themselves are applied on a compiled function with
a call by `RegLevelCorrectCWitness` (through `realizes_allC`).
-/

namespace Backend.Proof.RegLevelLocBWitness

open Backend Backend.Proof E2E

/-- A callee hook that returns to the next instruction. -/
def H0 : ArmHooks := ⟨fun _ s => Arm.w .PC (Arm.r .PC s + 4) s, fun _ _ s => s⟩

/-- External semantics with no call. -/
def X0 : ExtSem := ⟨fun _ _ _ => none, fun _ _ => 0, 0, fun _ _ => Arm.PState.zero⟩

theorem calleeOkGP_none (F : BitVec 64 → Prop) (K : Nat) (G : BitVec 64 → Prop)
    (s0 : Arm.ArmState) (Pc : BitVec 64 → MInst → Prop) (S : CallInfo → Prop)
    (gv : Nat → String → Prop) : CalleeOkGP (fun _ => False) F K G s0 Pc X0 H0 S gv :=
  ⟨fun _ _ _ _ h => h.elim, fun _ s _ _ => Arm.r_of_w_same .., fun _ _ _ _ _ h => by cases h⟩

theorem calleeTryOkGP_none (F : BitVec 64 → Prop) (K : Nat) (G : BitVec 64 → Prop)
    (s0 : Arm.ArmState) (Pc : BitVec 64 → MInst → Prop) (S : CallInfo → TryInfo → Prop)
    (gv : Nat → String → Prop) : CalleeTryOkGP (fun _ => False) F K G s0 Pc X0 H0 S gv :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => h.elim

theorem calleeOkGP_of {F : BitVec 64 → Prop} {K : Nat} {G : BitVec 64 → Prop} {s0 : Arm.ArmState}
    {Pc : BitVec 64 → MInst → Prop} {X : ExtSem} {H : ArmHooks} {S : CallInfo → Prop}
    {gv : Nat → String → Prop} (h : CalleeOkG F K G s0 Pc X H S gv) :
    CalleeOkGP (fun s => spOf s = 0x8000#64) F K G s0 Pc X H S gv :=
  h.p _

theorem callSt_faC (R : RL) (hfa : R.fa = LinkArmProphThmWitness.faC) (hb : R.base = 0x1000#64) :
    R.CallSt LinkArmProphThmWitness.u0 := by
  unfold RL.CallSt
  rw [hfa, hb]
  exact LinkArmProphThmWitness.callPc_u0 0

theorem noCallAt_faC (R : RL) (hfa : R.fa = LinkArmProphThmWitness.faC) (hb : R.base = 0x1000#64)
    (u : Arm.ArmState) (hu : Arm.r .PC u = 0x1004#64) : R.NoCallAt u := by
  rintro ⟨j, i, t, hj, -, he⟩
  rw [hfa] at hj
  rw [hfa, hb, hu] at he
  cases j with
  | zero => simp [LinkArmProphThmWitness.faC, lineOffset] at he
  | succ j => simp [LinkArmProphThmWitness.faC] at hj

theorem runsAsS_none (R : RL) (i' : MInst) (ls1 : List Line) (pre : Arm.ArmState → Prop)
    (Seg : Arm.ArmState → Nat → Prop) : RunsAsS R (fun _ _ _ => none) i' ls1 pre Seg :=
  fun _ _ _ _ _ _ _ _ _ _ h => by cases h

end Backend.Proof.RegLevelLocBWitness

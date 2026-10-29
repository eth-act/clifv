module

public import FV.E2E.LinkArmDetX
public import FV.E2E.LinkArmProphDetRWitness
public import FV.E2E.LinkArmStepLineWitness
public import FV.E2E.LinkArmProphReg

@[expose] public section

/-!
# Witnesses for the determinism clause up to the return address (`LinkArmDetX.lean`)

* `thmPDERX_LU`: `ThmPDERX` at every depth for `LinkArmProphDetWitness.Lu` (a program with a
  call); `thmPR_of_thmPDERX_LU`: `ThmPDERX.thmPR` on it;
* `ret_retAgreeX`: the `ret` line of `StepLineWitness.faW` stepped from two states differing in
  `x30`, with the saved-LR word below `c` in the lock-step set, agrees for the caller
  (`retAgreeX_of_ret`);
* `proph_lockstep`, `reg_lockstep`: the byte and register prophecies of a run carried to the run
  from the same state with another `x30` (identity machine).
-/

namespace E2E.LinkArmDetXWitness

open Arm Backend Backend.Proof LinkArmProphDetWitness StepLineWitness

theorem thmPDERX_LU (M : Nat) : Lu.ThmPDERX (fun M _ => Lu.K M) M :=
  LinkSys.ThmPDER.thmPDERX Lu (LinkArmProphDetRWitness.thmPDER_LU M)

theorem thmPR_of_thmPDERX_LU : Lu.ThmPR (fun M _ => Lu.K M) 3 :=
  LinkSys.ThmPDERX.thmPR Lu (thmPDERX_LU 3)

theorem ret_retAgreeX (X : ExtSem) (H : ArmHooks) (v c : BitVec 64) :
    RetAgreeX 16 c (ArmStepX X H faW (GprFoot.setGpr 30#5 v (tAt 3))) (ArmStepX X H faW (tAt 3)) :=
  retAgreeX_of_ret (Z := StackBelow 8 c) (onLine 3 _ rfl (by decide)) (stEqOutX_setGpr30 v _)
    fun _ _ h8 hz => h8 hz

theorem proph_lockstep (v : BitVec 64) (K : Nat) (c : BitVec 64) (fa : FnAsm) (base : BitVec 64)
    (s : ArmState) (n : Nat) :
    ProphOkUpTo K c id fa base s (prophOf id fa base (GprFoot.setGpr 30#5 v s)) n :=
  prophOkUpTo_of_lockstepX (Zs := fun _ _ => False) (lockstep_id v n s)
    (fun _ _ _ _ _ _ h => h) ((prophOk_prophOf K c id fa base _).upTo n)

theorem reg_lockstep (v : BitVec 64) (c : BitVec 64) (fa : FnAsm) (base : BitVec 64)
    (s : ArmState) (n : Nat) :
    ProphRegOkUpToX c id fa base s (prophStOf id fa base (GprFoot.setGpr 30#5 v s)) n :=
  prophRegOkUpToX_of_lockstepX (Zs := fun _ _ => False) (lockstep_id v n s)
    fun i _ hc _ f _ _ _ => by rw [prophStOf_call hc]

end E2E.LinkArmDetXWitness

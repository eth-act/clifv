import FV.Concurrency.CallStepT
import FV.Concurrency.ClifThreadIWitness

/-!
# Witnesses: the event-free steps between segments (#473, step (4))

* `call_W`: `realizedT_call` for the call of `%g` (an 8-byte placed slot) by `%f` of
  `ClifThreadIWitness`: one event-free label realizes the call, the callee entered with no
  callers of its own below `%f`'s frame, its slot bytes added to the mask;
* `priv_W`: `realizedT_priv` on an event-free label;
* `ret_W`: `cstepS_ret_lift` for a frame with no results returning to a suspended caller.
-/

namespace Concurrency.CallStepT.Witness

open Prog ClifThread ClifThreadI ThreadRefine CallComposeT ArmThread ClifLift
  Concurrency.ClifThreadI.Witness

theorem pushC_nil (s : Clif.State) : pushC [] s = s := by
  simp [pushC]

theorem call_W (l : Lab) (L : List Lab) (hl : l.evs = []) (U D : Nat → Prop) :
    ∃ (vals : List Clif.Val) (B0 : Clif.Block) (cs : Clif.State),
      RealizedT envW pW (fun _ => True) (l :: L) 1 (encT U (.run (csW memW)))
        (encT (fun a => U a ∨ slotZ gW memW a)
          (.run (pushC [({ (csW memW).frame with body := [] }, [1])] cs))) D D ∧
      cs.callers = [] ∧ cs.frame.func = gW := by
  obtain ⟨hb, he, hc, -, -, hs, -⟩ := factsW
  have hs' : ∃ s1, Clif.step envW pW (pushC [] (csW memW)) = .next s1 := by
    rw [pushC_nil]
    cases h : Clif.step envW pW (csW memW) with
    | next s1 => exact ⟨s1, rfl⟩
    | _ => rw [h] at hs; cases hs
  obtain ⟨s1, hs1⟩ := hs'
  obtain ⟨vals, B0, cs, -, -, hR, hcs, hf, -⟩ := realizedT_call (Bnd := fun _ => True) hl []
    (s := csW memW) (by exact hb) he hc hs1 U D
  refine ⟨vals, B0, cs, ?_, hcs, hf⟩
  have e : (csW memW).callers = [] := rfl
  rw [pushC_nil, e, List.nil_append] at hR
  exact hR

theorem priv_W (env : Clif.Env) (p : Clif.Program) (l : Lab) (hl : l.evs = []) (c : TState)
    (D : Nat → Prop) :
    RealizedT env p (fun _ => True) [l] 1 c c D (fun a => D a ∨ False) :=
  realizedT_priv (by simp) (P := fun _ => False)
    (fun q y hy => by
      rw [show ArmAllocThread.evTr (List.take 1 [l]) = [[]] by simp [ArmAllocThread.evTr, hl],
        CallStepT.evAt_nil1] at hy
      cases hy)
    (fun l' hl' e he => by simp at hl'; subst hl'; rw [hl] at he; cases he)
    (fun x hx => absurd hx List.not_mem_nil) .nil (fun _ h => h.elim) D

/-- A frame of `default` with nothing left to run, returning nothing. -/
def frR : Clif.Frame := { func := default, regs := Clif.Regs.empty, slots := [], body := [], term := .ret [] }

theorem ret_W (env : Clif.Env) (p : Clif.Program) (cs : List (Clif.Frame × List Clif.ValueId))
    (m : Clif.Mem) (U : Nat → Prop) :
    CStepS env p (encT U (.run (pushC ((frR, []) :: cs) ⟨frR, [], m⟩))) []
      (encT U (.run ⟨{ frR with regs := frR.regs }, cs, (m.free []).leave⟩)) :=
  cstepS_ret_lift (s := ⟨frR, [], m⟩) rfl rfl rfl (vals := []) rfl (u := ()) rfl (regs := frR.regs)
    rfl U

end Concurrency.CallStepT.Witness

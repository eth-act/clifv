module

public import FV.Concurrency.CallStepT
public import FV.Concurrency.CallRetLink

@[expose] public section

/-!
# A callee's return end as a `RealizedT` of the thread (#473, step (4))

At a callee's return end (`CallRetsEnd.RetEnd` at its `return`, the activation's CLIF state
`s'` without callers of its own below its caller's frame), on the linked machine
(`LinkedMachine.Link.ret_end`: the epilogue and `ret`, `n` private steps without `relXW`):

* `cstepS_ret_pop`: the CLIF return (`CallRets.ret_pop`) as a `CStepS` step, the mask kept;
* **`realizedT_ret`**: every precise run from the pause is realized: before the `ret` by no CLIF
  step, from the `ret` on by the CLIF return into the caller, with `RetC` at the state after the
  `ret` and the Arm writes (private to the callee's activation) dirty.
-/

namespace Concurrency.CallRetT

open Arm ArmThread Prog ClifThread ClifThreadI ThreadRefine CallComposeT ArmAllocThread ClifLift
  ClifCStepTerm CallRetsEnd IselCallRet LinkedMachine LinkedMachine.Link Backend Backend.Proof
  E2E CallStepT

variable {env : Clif.Env} {p : Clif.Program} {Bnd : Nat → Prop}

/-- **The CLIF return pop as a `CStepS` step** (module doc). -/
theorem cstepS_ret_pop {s : Clif.State} (hcall : s.callers = []) (hat : AtRetS s)
    {vals : List Clif.Val} {cm : Clif.Mem} (hs : Clif.step env p s = .done vals cm)
    {caller : Clif.Frame} {results : List Clif.ValueId} {cs : List (Clif.Frame × List Clif.ValueId)}
    {regs : Clif.Regs} (hr : caller.regs.setMany results vals = some regs) (U : Nat → Prop) :
    CStepS env p (encT U (.run (pushC ((caller, results) :: cs) s))) []
      (encT U (.run ⟨{ caller with regs := regs }, cs, cm⟩)) := by
  obtain ⟨hb, xs, hT⟩ := hat
  have h := CallRets.ret_pop hcall hb hT hs (cs := cs) hr
  have hI := cstepI_of_cstep h (U := U) (fun e he => absurd he List.not_mem_nil)
  have e : (fun a => U a ∧ ¬ writes ([] : List (Ev SKind BVal)) a) = U := by
    funext a
    have : ¬ writes ([] : List (Ev SKind BVal)) a := fun ⟨_, h, _⟩ => absurd h List.not_mem_nil
    exact propext ⟨fun h => h.1, fun h => ⟨h, this⟩⟩
  rw [e] at hI
  exact cstepS_of_cstepI hI

variable {L : Link} {FB : LFn} {s0 : ArmState} {K : Nat} {G : BitVec 64 → Prop}

/-- **The return end realized** (module doc). -/
theorem realizedT_ret (hL : L.Ok) {nB : String} (hB : (nB, FB) ∈ L.fns)
    (hRB : (L.act FB s0 K G).Wf) {ra : BitVec 64} (hent : AbiCall FB.fb FB.base ra s0)
    (hra : ∀ k < FB.fb.words.size, ra ≠ FB.base + BitVec.ofNat 64 (4 * k))
    {nA : String} {FA : LFn} (hA : (nA, FA) ∈ L.fns) (hrA : FA.InRange ra)
    {MR : MemRelT} {slots : List (Clif.SlotId × Nat)} {r₀ : Reg → CV} {x : ArmState}
    {s' : Clif.State} (hret : RetEnd (L.act FB s0 K G) ra env p MR slots r₀ x s')
    (hat : AtRetS s') (hcall : s'.callers = [])
    (hb : ∀ l, PrivA (L.act FB s0 K G) l → Bnd l) :
    ∃ n vals cm, 0 < n ∧ Clif.step env p s' = .done vals cm ∧
      RetC (L.act FB s0 K G) ra r₀ (iterN (L.act FB s0 K G).step n x) ∧
      (iterN (L.act FB s0 K G).step n x).mem = x.mem ∧
      ∀ {caller : Clif.Frame} {results : List Clif.ValueId}
        {cs : List (Clif.Frame × List Clif.ValueId)} {regs : Clif.Regs},
        caller.regs.setMany results vals = some regs → ∀ (U D : Nat → Prop)
        {mon : Mon} {ls : List Lab} {t' : ArmState × Mon},
        PRun Policy.arm L.M (OkPriv (L.act FB s0 K G)) (x, mon) ls t' →
        (ls.length < n → RealizedT env p Bnd ls ls.length
          (encT U (.run (pushC ((caller, results) :: cs) s')))
          (encT U (.run (pushC ((caller, results) :: cs) s')))
          D (fun a => D a ∨ PrivA (L.act FB s0 K G) a)) ∧
        (n ≤ ls.length → ∃ v, PRun Policy.arm L.M (OkPriv (L.act FB s0 K G)) (x, mon) (ls.take n) v ∧
          v.1 = set_program (iterN (L.act FB s0 K G).step n x) (FA.fb.program FA.base) ∧
          RealizedT env p Bnd ls n (encT U (.run (pushC ((caller, results) :: cs) s')))
            (encT U (.run ⟨{ caller with regs := regs }, cs, cm⟩))
            D (fun a => D a ∨ PrivA (L.act FB s0 K G) a)) := by
  have hret0 := hret
  obtain ⟨-, -, -, -, -, -, -, -, -, -, vals, cm, -, -, -, -, -, hdone, -⟩ := hret0
  obtain ⟨n, hn0, hRC, hmem, hrun⟩ := ret_end hL hB hRB hent hra hA hrA hret
  refine ⟨n, vals, cm, hn0, hdone, hRC, hmem, fun {caller results cs regs} hr U D {mon ls t'} hr' =>
    ⟨fun hlt => ?_, fun hle => ?_⟩⟩
  · obtain ⟨-, -, hW, hk⟩ := (hrun hr').1 hlt
    exact realizedT_priv (Nat.le_refl _) (by rw [List.take_length]; exact hW)
      (by rw [List.take_length]; exact hk) (fun x hx => absurd hx List.not_mem_nil) .nil hb D
  · obtain ⟨v, hv, hv1, -, hW, hk⟩ := (hrun hr').2 hle
    exact ⟨v, hv, hv1, realizedT_priv hle hW hk (fun x hx => by simp at hx; exact hx)
      (.cons (cstepS_ret_pop hcall hat hdone hr U) .nil) hb D⟩

end Concurrency.CallRetT

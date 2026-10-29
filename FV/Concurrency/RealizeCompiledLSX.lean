module

public import FV.Concurrency.RealizeCompiled
public import FV.Concurrency.ArmAllocLSX

@[expose] public section

/-!
# One compiled thread with the stack offsets built in `x16` (T2j, #473)

`RealizeCompiled.thread_full_of_sim` for the scope `ArmAllocThread.MemScopeLSX` (every plain
load/store at a final or stack mode, the stack offsets that `memFinalize` builds in `x16`
included):

* `coveredCode_of_lsx`: its code is covered (`ThreadProgress.CoveredCode`, from
  `ArmAllocThread.lsFormX_covered`);
* `CompiledLSX`, `CompiledLS.toLSX`: `RealizeCompiled.CompiledLS` with `MemScopeLSX`;
* **`thread_compiledLSX_full`**: the realized prefix of the thread is its whole Arm run, or a CLIF
  thread run from `cs` realizes it and stops there (`thread_compiledLS_full`'s conclusion).
-/

namespace Concurrency.RealizeCompiled

open Arm ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine ThreadProgress
  ArmAllocThread ThreadCompose

/-- **The scope with every plain load/store is covered.** -/
theorem coveredCode_of_lsx {R : RL} (h : MemScopeLSX R) : CoveredCode R := fun b vb k i hb hi =>
  (h b vb k i hb hi).elim covered_of_memFormL fun h => h.elim covered_of_brForm fun h =>
    covered_of_formOk (lsFormX_covered h).2.1

/-- `Compiled` for functions with LL/SC loops, block-ending branches and plain loads/stores at
final or stack modes (`MemScopeLSX`, layer 4b `arm_alloc_refines_lsx`). -/
structure CompiledLSX (env : Clif.Env) (p : Clif.Program) (RA : RL) (cs : Clif.State)
    (s : ArmState) : Prop where
  wf : RA.Wf
  scope : MemScopeLSX RA
  gv : RA.gv = fun _ _ => False
  front : Front env p RA cs s

theorem CompiledLS.toLSX {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    {s : ArmState} (hc : CompiledLS env p RA cs s) : CompiledLSX env p RA cs s :=
  ⟨hc.wf, memScopeLSX_of_memScopeLS hc.scope, hc.gv, hc.front⟩

/-- **One compiled thread with loops, branches and plain loads/stores at final or stack modes
(the offsets built in `x16` included), its realized prefix the whole run or ending where the
CLIF thread stops** (`thread_full_of_sim` for `MemScopeLSX`). -/
theorem thread_compiledLSX_full {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    {s : ArmState} (hc : CompiledLSX env p RA cs s) {mon : Mon} {ls : List Lab}
    {t' : ArmState × Mon} (hr : PRun Policy.arm RA.step (OkPriv RA) (s, mon) ls t') :
    ∃ (k : Nat) (trS : List (List (Ev SKind BVal))) (st : Nat → TState) (ψ : Nat × Nat → Nat × Nat),
      k ≤ ls.length ∧ st 0 = .run cs ∧
      (∀ j (h : j < trS.length), CStep env p (st j) trS[j] (st (j + 1))) ∧
      Refines Maps (PrivA RA) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p (st trS.length)) :=
  thread_full_of_sim hc.gv hc.front (itemSim_lsx hc.wf hc.scope) (coveredCode_of_lsx hc.scope) hr

end Concurrency.RealizeCompiled

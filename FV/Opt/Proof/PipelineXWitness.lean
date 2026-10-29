module

public import FV.Opt.Proof.PipelineX
public import FV.E2E.LinkClif
public import FV.Clif.Parse

@[expose] public section

/-! # Non-vacuity of `Opt.optimizeProgramExe_refines`, and why `optimizeExe` has its guard

**Witness.** `prog` has three functions: `%add3` (a duplicate computation and an unreachable
block), `%ci` (a `call_indirect` through `func_addr`, an unreachable block) and `%main` (a
`try_call_indirect` of `%ci`, then a duplicate computation and a `try_call` of `%add3`, an
unreachable block). The executable compiler's mid-end (`Opt.optimizeExe`, `Opt.exeConfig`)
changes every one of them; `Clif.run` of `%main` on `5` returns `29`
(`add3(2 * (add3(5) + 5))`), and `Opt.optimizeProgramExe_refines` gives the optimised program's
run returning `29` with the same memory (`optimizeProgramExe_witness`).

**Counterexample without the guard.** `Opt.optimize` alone does not refine every program with a
`try_call`: in `badProg`, `%bad`'s `try_call` binds its result at the function's fresh value
(`Clif.Function.freshValue`, one above every defined value: `v2`, because the unreachable
`block2` defines `v1`), and the normal-return successor `block1` reads `v2` without defining it
(ill-formed CLIF, which Cranelift's verifier rejects, but `Clif.run` gives it a meaning).
`removeUnreachable` drops `block2`, the fresh value drops to `v1`, the call's result lands in
`v1`, and `block1`'s read of `v2` is stuck. So the source run returns `8` and no run of
`Opt.optimizeProgram` does (`optimize_not_refines`). `Opt.optimizeExe` leaves `%bad` unchanged
(`freshOkB`, `FV/Opt/OptimizeX.lean`). The earlier theorems (`Opt.optimizeProgram_refines`,
`E2E.backend_correct_opt_proven`) exclude `try_call`/`try_call_indirect` (`NoCallIndirect`,
`hnt`), so this case was outside their claims.
-/

namespace Opt.PipelineXWitness

open Clif

/-- More fuel does not change a `Clif.run` that ended. -/
theorem run_add (env : Env) (p : Program) (f : String) (args : List Val) (N : Nat)
    (h : run env p f args N ≠ .outOfFuel) (k : Nat) :
    run env p f args (N + k) = run env p f args N := by
  unfold run runWith at *
  split
  · rename_i mem hm
    rw [hm] at h
    simp only at h
    split
    · rename_i s hs
      rw [hs] at h
      exact Clif.runLoop_add env p N s h k
    · rfl
    · rfl
  · rfl
  · rfl

/-- The witness program (module doc). -/
def src : String := "; data: %fv_image = 00

function %add3(i64) -> i64 system_v {
block0(v0: i64):
    v1 = iconst.i64 3
    v2 = iadd v0, v1
    v3 = iadd v0, v1
    v4 = isub v2, v3
    v5 = iadd v2, v4
    return v5
block1:
    v6 = iconst.i64 0
    return v6
}

function %ci(i64) -> i64 system_v {
    sig0 = (i64) -> i64 system_v
    fn0 = %add3(i64) -> i64 system_v
block0(v0: i64):
    v1 = func_addr.i64 fn0
    v2 = call_indirect sig0, v1(v0)
    return v2
block1:
    v3 = iconst.i64 0
    return v3
}

function %main(i64) -> i64 system_v {
    sig0 = (i64) -> i64 system_v
    fn0 = %ci(i64) -> i64 system_v
    fn1 = %add3(i64) -> i64 system_v
block0(v0: i64):
    v1 = func_addr.i64 fn0
    try_call_indirect v1(v0), sig0, block1(ret0), [ tag0: block3(exn0) ]
block1(v2: i64):
    v3 = iadd v2, v0
    v4 = iadd v2, v0
    v5 = iadd v3, v4
    try_call fn1(v5), sig0, block2(ret0), [ tag0: block3(exn0) ]
block2(v6: i64):
    return v6
block3(v7: i64):
    v8 = iconst.i64 -1
    return v8
block4:
    v9 = iconst.i64 0
    return v9
}
"

/-- The parsed witness program. -/
def prog : Program := match Clif.parse src with | .ok p => p | .error _ => default

/-- The run returns the single value `v` (any memory). -/
def retB (v : Val) (o : Outcome) : Bool :=
  match o with
  | .returned [w] _ => decide (w = v)
  | _ => false

/-- The memory of a returned outcome. -/
def retMem (o : Outcome) : Mem :=
  match o with
  | .returned _ m => m
  | _ => Mem.empty

theorem eq_of_retB {v : Val} {o : Outcome} (h : retB v o = true) : o = .returned [v] (retMem o) := by
  unfold retB at h
  split at h
  · rename_i w m
    simp only [decide_eq_true_eq] at h
    subst h
    rfl
  · cases h

/-- A `call_indirect`, a `try_call` and a `try_call_indirect`. -/
def shapeB (p : Program) : Bool :=
  p.funcs.any (fun g => g.blocks.any fun b => b.body.any fun st =>
    match st.inst with | .callIndirect .. => true | _ => false) &&
  p.funcs.any (fun g => g.blocks.any fun b => match b.term with | .tryCall .. => true | _ => false) &&
  p.funcs.any (fun g => g.blocks.any fun b =>
    match b.term with | .tryCallIndirect .. => true | _ => false)

/-- The decided facts: three functions, each changed by the mid-end; the shapes; the run. -/
def factsB : Bool :=
  decide (prog.funcs.length = 3) && prog.funcs.all (fun g => !decide (optimizeExe g exeConfig = g)) &&
  shapeB prog && retB ⟨.i64, 29#64⟩ (run {} prog "main" [⟨.i64, 5#64⟩] 100)

theorem factsB_true : factsB = true := by native_decide

theorem envKeeps : EnvKeepsSymbols ({} : Env) := fun _ _ h => by cases h

/-- **Non-vacuity of `Opt.optimizeProgramExe_refines`**: on a program with a `call_indirect`, a
`try_call` and a `try_call_indirect`, whose three functions the mid-end all changes, the source
run of `%main` on `5` returns `29` and the optimised program's run returns `29` with the same
memory. -/
theorem optimizeProgramExe_witness :
    prog.funcs.length = 3 ∧ (∀ g ∈ prog.funcs, optimizeExe g exeConfig ≠ g) ∧
    shapeB prog = true ∧
    ∃ m, run {} prog "main" [⟨.i64, 5#64⟩] 100 = .returned [⟨.i64, 29#64⟩] m ∧
      ∃ fuel', run {} (optimizeProgramExe prog exeConfig) "main" [⟨.i64, 5#64⟩] fuel' =
        .returned [⟨.i64, 29#64⟩] m := by
  have h := factsB_true
  simp only [factsB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨hl, hc⟩, hs⟩, hr⟩ := h
  have hrun := eq_of_retB hr
  obtain ⟨fuel', h1, -⟩ := optimizeProgramExe_refines exeConfig simplifyPassSimX_exe envKeeps prog
    "main" [⟨.i64, 5#64⟩] 100
  exact ⟨hl, hc, hs, _, hrun, fuel', h1 _ _ hrun⟩

/-- The counterexample program (module doc). -/
def badSrc : String := "function %add3(i64) -> i64 system_v {
block0(v0: i64):
    v1 = iconst.i64 3
    v2 = iadd v0, v1
    return v2
}

function %bad(i64) -> i64 system_v {
    sig0 = (i64) -> i64 system_v
    fn0 = %add3(i64) -> i64 system_v
block0(v0: i64):
    try_call fn0(v0), sig0, block1, [ tag0: block1 ]
block1:
    return v2
block2:
    v1 = iconst.i64 0
    return v1
}
"

/-- The parsed counterexample program. -/
def badProg : Program := match Clif.parse badSrc with | .ok p => p | .error _ => default

/-- The run is stuck. -/
def stuckB (o : Outcome) : Bool := match o with | .stuck _ => true | _ => false

/-- The decided facts: the source run of `%bad` on `5` returns `8`; the run of `optimize`'s
program is stuck; `optimizeExe` keeps `%bad` (`freshOkB` fails on it). -/
def badB : Bool :=
  retB ⟨.i64, 8#64⟩ (run {} badProg "bad" [⟨.i64, 5#64⟩] 100) &&
  stuckB (run {} (optimizeProgram badProg exeConfig) "bad" [⟨.i64, 5#64⟩] 100) &&
  badProg.funcs.any (fun g => g.name == "bad" && !freshOkB g && decide (optimizeExe g exeConfig = g))

theorem badB_true : badB = true := by native_decide

/-- **`Opt.optimize` without the fresh-value guard does not refine every program with a
`try_call`**: the source run of `%bad` on `5` returns `8`, and no run of `Opt.optimizeProgram`'s
program (with the executable compiler's configuration) returns. -/
theorem optimize_not_refines :
    ∃ m, run {} badProg "bad" [⟨.i64, 5#64⟩] 100 = .returned [⟨.i64, 8#64⟩] m ∧
      ¬ ∃ fuel', OutcomeRefines (run {} badProg "bad" [⟨.i64, 5#64⟩] 100)
        (run {} (optimizeProgram badProg exeConfig) "bad" [⟨.i64, 5#64⟩] fuel') := by
  have h := badB_true
  simp only [badB, Bool.and_eq_true] at h
  obtain ⟨⟨hr, hs⟩, -⟩ := h
  have hrun := eq_of_retB hr
  refine ⟨_, hrun, ?_⟩
  rintro ⟨fuel', h1, _⟩
  have ht := h1 _ _ hrun
  have hs' : stuckB (run {} (optimizeProgram badProg exeConfig) "bad" [⟨.i64, 5#64⟩]
      (100 + fuel')) = true := by
    rw [run_add _ _ _ _ 100 (fun he => by rw [he] at hs; cases hs)]
    exact hs
  have hne : run {} (optimizeProgram badProg exeConfig) "bad" [⟨.i64, 5#64⟩] fuel' ≠ .outOfFuel := by
    rw [ht]; exact fun h => by cases h
  rw [Nat.add_comm, run_add _ _ _ _ fuel' hne, ht] at hs'
  cases hs'

end Opt.PipelineXWitness

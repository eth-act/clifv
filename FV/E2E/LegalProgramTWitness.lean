import FV.E2E.NonVacuityLegalProgram
import FV.E2E.LegalProgXWitness
import FV.E2E.LegalProgramT
import FV.E2E.LegalProgXT

/-!
# Non-vacuity of `legalProg_refinesT` and `legalProg_refinesXT` on the old domain (#1076)

The whole-program refinements on the new source domains (`ProgCtxT`, `ProgCtxXT`) applied through
the bridges `ProgCtx.toT`/`ProgCtxX.toT` to the programs of S3's and S10f's witnesses
(`FV/E2E/NonVacuityLegalProgram.lean`, `FV/E2E/LegalProgXWitness.lean`): the same conclusions
(`add_refinesT`: a legalised `add128`; `caught_refinesXT`: an exception raised in a callee and
caught by a `try_call`'s handler). A function only in the new domain (an `i128` function with a
`try_call_indirect` raising into its handler): `Clif.Rust.LegalXTWitness.refines`
(`checkW_refinesXT`) and `E2E.I128TryIndTWitness` (`attemptT_correct_sourceTB`).
-/

namespace E2E.LegalProgram.Witness

open Clif Opt.Legal Opt.Legalize128 E2E.LinkCheck

/-- **`add128` on two `i128` values** (legalised; its arguments and result split into `i64`
halves): the source run returns the sum `2^64 + 8`; `legalProg_refinesT` (on `ProgCtx.toT`)
gives the legalised `add128`'s run on the split arguments `3, 1, 5, 0` the split sum `8, 1`. -/
theorem add_refinesT : ∃ fr fr' m1 m2 k,
    enterFunc addF [⟨.i128, 1#64 ++ 3#64⟩, ⟨.i128, 0#64 ++ 5#64⟩] Mem.empty = .ok (fr, m1) ∧
    enterFunc (legalize addF) [⟨.i64, 3#64⟩, ⟨.i64, 1#64⟩, ⟨.i64, 5#64⟩, ⟨.i64, 0#64⟩] Mem.empty =
      .ok (fr', m1) ∧
    Clif.runLoop Clif.Rust.env P 40 ⟨fr, [], m1⟩ = .returned [⟨.i128, 1#64 ++ 8#64⟩] m2 ∧
    Clif.runLoop Clif.Rust.env (legalProg P) k ⟨fr', [], m1⟩ =
      .returned [⟨.i64, 8#64⟩, ⟨.i64, 1#64⟩] m2 := by
  obtain ⟨⟨fr, m1⟩, he⟩ : ∃ r, enterFunc addF [⟨.i128, 1#64 ++ 3#64⟩, ⟨.i128, 0#64 ++ 5#64⟩]
      Mem.empty = .ok r := ⟨_, rfl⟩
  have hgs : groups addF.sig.params = some [[.lo, .hi], [.lo, .hi]] := rfl
  have hexp : ExpRel ((groups addF.sig.params).getD [])
      [⟨.i128, 1#64 ++ 3#64⟩, ⟨.i128, 0#64 ++ 5#64⟩]
      [⟨.i64, 3#64⟩, ⟨.i64, 1#64⟩, ⟨.i64, 5#64⟩, ⟨.i64, 0#64⟩] := by
    rw [hgs, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, ⟨5#64, 0#64, rfl, rfl, rfl⟩, trivial⟩
  have hh : addF ∈ P.funcs := by decide
  obtain ⟨fr', he'⟩ := enterFunc_legal (legalOk addF hh) he hexp
  obtain ⟨m2, hr⟩ := run_of_runWith (n := "add128") (by decide) he (N := 40)
    (rv := [⟨.i128, 1#64 ++ 8#64⟩]) (by decide)
  have hfacts := legalFacts (legalOk addF hh)
  have hE := EntryRel.of_enter ⟨hfacts.name, hfacts.slots⟩ he he' hexp
  obtain ⟨rv', hrel, k, hk⟩ := (legalProg_refinesT ctx.toT hh hE (good_of_run hh he hr) 40).1 _ _ hr
  have hrg : groups addF.sig.returns = some [[.lo, .hi]] := rfl
  rw [hrg, Option.getD_some] at hrel
  obtain ⟨a, b, rest, rfl, ⟨l, hh', e1, rfl, rfl⟩, hrest⟩ : ∃ a b rest, rv' = a :: b :: rest ∧
      Halves ⟨.i128, 1#64 ++ 8#64⟩ a b ∧ ExpRel [] [] rest := by
    match rv', hrel with
    | a :: b :: rest, ⟨hv, hr⟩ => exact ⟨a, b, rest, rfl, hv, hr⟩
  cases rest with
  | cons => exact absurd hrest id
  | nil =>
    obtain ⟨-, e1⟩ := Val.mk.inj e1
    have hl : l = 8#64 := by
      have := congrArg (fun x : BitVec 128 => x.extractLsb' 0 64) (eq_of_heq e1)
      have h2 : (hh' ++ l).extractLsb' 0 64 = 8#64 := by simpa using this.symm
      exact (BitVec.extractLsb'_append_eq_right (a := hh')).symm.trans h2
    have hh2 : hh' = 1#64 := by
      have := congrArg (fun x : BitVec 128 => x.extractLsb' 64 64) (eq_of_heq e1)
      have h2 : (hh' ++ l).extractLsb' 64 64 = 1#64 := by simpa using this.symm
      exact (BitVec.extractLsb'_append_eq_left (b := l)).symm.trans h2
    subst hl hh2
    exact ⟨fr, fr', m1, m2, k, he, he', hr, hk⟩


end E2E.LegalProgram.Witness

namespace E2E.LegalProgram.XWitness

open Clif Opt.Legal Opt.Legal.X Opt.Legalize128 E2E.LinkCheck Clif.Rust

/-- **`w(5)` raises in `mid` and catches**: the source run with unwinding returns, and
`legalProg_refinesXT` (on `ProgCtxX.toT`) gives the legalised program's run of the legalised `w`
on the halves `5, 0` the same return with the same memory. -/
theorem caught_refinesXT : ∃ fr fr' m1 m2 k,
    enterFunc wF [⟨.i128, 5⟩] Mem.empty = .ok (fr, m1) ∧
    enterFunc (legalize wF) [⟨.i64, 5⟩, ⟨.i64, 0⟩] Mem.empty = .ok (fr', m1) ∧
    runLoopX xe P 20 ⟨⟨fr, [], m1⟩, []⟩ = .returned [] m2 ∧
    runLoopX xe (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = .returned [] m2 := by
  have hp : P.func? "w" = some wF := by decide
  have hh : wF ∈ P.funcs := by decide
  obtain ⟨fr, m1, he, ho, hG⟩ := entry_good hp w_facts (fun x hx => by
    cases x <;> simp_all [isReturned])
  obtain ⟨m2, hr⟩ : ∃ m2, runLoopX xe P 20 ⟨⟨fr, [], m1⟩, []⟩ = .returned [] m2 := by
    revert ho
    cases runLoopX xe P 20 ⟨⟨fr, [], m1⟩, []⟩ with
    | returned v m => intro h; simp only [isReturned, List.isEmpty_iff] at h; exact ⟨m, by rw [h]⟩
    | _ => simp [isReturned]
  have hgs : groups wF.sig.params = some [[.lo, .hi]] := rfl
  have hexp : ExpRel ((groups wF.sig.params).getD []) [⟨.i128, 5⟩] [⟨.i64, 5⟩, ⟨.i64, 0⟩] := by
    rw [hgs]; exact ⟨⟨5, 0, rfl, rfl, rfl⟩, trivial⟩
  obtain ⟨fr', he'⟩ := enterFunc_legal (legalOk wF hh) he hexp
  have hfacts := legalFacts (legalOk wF hh)
  have hE := EntryRel.of_enter ⟨hfacts.name, hfacts.slots⟩ he he' hexp
  obtain ⟨rv', hrel, k, hk⟩ := (legalProg_refinesXT ctxX.toT hh hE hG 20).1 _ _ hr
  have hrg : groups wF.sig.returns = some [] := rfl
  rw [hrg, Option.getD_some] at hrel
  cases rv' with
  | cons => exact absurd hrel id
  | nil => exact ⟨fr, fr', m1, m2, k, he, he', hr, hk⟩

end E2E.LegalProgram.XWitness

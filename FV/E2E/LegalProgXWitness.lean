import FV.E2E.LegalProgX
import FV.Opt.Proof.LegalRustX
import FV.E2E.LegalSource

/-!
# Non-vacuity of `legalProg_refinesX` (S10f)

The closed program `P = {w, mid}` under the trusted Rust environment with unwinding
`Clif.Rust.xenvWith raises 77` (`%throw` raises Rust's exception, object 77):

```
function %w(i128) system_v {               function %mid(i128) system_v {
    sig0 = (i128) system_v                     fn0 = %throw(i128) system_v
    fn0 = %mid(i128) system_v              block0(v0: i128):
block0(v0: i128):                              call fn0(v0)
    try_call fn0(v0), sig0, block1,            return
        [ tag0: block2(exn0) ]             }
block1:
    return
block2(v1: i64):
    return
}
```

Both mention `i128` and are legalised (their arguments split into `i64` halves). `ctxX`: `P` is in
the source domain with unwinding (`ProgCtxX`; `legalOkB`, `exnOk` decided). The whole-program
runs with unwinding:

* `caught_refines`: `w(5)` `try_call`s `mid`, whose call of `%throw` raises; the exception leaves
  `mid` (a frame of the program left by the unwinder) and `w`'s `tag0` handler catches it, the
  run returns. `legalProg_refinesX` gives the legalised program's run of the legalised `w` on the
  halves `5, 0` the same return.
* `unwound_refines`: `mid(5)` raises; the exception leaves `mid` (`unwound`). The theorem gives
  the legalised `mid` on the halves raising the same exception with the same memory.

The source runs' good states (`GoodFromX`): no allocation on the way (`allBX`, decided), no
load/store trap (the runs end, `memTrapFree_of_runX`), no indirect call.
-/

namespace E2E.LegalProgram.XWitness

open Clif Opt.Legal Opt.Legal.X Opt.Legalize128 E2E.LinkCheck Clif.Rust

/-! ## Good states, decided along a run -/

/-- Every state the run with unwinding from `xs` passes within `N` steps satisfies `Q`, and the
run ends within `N` steps. -/
def allBX (env : XEnv) (p : Program) (Q : XState → Bool) : Nat → XState → Bool
  | 0, _ => false
  | N + 1, xs => Q xs && match stepX env p xs with
    | .next xs' => allBX env p Q N xs'
    | _ => true

theorem allBX_sound {env : XEnv} {p : Program} {Q : XState → Bool} :
    ∀ (N : Nat) (xs : XState), allBX env p Q N xs = true → ∀ u, ReachesX env p xs u → Q u = true
  | 0, _, h => by simp [allBX] at h
  | N + 1, xs, h => by
    simp only [allBX, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    intro u hu
    cases hu with
    | refl => exact h1
    | next hs hu' =>
      rw [hs] at h2
      exact allBX_sound N _ h2 u hu'

/-- A memory without allocations has no valid range. -/
theorem memBounded_of_nil {m : Mem} (h : m.allocs.isEmpty = true) : MemBounded m := by
  intro a n hv
  simp only [List.isEmpty_iff] at h
  simp [Mem.valid, h] at hv

/-! ## The program -/

def i128p : AbiParam := { ty := .i128 }
def sigP : Signature := { params := [i128p], returns := [], callConv := some .systemV }

def et : ExnTable :=
  { sig := 0, normal := { block := 1, args := [] }, items := [.tag 0 { block := 2, args := [.exn 0] }] }

/-- `w`: `try_call %mid(v0)`, a `tag0` handler. -/
def wF : Function :=
  { name := "w", sig := sigP, externs := [(0, { name := "mid", sig := sigP })],
    sigDecls := [(0, sigP)],
    blocks := [
      { id := 0, params := [(0, .i128)], term := .tryCall 0 [0] et },
      { id := 1, params := [], term := .ret [] },
      { id := 2, params := [(1, .i64)], term := .ret [] }] }

/-- `mid`: `call %throw(v0)`. -/
def midF : Function :=
  { name := "mid", sig := sigP, externs := [(0, { name := "throw", sig := sigP })],
    blocks := [
      { id := 0, params := [(0, .i128)], body := [{ results := [], inst := .call 0 [0] }],
        term := .ret [] }] }

def P : Program := { funcs := [wF, midF] }

def raises (n : String) : Bool := n == "throw"

def xe : XEnv := xenvWith raises 77

theorem legalOk : ∀ f ∈ P.funcs, legalOkB f = true := by decide

theorem legalised : mentions128 wF = true ∧ mentions128 midF = true ∧ legalize wF ≠ wF ∧
    legalize midF ≠ midF := by decide

theorem indFree_legal : ∀ g ∈ (legalProg P).funcs, indFreeB g = true := by decide

/-- The handler-edge check of both legalisations (decided). -/
def exnOkAll : Bool :=
  P.funcs.all fun f => match function128Cert f with
    | .ok (g, cert) => exnOk f g cert
    | .error _ => true

theorem exnOkAll_true : exnOkAll = true := by decide +kernel

theorem not_someInd : ¬ SomeInd (legalProg P) :=
  fun ⟨g, hg, hn⟩ => absurd (indFreeB_sound (indFree_legal g hg)) hn

/-- **`P` is in the source domain with unwinding.** -/
theorem ctxX : ProgCtxX P xe (fun _ => none) where
  ctx :=
    { ok := legalOk
      nd := by decide
      free := fun f hf => linkFreeB_sound (by revert f; decide)
      free' := fun f hf => linkFreeB_sound (by revert f; decide)
      decl := fun g hg => declSigB_sound (by revert g; decide)
      decl' := fun g hg => declSigB_sound (by revert g; decide)
      helpers := fun op => by cases op <;> decide
      base := fun _ => ⟨xenvWith_helperOk raises 77, xenvWith_extLegal raises 77,
        (xenvWith_envKeepsAllocs raises 77).bounded⟩
      ind := fun h => absurd h not_someInd }
  baseX := fun _ => ⟨xenvWith_extLegalX raises 77, xenvWith_envKeepsAllocsX raises 77,
    xenvWith_exnArityOk raises 77⟩
  indX := fun h => absurd h not_someInd
  exn := fun f hf _ g cert hc => by
    have h := exnOkAll_true
    simp only [exnOkAll, List.all_eq_true] at h
    have := h f hf
    rw [hc] at this
    exact this

/-! ## The runs -/

/-- The decided facts of an entry from the empty memory: the run's outcome within 20 steps, no
allocation on its way. -/
def runFacts (n : String) (vals : List Val) (o : XOutcome → Bool) : Bool :=
  match initState P n vals Mem.empty with
  | .ok s => o (runLoopX xe P 20 s.toX) && allBX xe P (fun u => u.s.mem.allocs.isEmpty) 20 s.toX
  | _ => false

def isReturned : XOutcome → Bool
  | .returned v _ => v.isEmpty
  | _ => false

def isUnwound77 : XOutcome → Bool
  | .unwound e _ => e.payload == [⟨.i64, 77⟩, ⟨.i64, 0⟩]
  | _ => false

theorem w_facts : runFacts "w" [⟨.i128, 5⟩] isReturned = true := by decide +kernel

theorem mid_facts : runFacts "mid" [⟨.i128, 5⟩] isUnwound77 = true := by decide +kernel

/-- The entry of a function of `P`: its frame, the decided outcome, good states. -/
theorem entry_good {n : String} {h : Function} (hp : P.func? n = some h) {vals : List Val}
    {o : XOutcome → Bool} (hf : runFacts n vals o = true)
    (hend : ∀ x, o x = true → (∀ c, x ≠ .trapped c) ∧ x ≠ .outOfFuel) :
    ∃ fr m1, enterFunc h vals Mem.empty = .ok (fr, m1) ∧
      o (runLoopX xe P 20 ⟨⟨fr, [], m1⟩, []⟩) = true ∧
      GoodFromX xe P (SomeInd (legalProg P)) (fun _ => none) ⟨⟨fr, [], m1⟩, []⟩ := by
  unfold runFacts at hf
  cases hin : initState P n vals Mem.empty with
  | ok s =>
    rw [hin] at hf
    simp only [Bool.and_eq_true] at hf
    obtain ⟨ho, ha⟩ := hf
    obtain ⟨fr, m1, he, rfl⟩ := (initState_ok_iff hp).mp hin
    refine ⟨fr, m1, he, ho, fun u hu => ⟨memBounded_of_nil (allBX_sound _ _ ha u hu),
      memTrapFree_of_runX rfl (hend _ ho).1 (hend _ ho).2 u hu, fun h => absurd h not_someInd⟩⟩
  | trap c => rw [hin] at hf; cases hf
  | stuck m => rw [hin] at hf; cases hf

/-- **`w(5)` raises in `mid` and catches**: the source run with unwinding returns, and
`legalProg_refinesX` gives the legalised program's run of the legalised `w` on the halves `5, 0`
the same return with the same memory. -/
theorem caught_refines : ∃ fr fr' m1 m2 k,
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
  obtain ⟨rv', hrel, k, hk⟩ := (legalProg_refinesX ctxX hh hE hG 20).1 _ _ hr
  have hrg : groups wF.sig.returns = some [] := rfl
  rw [hrg, Option.getD_some] at hrel
  cases rv' with
  | cons => exact absurd hrel id
  | nil => exact ⟨fr, fr', m1, m2, k, he, he', hr, hk⟩

/-- **`mid(5)` raises**: the exception leaves `mid`; `legalProg_refinesX` gives the legalised
`mid` on the halves `5, 0` raising the same exception (Rust's, object 77) with the same
memory. -/
theorem unwound_refines : ∃ fr fr' m1 e m2 k,
    enterFunc midF [⟨.i128, 5⟩] Mem.empty = .ok (fr, m1) ∧
    enterFunc (legalize midF) [⟨.i64, 5⟩, ⟨.i64, 0⟩] Mem.empty = .ok (fr', m1) ∧
    runLoopX xe P 20 ⟨⟨fr, [], m1⟩, []⟩ = .unwound e m2 ∧
    e.payload = [⟨.i64, 77⟩, ⟨.i64, 0⟩] ∧
    runLoopX xe (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = .unwound e m2 := by
  have hp : P.func? "mid" = some midF := by decide
  have hh : midF ∈ P.funcs := by decide
  obtain ⟨fr, m1, he, ho, hG⟩ := entry_good hp mid_facts (fun x hx => by
    cases x <;> simp_all [isUnwound77])
  obtain ⟨e, m2, hr, hpay⟩ : ∃ e m2, runLoopX xe P 20 ⟨⟨fr, [], m1⟩, []⟩ = .unwound e m2 ∧
      e.payload = [⟨.i64, 77⟩, ⟨.i64, 0⟩] := by
    revert ho
    cases runLoopX xe P 20 ⟨⟨fr, [], m1⟩, []⟩ with
    | unwound e m => intro h; simp only [isUnwound77, beq_iff_eq] at h; exact ⟨e, m, rfl, h⟩
    | _ => simp [isUnwound77]
  have hgs : groups midF.sig.params = some [[.lo, .hi]] := rfl
  have hexp : ExpRel ((groups midF.sig.params).getD []) [⟨.i128, 5⟩] [⟨.i64, 5⟩, ⟨.i64, 0⟩] := by
    rw [hgs]; exact ⟨⟨5, 0, rfl, rfl, rfl⟩, trivial⟩
  obtain ⟨fr', he'⟩ := enterFunc_legal (legalOk midF hh) he hexp
  have hfacts := legalFacts (legalOk midF hh)
  have hE := EntryRel.of_enter ⟨hfacts.name, hfacts.slots⟩ he he' hexp
  obtain ⟨k, hk⟩ := (legalProg_refinesX ctxX hh hE hG 20).2.2 e m2 hr
  exact ⟨fr, fr', m1, e, m2, k, he, he', hr, hpay, hk⟩

end E2E.LegalProgram.XWitness

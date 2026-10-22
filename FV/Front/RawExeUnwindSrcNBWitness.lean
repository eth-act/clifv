import FV.Front.RawExeUnwindSrcNB
import FV.Front.RawExeUnwindSrcWitness

/-!
# Non-vacuity of the memory bound of runs with unwinding (A2/B1, S10f)

The bound `∀ u, ReachesX … → MemBounded u.s.mem` that `raw_legal_unwind` takes, derived by
`E2E.SrcBoundedX` instead of decided along the run, on the program `P = {w, mid}` of
`E2E.LegalProgram.XWitness` (`w` `try_call`s `mid`, whose call of `%throw` raises Rust's exception):

* `slotless_w`: `srcBoundedX_slotless` on `w(5)`'s run (raise in `mid`, caught by `w`'s
  `try_call`, return);
* `raw_caught_nb`, `raw_unwound_nb`: `Front.raw_legal_unwind` on `w(5)` and `mid(5)` with that
  derived bound (`RawExeUnwindSrcWitness.raw_caught`/`raw_unwound` decide it);
* `placed_w`: `srcBoundedX_placed` on `w(5)`'s run with the slot-placement oracle set (the
  activation of `mid` is placed by it, then left by the exception), under an environment whose
  only extern `%throw` raises.
-/

namespace Front.RawExeUnwindSrcNBWitness
set_option autoImplicit false

open Clif E2E E2E.LegalProgram E2E.LegalProgram.XWitness Opt.Legal Opt.Legal.X Opt.Legalize128
  E2E.SrcBoundedX Front.RawExeUnwindSrcWitness Clif.Rust

theorem xinv_of_entry {Q : Program} {f : Function} {args : List Val} {cs : State}
    (hf : f ∈ Q.funcs) (hcs : ClifEntry f args cs) : XInv Q cs.toX := by
  have hL : LInv Q cs := by
    obtain ⟨b, hb, h2, h3, -, -⟩ := hcs.entry
    refine ⟨⟨by rw [hcs.func]; exact hf, .inl ⟨b, by rw [hcs.func]; exact entry_mem hb, ?_, ?_⟩⟩,
      fun c hc => by rw [hcs.callers] at hc; cases hc⟩
    · rw [h2]; exact List.suffix_refl _
    · rw [h3]
  exact ⟨hL, by simp [XState.Aligned, State.toX, hcs.callers]⟩

theorem slots_nil : ∀ g ∈ P.funcs, g.slots = [] := by decide

/-- The entry of `h` on `5 : i128` from the empty memory allocates nothing (decided). -/
def entryNil (h : Function) : Bool :=
  match enterFunc h [⟨.i128, 5⟩] Mem.empty with
  | .ok (_, m) => m.allocs.isEmpty
  | _ => false

theorem w_nil : entryNil wF = true := by decide +kernel

theorem mid_nil : entryNil midF = true := by decide +kernel

/-- `RawExeUnwindSrcWitness.entryPair` with the bound derived by `srcBoundedX_slotless`. -/
theorem entryPairNB {h : Function} (hp : P.func? h.name = some h) (hs : h.sig = sigP)
    {o : XOutcome → Bool} (hf : runFacts h.name [⟨.i128, 5⟩] o = true)
    (hend : ∀ x, o x = true → (∀ c, x ≠ .trapped c) ∧ x ≠ .outOfFuel)
    (hnil : entryNil h = true) :
    ∃ cs cs', ClifEntry h [⟨.i128, 5⟩] cs ∧
      ClifEntry (legalize (h.rename Ren.id.fwd)) [⟨.i64, 5⟩, ⟨.i64, 0⟩] cs' ∧
      ExpRel ((groups h.sig.params).getD []) [⟨.i128, 5⟩] [⟨.i64, 5⟩, ⟨.i64, 0⟩] ∧
      cs'.frame.slots = cs.frame.slots ∧ cs'.mem = cs.mem.ren Ren.id ∧
      o (runLoopX xe P 20 cs.toX) = true ∧ (∀ u, ReachesX xe P cs.toX u → MemBounded u.s.mem) := by
  have hh := (Program.func?_some hp).1
  obtain ⟨fr, m1, he, ho, -⟩ := entry_good hp hf hend
  have hgs : groups h.sig.params = some [[.lo, .hi]] := by rw [hs]; rfl
  have hexp : ExpRel ((groups h.sig.params).getD []) [⟨.i128, 5⟩] [⟨.i64, 5⟩, ⟨.i64, 0⟩] := by
    rw [hgs]; exact ⟨⟨5, 0, rfl, rfl, rfl⟩, trivial⟩
  obtain ⟨fr', he'⟩ := enterFunc_legal (legalOk h hh) he hexp
  have hfacts := legalFacts (legalOk h hh)
  have hE := EntryRel.of_enter ⟨hfacts.name, hfacts.slots⟩ he he' hexp
  have hp' : (legalProg P).func? (legalize h).name = some (legalize h) := by
    rw [hfacts.name]; exact ctxX.ctx.func?_some hp
  have hcs := clifEntry_initState hp ((initState_ok_iff hp).mpr ⟨fr, m1, he, rfl⟩)
  have hm1 : m1.allocs.isEmpty = true := by
    unfold entryNil at hnil
    rw [he] at hnil
    exact hnil
  have hb : ∀ u, ReachesX xe P (⟨fr, [], m1⟩ : State).toX u → MemBounded u.s.mem :=
    srcBoundedX_slotless ctxX.ctx.free (xenvWith_envKeepsAllocs raises 77).bounded
      (xenvWith_envKeepsAllocsX raises 77).bounded (xinv_of_entry hh hcs) (memBounded_of_nil hm1)
      fun _ xs1 _ hIt hs _ _ => slots_nil _ (stepX_next_xinv ctxX.ctx.free hIt hs).1.1.1
  refine ⟨⟨fr, [], m1⟩, ⟨fr', [], m1⟩, hcs, ?_, hexp, hE.slots, (mem_ren_id m1).symm, ho, hb⟩
  rw [rename_idf]
  exact clifEntry_initState hp' ((initState_ok_iff hp').mpr ⟨fr', m1, he', rfl⟩)

/-- **`srcBoundedX_slotless` on `w(5)`**: the run raises in `mid`, catches at `w`'s `try_call`
and returns; every state it reaches has bounded memory. -/
theorem slotless_w : ∃ cs m2, ClifEntry wF [⟨.i128, 5⟩] cs ∧
    runLoopX xe P 20 cs.toX = .returned [] m2 ∧
    ∀ u, ReachesX xe P cs.toX u → MemBounded u.s.mem := by
  have hp : P.func? wF.name = some wF := by decide
  obtain ⟨cs, -, hcs, -, -, -, -, ho, hb⟩ := entryPairNB hp rfl w_facts
    (fun x hx => by cases x <;> simp_all [isReturned]) w_nil
  obtain ⟨m2, hr⟩ : ∃ m2, runLoopX xe P 20 cs.toX = .returned [] m2 := by
    revert ho
    cases runLoopX xe P 20 cs.toX with
    | returned v m => intro h; simp only [isReturned, List.isEmpty_iff] at h; exact ⟨m, by rw [h]⟩
    | _ => simp [isReturned]
  exact ⟨cs, m2, hcs, hr, hb⟩

/-- **`raw_legal_unwind` on `w(5)` with the derived bound**: the source run raises in `mid`,
catches and returns; the legalised program's run of the legalised `w` on the halves returns the
same with the same memory. -/
theorem raw_caught_nb : ∃ cs cs' m2 k, ClifEntry wF [⟨.i128, 5⟩] cs ∧
    ClifEntry (legalize wF) [⟨.i64, 5⟩, ⟨.i64, 0⟩] cs' ∧
    runLoopX xe P 20 cs.toX = .returned [] m2 ∧
    runLoopX xe (legalProg P) k cs'.toX = .returned [] m2 := by
  have hp : P.func? wF.name = some wF := by decide
  obtain ⟨cs, cs', hcs, hcs', hexp, hsl, hmem, ho, hb⟩ := entryPairNB hp rfl w_facts
    (fun x hx => by cases x <;> simp_all [isReturned]) w_nil
  obtain ⟨m2, hr⟩ : ∃ m2, runLoopX xe P 20 cs.toX = .returned [] m2 := by
    revert ho
    cases runLoopX xe P 20 cs.toX with
    | returned v m => intro h; simp only [isReturned, List.isEmpty_iff] at h; exact ⟨m, by rw [h]⟩
    | _ => simp [isReturned]
  obtain ⟨rv', hrel, k, hk⟩ := (raw_legal_unwind ctxId hp hcs hcs' hexp hsl hmem
    (fun h => hsymId h cs') hb).1 20 [] m2 hr
  have hrg : groups wF.sig.returns = some [] := rfl
  rw [hrg, Option.getD_some] at hrel
  rw [xenv_ren_id, prog_rename_id, mem_ren_id] at hk
  rw [rename_idf] at hcs'
  cases rv' with
  | cons => exact absurd hrel id
  | nil => exact ⟨cs, cs', m2, k, hcs, hcs', hr, hk⟩

/-- **`raw_legal_unwind` on `mid(5)` with the derived bound**: the exception (object 77) leaves
`mid`; the legalised `mid` on the halves raises it with the same memory. -/
theorem raw_unwound_nb : ∃ cs cs' e m2 k, ClifEntry midF [⟨.i128, 5⟩] cs ∧
    ClifEntry (legalize midF) [⟨.i64, 5⟩, ⟨.i64, 0⟩] cs' ∧
    runLoopX xe P 20 cs.toX = .unwound e m2 ∧ e.payload = [⟨.i64, 77⟩, ⟨.i64, 0⟩] ∧
    runLoopX xe (legalProg P) k cs'.toX = .unwound e m2 := by
  have hp : P.func? midF.name = some midF := by decide
  obtain ⟨cs, cs', hcs, hcs', hexp, hsl, hmem, ho, hb⟩ := entryPairNB hp rfl mid_facts
    (fun x hx => by cases x <;> simp_all [isUnwound77]) mid_nil
  obtain ⟨e, m2, hr, hpay⟩ : ∃ e m2, runLoopX xe P 20 cs.toX = .unwound e m2 ∧
      e.payload = [⟨.i64, 77⟩, ⟨.i64, 0⟩] := by
    revert ho
    cases runLoopX xe P 20 cs.toX with
    | unwound e m => intro h; simp only [isUnwound77, beq_iff_eq] at h; exact ⟨e, m, rfl, h⟩
    | _ => simp [isUnwound77]
  obtain ⟨k, hk⟩ := (raw_legal_unwind ctxId hp hcs hcs' hexp hsl hmem
    (fun h => hsymId h cs') hb).2.2 20 e m2 hr
  rw [xenv_ren_id, prog_rename_id, mem_ren_id] at hk
  rw [rename_idf] at hcs'
  exact ⟨cs, cs', e, m2, k, hcs, hcs', hr, hpay, hk⟩

/-! ## Placed slots -/

/-- An environment whose only extern `%throw` raises Rust's exception, the memory unchanged. -/
def xeU : XEnv where
  extern n := if n == "throw" then some fun _ m => .unwound (Clif.Rust.panicExn 77) m else none

theorem xeU_unwound {n : String} {g : List Val → Mem → XOutcome} (hg : xeU.extern n = some g)
    {vals : List Val} {m : Mem} {e : Exn} {m' : Mem} (hu : g vals m = .unwound e m') : m' = m := by
  simp only [xeU] at hg
  split at hg
  · cases hg
    simp only [XOutcome.unwound.injEq] at hu
    exact hu.2.symm
  · cases hg

theorem xeU_noReturn {n : String} {g : List Val → Mem → Outcome} (hg : xeU.toEnv.extern n = some g)
    {vals : List Val} {m : Mem} {rv : List Val} {m' : Mem} (hr : g vals m = .returned rv m') :
    False := by
  simp only [XEnv.toEnv, xeU, Option.map_eq_some_iff] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  split at hg0
  · cases hg0; simp [XOutcome.toOutcome] at hr
  · cases hg0

/-- The oracle's frames: every function drops an empty frame with its slots at offset 0. -/
def frO : String → Option (Nat × (SlotId → Nat)) := fun _ => some (0, fun _ => 0)

/-- `w`'s entry state on `5 : i128` from the empty memory, with the oracle at stack pointer
`0x8000`. -/
def placeB : Bool :=
  match initState P "w" [⟨.i128, 5⟩] Mem.empty with
  | .ok s => s.mem.allocs.isEmpty &&
      isReturned (runLoopX xeU P 20 { s with mem := { s.mem with place := some ⟨[0x8000], frO⟩ } }.toX)
  | _ => false

theorem placeB_true : placeB = true := by decide +kernel

/-- **`srcBoundedX_placed` on `w(5)` with the oracle**: the run enters `mid` (its activation
placed by the oracle), raises there, catches at `w`'s `try_call` and returns; every state it
reaches has bounded memory. -/
theorem placed_w : ∃ cs m2, ClifEntry wF [⟨.i128, 5⟩] cs ∧ cs.mem.place ≠ none ∧
    runLoopX xeU P 20 cs.toX = .returned [] m2 ∧
    ∀ u, ReachesX xeU P cs.toX u → MemBounded u.s.mem := by
  have hp : P.func? wF.name = some wF := by decide
  have h := placeB_true
  unfold placeB at h
  cases hin : initState P "w" [⟨.i128, 5⟩] Mem.empty with
  | ok s =>
    rw [hin] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hal, ho⟩ := h
    have hs0 := clifEntry_initState hp hin
    let cs : State := { s with mem := { s.mem with place := some ⟨[0x8000], frO⟩ } }
    have hcs : ClifEntry wF [⟨.i128, 5⟩] cs :=
      ⟨hs0.callers, hs0.func, hs0.sig, hs0.entry, hs0.slotIds⟩
    obtain ⟨m2, hr⟩ : ∃ m2, runLoopX xeU P 20 cs.toX = .returned [] m2 := by
      revert ho
      cases runLoopX xeU P 20 cs.toX with
      | returned v m => intro h; simp only [isReturned, List.isEmpty_iff] at h; exact ⟨m, by rw [h]⟩
      | _ => simp [isReturned]
    refine ⟨cs, m2, hcs, by simp [cs], hr, ?_⟩
    refine srcBoundedX_placed ctxX.ctx.free (fun n g hg _ _ _ _ hret => (xeU_noReturn hg hret).elim)
      (fun n g hg vals m e m' hu => by rw [xeU_unwound hg hu])
      (fun n g hg _ _ _ _ hret _ => (xeU_noReturn hg hret).elim)
      (fun n g hg vals m e m' hu hM => by rw [xeU_unwound hg hu]; exact hM)
      (fun _ _ => 0) (fun _ => True) frO (xinv_of_entry (Program.func?_some hp).1 hcs)
      (memBounded_of_nil hal) (by simp [State.toX, hcs.callers])
      (c := 0x8000) (sps := []) rfl (Nat.zero_le _) trivial ?_
    intro t xs1 _ hIt _ hs _ _
    refine ⟨0, fun _ => 0, rfl, fun p hp => ?_, Nat.le_refl _, trivial⟩
    rw [slots_nil _ (stepX_next_xinv ctxX.ctx.free hIt hs).1.1.1] at hp
    cases hp
  | trap c => rw [hin] at h; cases h
  | stuck m => rw [hin] at h; cases h

end Front.RawExeUnwindSrcNBWitness

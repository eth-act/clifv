import FV.Front.RawExeUnwindSrc
import FV.E2E.LegalProgXWitness

/-!
# Non-vacuity of `Front.raw_legal_unwind` (S10f)

`Front.raw_legal_unwind` (the CLIF half of `bundle_correct_raw_unwind_src`: cg_clif's run with
unwinding matched by the legalised program under the linked names) instantiated at the program
`P = {w, mid}` of `E2E.LegalProgram.XWitness` (both functions mention `i128`; `w` `try_call`s
`mid`, whose call of `%throw` raises Rust's exception) as cg_clif's program, its names kept
(`Ren.id`; renaming invariance itself: `Front.RenameRunXWitness.renamed_unwinds`), under
`Clif.Rust.xenvWith`, from the entries of `w` and `mid` on `5 : i128` and of their legalisations on
the halves `5, 0`:

* `raw_caught`: `w`'s run raises in `mid`, catches and returns; the theorem gives the legalised
  program's run the same return;
* `raw_unwound`: `mid`'s run raises; the theorem gives the legalised program's run the same
  exception (object 77) with the same memory.
-/

namespace Front.RawExeUnwindSrcWitness

open Clif E2E E2E.LegalProgram E2E.LegalProgram.XWitness Opt.Legal Opt.Legal.X Opt.Legalize128

theorem mem_ren_id (m : Mem) : m.ren Ren.id = m := by
  obtain ⟨b, a, s, p, pl⟩ := m
  cases pl <;> rfl

theorem rename_idf (f : Function) : f.rename Ren.id.fwd = f := Front.Function.rename_id' f

theorem xoutcome_ren_id (o : XOutcome) : o.ren Ren.id = o := by
  cases o <;> simp [XOutcome.ren, mem_ren_id]

theorem xenv_ren_id (E : XEnv) : E.ren Ren.id = E := by
  obtain ⟨ext, names, sigOf⟩ := E
  simp only [XEnv.ren, XEnv.mk.injEq]
  refine ⟨?_, ?_, rfl⟩
  · funext n
    change Option.map (fun h vals m => XOutcome.ren Ren.id (h vals (Mem.ren Ren.id.symm m)))
      (ext n) = ext n
    cases ext n with
    | none => rfl
    | some g =>
      simp only [Option.map_some, Option.some.injEq]
      funext vals m
      rw [show Ren.id.symm = Ren.id from rfl, mem_ren_id, xoutcome_ren_id]
  · exact List.map_id' names

theorem prog_rename_id : P.rename Ren.id.fwd = P := by
  simp only [Program.rename, P, Ren.id, List.map_nil, List.map_cons, Front.Function.rename_id']

theorem ctxId : ProgCtxX (P.rename Ren.id.fwd) (xe.ren Ren.id) (fun _ => none) := by
  rw [prog_rename_id, xenv_ren_id]; exact ctxX

/-- The entries of a function `h` of `P` on `5 : i128` (from the empty memory) and of its
legalisation on the halves, with the decided facts of `h`'s run. -/
theorem entryPair {h : Function} (hp : P.func? h.name = some h) (hs : h.sig = sigP)
    {o : XOutcome → Bool} (hf : runFacts h.name [⟨.i128, 5⟩] o = true)
    (hend : ∀ x, o x = true → (∀ c, x ≠ .trapped c) ∧ x ≠ .outOfFuel) :
    ∃ cs cs', ClifEntry h [⟨.i128, 5⟩] cs ∧
      ClifEntry (legalize (h.rename Ren.id.fwd)) [⟨.i64, 5⟩, ⟨.i64, 0⟩] cs' ∧
      ExpRel ((groups h.sig.params).getD []) [⟨.i128, 5⟩] [⟨.i64, 5⟩, ⟨.i64, 0⟩] ∧
      cs'.frame.slots = cs.frame.slots ∧ cs'.mem = cs.mem.ren Ren.id ∧
      o (runLoopX xe P 20 cs.toX) = true ∧ (∀ u, ReachesX xe P cs.toX u → MemBounded u.s.mem) := by
  have hh := (Program.func?_some hp).1
  obtain ⟨fr, m1, he, ho, hG⟩ := entry_good hp hf hend
  have hgs : groups h.sig.params = some [[.lo, .hi]] := by rw [hs]; rfl
  have hexp : ExpRel ((groups h.sig.params).getD []) [⟨.i128, 5⟩] [⟨.i64, 5⟩, ⟨.i64, 0⟩] := by
    rw [hgs]; exact ⟨⟨5, 0, rfl, rfl, rfl⟩, trivial⟩
  obtain ⟨fr', he'⟩ := enterFunc_legal (legalOk h hh) he hexp
  have hfacts := legalFacts (legalOk h hh)
  have hE := EntryRel.of_enter ⟨hfacts.name, hfacts.slots⟩ he he' hexp
  have hp' : (legalProg P).func? (legalize h).name = some (legalize h) := by
    rw [hfacts.name]; exact ctxX.ctx.func?_some hp
  refine ⟨⟨fr, [], m1⟩, ⟨fr', [], m1⟩,
    clifEntry_initState hp ((initState_ok_iff hp).mpr ⟨fr, m1, he, rfl⟩), ?_, hexp, hE.slots,
    (mem_ren_id m1).symm, ho, fun u hu => (hG u hu).1⟩
  rw [rename_idf]
  exact clifEntry_initState hp' ((initState_ok_iff hp').mpr ⟨fr', m1, he', rfl⟩)

theorem hsymId : SomeInd (legalProg (P.rename Ren.id.fwd)) → ∀ cs' : State,
    cs'.mem.symbols = (fun _ => none) := by
  rw [prog_rename_id]; exact fun h => absurd h not_someInd

/-- **`raw_legal_unwind` on `w(5)`, which raises in `mid` and catches**: the source run with
unwinding returns, and the theorem gives the legalised program's run of the legalised `w` on the
halves the same return with the same memory. -/
theorem raw_caught : ∃ cs cs' m2 k, ClifEntry wF [⟨.i128, 5⟩] cs ∧
    ClifEntry (legalize wF) [⟨.i64, 5⟩, ⟨.i64, 0⟩] cs' ∧
    runLoopX xe P 20 cs.toX = .returned [] m2 ∧
    runLoopX xe (legalProg P) k cs'.toX = .returned [] m2 := by
  have hp : P.func? wF.name = some wF := by decide
  obtain ⟨cs, cs', hcs, hcs', hexp, hsl, hmem, ho, hb⟩ := entryPair hp rfl w_facts
    (fun x hx => by cases x <;> simp_all [isReturned])
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

/-- **`raw_legal_unwind` on `mid(5)`, which raises**: the exception (Rust's, object 77) leaves
`mid`; the theorem gives the legalised `mid` on the halves raising it with the same memory. -/
theorem raw_unwound : ∃ cs cs' e m2 k, ClifEntry midF [⟨.i128, 5⟩] cs ∧
    ClifEntry (legalize midF) [⟨.i64, 5⟩, ⟨.i64, 0⟩] cs' ∧
    runLoopX xe P 20 cs.toX = .unwound e m2 ∧ e.payload = [⟨.i64, 77⟩, ⟨.i64, 0⟩] ∧
    runLoopX xe (legalProg P) k cs'.toX = .unwound e m2 := by
  have hp : P.func? midF.name = some midF := by decide
  obtain ⟨cs, cs', hcs, hcs', hexp, hsl, hmem, ho, hb⟩ := entryPair hp rfl mid_facts
    (fun x hx => by cases x <;> simp_all [isUnwound77])
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

end Front.RawExeUnwindSrcWitness

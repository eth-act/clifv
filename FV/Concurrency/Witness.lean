import FV.Concurrency.Interleave

/-!
# Non-vacuity witnesses for the memory-model theorems (T2, #38)

Two concrete Arm executions of compiled code that satisfy every premise of the theorems of
`FV/Concurrency/{Armv8,ClifMM,Mapping,Interleave}.lean`:

* `incX`: two threads `atomic_rmw add` the same location after an initialising `atomic_store`.
  Thread 2's first LL/SC iteration fails: its `ldaxr` (event 3) read the initial value, thread 1's
  update came in between, and the `stlxr` failed. Event 3 is an extra Arm event, not a CLIF event
  (`S`). Every premise is decided by the kernel (`decide`); the acyclicity axioms by ranks.
* `mp`: message passing with plain data and an atomic flag: `str x; stlr y || ldar y; ldr x`, the
  reader seeing the flag and the data. The data accesses are non-atomic and ordered by `hb`, so
  `RaceFree` holds non-trivially.
-/

namespace Concurrency.Witness

-- the decided goals are disjunctions over a few events; instance synthesis needs more room
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

open Rel

/-! ## Two atomic increments with a failed LL/SC iteration -/

/-- Events: 0 `stlr` (init, thread 0); thread 1: 1 `ldaxr`, 2 `stlxr`; thread 2: 3 `ldaxr`
(failed iteration), 4 `ldaxr`, 5 `stlxr`. -/
abbrev incX : Exec (Fin 6) where
  tid e := ([0, 1, 1, 2, 2, 2] : List Nat).getD e.val 0
  dir e := ([.W, .R, .W, .R, .R, .W] : List Dir).getD e.val .F
  loc _ := 0
  po a b := (a.val, b.val) ∈ [(1, 2), (3, 4), (3, 5), (4, 5)]
  rf a b := (a.val, b.val) ∈ [(0, 1), (0, 3), (2, 4)]
  co a b := (a.val, b.val) ∈ [(0, 2), (0, 5), (2, 5)]
  rmw a b := (a.val, b.val) ∈ [(1, 2), (4, 5)]

/-- The Arm kinds. -/
abbrev incAK (e : Fin 6) : AKind :=
  ([.relW, .acqXR, .relXW, .acqXR, .acqXR, .relXW] : List AKind).getD e.val .dmb

/-- The CLIF events: all but the failed iteration's read. -/
abbrev incS (e : Fin 6) : Prop := e.val ≠ 3

/-- The CLIF kinds (event 3's is irrelevant). -/
abbrev incSK (e : Fin 6) : SKind :=
  ([.scW, .scR, .scW, .scR, .scR, .scW] : List SKind).getD e.val .fence

/-- The interleaving rank (`0, 1, 3, 2, 4, 5`). -/
abbrev incRank (e : Fin 6) : Nat := ([0, 1, 3, 2, 4, 5] : List Nat).getD e.val 0

theorem incX_wf : incX.Wf := by
  constructor <;> decide

theorem incX_kind : Armv8.KindOk incX incAK := by
  unfold Armv8.KindOk AKind.dir; decide

theorem incX_consistent : Armv8.Consistent incX incAK where
  internal := by
    refine acyclic_of_rank incRank ?_
    simp only [union, Exec.poLoc, Exec.com, Exec.fr]
    decide
  atomic := by
    simp only [Exec.ext, Exec.fr]
    decide
  external := by
    refine acyclic_of_rank incRank ?_
    simp only [Armv8.ob, Armv8.obs, Armv8.bob, Armv8.A, Armv8.L, Exec.ext, Exec.fr]
    decide

theorem incX_compiled : Mapping.Compiled incX incAK incS incSK where
  maps := by decide
  rf_src := by decide

theorem incX_raceFree : ClifMM.RaceFree (incX.restrict incS) (Mapping.srcKind incSK incS) := by
  have hat : ∀ e : Fin 6, e.val ≠ 3 → incSK e = .scR ∨ incSK e = .scW := by decide
  intro a b _ hn
  exact absurd ⟨hat a.1 a.2, hat b.1 b.2⟩ hn

/-- The CLIF events of `incX`, listed. -/
def incEvs : List {e : Fin 6 // incS e} :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩]

theorem incEvs_all : ∀ e, e ∈ incEvs := by
  rintro ⟨e, he⟩
  have : ∀ e : Fin 6, ∀ he : incS e, (⟨e, he⟩ : {e // incS e}) ∈ incEvs := by decide
  exact this e he

/-- **Non-vacuity of theorems 1–5** (`Armv8.atomics_sc`, `Mapping.armv8_to_clif`, `ClifMM.drf_sc`,
`Mapping.armv8_drf_sc`, `Mapping.armv8_interleaving`): every premise holds for `incX`, an
execution with an atomic-update pair on each thread and an extra (failed-iteration) Arm event. -/
theorem incX_premises :
    incX.Wf ∧ Armv8.KindOk incX incAK ∧ Armv8.Consistent incX incAK ∧
      Mapping.Compiled incX incAK incS incSK ∧
      ClifMM.RaceFree (incX.restrict incS) (Mapping.srcKind incSK incS) ∧
      ∀ e, e ∈ incEvs :=
  ⟨incX_wf, incX_kind, incX_consistent, incX_compiled, incX_raceFree, incEvs_all⟩

/-- The conclusions on `incX`. -/
theorem incX_conclusions :
    Acyclic (restr (fun e => Armv8.A incAK e ∨ Armv8.L incAK e) (union incX.po incX.com)) ∧
      ClifMM.Consistent (incX.restrict incS) (Mapping.srcKind incSK incS) ∧
      (incX.restrict incS).SC :=
  ⟨Armv8.atomics_sc incX_wf incX_consistent,
    Mapping.armv8_to_clif incX_wf incX_consistent incX_compiled,
    Mapping.armv8_drf_sc incX_wf incX_consistent incX_compiled incX_raceFree⟩

/-- The interleaving of `incX`'s CLIF events (theorem 5 on the witness). -/
theorem incX_interleaving : ∃ rank : {e : Fin 6 // incS e} → Nat,
    (∀ a b, union (incX.restrict incS).po (incX.restrict incS).com a b → rank a < rank b) ∧
    (∀ w r, (incX.restrict incS).rf w r → ∀ w', (incX.restrict incS).dir w' = .W →
      (incX.restrict incS).loc w' = (incX.restrict incS).loc r → w' ≠ w →
      rank w' < rank w ∨ rank r < rank w') ∧
    (∀ r w, (incX.restrict incS).rmw r w → ∀ w', (incX.restrict incS).dir w' = .W →
      (incX.restrict incS).loc w' = (incX.restrict incS).loc r → w' ≠ w →
      rank w' < rank r ∨ rank w < rank w') :=
  Mapping.armv8_interleaving incX_wf incX_consistent incX_compiled incX_raceFree incEvs incEvs_all

/-! ## Message passing with plain data -/

/-- Events: thread 1: 0 `str x`, 1 `stlr y`; thread 2: 2 `ldar y` (reads 1), 3 `ldr x`
(reads 0). `x` is location 0, `y` location 1. -/
abbrev mp : Exec (Fin 4) where
  tid e := ([1, 1, 2, 2] : List Nat).getD e.val 0
  dir e := ([.W, .W, .R, .R] : List Dir).getD e.val .F
  loc e := ([0, 1, 1, 0] : List Nat).getD e.val 0
  po a b := (a.val, b.val) ∈ [(0, 1), (2, 3)]
  rf a b := (a.val, b.val) ∈ [(1, 2), (0, 3)]
  co _ _ := False
  rmw _ _ := False

abbrev mpAK (e : Fin 4) : AKind := ([.plainW, .relW, .acqR, .plainR] : List AKind).getD e.val .dmb

abbrev mpSK (e : Fin 4) : SKind := ([.naW, .scW, .scR, .naR] : List SKind).getD e.val .fence

abbrev mpS (_ : Fin 4) : Prop := True

theorem mp_wf : mp.Wf := by
  constructor <;> decide

theorem mp_kind : Armv8.KindOk mp mpAK := by
  unfold Armv8.KindOk AKind.dir; decide

theorem mp_consistent : Armv8.Consistent mp mpAK where
  internal := by
    refine acyclic_of_rank (fun e => e.val) ?_
    simp only [union, Exec.poLoc, Exec.com, Exec.fr]
    decide
  atomic := by
    simp only [Exec.ext, Exec.fr]
    decide
  external := by
    refine acyclic_of_rank (fun e => e.val) ?_
    simp only [Armv8.ob, Armv8.obs, Armv8.bob, Armv8.A, Armv8.L, Exec.ext, Exec.fr]
    decide

theorem mp_compiled : Mapping.Compiled mp mpAK mpS mpSK where
  maps := by decide
  rf_src := by decide

/-- The data accesses are ordered by `hb`: `str x` `po` `stlr y` `sw` `ldar y` `po` `ldr x`. -/
theorem mp_raceFree : ClifMM.RaceFree (mp.restrict mpS) (Mapping.srcKind mpSK mpS) := by
  have hpairs : ∀ a b : Fin 4, a ≠ b → mp.loc a = mp.loc b → mp.dir a ≠ .F → mp.dir b ≠ .F →
      (mp.dir a = .W ∨ mp.dir b = .W) →
      ¬ ((mpSK a = .scR ∨ mpSK a = .scW) ∧ (mpSK b = .scR ∨ mpSK b = .scW)) →
      (a.val = 0 ∧ b.val = 3) ∨ (a.val = 3 ∧ b.val = 0) := by decide
  have p01 : (mp.restrict mpS).po ⟨0, trivial⟩ ⟨1, trivial⟩ := show mp.po 0 1 by decide
  have p23 : (mp.restrict mpS).po ⟨2, trivial⟩ ⟨3, trivial⟩ := show mp.po 2 3 by decide
  have s12 : ClifMM.sw (mp.restrict mpS) (Mapping.srcKind mpSK mpS) ⟨1, trivial⟩ ⟨2, trivial⟩ :=
    ⟨show mpSK 1 = .scW by decide, show mp.rf 1 2 by decide, show mpSK 2 = .scR by decide⟩
  have hb03 : ClifMM.hb (mp.restrict mpS) (Mapping.srcKind mpSK mpS) ⟨0, trivial⟩ ⟨3, trivial⟩ :=
    .tail (.tail (.single (.inl p01)) (.inr s12)) (.inl p23)
  rintro ⟨a, ⟨⟩⟩ ⟨b, ⟨⟩⟩ ⟨hne, hl, ha, hb, hw⟩ hn
  have hne' : a ≠ b := fun h => hne (by subst h; rfl)
  rcases hpairs a b hne' hl ha hb hw hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : a = 0 := Fin.ext h1
    have e2 : b = 3 := Fin.ext h2
    subst e1 e2; exact .inl hb03
  · have e1 : a = 3 := Fin.ext h1
    have e2 : b = 0 := Fin.ext h2
    subst e1 e2; exact .inr hb03

/-- **Non-vacuity with non-atomic accesses**: `mp` satisfies the premises of `armv8_drf_sc`
with a race-freedom that needs `hb` (release/acquire synchronisation). -/
theorem mp_premises :
    mp.Wf ∧ Armv8.KindOk mp mpAK ∧ Armv8.Consistent mp mpAK ∧
      Mapping.Compiled mp mpAK mpS mpSK ∧
      ClifMM.RaceFree (mp.restrict mpS) (Mapping.srcKind mpSK mpS) :=
  ⟨mp_wf, mp_kind, mp_consistent, mp_compiled, mp_raceFree⟩

theorem mp_sc : (mp.restrict mpS).SC :=
  Mapping.armv8_drf_sc mp_wf mp_consistent mp_compiled mp_raceFree

end Concurrency.Witness

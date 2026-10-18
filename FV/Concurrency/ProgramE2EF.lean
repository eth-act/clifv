import FV.Concurrency.ProgramE2E
import FV.Concurrency.ArmFence

/-!
# The program-level statement with fences and Rust orderings (T2f, #304)

`ProgE2E.program_correct` assumes race-freedom in every execution consistent for the contract of
`ClifMM.lean`, which gives `fence` no meaning. Rust's race-freedom (RC11 with every ordering) does
not imply it: store buffering with SC fences is contract-consistent but not RC11-consistent
(`Witness.sbf_*`). With Cranelift's documented fence semantics (`ClifMM.ConsistentF`) the chain
closes:

* `consistentCF`: the CLIF execution of an Armv8-consistent execution of Arm threads realizing it
  satisfies `ConsistentF` (`Mapping.Hom.psc_acyclic` along the embedding `φ`, which preserves
  program order between the CLIF events: positions without events are bypassed);
* `program_correctF`: `program_correct` with race-freedom only in every `ConsistentF` execution
  whose atomic updates are its two-event steps (`RaceFreeProgF`);
* `raceFreeProgF_of_rust`: race-freedom of the Rust program (its executions with the Rust
  orderings, `RustRaceFree`, RC11 without no-thin-air = C++20) implies it (`RC11.strength_sound`,
  `RC11.hb_strength`); `program_correct_rust` is the composition.

The per-thread contract (`Realizes`) is still not discharged (T2h, #311).
-/

namespace Concurrency.ProgE2E

open Rel Prog ClifThread

/-- **Race-freedom of a CLIF program in every execution consistent for the contract with
fences** (whose atomic updates are the `rmw`-paired two-event steps, `StepShape`). -/
def RaceFreeProgF (env : Clif.Env) (p : Clif.Program) (n : Nat) (s0 : Nat → TState) (M0 : Bytes) :
    Prop :=
  ∀ (P : Traces TState SKind BVal) (locs : List (Nat × Nat)) (rf co rmw : Rel PEv),
    P.n = n → (∀ i, P.st i 0 = s0 i) → P.Runs (CStep env p) →
    (P.exec locs rf co rmw).Wf → P.StepShape rmw →
    (∀ w r, rf w r → P.val bytesI M0 locs [] w = P.val bytesI M0 locs [] r) →
    InitFirst (P.exec locs rf co rmw) → ClifMM.ConsistentF (P.exec locs rf co rmw) (kindC P) →
    ∀ a b, (∀ q, a ≠ .init q) → (∀ q, b ≠ .init q) → ClifMM.Conflict (P.exec locs rf co rmw) a b →
      ¬ (ClifMM.At (kindC P) a ∧ ClifMM.At (kindC P) b) →
      ClifMM.hb (P.exec locs rf co rmw) (kindC P) a b ∨ ClifMM.hb (P.exec locs rf co rmw) (kindC P) b a

/-- **Race-freedom of the Rust program**: `ord P` gives each event of an execution of the CLIF
program its Rust ordering (cg_clif strengthened it to the event's CLIF kind); every execution
consistent for RC11 without no-thin-air (C++20) is race-free for RC11's happens-before. -/
def RustRaceFree (env : Clif.Env) (p : Clif.Program) (n : Nat) (s0 : Nat → TState) (M0 : Bytes)
    (ord : Traces TState SKind BVal → PEv → RKind) : Prop :=
  (∀ P e, (ord P e).strength = kindC P e) ∧
  ∀ (P : Traces TState SKind BVal) (locs : List (Nat × Nat)) (rf co rmw : Rel PEv),
    P.n = n → (∀ i, P.st i 0 = s0 i) → P.Runs (CStep env p) →
    (P.exec locs rf co rmw).Wf → P.StepShape rmw →
    (∀ w r, rf w r → P.val bytesI M0 locs [] w = P.val bytesI M0 locs [] r) →
    InitFirst (P.exec locs rf co rmw) → RC11.ConsistentNoNTA (P.exec locs rf co rmw) (ord P) →
    ∀ a b, (∀ q, a ≠ .init q) → (∀ q, b ≠ .init q) → ClifMM.Conflict (P.exec locs rf co rmw) a b →
      ¬ ((RC11.IsAtR (ord P) a ∨ RC11.IsAtW (ord P) a) ∧ (RC11.IsAtR (ord P) b ∨ RC11.IsAtW (ord P) b)) →
      RC11.hb (P.exec locs rf co rmw) (ord P) a b ∨ RC11.hb (P.exec locs rf co rmw) (ord P) b a

/-- Race-freedom over the contract's executions gives it over those with fences. -/
theorem raceFreeProgF_of_raceFreeProg {env : Clif.Env} {p : Clif.Program} {n : Nat}
    {s0 : Nat → TState} {M0 : Bytes} (h : RaceFreeProg env p n s0 M0) :
    RaceFreeProgF env p n s0 M0 :=
  fun P locs rf co rmw hn hs0 hC hwf _ hval hinit hcF =>
    h P locs rf co rmw hn hs0 hC hwf hval hinit hcF.toConsistent

theorem evShape_two (s : Clif.State) {L : List (SKind × Nat)} (hL : L ∈ evShape s)
    (h2 : 2 ≤ L.length) : ∃ n1 n2, L = [(.scR, n1), (.scW, n2)] := by
  unfold evShape at hL
  split at hL
  · split at hL <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hL <;>
      (try rcases hL with rfl | rfl) <;> (try subst hL) <;> simp at h2 ⊢
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hL; subst hL; simp at h2

/-- In an execution of CLIF threads the atomic updates (two-event steps) are atomics. -/
theorem rmw_sc {env : Clif.Env} {p : Clif.Program} {P : Traces TState SKind BVal}
    {locs : List (Nat × Nat)} {rf co rmw : Rel PEv} (hC : P.Runs (CStep env p))
    (hwf : (P.exec locs rf co rmw).Wf) (hs : P.StepShape rmw) {a b : PEv} (h : rmw a b) :
    kindC P a = .scR ∧ kindC P b = .scW := by
  obtain ⟨i, j, rfl, rfl⟩ := hs.2 a b h
  have hd := hwf.rmw_dir _ _ h
  rcases hx1 : P.evAt (.thr i j 1) with _ | x1
  · rw [exec_thr_none hx1] at hd; exact absurd hd.2 (by decide)
  obtain ⟨hi, hj, hk1, hx1e⟩ := Traces.evAt_some hx1
  have hx0 := Traces.evAt_thr hi hj (show 0 < ((P.tr i)[j]).length by omega)
  have hst := hC i hi j hj
  unfold CStep at hst
  split at hst
  · exact hst.elim
  · rename_i s _
    obtain ⟨⟨hsh, -⟩, -, -⟩ := hst
    obtain ⟨n1, n2, he⟩ := evShape_two s hsh (by simp; omega)
    have h0 := congrArg (fun L => (L[0]?).map Prod.fst) he
    have h1 := congrArg (fun L => (L[1]?).map Prod.fst) he
    simp only [List.getElem?_map] at h0 h1
    rw [List.getElem?_eq_getElem (by omega)] at h0
    rw [List.getElem?_eq_getElem hk1] at h1
    simp only [Option.map_some, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at h0 h1
    refine ⟨?_, ?_⟩
    · simp only [kindC, hx0]; exact h0
    · simp only [kindC, hx1, ← hx1e]; exact h1

/-- **Rust race-freedom implies race-freedom in every execution consistent for the contract with
fences** (`RC11.strength_sound`, `RC11.hb_strength`). -/
theorem raceFreeProgF_of_rust {env : Clif.Env} {p : Clif.Program} {n : Nat} {s0 : Nat → TState}
    {M0 : Bytes} {ord : Traces TState SKind BVal → PEv → RKind}
    (h : RustRaceFree env p n s0 M0 ord) : RaceFreeProgF env p n s0 M0 := by
  intro P locs rf co rmw hn hs0 hC hwf hsh hval hinit hcF a b ha hb hconf hat
  have hk : (fun e => (ord P e).strength) = kindC P := funext (h.1 P)
  have hrmwk : RC11.RmwAt (P.exec locs rf co rmw) (ord P) := by
    intro x y hxy
    obtain ⟨h1, h2⟩ := rmw_sc hC hwf hsh hxy
    rw [← h.1 P x] at h1
    rw [← h.1 P y] at h2
    refine ⟨?_, ?_⟩
    · rcases hko : ord P x with _ | _ | o | o | o <;> rw [hko] at h1 <;>
        simp [RKind.strength] at h1
      exact ⟨o, hko⟩
    · rcases hko : ord P y with _ | _ | o | o | o <;> rw [hko] at h2 <;>
        simp [RKind.strength] at h2
      exact ⟨o, hko⟩
  have hc : RC11.ConsistentNoNTA (P.exec locs rf co rmw) (ord P) :=
    RC11.strength_sound hwf hrmwk (by rw [hk]; exact hcF)
  have hatk : ∀ e, ClifMM.At (kindC P) e ↔ (RC11.IsAtR (ord P) e ∨ RC11.IsAtW (ord P) e) := by
    intro e; rw [← hk]; exact RC11.at_strength
  rcases h.2 P locs rf co rmw hn hs0 hC hwf hsh hval hinit hc a b ha hb hconf
      (fun h' => hat ⟨(hatk a).mpr h'.1, (hatk b).mpr h'.2⟩) with h' | h'
  · have := RC11.hb_strength hwf hrmwk h'
    rw [hk] at this; exact .inl this
  · have := RC11.hb_strength hwf hrmwk h'
    rw [hk] at this; exact .inr this

/-- The `dmb`s of Arm threads are fences (their events' directions are their kinds'). -/
theorem dmbF_of_runs {P : ArmThread.Policy} {PA : Traces AState AKind BVal}
    {locsA : List (Nat × Nat)} {rfA coA rmwA : Rel PEv} (hA : PA.Runs (ATStep P)) :
    Armv8.DmbF (PA.exec locsA rfA coA rmwA) (kindA PA) := by
  intro e he
  cases e with
  | init q => simp [kindA, Traces.evAt] at he
  | thr i j k =>
    rcases hx : PA.evAt (.thr i j k) with _ | x
    · simp [kindA, hx] at he
    · obtain ⟨hi, hj, hk, hxe⟩ := Traces.evAt_some hx
      obtain ⟨-, l, -, hevs⟩ := hA i hi j hj
      have hmem : x ∈ l.evs.map convEv := by rw [← hevs, ← hxe]; exact List.getElem_mem hk
      obtain ⟨e', -, rfl⟩ := List.mem_map.mp hmem
      simp only [kindA, hx, convEv] at he
      simp [Traces.exec, hx, convEv, he, AKind.dir]

/-! ## The CLIF execution with fences -/

section clif

variable {PA : Traces AState AKind BVal} {locsA : List (Nat × Nat)} {MA0 : Bytes}
  {rfA coA rmwA : Rel PEv} {PC : Traces TState SKind BVal} {locsC : List (Nat × Nat)}
  {MC0 : Bytes} {φ : PEv → PEv} {Obs : Nat → AState → TState → Prop}

theorem valid_of_kind {e : PEv} (h : kindC PC e = .scR ∨ kindC PC e = .scW ∨ kindC PC e = .fence) :
    Valid PC locsC e := by
  cases e with
  | init q => rcases h with h | h | h <;> simp [kindC, Traces.evAt] at h
  | thr i j k =>
    show (PC.evAt (.thr i j k)).isSome
    rcases hx : PC.evAt (.thr i j k) with _ | x
    · rcases h with h | h | h <;> simp [kindC, hx] at h
    · rfl

variable (hR : Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ Obs)
  (hwfA : (PA.exec locsA rfA coA rmwA).Wf)
include hR hwfA

/-- **The CLIF execution is consistent for the contract with fences** (`Mapping.Hom.psc_acyclic`
along `φ` on the CLIF events). -/
theorem consistentCF {env : Clif.Env} {p : Clif.Program} {P : ArmThread.Policy}
    (hA : PA.Runs (ATStep P)) (hC : PC.Runs (CStep env p))
    (hcA : Armv8.Consistent (PA.exec locsA rfA coA rmwA) (kindA PA)) :
    ClifMM.ConsistentF (XC PC locsC φ rfA coA rmwA) (kindC PC) where
  toConsistent := consistentC hR hwfA hcA
  psc := by
    have hh : Mapping.Hom (XC PC locsC φ rfA coA rmwA) (kindC PC) (PA.exec locsA rfA coA rmwA)
        (kindA PA) (Valid PC locsC) φ :=
      { vdir := fun _ h => valid_of_dir h
        vat := fun _ h => valid_of_kind h
        po := fun _ _ ha hb h => po_map hR ha hb h
        rf := fun _ _ h => h.2.2
        co := fun _ _ h => h.2.2
        kind := fun e h => hR.kind e (valid_of_kind h)
        rmw := fun _ _ h => rmw_sc hC (wfC hR hwfA) hR.shape h }
    exact hh.psc_acyclic hwfA (wfC hR hwfA) (dmbF_of_runs hA) hcA

/-- **Program-level correctness for programs race-free in every execution consistent for the
contract with fences, given the per-thread contract `Realizes`**: `program_correct` with the
weaker race-freedom premise `RaceFreeProgF`. **The contract is not discharged by
`E2E.backend_correct_final`** (`docs/plans/atomics.md` §3c, T2h). -/
theorem program_correctF {env : Clif.Env} {p : Clif.Program} {n : Nat} {s0 : Nat → TState}
    (hrace : RaceFreeProgF env p n s0 MC0)
    -- the Arm execution: runs of the Arm threads, Armv8-consistent
    (hA : PA.Runs (ATStep ArmThread.Policy.arm))
    (hcA : Armv8.Consistent (PA.exec locsA rfA coA rmwA) (kindA PA))
    (hvalA : ∀ w r, rfA w r → PA.val bytesI MA0 locsA [] w = PA.val bytesI MA0 locsA [] r)
    (hovA : NoOverlap (PA.exec locsA rfA coA rmwA) (PA.sz locsA))
    (hiA : InitFirst (PA.exec locsA rfA coA rmwA))
    -- the CLIF threads' traces
    (hC : PC.Runs (CStep env p)) (hn : PC.n = n) (hs0 : ∀ i, PC.st i 0 = s0 i) :
    (XC PC locsC φ rfA coA rmwA).SC ∧
    ∃ ts B, MTRun env p (s0, MC0) (ts, B) ∧
      StripEq ts (fun i => PC.st i (if i < PC.n then (PC.tr i).length else 0)) ∧
      (∀ w, (XC PC locsC φ rfA coA rmwA).dir w = .W →
        (∀ w', (XC PC locsC φ rfA coA rmwA).dir w' = .W →
          (XC PC locsC φ rfA coA rmwA).loc w' = (XC PC locsC φ rfA coA rmwA).loc w → w' ≠ w →
          pull φ (Valid PC locsC) coA w' w) →
        getB B ((XC PC locsC φ rfA coA rmwA).loc w) (PC.sz locsC w) = PC.val bytesI MC0 locsC [] w) ∧
      (∀ i < PC.n, Obs i (PA.st i (PA.tr i).length) (PC.st i (PC.tr i).length)) :=
  correct_of_raceFree hR hwfA hcA hvalA hovA hiA hC hs0
    (hrace PC locsC _ _ _ hn hs0 hC (wfC hR hwfA) hR.shape (valC hR hvalA) (initC hR hiA)
      (consistentCF hR hwfA hA hC hcA))

/-- **Program-level correctness for race-free Rust programs, given the per-thread contract
`Realizes`**: the Rust program (orderings `ord`, strengthened by cg_clif to the CLIF kinds) is
race-free in every C++20-consistent execution; then every Armv8-consistent execution of the Arm
threads realizing the CLIF threads is SC on the CLIF side and a run of the multi-threaded
`Clif.run` (`program_correctF` ∘ `raceFreeProgF_of_rust`). **The contract is not discharged by
`E2E.backend_correct_final`** (`docs/plans/atomics.md` §3c, T2h). -/
theorem program_correct_rust {env : Clif.Env} {p : Clif.Program} {n : Nat} {s0 : Nat → TState}
    {ord : Traces TState SKind BVal → PEv → RKind}
    (hrust : RustRaceFree env p n s0 MC0 ord)
    (hA : PA.Runs (ATStep ArmThread.Policy.arm))
    (hcA : Armv8.Consistent (PA.exec locsA rfA coA rmwA) (kindA PA))
    (hvalA : ∀ w r, rfA w r → PA.val bytesI MA0 locsA [] w = PA.val bytesI MA0 locsA [] r)
    (hovA : NoOverlap (PA.exec locsA rfA coA rmwA) (PA.sz locsA))
    (hiA : InitFirst (PA.exec locsA rfA coA rmwA))
    (hC : PC.Runs (CStep env p)) (hn : PC.n = n) (hs0 : ∀ i, PC.st i 0 = s0 i) :
    (XC PC locsC φ rfA coA rmwA).SC ∧
    ∃ ts B, MTRun env p (s0, MC0) (ts, B) ∧
      StripEq ts (fun i => PC.st i (if i < PC.n then (PC.tr i).length else 0)) ∧
      (∀ w, (XC PC locsC φ rfA coA rmwA).dir w = .W →
        (∀ w', (XC PC locsC φ rfA coA rmwA).dir w' = .W →
          (XC PC locsC φ rfA coA rmwA).loc w' = (XC PC locsC φ rfA coA rmwA).loc w → w' ≠ w →
          pull φ (Valid PC locsC) coA w' w) →
        getB B ((XC PC locsC φ rfA coA rmwA).loc w) (PC.sz locsC w) = PC.val bytesI MC0 locsC [] w) ∧
      (∀ i < PC.n, Obs i (PA.st i (PA.tr i).length) (PC.st i (PC.tr i).length)) :=
  program_correctF hR hwfA (raceFreeProgF_of_rust hrust) hA hcA hvalA hovA hiA hC hn hs0

end clif

end Concurrency.ProgE2E

import FV.Concurrency.Replay
import FV.Concurrency.ClifThread
import FV.Concurrency.ArmThread
import FV.Concurrency.Mapping

/-!
# The program-level statement (T2e, #303)

`program_correct`: every Armv8-consistent execution of a multi-threaded Arm program that
**realizes** a race-free multi-threaded CLIF program is, on the CLIF side, sequentially consistent,
and the CLIF program reaches the same thread outcomes by a run of the multi-threaded `Clif.run`
(`ClifThread.MTRun`).

* **The Arm side**: the threads run the per-thread event semantics `ArmThread.TStep` under the
  Arm monitor policy (`ATStep`; each thread with its machine, e.g. `ArmStepX X H fa` of its
  compiled function), forming an execution (`Prog.Traces.exec`) that is well-formed,
  `Armv8.Consistent`, reads its writes' values, has no partially overlapping accesses and
  `co`-first initial writes.
* **Race-freedom** (`RaceFreeProg`): every execution of the CLIF program that is consistent for the
  Cranelift contract is race-free. This is the C++20/Rust definition of a program without
  undefined behaviour (data races are UB in every consistent execution of the source model), so no
  prefix argument is needed (which would fail here: neither the contract nor the Arm fragment
  forbids load-buffering cycles through plain accesses, `docs/plans/atomics.md` §2).
* **The contract `Realizes`** (per thread, assembled): the CLIF threads' traces of `CStep` embed
  into the Arm threads' traces (`φ`, preserving program order, thread, direction, location, size,
  value, initial writes, and mapping kinds by Cranelift's table `Maps`); CLIF reads read from CLIF
  writes (frame separation); atomic updates are `rmw`-paired; and the threads' outcomes are
  related (`Obs`). **This is the per-thread event-level refinement of compiled code (a
  footprint-preserving simulation with interference, CASCompCert-style). It is not implied by
  `E2E.backend_correct_final`**, which is a whole-run theorem without interference (`Clif.runLoop`
  reads its own memory; extern results are a function of the arguments and the memory) and says
  nothing about the compiled code's intermediate memory footprint. Discharging `Realizes` needs the
  isel/prepare/register-level layers re-proven with interference (`docs/plans/atomics.md` §3e,
  T2h; the reduction to per-thread refinements is `ThreadRefine.realizes_of_threads`). Until then
  `program_correct` is the composition of the memory-model layer with that contract, not a
  multi-threaded compiler theorem.

Proof: the CLIF execution (`φ`-pullback of the Arm relations) is well-formed (`wfC`), consistent
for the contract (`consistentC`, from `Armv8.coherence`/`atomicity`/`atomics_sc` along `φ`),
race-free by the premise, SC by DRF-SC (`Prog.drf_sc_init`), a run of the interleaving machine by
`Prog.replay`, and a run of the multi-threaded `Clif.run` by `ClifThread.mrun_mt`.
-/

namespace Concurrency.ProgE2E

open Rel Prog ClifThread

/-! ## Arm threads as a thread semantics -/

/-- The bytes of an `n`-byte value. -/
def bytesOf (n : Nat) (v : BitVec (n * 8)) : BVal :=
  (List.range n).map fun k => some (v.extractLsb' (8 * k) 8)

/-- An Arm event as a program event. -/
def convEv (e : ArmThread.Ev) : Ev AKind BVal :=
  ⟨e.k, e.k.dir, e.addr.toNat, e.n, bytesOf e.n e.val⟩

/-- An Arm thread: its machine, its state and its exclusive monitor. -/
abbrev AState := (Arm.ArmState → Arm.ArmState) × Arm.ArmState × ArmThread.Mon

/-- A step of an Arm thread (`ArmThread.TStep` of its machine). -/
def ATStep (P : ArmThread.Policy) : TSem AState AKind BVal := fun t evs t' =>
  t'.1 = t.1 ∧ ∃ l, ArmThread.TStep P t.1 (t.2.1, t.2.2) l (t'.2.1, t'.2.2) ∧
    evs = l.evs.map convEv

/-! ## Executions -/

variable {σ K : Type}

/-- The events of an execution of `P` with initial locations `locs`. -/
def Valid (P : Traces σ K BVal) (locs : List (Nat × Nat)) : PEv → Prop
  | .init q => q < locs.length
  | e => (P.evAt e).isSome

/-- The kind of an Arm event (initial writes: plain writes). -/
def kindA (P : Traces AState AKind BVal) (e : PEv) : AKind :=
  match P.evAt e with
  | some x => x.k
  | none => .plainW

/-- The kind of a CLIF event (initial writes: non-atomic writes). -/
def kindC (P : Traces TState SKind BVal) (e : PEv) : SKind :=
  match P.evAt e with
  | some x => x.k
  | none => .naW

/-- A relation pulled back along `φ`, on the events `V`. -/
def pull (φ : PEv → PEv) (V : PEv → Prop) (r : Rel PEv) : Rel PEv :=
  fun a b => V a ∧ V b ∧ r (φ a) (φ b)

/-- **Race-freedom of a CLIF program in every execution consistent for the Cranelift contract**
(threads `0 … n-1` from `s0`, initial bytes `M0`): conflicting non-initial accesses, not both
atomic, are ordered by happens-before. -/
def RaceFreeProg (env : Clif.Env) (p : Clif.Program) (n : Nat) (s0 : Nat → TState) (M0 : Bytes) :
    Prop :=
  ∀ (P : Traces TState SKind BVal) (locs : List (Nat × Nat)) (rf co rmw : Rel PEv),
    P.n = n → (∀ i, P.st i 0 = s0 i) → P.Runs (CStep env p) →
    (P.exec locs rf co rmw).Wf →
    (∀ w r, rf w r → P.val bytesI M0 locs [] w = P.val bytesI M0 locs [] r) →
    InitFirst (P.exec locs rf co rmw) → ClifMM.Consistent (P.exec locs rf co rmw) (kindC P) →
    ∀ a b, (∀ q, a ≠ .init q) → (∀ q, b ≠ .init q) → ClifMM.Conflict (P.exec locs rf co rmw) a b →
      ¬ (ClifMM.At (kindC P) a ∧ ClifMM.At (kindC P) b) →
      ClifMM.hb (P.exec locs rf co rmw) (kindC P) a b ∨ ClifMM.hb (P.exec locs rf co rmw) (kindC P) b a

/-- **The contract: the CLIF threads' traces `PC` are realized by the Arm threads' traces `PA`**
through the event embedding `φ` (see the module doc; per-thread event-level refinement). -/
structure Realizes (PA : Traces AState AKind BVal) (locsA : List (Nat × Nat)) (MA0 : Bytes)
    (rfA coA rmwA : Rel PEv) (PC : Traces TState SKind BVal) (locsC : List (Nat × Nat))
    (MC0 : Bytes) (φ : PEv → PEv) (Obs : Nat → AState → TState → Prop) : Prop where
  threads : PC.n = PA.n
  valid : ∀ e, Valid PC locsC e → Valid PA locsA (φ e)
  inj : ∀ a b, Valid PC locsC a → Valid PC locsC b → φ a = φ b → a = b
  po : ∀ a b, Valid PC locsC a → Valid PC locsC b → (PEv.po a b ↔ PEv.po (φ a) (φ b))
  init : ∀ q, q < locsC.length → ∃ q', φ (.init q) = .init q'
  dir : ∀ e, Valid PC locsC e →
    (PA.exec locsA rfA coA rmwA).dir (φ e) = (PC.exec locsC rfA coA rmwA).dir e
  loc : ∀ e, Valid PC locsC e →
    (PA.exec locsA rfA coA rmwA).loc (φ e) = (PC.exec locsC rfA coA rmwA).loc e
  sz : ∀ e, Valid PC locsC e → PA.sz locsA (φ e) = PC.sz locsC e
  val : ∀ e, Valid PC locsC e → PA.val bytesI MA0 locsA [] (φ e) = PC.val bytesI MC0 locsC [] e
  kind : ∀ e, Valid PC locsC e → Maps (kindC PC e) (kindA PA (φ e))
  /-- CLIF reads read from CLIF writes (the frame separation of compiled code) -/
  rf_src : ∀ w e, Valid PC locsC e → rfA w (φ e) → ∃ w', Valid PC locsC w' ∧ φ w' = w
  /-- the atomic updates of the CLIF steps are `rmw`-paired on Arm -/
  shape : PC.StepShape (pull φ (Valid PC locsC) rmwA)
  /-- the threads' outcomes -/
  obs : ∀ i < PC.n, Obs i (PA.st i (PA.tr i).length) (PC.st i (PC.tr i).length)

/-! ## Facts about program order -/

theorem PEv.po_irrefl (a : PEv) : ¬ PEv.po a a := by
  cases a <;> simp [PEv.po]

theorem PEv.po_trans {a b c : PEv} (h1 : PEv.po a b) (h2 : PEv.po b c) : PEv.po a c := by
  cases a <;> cases b <;> cases c <;> simp only [PEv.po] at h1 h2 ⊢
  all_goals first
    | omega
    | exact h1.elim
    | exact h2.elim
    | (obtain ⟨rfl, h1⟩ := h1; obtain ⟨rfl, h2⟩ := h2; exact ⟨rfl, by omega⟩)

theorem PEv.po_tid {a b : PEv} (h : PEv.po a b) : a.tid = b.tid := by
  cases a <;> cases b <;> simp_all [PEv.po, PEv.tid]

theorem PEv.po_total {a b : PEv} (ht : a.tid = b.tid) (hne : a ≠ b) : PEv.po a b ∨ PEv.po b a := by
  cases a <;> cases b <;> simp_all [PEv.po, PEv.tid] <;> omega

theorem valid_of_dir {P : Traces σ K BVal} {locs : List (Nat × Nat)} {rf co rmw : Rel PEv}
    {e : PEv} (h : (P.exec locs rf co rmw).dir e ≠ .F) : Valid P locs e := by
  cases e with
  | init q =>
    show q < locs.length
    by_cases hq : q < locs.length
    · exact hq
    · simp [Traces.exec, hq] at h
  | thr i j k =>
    show (P.evAt (.thr i j k)).isSome
    rcases hx : P.evAt (.thr i j k) with _ | x
    · simp [Traces.exec, hx] at h
    · rfl

/-! ## The CLIF execution -/

section clif

variable {PA : Traces AState AKind BVal} {locsA : List (Nat × Nat)} {MA0 : Bytes}
  {rfA coA rmwA : Rel PEv} {PC : Traces TState SKind BVal} {locsC : List (Nat × Nat)}
  {MC0 : Bytes} {φ : PEv → PEv} {Obs : Nat → AState → TState → Prop}

/-- The CLIF execution: the Arm relations pulled back along `φ`. -/
abbrev XC (PC : Traces TState SKind BVal) (locsC : List (Nat × Nat)) (φ : PEv → PEv)
    (rfA coA rmwA : Rel PEv) : Exec PEv :=
  PC.exec locsC (pull φ (Valid PC locsC) rfA) (pull φ (Valid PC locsC) coA)
    (pull φ (Valid PC locsC) rmwA)

theorem dirC (e : PEv) (r1 r2 r3 r1' r2' r3' : Rel PEv) :
    (PC.exec locsC r1 r2 r3).dir e = (PC.exec locsC r1' r2' r3').dir e := rfl

theorem locC (e : PEv) (r1 r2 r3 r1' r2' r3' : Rel PEv) :
    (PC.exec locsC r1 r2 r3).loc e = (PC.exec locsC r1' r2' r3').loc e := rfl

variable (hR : Realizes PA locsA MA0 rfA coA rmwA PC locsC MC0 φ Obs)
  (hwfA : (PA.exec locsA rfA coA rmwA).Wf)
include hR hwfA

omit hwfA in
theorem dir_eq {e : PEv} (he : Valid PC locsC e) :
    (PA.exec locsA rfA coA rmwA).dir (φ e) = (XC PC locsC φ rfA coA rmwA).dir e :=
  hR.dir e he

omit hwfA in
theorem loc_eq {e : PEv} (he : Valid PC locsC e) :
    (PA.exec locsA rfA coA rmwA).loc (φ e) = (XC PC locsC φ rfA coA rmwA).loc e :=
  hR.loc e he

/-- **The CLIF execution is well-formed.** -/
theorem wfC : (XC PC locsC φ rfA coA rmwA).Wf where
  po_irrefl a := PEv.po_irrefl a
  po_trans _ _ _ := PEv.po_trans
  po_tid _ _ := PEv.po_tid
  po_total _ _ := PEv.po_total
  rf_dir a b h := by
    obtain ⟨ha, hb, h⟩ := h
    have := hwfA.rf_dir _ _ h
    rw [dir_eq hR ha, dir_eq hR hb] at this; exact this
  rf_loc a b h := by
    obtain ⟨ha, hb, h⟩ := h
    have := hwfA.rf_loc _ _ h
    rwa [loc_eq hR ha, loc_eq hR hb] at this
  rf_func a a' b h1 h2 := hR.inj _ _ h1.1 h2.1 (hwfA.rf_func _ _ _ h1.2.2 h2.2.2)
  rf_total b hb := by
    have hv := valid_of_dir (show (XC PC locsC φ rfA coA rmwA).dir b ≠ .F by rw [hb]; decide)
    obtain ⟨w, hw⟩ := hwfA.rf_total (φ b) (by rw [dir_eq hR hv]; exact hb)
    obtain ⟨w', hw', rfl⟩ := hR.rf_src w b hv hw
    exact ⟨w', hw', hv, hw⟩
  co_dir a b h := by
    obtain ⟨ha, hb, h⟩ := h
    have := hwfA.co_dir _ _ h
    rw [dir_eq hR ha, dir_eq hR hb] at this; exact this
  co_loc a b h := by
    obtain ⟨ha, hb, h⟩ := h
    have := hwfA.co_loc _ _ h
    rwa [loc_eq hR ha, loc_eq hR hb] at this
  co_irrefl a h := hwfA.co_irrefl _ h.2.2
  co_trans a b c h1 h2 := ⟨h1.1, h2.2.1, hwfA.co_trans _ _ _ h1.2.2 h2.2.2⟩
  co_total a b ha hb hl hne := by
    have hva := valid_of_dir (show (XC PC locsC φ rfA coA rmwA).dir a ≠ .F by rw [ha]; decide)
    have hvb := valid_of_dir (show (XC PC locsC φ rfA coA rmwA).dir b ≠ .F by rw [hb]; decide)
    rcases hwfA.co_total (φ a) (φ b) (by rw [dir_eq hR hva]; exact ha)
        (by rw [dir_eq hR hvb]; exact hb)
        (by rw [loc_eq hR hva, loc_eq hR hvb]; exact hl)
        (fun e => hne (hR.inj _ _ hva hvb e)) with h | h
    · exact .inl ⟨hva, hvb, h⟩
    · exact .inr ⟨hvb, hva, h⟩
  rmw_dir a b h := by
    obtain ⟨ha, hb, h⟩ := h
    have := hwfA.rmw_dir _ _ h
    rw [dir_eq hR ha, dir_eq hR hb] at this; exact this
  rmw_loc a b h := by
    obtain ⟨ha, hb, h⟩ := h
    have := hwfA.rmw_loc _ _ h
    rwa [loc_eq hR ha, loc_eq hR hb] at this
  rmw_po a b h := (hR.po a b h.1 h.2.1).mpr (hwfA.rmw_po _ _ h.2.2)
  rmw_imm a b c h h1 h2 := by
    obtain ⟨i, j, rfl, rfl⟩ := hR.shape.2 a b h
    cases c <;> simp_all [Traces.exec, PEv.po] <;> omega

omit hR hwfA in
theorem valid_of_At {e : PEv} (h : ClifMM.At (kindC PC) e) : Valid PC locsC e := by
  cases e with
  | init q => rcases h with h | h <;> simp [kindC, Traces.evAt] at h
  | thr i j k =>
    show (PC.evAt (.thr i j k)).isSome
    rcases hx : PC.evAt (.thr i j k) with _ | x
    · rcases h with h | h <;> simp [kindC, hx] at h
    · rfl

omit hwfA in
theorem AL_of_At {e : PEv} (h : ClifMM.At (kindC PC) e) :
    Armv8.A (kindA PA) (φ e) ∨ Armv8.L (kindA PA) (φ e) := by
  have hm := hR.kind e (valid_of_At h)
  rcases h with h | h <;> rw [h] at hm
  · exact .inl hm
  · exact .inr hm

omit hR hwfA in
theorem com_map {a b : PEv} (h : (XC PC locsC φ rfA coA rmwA).com a b) :
    Valid PC locsC a ∧ Valid PC locsC b ∧ (PA.exec locsA rfA coA rmwA).com (φ a) (φ b) := by
  rcases h with ⟨ha, hb, h⟩ | ⟨ha, hb, h⟩ | ⟨w, ⟨hw, ha, h1⟩, ⟨-, hb, h2⟩⟩
  · exact ⟨ha, hb, .inl h⟩
  · exact ⟨ha, hb, .inr (.inl h)⟩
  · exact ⟨ha, hb, .inr (.inr ⟨φ w, h1, h2⟩)⟩

omit hwfA in
theorem po_map {a b : PEv} (ha : Valid PC locsC a) (hb : Valid PC locsC b)
    (h : (XC PC locsC φ rfA coA rmwA).po a b) : (PA.exec locsA rfA coA rmwA).po (φ a) (φ b) :=
  (hR.po a b ha hb).mp h

omit hwfA in
theorem sw_map {a b : PEv} (h : ClifMM.sw (XC PC locsC φ rfA coA rmwA) (kindC PC) a b) :
    Valid PC locsC a ∧ Valid PC locsC b ∧
      Armv8.swA (PA.exec locsA rfA coA rmwA) (kindA PA) (φ a) (φ b) := by
  obtain ⟨hk1, ⟨ha, hb, hrf⟩, hk2⟩ := h
  have m1 := hR.kind a ha
  have m2 := hR.kind b hb
  rw [hk1] at m1; rw [hk2] at m2
  exact ⟨ha, hb, m1, hrf, m2⟩

omit hwfA in
theorem seq_map : ∀ {x y : PEv}, Valid PC locsC x →
    Relation.TransGen (seq (opt (XC PC locsC φ rfA coA rmwA).po)
      (ClifMM.sw (XC PC locsC φ rfA coA rmwA) (kindC PC))) x y →
    Valid PC locsC y ∧ Armv8.hbA (PA.exec locsA rfA coA rmwA) (kindA PA) (φ x) (φ y) := by
  have one : ∀ {x y : PEv}, Valid PC locsC x →
      seq (opt (XC PC locsC φ rfA coA rmwA).po) (ClifMM.sw (XC PC locsC φ rfA coA rmwA) (kindC PC)) x y →
      Valid PC locsC y ∧ Armv8.hbA (PA.exec locsA rfA coA rmwA) (kindA PA) (φ x) (φ y) := by
    rintro x y hx ⟨z, hxz, hzy⟩
    obtain ⟨hz, hy, hsw⟩ := sw_map hR hzy
    refine ⟨hy, ?_⟩
    rcases hxz with rfl | hxz
    · exact .single (.inr hsw)
    · exact .tail (.single (.inl (po_map hR hx hz hxz))) (.inr hsw)
  intro x y hx h
  induction h with
  | single h => exact one hx h
  | tail _ h2 ih =>
    obtain ⟨hc, h1⟩ := ih
    obtain ⟨hy, h2⟩ := one hc h2
    exact ⟨hy, h1.trans h2⟩

theorem hb_map {a b : PEv} (ha : Valid PC locsC a) (hb : Valid PC locsC b)
    (h : ClifMM.hb (XC PC locsC φ rfA coA rmwA) (kindC PC) a b) :
    Armv8.hbA (PA.exec locsA rfA coA rmwA) (kindA PA) (φ a) (φ b) := by
  rcases path_split (wfC hR hwfA).po_trans h with h | ⟨c, hp, hc⟩
  · exact .single (.inl (po_map hR ha hb h))
  · obtain ⟨hcv, h1⟩ := seq_map hR ha hp
    rcases hc with rfl | hc
    · exact h1
    · exact h1.tail (.inl (po_map hR hcv hb hc))

/-- **The CLIF execution is consistent for the Cranelift contract** (theorem 2 along `φ`). -/
theorem consistentC (hcA : Armv8.Consistent (PA.exec locsA rfA coA rmwA) (kindA PA)) :
    ClifMM.Consistent (XC PC locsC φ rfA coA rmwA) (kindC PC) where
  coherence a b hab he := by
    rcases he with rfl | he
    · rcases cycle_split (wfC hR hwfA).po_trans hab with h | ⟨b, hb⟩
      · exact (wfC hR hwfA).po_irrefl _ h
      · obtain ⟨c, ⟨z, -, hz⟩⟩ := plus_last hb
        have hv : Valid PC locsC b := (sw_map hR hz).2.1
        exact Armv8.coherence hwfA hcA (seq_map hR hv hb).2 (.inl rfl)
    · obtain ⟨c, hc, -⟩ := plus_head he
      obtain ⟨d, hd⟩ := plus_last he
      have hbv := (com_map (PA := PA) (locsA := locsA) hc).1
      have hav := (com_map (PA := PA) (locsA := locsA) hd).2.1
      exact Armv8.coherence hwfA hcA (hb_map hR hwfA hav hbv hab)
        (.inr (plus_map φ (fun _ _ h => (com_map h).2.2) he))
  atomicity a b hr := by
    rintro ⟨c, ⟨w, ⟨-, -, h1⟩, ⟨-, -, h2⟩⟩, ⟨-, -, h3⟩⟩
    exact Armv8.atomicity hwfA hcA hr.2.2 ⟨φ w, h1, h2⟩ h3
  sc a h := by
    refine Armv8.atomics_sc hwfA hcA (φ a) (plus_map φ ?_ h)
    rintro x y ⟨hx, hxy, hy⟩
    refine ⟨AL_of_At hR hx, ?_, AL_of_At hR hy⟩
    rcases hxy with hxy | hxy
    · exact .inl (po_map hR (valid_of_At hx) (valid_of_At hy) hxy)
    · exact .inr (com_map hxy).2.2

/-! ## The program-level statement -/

omit hwfA in
/-- The CLIF reads read their writes' values. -/
theorem valC (hvalA : ∀ w r, rfA w r → PA.val bytesI MA0 locsA [] w = PA.val bytesI MA0 locsA [] r) :
    ∀ w r, pull φ (Valid PC locsC) rfA w r →
      PC.val bytesI MC0 locsC [] w = PC.val bytesI MC0 locsC [] r := fun w r h => by
  rw [← hR.val w h.1, ← hR.val r h.2.1]; exact hvalA _ _ h.2.2

omit hwfA in
/-- The CLIF initial writes are `co`-first. -/
theorem initC (hiA : InitFirst (PA.exec locsA rfA coA rmwA)) :
    InitFirst (XC PC locsC φ rfA coA rmwA) := fun w q h => by
  obtain ⟨-, hq, h⟩ := h
  obtain ⟨q', e⟩ := hR.init q hq
  rw [e] at h; exact hiA _ _ h

/-- **The program-level conclusion from race-freedom of the CLIF execution** (the common part of
`program_correct` and `program_correctF`, `FV/Concurrency/ProgramE2EF.lean`). -/
theorem correct_of_raceFree {env : Clif.Env} {p : Clif.Program} {s0 : Nat → TState}
    (hcA : Armv8.Consistent (PA.exec locsA rfA coA rmwA) (kindA PA))
    (hvalA : ∀ w r, rfA w r → PA.val bytesI MA0 locsA [] w = PA.val bytesI MA0 locsA [] r)
    (hovA : NoOverlap (PA.exec locsA rfA coA rmwA) (PA.sz locsA))
    (hiA : InitFirst (PA.exec locsA rfA coA rmwA))
    (hC : PC.Runs (CStep env p)) (hs0 : ∀ i, PC.st i 0 = s0 i)
    (hrfC : ∀ a b, (∀ q, a ≠ .init q) → (∀ q, b ≠ .init q) →
      ClifMM.Conflict (XC PC locsC φ rfA coA rmwA) a b →
      ¬ (ClifMM.At (kindC PC) a ∧ ClifMM.At (kindC PC) b) →
      ClifMM.hb (XC PC locsC φ rfA coA rmwA) (kindC PC) a b ∨
        ClifMM.hb (XC PC locsC φ rfA coA rmwA) (kindC PC) b a) :
    (XC PC locsC φ rfA coA rmwA).SC ∧
    ∃ ts B, MTRun env p (s0, MC0) (ts, B) ∧
      StripEq ts (fun i => PC.st i (if i < PC.n then (PC.tr i).length else 0)) ∧
      (∀ w, (XC PC locsC φ rfA coA rmwA).dir w = .W →
        (∀ w', (XC PC locsC φ rfA coA rmwA).dir w' = .W →
          (XC PC locsC φ rfA coA rmwA).loc w' = (XC PC locsC φ rfA coA rmwA).loc w → w' ≠ w →
          pull φ (Valid PC locsC) coA w' w) →
        getB B ((XC PC locsC φ rfA coA rmwA).loc w) (PC.sz locsC w) = PC.val bytesI MC0 locsC [] w) ∧
      (∀ i < PC.n, Obs i (PA.st i (PA.tr i).length) (PC.st i (PC.tr i).length)) := by
  have hwfC := wfC hR hwfA
  have hcC := consistentC hR hwfA hcA
  have hvalC := valC hR hvalA
  have hiC := initC hR hiA
  -- initial writes have only `po` edges from initial writes coming in
  have hin : ∀ a b, (∃ q, b = PEv.init q) →
      union (XC PC locsC φ rfA coA rmwA).po (XC PC locsC φ rfA coA rmwA).com a b →
      (∃ q, a = PEv.init q) ∧ (XC PC locsC φ rfA coA rmwA).po a b := by
    rintro a b ⟨q, rfl⟩ (h | h)
    · cases a with
      | init q' => exact ⟨⟨q', rfl⟩, h⟩
      | thr => exact h.elim
    · exfalso
      rcases h with h | h | ⟨w, -, h⟩
      · have := (hwfC.rf_dir _ _ h).2
        simp only [Traces.exec] at this
        split at this <;> cases this
      · exact hiC _ _ h
      · exact hiC _ _ h
  have hsc : (XC PC locsC φ rfA coA rmwA).SC :=
    drf_sc_init (Init := fun e => ∃ q, e = PEv.init q) hwfC hcC
      (fun a b ha hb => hrfC a b (fun q e => ha ⟨q, e⟩) (fun q e => hb ⟨q, e⟩)) hin
  -- replay
  have hov : NoOverlap (XC PC locsC φ rfA coA rmwA) (PC.sz locsC) := by
    intro a b ha hb
    have hva := valid_of_dir ha
    have hvb := valid_of_dir hb
    have := hovA (φ a) (φ b) (by rw [dir_eq hR hva]; exact ha) (by rw [dir_eq hR hvb]; exact hb)
    rw [loc_eq hR hva, loc_eq hR hvb, hR.sz a hva, hR.sz b hvb] at this
    exact this
  have hwok : ∀ i j k x, PC.evAt (.thr i j k) = some x → x.dir = .W → bytesI.ok x.n x.val := by
    intro i j k x hx _
    obtain ⟨hi, hj, hk, hxe⟩ := Traces.evAt_some hx
    have hst := hC i hi j hj
    unfold CStep at hst
    split at hst
    · exact hst.elim
    · exact (hst.1.2 x (by rw [← hxe]; exact List.getElem_mem hk)).2
  have H : ReplayHyp bytesI (CStep env p) PC locsC (pull φ (Valid PC locsC) rfA)
      (pull φ (Valid PC locsC) coA) (pull φ (Valid PC locsC) rmwA) MC0 [] :=
    ⟨hC, hwfC, hsc, hcC.atomicity, hvalC, hR.shape, hov, hiC, hwok⟩
  obtain ⟨M', hrun, hmem⟩ := replay (H := H)
  obtain ⟨ts, hmt, heq⟩ := mrun_mt hrun
  have e0 : (fun i => PC.st i 0) = s0 := funext hs0
  rw [e0] at hmt
  exact ⟨hsc, ts, M', hmt, heq, hmem, hR.obs⟩

/-- **Program-level correctness for race-free programs, given the per-thread event-level
refinement contract `Realizes`.** An execution of Arm threads (`ATStep` under the Arm monitor
policy) that is Armv8-consistent and realizes the CLIF threads' traces `PC` of a CLIF program
that is race-free in every contract-consistent execution: the CLIF execution is sequentially
consistent, the multi-threaded `Clif.run` reaches the CLIF threads' final states (up to their
local bytes) with final shared bytes holding the `co`-last write of every location, and the
threads' outcomes are related by `Obs`. **The contract is not discharged by
`E2E.backend_correct_final`** (module doc; `docs/plans/atomics.md` §3e, T2h). -/
theorem program_correct {env : Clif.Env} {p : Clif.Program} {n : Nat} {s0 : Nat → TState}
    (hrace : RaceFreeProg env p n s0 MC0)
    -- the Arm execution: runs of the Arm threads, Armv8-consistent
    (_hA : PA.Runs (ATStep ArmThread.Policy.arm))
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
    (hrace PC locsC _ _ _ hn hs0 hC (wfC hR hwfA) (valC hR hvalA) (initC hR hiA)
      (consistentC hR hwfA hcA))

end clif

end Concurrency.ProgE2E

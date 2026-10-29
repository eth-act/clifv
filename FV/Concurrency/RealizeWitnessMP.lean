module

public import FV.Concurrency.RealizeWitnessStore

@[expose] public section

/-!
# `Realizes` for two compiled threads communicating through `stlr`/`ldar` (T2l, #311)

Message passing between compiled code: thread 0 runs the compiled `atomic_store` (`WitnessS`,
`act`: `sp = 0x8000`, code at `0x10000`), thread 1 the compiled `atomic_load` (`WitnessL`,
`actAt`: `sp = 0x6000`, code at `0x20000`), both on the CLIF location `(0, 8)`.

* `realizes_n`: for `n` compiled threads whose runs are private plain accesses then one shared
  access each (no `relXW`), with pairwise disjoint private sets that the shared accesses avoid,
  every execution of the realized prefixes with the initial locations `locsC` (the CLIF ones,
  holding every shared access's location) then the private events' (`privsN`), reads from the
  latest earlier write across threads (`wf_multi`) and any initial memory is `Realizes`d by CLIF
  threads from the `cs i` (`realizes_compiled`);
* `fB_iv`, `privS_or`, `privL_or`, `priv_disj`: the two activations' private sets are disjoint
  (frames `[0x7f10, 0x8000)`, `[0x5f10, 0x6000)`, code at `0x10000`, `0x20000`);
* **`realizes_mp`**: the store thread's run ends with its `stlr` (`relW`, 8 bytes at 0), the load
  thread's with its `ldar` (`acqR`, 8 bytes at 0); every execution of their realized prefixes on
  the CLIF location `(0, 8)` is `Realizes`d by two CLIF threads from `csS`, `csL`;
* `mp_reads`: when both prefixes are the whole runs, the `ldar` reads from the `stlr` in that
  execution (the store's write is the latest earlier write of location 0: the load thread's
  earlier events are private).

Checks by `native_decide` (witness only).
-/

namespace Concurrency.RealizeCompiled.WitnessMP

open Arm ArmThread Prog ClifThread ProgE2E Backend Backend.Proof VCodeThread PrepThread
  AllocThread ThreadRefine ArmAllocThread ThreadCompose E2E ArmInstFoot Code
  RealizeCompiled.Witness RealizeCompiled.WitnessL RealizeCompiled.WitnessS

/-! ## `n` compiled threads -/

/-- The Arm threads of the realized prefixes. -/
noncomputable def PAn (n : Nat) (RA : Nat → Backend.Proof.RL) (sA : Nat → ArmState)
    (ls : Nat → List Lab) (k : Nat → Nat) : Traces ProgE2E.AState AKind BVal :=
  ⟨n, fun i => conv (evTr ((ls i).take (k i))), fun i _ => ((RA i).step, sA i, none)⟩

/-- The locations of the private events of the threads. -/
def privsN (n : Nat) (lsP : Nat → List Lab) : List (Nat × Nat) :=
  (List.range n).flatMap fun i => ((lsP i).flatMap (·.evs)).map fun e => (e.addr.toNat, e.n)

theorem PAn_ev {n : Nat} {RA : Nat → Backend.Proof.RL} {sA : Nat → ArmState}
    {ls : Nat → List Lab} {k : Nat → Nat} {i j kk : Nat} {x : Prog.Ev AKind BVal}
    (hx : (PAn n RA sA ls k).evAt (.thr i j kk) = some x) :
    i < n ∧ ∃ l ∈ ls i, ∃ e' ∈ l.evs, x = ProgE2E.convEv e' := by
  by_cases hi : i < n
  · simp only [Traces.evAt, PAn, hi, ite_true] at hx
    obtain ⟨l, hl, e', he', rfl⟩ := evAt_conv_mem (p := (j, kk)) hx
    exact ⟨hi, l, List.mem_of_mem_take hl, e', he', rfl⟩
  · simp [Traces.evAt, PAn, hi] at hx

/-- **`Realizes` for `n` compiled threads, each a private plain prefix then one shared access**
(module doc), the realized prefixes covering the runs (`Covers`). -/
theorem realizes_n_cov {n : Nat} {RA : Nat → Backend.Proof.RL} {cs : Nat → Clif.State}
    {sA : Nat → ArmState} (hc : ∀ i < n, ∀ env p, Compiled env p (RA i) (cs i) (sA i))
    {lsP : Nat → List Lab} {e : Nat → Ev} {t' : Nat → ArmState × Mon}
    (hr : ∀ i < n, PRun Policy.arm (RA i).step (OkPriv (RA i)) (sA i, none)
      (lsP i ++ [⟨[e i], false⟩]) (t' i))
    (hevP : ∀ i < n, ∀ l ∈ lsP i, ∀ e' ∈ l.evs,
      PrivA (RA i) e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR))
    (he : ∀ i < n, (e i).k ≠ .relXW) (locsC : List (Nat × Nat))
    (hC : ∀ i < n, ∃ q : Nat, (locsC[q]?).map (fun c : Nat × Nat => c.1) = some (e i).addr.toNat)
    (hdP : ∀ i < n, ∀ j < n, j ≠ i → ∀ a, PrivA (RA i) a → ¬ PrivA (RA j) a)
    (hdE : ∀ i < n, ∀ j < n, j ≠ i → ¬ PrivA (RA j) (e i).addr.toNat)
    (env : Clif.Env) (p : Clif.Program) (M0 : Bytes) :
    ∃ k : Nat → Nat, (∀ i < n, k i ≤ (lsP i).length + 1) ∧
      (∀ i < n, Covers env p (RA i) (cs i) (lsP i ++ [⟨[e i], false⟩]) (k i)) ∧
      ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = n ∧
        (∀ i < n, PC.st i 0 = .run (cs i)) ∧ PC.Runs (CStep env p) ∧
        Realizes (PAn n RA sA (fun i => lsP i ++ [⟨[e i], false⟩]) k) (locsC ++ privsN n lsP) M0
          (latestW (PAn n RA sA (fun i => lsP i ++ [⟨[e i], false⟩]) k) (locsC ++ privsN n lsP))
          (coL (PAn n RA sA (fun i => lsP i ++ [⟨[e i], false⟩]) k) (locsC ++ privsN n lsP))
          (fun _ _ => False) PC locsC M0 φ (fun _ _ _ => True) := by
  obtain ⟨k, hk, hcv, hR⟩ := realizes_compiled_full (n := n) (env := env) (p := p) (RA := RA)
    (cs := cs) (sA := sA) (fun i hi => hc i hi env p) (mon := fun _ => none)
    (ls := fun i => lsP i ++ [⟨[e i], false⟩]) (t' := t') hr
  -- the events of the runs
  have hevs : ∀ i < n, ∀ l ∈ lsP i ++ [⟨[e i], false⟩], ∀ e' ∈ l.evs,
      e' = e i ∨ (∃ q : Nat, (privsN n lsP)[q]? = some (e'.addr.toNat, e'.n)) ∧
        PrivA (RA i) e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR) := by
    intro i hi l hl e' he'
    rcases List.mem_append.mp hl with hl | hl
    · refine .inr ⟨?_, hevP i hi l hl e' he'⟩
      exact List.mem_iff_getElem?.mp (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
        List.mem_map_of_mem (f := fun e : Ev => (e.addr.toNat, e.n))
          (List.mem_flatMap.mpr ⟨l, hl, he'⟩)⟩)
    · simp only [List.mem_singleton] at hl
      subst hl
      exact .inl (List.mem_singleton.mp he')
  have hkind : ∀ i < n, ∀ l ∈ lsP i ++ [⟨[e i], false⟩], ∀ e' ∈ l.evs, e'.k ≠ .relXW := by
    intro i hi l hl e' he'
    rcases hevs i hi l hl e' he' with rfl | ⟨-, -, h | h⟩
    · exact he i hi
    all_goals rw [h]; decide
  let P := PAn n RA sA (fun i => lsP i ++ [⟨[e i], false⟩]) k
  let locs := locsC ++ privsN n lsP
  have hwf := wf_multi (P := P) (locs := locs)
    (fun i hi => take_len_le (hr i hi) (k i)) (fun r hr' => by
      cases r with
      | init q =>
        simp only [X0, Traces.exec] at hr'
        split at hr' <;> cases hr'
      | thr i j kk =>
        simp only [X0, Traces.exec] at hr' ⊢
        split at hr'
        · rename_i x hx
          obtain ⟨hi, l, hl, e', he', rfl⟩ := PAn_ev hx
          rcases hevs i hi l hl e' he' with rfl | ⟨⟨q, hq⟩, -⟩
          · obtain ⟨q, hq⟩ := hC i hi
            obtain ⟨c, hc', hc1⟩ := Option.map_eq_some_iff.mp hq
            have hq' : q < locsC.length := (List.getElem?_eq_some_iff.mp hc').1
            refine ⟨.init q, by simp only [locs, List.length_append]; simp only [show q <
              locsC.length + (privsN n lsP).length by omega, ite_true], ?_, trivial⟩
            simp only [hx, locs, List.getElem?_append_left hq', hc', Option.getD_some,
              ProgE2E.convEv, hc1]
          · have hq2 := (List.getElem?_eq_some_iff.mp hq).1
            refine ⟨.init (locsC.length + q), by
              simp only [locs, List.length_append, show locsC.length + q <
                locsC.length + (privsN n lsP).length by omega, ite_true], ?_, trivial⟩
            simp only [hx, locs, List.getElem?_append_right (Nat.le_add_right _ _),
              Nat.add_sub_cancel_left, hq, Option.getD_some, ProgE2E.convEv]
        · cases hr')
  obtain ⟨PC, φ, h1, h2, h3, h4⟩ := hR P locs locsC M0 M0 (latestW P locs) (coL P locs)
    (fun _ _ => False) rfl (fun i hi => rfl) hwf
    (fun i hi a b => by
      refine ⟨False.elim, fun ⟨_, ⟨y, hy, hyk⟩, _⟩ => ?_⟩
      obtain ⟨l, hl, hyl⟩ := evAt_evTr_mem hy
      exact hkind i hi l (List.mem_of_mem_take hl) y hyl hyk)
    (List.prefix_append _ _)
    (fun q hq hq1 => by
      have hq2 : q - locsC.length < (privsN n lsP).length := by
        simp only [locs, List.length_append] at hq; omega
      have e1 : locs[q] = (privsN n lsP)[q - locsC.length] := List.getElem_append_right hq1
      obtain ⟨i, hi, hm⟩ := List.mem_flatMap.mp (List.getElem_mem hq2)
      obtain ⟨e', he', he'q⟩ := List.mem_map.mp hm
      obtain ⟨l, hl, he'l⟩ := List.mem_flatMap.mp he'
      have hi' := List.mem_range.mp hi
      refine ⟨i, hi', ?_⟩
      rw [e1, ← he'q]
      exact (hevP i hi' l hl e' he'l).1)
    (fun q h => rfl)
    (fun i hi j hj hne q x hx hF => by
      obtain ⟨l, hl, e', he', rfl⟩ := evAt_conv_mem hx
      rcases hevs i hi l (List.mem_of_mem_take hl) e' he' with rfl | ⟨-, hP, -⟩
      · exact hdE i hi j hj hne
      · exact hdP i hi j hj hne _ hP)
  exact ⟨k, fun i hi => by have := hk i hi; simpa using this, hcv, PC, φ, h1, h2, h3, h4⟩

/-- **`Realizes` for `n` compiled threads, each a private plain prefix then one shared access**
(`realizes_n_cov` without the coverage). -/
theorem realizes_n {n : Nat} {RA : Nat → Backend.Proof.RL} {cs : Nat → Clif.State}
    {sA : Nat → ArmState} (hc : ∀ i < n, ∀ env p, Compiled env p (RA i) (cs i) (sA i))
    {lsP : Nat → List Lab} {e : Nat → Ev} {t' : Nat → ArmState × Mon}
    (hr : ∀ i < n, PRun Policy.arm (RA i).step (OkPriv (RA i)) (sA i, none)
      (lsP i ++ [⟨[e i], false⟩]) (t' i))
    (hevP : ∀ i < n, ∀ l ∈ lsP i, ∀ e' ∈ l.evs,
      PrivA (RA i) e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR))
    (he : ∀ i < n, (e i).k ≠ .relXW) (locsC : List (Nat × Nat))
    (hC : ∀ i < n, ∃ q : Nat, (locsC[q]?).map (fun c : Nat × Nat => c.1) = some (e i).addr.toNat)
    (hdP : ∀ i < n, ∀ j < n, j ≠ i → ∀ a, PrivA (RA i) a → ¬ PrivA (RA j) a)
    (hdE : ∀ i < n, ∀ j < n, j ≠ i → ¬ PrivA (RA j) (e i).addr.toNat)
    (env : Clif.Env) (p : Clif.Program) (M0 : Bytes) :
    ∃ k : Nat → Nat, (∀ i < n, k i ≤ (lsP i).length + 1) ∧
      ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = n ∧
        (∀ i < n, PC.st i 0 = .run (cs i)) ∧ PC.Runs (CStep env p) ∧
        Realizes (PAn n RA sA (fun i => lsP i ++ [⟨[e i], false⟩]) k) (locsC ++ privsN n lsP) M0
          (latestW (PAn n RA sA (fun i => lsP i ++ [⟨[e i], false⟩]) k) (locsC ++ privsN n lsP))
          (coL (PAn n RA sA (fun i => lsP i ++ [⟨[e i], false⟩]) k) (locsC ++ privsN n lsP))
          (fun _ _ => False) PC locsC M0 φ (fun _ _ _ => True) := by
  obtain ⟨k, hk, -, h⟩ := realizes_n_cov hc hr hevP he locsC hC hdP hdE env p M0
  exact ⟨k, hk, h⟩

/-! ## The two activations' private sets -/

theorem fB_iv {R : Backend.Proof.RL} {x : BitVec 64} (h : fB R x = true)
    (hprog : R.s0.program = R.fb.program R.base) :
    (x - (spv R.s0 - BitVec.ofNat 64 (frameDrop R.af))).toNat < max R.fr.size (frameDrop R.af) ∨
      ∃ j < R.fb.words.size, (x - (R.base + BitVec.ofNat 64 (4 * j))).toNat < 4 := by
  simp only [fB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with (⟨-, h⟩ | ⟨-, h⟩) | h
  · exact .inl (by omega)
  · exact .inl (by omega)
  · right
    obtain ⟨p, hp, hd⟩ := List.any_eq_true.mp h
    have hd' := of_decide_eq_true hd
    rw [hprog] at hp
    simp only [FnBin.program] at hp
    obtain ⟨j, hj, he⟩ := ArmAllocThread.Witness.wordsAt_addr hp
    refine ⟨j, by simpa using hj, ?_⟩
    rw [he, Nat.zero_add] at hd'
    exact hd'

theorem numsS : spv RAS.s0 - BitVec.ofNat 64 (frameDrop RAS.af) = 32528#64 ∧
    max RAS.fr.size (frameDrop RAS.af) = 240 ∧ RAS.fb.words.size = 47 ∧ RAS.base = 0x10000#64 := by
  native_decide

theorem numsL : spv RAL.s0 - BitVec.ofNat 64 (frameDrop RAL.af) = 24336#64 ∧
    max RAL.fr.size (frameDrop RAL.af) = 240 ∧ RAL.fb.words.size = 47 ∧ RAL.base = 0x20000#64 := by
  native_decide

theorem privS_or {x : BitVec 64} (h : RAS.F x) :
    (32528 ≤ x.toNat ∧ x.toNat < 32768) ∨ (65536 ≤ x.toNat ∧ x.toNat < 65536 + 4 * 47 + 4) := by
  have hb := fB_iv (fB_of rfl (fun _ h => h) h) wfRS.prog0
  obtain ⟨h1, h2, h3, h4⟩ := numsS
  rw [h1, h2, h3, h4] at hb
  rcases hb with hb | ⟨j, hj, hd⟩
  · left; bv_omega
  · right; bv_omega

theorem privL_or {x : BitVec 64} (h : RAL.F x) :
    (24336 ≤ x.toNat ∧ x.toNat < 24576) ∨ (131072 ≤ x.toNat ∧ x.toNat < 131072 + 4 * 47 + 4) := by
  have hb := fB_iv (fB_of rfl (fun _ h => h) h) wfRL.prog0
  obtain ⟨h1, h2, h3, h4⟩ := numsL
  rw [h1, h2, h3, h4] at hb
  rcases hb with hb | ⟨j, hj, hd⟩
  · left; bv_omega
  · right; bv_omega

/-- **The two activations' private sets are disjoint.** -/
theorem priv_disj {a : Nat} (hS : PrivA RAS a) (hL : PrivA RAL a) : False := by
  have h1 := privS_or hS
  have h2 := privL_or hL
  omega

/-! ## Message passing -/

/-- The activations of the two threads. -/
abbrev RA2 (i : Nat) : Backend.Proof.RL := if i = 0 then RAS else RAL

/-- The CLIF entry states of the two threads. -/
def cs2 (i : Nat) : Clif.State := if i = 0 then csS else csL

/-- **`Realizes` for the compiled `atomic_store` and `atomic_load` as two threads** (module
doc): thread 0's run ends with its `stlr` of 8 bytes at 0, thread 1's with its `ldar` of 8 bytes
at 0; every execution of their realized prefixes on the CLIF location `(0, 8)` (reads from the
latest earlier write, across the threads) is `Realizes`d by CLIF threads from `csS`, `csL`. -/
theorem realizes_mp : ∃ (sA : Nat → ArmState) (lsP : Nat → List Lab) (e : Nat → Ev)
    (t' : Nat → ArmState × Mon),
    (∀ i < 2, PRun Policy.arm (RA2 i).step (OkPriv (RA2 i)) (sA i, none)
      (lsP i ++ [⟨[e i], false⟩]) (t' i)) ∧
    (e 0).k = .relW ∧ (e 1).k = .acqR ∧ (e 0).addr = 0 ∧ (e 1).addr = 0 ∧ (e 0).n = 8 ∧
    (e 1).n = 8 ∧
    (∀ i < 2, ∀ l ∈ lsP i, ∀ e' ∈ l.evs, PrivA (RA2 i) e'.addr.toNat ∧
      (e'.k = .plainW ∨ e'.k = .plainR)) ∧
    ∀ (env : Clif.Env) (p : Clif.Program) (M0 : Bytes), ∃ k : Nat → Nat,
      (∀ i < 2, k i ≤ (lsP i).length + 1) ∧
      ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 2 ∧
        PC.st 0 0 = .run csS ∧ PC.st 1 0 = .run csL ∧ PC.Runs (CStep env p) ∧
        Realizes (PAn 2 RA2 sA (fun i => lsP i ++ [⟨[e i], false⟩]) k) ([(0, 8)] ++ privsN 2 lsP) M0
          (latestW (PAn 2 RA2 sA (fun i => lsP i ++ [⟨[e i], false⟩]) k) ([(0, 8)] ++ privsN 2 lsP))
          (coL (PAn 2 RA2 sA (fun i => lsP i ++ [⟨[e i], false⟩]) k) ([(0, 8)] ++ privsN 2 lsP))
          (fun _ _ => False) PC [(0, 8)] M0 φ (fun _ _ _ => True) := by
  obtain ⟨nS, lsS, eS, tS, hcS, hrS, hkS, hnS, haS, hevS⟩ := run_store
  obtain ⟨nL, lsL, eL, tL, hcL, hrL, hkL, hnL, haL, hevL⟩ := run_load
  let sA : Nat → ArmState := fun i => if i = 0 then iterN RAS.step nS RAS.s0 else iterN RAL.step nL RAL.s0
  let lsP : Nat → List Lab := fun i => if i = 0 then lsS else lsL
  let e : Nat → Ev := fun i => if i = 0 then eS else eL
  let t' : Nat → ArmState × Mon := fun i => if i = 0 then tS else tL
  have two : ∀ i < 2, i = 0 ∨ i = 1 := fun i hi => by omega
  have hr : ∀ i < 2, PRun Policy.arm (RA2 i).step (OkPriv (RA2 i)) (sA i, none)
      (lsP i ++ [⟨[e i], false⟩]) (t' i) := fun i hi => by
    rcases two i hi with rfl | rfl
    · exact hrS
    · exact hrL
  have hevP : ∀ i < 2, ∀ l ∈ lsP i, ∀ e' ∈ l.evs, PrivA (RA2 i) e'.addr.toNat ∧
      (e'.k = .plainW ∨ e'.k = .plainR) := fun i hi => by
    rcases two i hi with rfl | rfl
    · exact hevS
    · exact hevL
  refine ⟨sA, lsP, e, t', hr, hkS, hkL, haS, haL, hnS, hnL, hevP, fun env p M0 => ?_⟩
  have hz : ∀ i < 2, (e i).addr = 0 := fun i hi => by
    rcases two i hi with rfl | rfl
    · exact haS
    · exact haL
  obtain ⟨k, hk, PC, φ, h1, h2, h3, h4⟩ := realizes_n (n := 2) (RA := RA2) (cs := cs2) (sA := sA)
    (fun i hi env p => by
      rcases two i hi with rfl | rfl
      · exact hcS env p
      · exact hcL env p) hr hevP
    (fun i hi => by
      rcases two i hi with rfl | rfl
      · show eS.k ≠ _; rw [hkS]; decide
      · show eL.k ≠ _; rw [hkL]; decide)
    [(0, 8)] (fun i hi => ⟨0, by simp [hz i hi]⟩)
    (fun i hi j hj hne a hPi hPj => by
      rcases two i hi with rfl | rfl <;> rcases two j hj with rfl | rfl
      · exact hne rfl
      · exact priv_disj hPi hPj
      · exact priv_disj hPj hPi
      · exact hne rfl)
    (fun i hi j hj hne hP => by
      rw [hz i hi] at hP
      rcases two j hj with rfl | rfl
      · exact notF_lowS 0 (by decide) hP
      · exact notF_low 0 (by decide) hP)
    env p M0
  exact ⟨k, hk, PC, φ, h1, h2 0 (by decide), h2 1 (by decide), h3, h4⟩

/-- **`Realizes` for the compiled `atomic_store` and `atomic_load` as two threads, on the whole
runs** (T2j): `realizes_mp` with both realized prefixes the whole runs (`WitnessL.one_full`: the
CLIF threads from `csS` and `csL` step with their access and cannot stop at their start), so
`mp_reads` applies: the `ldar` reads from the `stlr`. -/
theorem realizes_mp_full : ∃ (sA : Nat → ArmState) (lsP : Nat → List Lab) (e : Nat → Ev)
    (t' : Nat → ArmState × Mon),
    (∀ i < 2, PRun Policy.arm (RA2 i).step (OkPriv (RA2 i)) (sA i, none)
      (lsP i ++ [⟨[e i], false⟩]) (t' i)) ∧
    (e 0).k = .relW ∧ (e 1).k = .acqR ∧ (e 0).addr = 0 ∧ (e 1).addr = 0 ∧ (e 0).n = 8 ∧
    (e 1).n = 8 ∧
    (∀ i < 2, ∀ l ∈ lsP i, ∀ e' ∈ l.evs, PrivA (RA2 i) e'.addr.toNat ∧
      (e'.k = .plainW ∨ e'.k = .plainR)) ∧
    ∀ (env : Clif.Env) (p : Clif.Program) (M0 : Bytes), ∃ k : Nat → Nat,
      (∀ i < 2, k i = (lsP i).length + 1) ∧
      ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 2 ∧
        PC.st 0 0 = .run csS ∧ PC.st 1 0 = .run csL ∧ PC.Runs (CStep env p) ∧
        Realizes (PAn 2 RA2 sA (fun i => lsP i ++ [⟨[e i], false⟩]) k) ([(0, 8)] ++ privsN 2 lsP) M0
          (latestW (PAn 2 RA2 sA (fun i => lsP i ++ [⟨[e i], false⟩]) k) ([(0, 8)] ++ privsN 2 lsP))
          (coL (PAn 2 RA2 sA (fun i => lsP i ++ [⟨[e i], false⟩]) k) ([(0, 8)] ++ privsN 2 lsP))
          (fun _ _ => False) PC [(0, 8)] M0 φ (fun _ _ _ => True) := by
  obtain ⟨nS, lsS, eS, tS, hcS, hrS, hkS, hnS, haS, hevS⟩ := run_store
  obtain ⟨nL, lsL, eL, tL, hcL, hrL, hkL, hnL, haL, hevL⟩ := run_load
  let sA : Nat → ArmState := fun i => if i = 0 then iterN RAS.step nS RAS.s0 else iterN RAL.step nL RAL.s0
  let lsP : Nat → List Lab := fun i => if i = 0 then lsS else lsL
  let e : Nat → Ev := fun i => if i = 0 then eS else eL
  let t' : Nat → ArmState × Mon := fun i => if i = 0 then tS else tL
  have two : ∀ i < 2, i = 0 ∨ i = 1 := fun i hi => by omega
  have hr : ∀ i < 2, PRun Policy.arm (RA2 i).step (OkPriv (RA2 i)) (sA i, none)
      (lsP i ++ [⟨[e i], false⟩]) (t' i) := fun i hi => by
    rcases two i hi with rfl | rfl
    · exact hrS
    · exact hrL
  have hevP : ∀ i < 2, ∀ l ∈ lsP i, ∀ e' ∈ l.evs, PrivA (RA2 i) e'.addr.toNat ∧
      (e'.k = .plainW ∨ e'.k = .plainR) := fun i hi => by
    rcases two i hi with rfl | rfl
    · exact hevS
    · exact hevL
  refine ⟨sA, lsP, e, t', hr, hkS, hkL, haS, haL, hnS, hnL, hevP, fun env p M0 => ?_⟩
  have hz : ∀ i < 2, (e i).addr = 0 := fun i hi => by
    rcases two i hi with rfl | rfl
    · exact haS
    · exact haL
  obtain ⟨k, hk, hcv, PC, φ, h1, h2, h3, h4⟩ := realizes_n_cov (n := 2) (RA := RA2) (cs := cs2)
    (sA := sA)
    (fun i hi env p => by
      rcases two i hi with rfl | rfl
      · exact hcS env p
      · exact hcL env p) hr hevP
    (fun i hi => by
      rcases two i hi with rfl | rfl
      · show eS.k ≠ _; rw [hkS]; decide
      · show eL.k ≠ _; rw [hkL]; decide)
    [(0, 8)] (fun i hi => ⟨0, by simp [hz i hi]⟩)
    (fun i hi j hj hne a hPi hPj => by
      rcases two i hi with rfl | rfl <;> rcases two j hj with rfl | rfl
      · exact hne rfl
      · exact priv_disj hPi hPj
      · exact priv_disj hPj hPi
      · exact hne rfl)
    (fun i hi j hj hne hP => by
      rw [hz i hi] at hP
      rcases two j hj with rfl | rfl
      · exact notF_lowS 0 (by decide) hP
      · exact notF_low 0 (by decide) hP)
    env p M0
  refine ⟨k, fun i hi => ?_, PC, φ, h1, h2 0 (by decide), h2 1 (by decide), h3, h4⟩
  rcases two i hi with rfl | rfl
  · exact one_full (hcv 0 (by decide)) (hk 0 (by decide)) (fun l hl e' he' => (hevS l hl e' he').1)
      (notStop_csS env p) (fun _ _ hs => nonFence_one shapeS1 (by decide) hs)
  · exact one_full (hcv 1 (by decide)) (hk 1 (by decide)) (fun l hl e' he' => (hevL l hl e' he').1)
      (notStop_csL env p) (fun _ _ hs => nonFence_one shapeL1 (by decide) hs)

theorem evAt_PAn {n : Nat} {RA : Nat → Backend.Proof.RL} {sA : Nat → ArmState}
    {ls : Nat → List Lab} {k : Nat → Nat} {i : Nat} (hi : i < n) (j kk : Nat) :
    (PAn n RA sA ls k).evAt (.thr i j kk) =
      (((ls i).take (k i))[j]?).bind (fun l => (l.evs.map ProgE2E.convEv)[kk]?) := by
  simp only [Traces.evAt, PAn, hi, ite_true, conv, evTr, List.map_map, List.getElem?_map]
  cases ((ls i).take (k i))[j]? <;> simp

/-- **The `ldar` reads from the `stlr`** in the execution of `realizes_mp` when both realized
prefixes are the whole runs: the store's write is the latest earlier write of location 0 (the
load thread's earlier events are private, at nonzero addresses). -/
theorem mp_reads {sA : Nat → ArmState} {lsP : Nat → List Lab} {e : Nat → Ev}
    (hk0' : (e 0).k = .relW) (hk1' : (e 1).k = .acqR) (ha0 : (e 0).addr = 0) (ha1 : (e 1).addr = 0)
    (hev1 : ∀ l ∈ lsP 1, ∀ e' ∈ l.evs, PrivA RAL e'.addr.toNat) {k : Nat → Nat}
    (hk0 : k 0 = (lsP 0).length + 1) (hk1 : k 1 = (lsP 1).length + 1) (locs : List (Nat × Nat)) :
    latestW (PAn 2 RA2 sA (fun i => lsP i ++ [⟨[e i], false⟩]) k) locs
      (.thr 0 (lsP 0).length 0) (.thr 1 (lsP 1).length 0) := by
  have hx : ∀ i < 2, k i = (lsP i).length + 1 →
      (PAn 2 RA2 sA (fun i => lsP i ++ [⟨[e i], false⟩]) k).evAt (.thr i (lsP i).length 0) =
        some (ProgE2E.convEv (e i)) := fun i hi hki => by
    rw [evAt_PAn hi, hki]
    simp
  have hx0 := hx 0 (by decide) hk0
  have hx1 := hx 1 (by decide) hk1
  refine ⟨?_, ?_, ?_, by simp [PEvLt], fun w' hw' hl' h1 h2 => ?_⟩
  · simp only [X0, Traces.exec, hx1, ProgE2E.convEv, hk1']; rfl
  · simp only [X0, Traces.exec, hx0, ProgE2E.convEv, hk0']; rfl
  · simp only [X0, Traces.exec, hx0, hx1, ProgE2E.convEv, ha0, ha1]
  cases w' with
  | init q => simp [PEvLt] at h1
  | thr i j kk =>
    simp only [X0, Traces.exec] at hw' hl'
    split at hw'
    · rename_i x hxx
      simp only [hxx, hx1, ProgE2E.convEv, ha1] at hl'
      simp only [PEvLt] at h1 h2
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl
      · -- thread 0 after its `stlr`: no event
        rw [evAt_PAn (by decide), hk0] at hxx
        rw [List.take_of_length_le (by simp)] at hxx
        rcases h1 with h1 | ⟨-, h1 | ⟨rfl, h1⟩⟩
        · omega
        · rw [List.getElem?_eq_none (by simp; omega)] at hxx; cases hxx
        · simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
            List.getElem?_cons_zero, List.length_cons, List.length_nil, Option.bind_some,
            List.map_cons, List.map_nil] at hxx
          rw [List.getElem?_eq_none (by simp; omega)] at hxx; cases hxx
      · -- thread 1 before its `ldar`: a private event
        rw [evAt_PAn (by decide), hk1] at hxx
        rw [List.take_of_length_le (by simp)] at hxx
        have hj : j < (lsP 1).length := by omega
        rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj, Option.bind_some,
          List.getElem?_map] at hxx
        obtain ⟨e', he', rfl⟩ : ∃ e' ∈ ((lsP 1)[j]).evs, x = ProgE2E.convEv e' := by
          cases h : ((lsP 1)[j]).evs[kk]? with
          | none => rw [h] at hxx; cases hxx
          | some e' =>
            rw [h] at hxx
            exact ⟨e', List.mem_of_getElem? h, (Option.some.inj hxx).symm⟩
        have hP := hev1 _ (List.getElem_mem hj) e' he'
        simp only [ProgE2E.convEv] at hl'
        rw [hl'] at hP
        exact notF_low 0 (by decide) hP
    · cases hw'

end Concurrency.RealizeCompiled.WitnessMP

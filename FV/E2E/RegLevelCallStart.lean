import FV.E2E.RegLevelCorrectPRS

/-!
# Call states are segment starts (SEM1 #537, executable level; the body `sp` at call states)

`realizes_allC` realises each allocated-code step by a machine segment with `opCalls` call states
(`RL.CallSt`), but its trace (`RL.GoodX`) does not say where they are. They are always the
segment's **first** state: only a `call`/`try_call` item's segment has a call state, and its
first state (where the simulation relation `Q` holds) is at the item's `bl`/`blr`
(`RL.callSt_of_q_call`). There `StRel.sp` gives the body `sp`, so the per-state trace can carry
`spOf u = R.spB` at every call state, and the counted run can carry the call contract's
precondition (`OnCall … n u` for the call count `n` of `u`) at every call state.

* `countIn_one_le`, `countIn_two_le` (generic counting);
* `opCalls_pos`: an item with a call is a `call`/`try_call` instruction;
* **`RL.callSt_of_q_call`**: a `Q`-state at a call item is a call state;
* `RealizesCP0`: `RealizesCP` whose segments' `C`-states are their first;
* **`realizes_allC0`**: `realizes_allC_sp`'s premises give `RealizesCP0` with the trace
  `R.GoodX u ∧ (R.CallSt u → spOf u = R.spB)`;
* **`RealizesCP0.countedRun`**: `RealizesCP.countedRun` whose trace also records, at a `C`-state,
  the precondition of the index of its segment (`∃ m, T m u ∧ (C u → P m u)`).
-/

namespace Backend.Proof

open Backend E2E

section
variable {S : Type}

/-- **A count over a nonempty run is at least the first state's.** -/
theorem countIn_one_le {C : S → Prop} {step : S → S} {s : S} {n : Nat} (hn : 0 < n) (hc : C s) :
    1 ≤ countIn C step s n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = 1 + n' := ⟨n - 1, by omega⟩
  rw [countIn_add]
  have : countIn C step s 1 = 1 := by
    show 0 + ind (C s) = 1
    simp [ind, hc]
  omega

/-- **Two `C`-states, the first and one at `i > 0`: the count is at least two.** -/
theorem countIn_two_le {C : S → Prop} {step : S → S} {s : S} {n i : Nat} (hc : C s)
    (hi0 : 0 < i) (hi : i < n) (hci : C (iterN step i s)) : 2 ≤ countIn C step s n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = i + n' := ⟨n - i, by omega⟩
  rw [countIn_add]
  have h1 := countIn_one_le (step := step) hi0 hc
  have h2 := countIn_one_le (step := step) (s := iterN step i s) (n := n') (by omega) hci
  omega

end

section
variable {V W : Type} {vc : VCode} {rf : RFunc} {keep : Reg → V → V}

/-- **An item with a call** is a `call`/`try_call` instruction of the block. -/
theorem opCalls_pos {c : MConf V W} (h : 0 < opCalls vc c) :
    ∃ b k allocs its m w vb i, c = .run ⟨b, .op k allocs :: its, m, w⟩ ∧
      vc.blocks[b]? = some vb ∧ vb.insts[k]? = some i ∧ i.isCallI = true := by
  unfold opCalls at h
  split at h
  · rename_i b k allocs its m w
    split at h
    · rename_i vb hvb
      split at h
      · rename_i i hi
        by_cases hc : i.isCallI = true
        · exact ⟨b, k, allocs, its, m, w, vb, i, rfl, hvb, hi, hc⟩
        · simp [hc] at h
      · omega
    · omega
  · omega

/-- **`RealizesCP` whose segments' `C`-states are their first states.** -/
def RealizesCP0 {S : Type} (vc : VCode) (rf : RFunc) (sem : ISem V W) (keep : Reg → V → V)
    (step : S → S) (Q : S → MConf V W → Prop) (T : S → Prop) (C : S → Prop) (P : S → Prop) :
    Prop :=
  ∀ s c c', Q s c → P s → MStep vc sem keep rf c c' →
    ∃ n c'', MStep vc sem keep rf c c'' ∧ Q (iterN step n s) c'' ∧ (∀ i < n, T (iterN step i s)) ∧
      countIn C step s n = opCalls vc c ∧ ∀ i < n, C (iterN step i s) → i = 0

/-- **The counted run with the segment's precondition at its `C`-states**: `RealizesCP.countedRun`
for `RealizesCP0` at every index `n` (trace `T n`), whose trace also says that a `C`-state has
the precondition `P m` and the trace `T m` of one index `m` (its segment's, i.e. its count). -/
theorem RealizesCP0.countedRun {S : Type} {sem : Nat → ISem V W} {step : S → S}
    {Q : S → MConf V W → Prop} {T : Nat → S → Prop} {C : S → Prop} {P : Nat → S → Prop}
    {s0 : S}
    (h : ∀ n, RealizesCP0 vc rf (sem n) keep step Q (T n) C (P n))
    (hP : ∀ i, P (countIn C step s0 i) (iterN step i s0)) :
    Realizes vc rf (ISem.counted sem) keep (stepC C step)
      (fun p c => Q p.1 (c.mapW Prod.fst) ∧ p.2 = c.world.2 ∧
        ∃ i, p = iterN (stepC C step) i (s0, 0))
      (fun p => ∃ m, T m p.1 ∧ (C p.1 → P m p.1)) := by
  rintro ⟨s, k⟩ c c' ⟨hq, hk, i, hi⟩ hs
  rw [iterN_stepC] at hi
  simp only [Prod.mk.injEq, Nat.zero_add] at hi
  obtain ⟨rfl, rfl⟩ := hi
  cases c with
  | run vs =>
    obtain ⟨b, its, m, ⟨w, n⟩⟩ := vs
    simp only [MConf.world] at hk
    subst hk
    obtain ⟨j, d, hd, hq', ht, hcnt, hst⟩ :=
      h (countIn C step s0 i) _ _ _ hq (hP i) (MStep.counted_proj hs)
    obtain ⟨c'', rfl, hc''⟩ := MStep.counted_lift hd
    refine ⟨j, c'', hc'', ⟨?_, ?_, i + j, ?_⟩, fun i' hi' => ?_⟩
    · rw [iterN_stepC]; exact hq'
    · rw [iterN_stepC, MStep.counted_ctr hc'', hcnt, opCalls_mapW]
      rfl
    · simp only [iterN_add, iterN_stepC, Nat.zero_add]
    · rw [iterN_stepC]
      refine ⟨countIn C step s0 i, ht i' hi', fun hc => ?_⟩
      obtain rfl := hst i' hi' hc
      exact hP i
  | ret => cases hs
  | halt => cases hs

end

/-- **A `Q`-state at a call item is a call state**: the item's allocated `call`/`try_call` starts
with its `bl`/`blr`, at the state's pc (`callAt_of_q`). -/
theorem RL.callSt_of_q_call {R : RL} {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {i : MInst}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hc : i.isCallI = true) :
    R.CallSt s := by
  obtain ⟨-, -, -, regs, i', -, -, -, -, -, -, -, -, -, -, -, hal, -, -, hasg, -⟩ := q_op hq hvb hi
  have hcall : ∀ regs i', i.assign regs = .ok i' → (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us) ∧
      ∃ x ls, (∀ ps, i'.lines R.ctx ps = .ok (.ins x none :: ls, ps)) ∧
        ((∃ n, x = .bl n) ∨ (∃ r, x = .blr r)) ∧ i'.callInsn? = some x := by
    cases i with
    | call info => exact call_hcall
    | tryCall info ti => exact tryCall_hcall
    | _ => simp [MInst.isCallI] at hc
  obtain ⟨j, x, t, hj, hxi, hpc⟩ := callAt_of_q hq hvb hi hcall regs i' hal hasg
  obtain ⟨-, -, x', -, -, hx', hxi'⟩ := hcall regs i' hasg
  rw [hxi] at hxi'
  cases hxi'
  exact ⟨j, x, t, hj, hx', hpc⟩

/-- **`realizes_allC_sp` with the call states at the segments' starts** (module doc): every call
state of a realised segment is its first state, so it has the body `sp`. -/
theorem realizes_allC0 {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (hC : CalleeOkGP (fun u => P u ∧ spOf u = R.spB) R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H
      R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP (fun u => P u ∧ spOf u = R.spB) R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H
        R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    RealizesCP0 R.vc R.rf R.sem ckeep R.step (QA R)
      (fun u => R.GoodX u ∧ (R.CallSt u → spOf u = R.spB)) R.CallSt P := by
  intro s c c' hqa hP h
  obtain ⟨n, c'', hm, hq', ht, hcnt⟩ := realizes_allC_sp hR hC hT hTls hcov s c c' hqa hP h
  have hsp : spOf s = R.spB := by
    cases c with
    | run st => obtain ⟨b, its, m, w⟩ := st; obtain ⟨mt, hq⟩ := qa_q hqa; exact (q_stRel hq).sp
    | _ => cases h
  have hstart : ∀ i < n, R.CallSt (iterN R.step i s) → i = 0 := by
    intro i hi hci
    refine Classical.byContradiction fun hne => ?_
    have h1 : 1 ≤ countIn R.CallSt R.step s n := by
      obtain ⟨n', rfl⟩ : ∃ n', n = i + n' := ⟨n - i, by omega⟩
      rw [countIn_add]
      have := countIn_one_le (step := R.step) (s := iterN R.step i s) (n := n') (by omega) hci
      omega
    rw [hcnt] at h1
    obtain ⟨b, k, allocs, its, m, w, vb, ins, rfl, hvb, hi', hcI⟩ := opCalls_pos (vc := R.vc) h1
    have hcs := RL.callSt_of_q_call
      (qa_op hqa hvb hi' (fun us e => by subst e; simp [MInst.isCallI] at hcI)).1 hvb hi' hcI
    have h2 := countIn_two_le hcs (Nat.pos_of_ne_zero hne) hi hci
    rw [hcnt] at h2
    simp [opCalls, hvb, hi', hcI] at h2
  exact ⟨n, c'', hm, hq', fun i hi => ⟨ht i hi, fun hci => by
    obtain rfl := hstart i hi hci; exact hsp⟩, hcnt, hstart⟩

end Backend.Proof

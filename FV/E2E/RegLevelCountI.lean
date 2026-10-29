module

public import FV.E2E.RegLevelCorrectI
public import FV.E2E.LinkArmProphThm

@[expose] public section

/-!
# The counter of the counted run against the machine's calls (SEM1 step 2, `docs/plans/uninit.md` §5.4)

The prophecy of call number `n` is the machine memory at the run's `n`-th call state
(`E2E.callsBefore`, `E2E.ProphOk`). To use it, the counted VCode run's counter must be the
number of call states the machine has passed. This file states what each realised item has to
give for that, and lifts it to the counted semantics:

* `countIn C step s n`: the states among the first `n` of the run of `step` from `s` satisfying
  `C` (`countIn_succ'`: the first one, then the rest); `stepC C step`: the machine with the count
  of the `C` states it has passed (`iterN_stepC`); `callsBefore_eq_countIn`: the machine's
  `callsBefore` is `countIn` of its call states;
* `opCalls vc c`: `1` when the next item of the allocated-code configuration `c` is a call
  (`MInst.isCallI`), else `0`; `MConf.world`; `MStep.counted_ctr`: a counted step adds `opCalls`
  to the counter;
* `RealizesC … C`: `Realizes` where each realised segment passes `opCalls` states satisfying `C`
  (the obligation of the `realizes_*` cases with `C` the call states, next item);
  `RealizesC.toRealizes`;
* `RealizesC.counted`: from `RealizesC` at every index, the machine with the count realises the
  counted semantics under `Q` of the first components **with the counter equal to the count**.
-/

namespace Backend.Proof

open Backend E2E

section
variable {S : Type}

open Classical in
/-- `1` if `p` holds, else `0`. -/
noncomputable def ind (p : Prop) : Nat := if p then 1 else 0

/-- The states among the first `n` of the run of `step` from `s` satisfying `C`. -/
noncomputable def countIn (C : S → Prop) (step : S → S) (s : S) : Nat → Nat
  | 0 => 0
  | n + 1 => countIn C step s n + ind (C (iterN step n s))

theorem countIn_succ' (C : S → Prop) (step : S → S) :
    ∀ (n : Nat) (s : S), countIn C step s (n + 1) = ind (C s) + countIn C step (step s) n
  | 0, s => by show 0 + ind (C s) = ind (C s) + 0; omega
  | n + 1, s => by
    show countIn C step s (n + 1) + ind (C (iterN step n (step s))) =
      ind (C s) + (countIn C step (step s) n + ind (C (iterN step n (step s))))
    rw [countIn_succ' C step n s]
    omega

/-- The machine with the count of the `C` states it has passed. -/
noncomputable def stepC (C : S → Prop) (step : S → S) (p : S × Nat) : S × Nat :=
  (step p.1, p.2 + ind (C p.1))

theorem iterN_stepC (C : S → Prop) (step : S → S) :
    ∀ (n : Nat) (s : S) (k : Nat),
      iterN (stepC C step) n (s, k) = (iterN step n s, k + countIn C step s n)
  | 0, s, k => rfl
  | n + 1, s, k => by
    show iterN (stepC C step) n (step s, k + ind (C s)) = (iterN step n (step s), _)
    rw [iterN_stepC C step n, countIn_succ']
    simp only [Prod.mk.injEq, true_and]
    omega

end

/-- **The machine's calls before step `i` are its call states among the first `i`.** -/
theorem callsBefore_eq_countIn (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm) (base : BitVec 64)
    (s : Arm.ArmState) : ∀ i, callsBefore Mm fa base s i =
      countIn (fun u => CallPc fa base (Arm.r .PC u)) Mm s i
  | 0 => rfl
  | i + 1 => by
    show callsBefore Mm fa base s i + _ = countIn _ Mm s i + ind _
    rw [callsBefore_eq_countIn Mm fa base s i, runX_eq]
    rfl

section
variable {V W : Type} {vc : VCode} {rf : RFunc} {keep : Reg → V → V}

/-- The world of a configuration. -/
def MConf.world : MConf V W → W
  | .run s => s.w
  | .ret _ _ w => w
  | .halt w => w

/-- The calls of the next item of `c`: `1` at a call instruction, else `0`. -/
def opCalls (vc : VCode) : MConf V W → Nat
  | .run ⟨b, .op k _ :: _, _, _⟩ => match vc.blocks[b]? with
    | some vb => (match vb.insts[k]? with
      | some i => if i.isCallI then 1 else 0
      | none => 0)
    | none => 0
  | _ => 0

theorem opCalls_mapW {W' : Type} (π : W → W') (c : MConf V W) :
    opCalls vc (c.mapW π) = opCalls vc c := by
  cases c with
  | run s =>
    obtain ⟨b, its, m, w⟩ := s
    cases its with
    | nil => rfl
    | cons it its => cases it <;> rfl
  | ret => rfl
  | halt => rfl

theorem MNext.world {b k n : Nat} {i : MInst} {uses : List V} {its : List RItem} {m : Loc → V}
    {w : W} {ctl : Ctl} {c : MConf V W} (h : MNext vc rf b k n i uses its m w ctl c) :
    c.world = w := by
  cases h <;> rfl

/-- **A counted step adds the calls of the item to the counter.** -/
theorem MStep.counted_ctr {sem : Nat → ISem V W} {c c' : MConf V (W × Nat)}
    (h : MStep vc (ISem.counted sem) keep rf c c') : c'.world.2 = c.world.2 + opCalls vc c := by
  cases h with
  | move => rfl
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hb hi ho ha hs hl hh hc hn =>
    rw [MNext.world hn, (ISem.counted_some hs).2]
    simp only [MConf.world, opCalls, hb, hi]
    split <;> simp

/-- **`Realizes` counting the `C` states of each realised segment**: a segment realising an
allocated-code step from `c` passes `opCalls vc c` of them. -/
def RealizesC {S : Type} (vc : VCode) (rf : RFunc) (sem : ISem V W) (keep : Reg → V → V)
    (step : S → S) (Q : S → MConf V W → Prop) (T : S → Prop) (C : S → Prop) : Prop :=
  ∀ s c c', Q s c → MStep vc sem keep rf c c' →
    ∃ n c'', MStep vc sem keep rf c c'' ∧ Q (iterN step n s) c'' ∧ (∀ i < n, T (iterN step i s)) ∧
      countIn C step s n = opCalls vc c

theorem RealizesC.toRealizes {S : Type} {sem : ISem V W} {step : S → S}
    {Q : S → MConf V W → Prop} {T C : S → Prop} (h : RealizesC vc rf sem keep step Q T C) :
    Realizes vc rf sem keep step Q T := fun s c c' hq hs =>
  let ⟨n, c'', hm, hq', ht, _⟩ := h s c c' hq hs
  ⟨n, c'', hm, hq', ht⟩

/-- **The counted semantics with the counter equal to the machine's count**: from `RealizesC`
at every index, the machine with the count (`stepC C step`) realises `ISem.counted sem` under
`Q` of the first components and *counter = count*. -/
theorem RealizesC.counted {S : Type} {sem : Nat → ISem V W} {step : S → S}
    {Q : S → MConf V W → Prop} {T C : S → Prop}
    (h : ∀ n, RealizesC vc rf (sem n) keep step Q T C) :
    Realizes vc rf (ISem.counted sem) keep (stepC C step)
      (fun p c => Q p.1 (c.mapW Prod.fst) ∧ p.2 = c.world.2) (fun p => T p.1) := by
  rintro ⟨s, k⟩ c c' ⟨hq, hk⟩ hs
  cases c with
  | run vs =>
    obtain ⟨b, its, m, ⟨w, n⟩⟩ := vs
    obtain ⟨j, d, hd, hq', ht, hcnt⟩ := h n s _ _ hq (MStep.counted_proj hs)
    obtain ⟨c'', rfl, hc''⟩ := MStep.counted_lift hd
    refine ⟨j, c'', hc'', ?_, fun i hi => ?_⟩
    · rw [iterN_stepC]
      refine ⟨hq', ?_⟩
      rw [MStep.counted_ctr hc'', hcnt, opCalls_mapW]
      simp only at hk ⊢
      rw [hk]
    · rw [iterN_stepC]; exact ht i hi
  | ret => cases hs
  | halt => cases hs

end

end Backend.Proof

import FV.E2E.LinkArmTableECall
import FV.E2E.LinkArmThmPRBRLE
import FV.E2E.LinkTrapCall
import FV.Arm.ProgramKeep

/-!
# The machine's own slot table (SEM1 #537, #680 (3), fix of #700, step 5)

`TableOfE M g s ini` asks the slot-byte oracle `ini` to be the table of the machine run of `g` from
`s`: at each program call of an error-free prefix, the entry of the callee's placed activation
holds the memory at the call, and the callee's run (one level down) continues the table. Here the
table is **read off the machine run** (`iniOf`), so a top-level entry needs no table premise:

* `HooksKeep`: the outside code's hooks keep an error state and the loaded program (the machine
  does not run on from a fault; the outside code does not reload the program);
* `mach_errK`, `runX_errK` (errors persist), `mach_progK`, `runX_progK` (the program persists);
* `calleeAt` (the program callee of a state, `callsTo_unique`), `retIdx` (a callee run's first
  return), `callStep` (the step of the `c`-th call);
* `callE M g s c`: the number of table entries of the `c`-th call (its callee's own entry if it
  has slots, plus the callee run's entries up to its first return); `cntE M g s N`: the entries of
  the first `N` steps;
* `tabB M g s k x`: the bytes of entry `x` of the table whose entries `k + 1, …` the run from `s`
  fills (the call owning `x` is the first whose range contains it);
* **`tabUpToE_tabB`**: every error-free prefix has the prefix-closed table `tabB` with count
  `cntE` (by induction on the depth; the range of a non-returning callee is unbounded, but an
  error-free prefix has no call after it);
* `iniOf M g s`, **`tableOfE_iniOf`**: the machine's own table is the run's (`TableOfE`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

theorem sumTo_mono (E : Nat → Nat) {a b : Nat} (h : a ≤ b) : Clif.sumTo E a ≤ Clif.sumTo E b := by
  induction b with
  | zero => obtain rfl : a = 0 := by omega
            exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_ge b a with hlt | hge
    · obtain rfl : a = b + 1 := by omega
      exact Nat.le_refl _
    · have := ih hge
      simp only [Clif.sumTo]
      omega

theorem sumTo_zeroFn (n : Nat) : Clif.sumTo (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Clif.sumTo, ih]

namespace LinkSys

variable (L : LinkSys)

/-- **The outside code's hooks keep an error state and the loaded program.** -/
structure HooksKeep : Prop where
  err : ∀ d s, Arm.r .ERR s ≠ .None → Arm.r .ERR (L.Hb.call d s) ≠ .None
  tlsErr : ∀ n r s, Arm.r .ERR s ≠ .None → Arm.r .ERR (L.Hb.tls n r s) ≠ .None
  prog : ∀ d s, (L.Hb.call d s).program = s.program
  tlsProg : ∀ n r s, (L.Hb.tls n r s).program = s.program

/-! ## Errors and the program persist -/

theorem callHook_errK (hK : L.HooksKeep) {pc : Clif.Function → Arm.ArmState → Arm.ArmState}
    (hpc : ∀ g s, Arm.r .ERR s ≠ .None → Arm.r .ERR (pc g s) ≠ .None) (d : Option String)
    (s : Arm.ArmState) (h : Arm.r .ERR s ≠ .None) :
    Arm.r .ERR (callHook L.Hb L.Xb L.P pc d s) ≠ .None := by
  unfold callHook
  split
  · split
    · exact hpc _ _ h
    · exact hK.err _ _ h
  · split
    · exact hpc _ _ h
    · exact hK.err _ _ h

theorem hooks_errK (hK : L.HooksKeep) :
    ∀ M d s, Arm.r .ERR s ≠ .None → Arm.r .ERR ((L.hooks M).call d s) ≠ .None
  | 0, d, s, h => L.callHook_errK hK (fun _ s _ => junkAt_err s) d s h
  | M + 1, d, s, h => by
    refine L.callHook_errK hK (fun g s hs => ?_) d s h
    show Arm.r .ERR (linkedCall _ _ _) ≠ .None
    unfold linkedCall
    split
    · rename_i hex
      exfalso
      obtain ⟨k, hk⟩ := hex
      refine runX_err (fun u hu => armStepX_err (hooks_errK hK M) ?_ hu) k _ ?_ hk.2.1
      · rw [hooks_tls]; exact hK.tlsErr
      · rw [enterAt_err]; exact hs
    · exact junkAt_err s

theorem mach_errK (hK : L.HooksKeep) (M : Nat) (g : Clif.Function) (s : Arm.ArmState)
    (h : Arm.r .ERR s ≠ .None) : Arm.r .ERR (L.mach M g s) ≠ .None :=
  armStepX_err (L.hooks_errK hK M) (by rw [hooks_tls]; exact hK.tlsErr) h

theorem runX_errK (hK : L.HooksKeep) (M : Nat) (g : Clif.Function) :
    ∀ n s, Arm.r .ERR s ≠ .None → Arm.r .ERR (runX (L.mach M g) n s) ≠ .None :=
  runX_err (L.mach_errK hK M g)

/-- **No error before an error-free state** of a run. -/
theorem errFree_before (hK : L.HooksKeep) {M : Nat} {g : Clif.Function} {s : Arm.ArmState}
    {n : Nat} (h : Arm.r .ERR (runX (L.mach M g) n s) = .None) :
    ∀ j ≤ n, Arm.r .ERR (runX (L.mach M g) j s) = .None := by
  intro j hj
  refine Classical.byContradiction fun hne => ?_
  have := L.runX_errK hK M g (n - j) _ hne
  rw [← runX_add, show j + (n - j) = n by omega] at this
  exact this h

theorem callHook_progK (hK : L.HooksKeep) {pc : Clif.Function → Arm.ArmState → Arm.ArmState}
    (hpc : ∀ g s, (pc g s).program = s.program) (d : Option String) (s : Arm.ArmState) :
    (callHook L.Hb L.Xb L.P pc d s).program = s.program := by
  unfold callHook
  split
  · split
    · exact hpc _ _
    · exact hK.prog _ _
  · split
    · exact hpc _ _
    · exact hK.prog _ _

theorem junkAt_prog (s : Arm.ArmState) : (junkAt s).program = s.program := by
  simp only [junkAt, Arm.w_program]

theorem hooks_progK (hK : L.HooksKeep) (M : Nat) (d : Option String) (s : Arm.ArmState) :
    ((L.hooks M).call d s).program = s.program := by
  cases M with
  | zero => exact L.callHook_progK hK (fun _ s => junkAt_prog s) d s
  | succ M =>
    refine L.callHook_progK hK (fun g s => ?_) d s
    show (linkedCall _ _ _).program = _
    unfold linkedCall
    split
    · simp only [program_set_program]
    · exact junkAt_prog s

theorem mach_progK (hK : L.HooksKeep) (M : Nat) (g : Clif.Function) (s : Arm.ArmState) :
    (L.mach M g s).program = s.program := by
  show (ArmStepX L.Xb (L.hooks M) (L.A g).fa s).program = s.program
  dsimp only [ArmStepX]
  split
  · exact L.hooks_progK hK M _ s
  · exact L.hooks_progK hK M _ s
  · simp only [Arm.w_program]
  · simp only [Arm.w_program]
  · simp only [Arm.w_program]
  · simp only [Arm.w_program]
  · simp only [Arm.w_program]
  · rw [hooks_tls]; exact hK.tlsProg _ _ _
  · exact Arm.ProgKeep.stepi_program s

theorem runX_progK (hK : L.HooksKeep) (M : Nat) (g : Clif.Function) :
    ∀ n s, (runX (L.mach M g) n s).program = s.program
  | 0, _ => rfl
  | n + 1, s => (runX_progK hK M g n (L.mach M g s)).trans (L.mach_progK hK M g s)

/-! ## The callee of a state, the first return, the step of a call -/

theorem callsTo_unique {g h h' : Clif.Function} {t : Arm.ArmState} (hc : L.CallsTo g t h)
    (hc' : L.CallsTo g t h') : h = h' := by
  rcases hc with ⟨n, hi, hn⟩ | ⟨⟨x, hi⟩, hb⟩ <;> rcases hc' with ⟨n', hi', hn'⟩ | ⟨⟨x', hi'⟩, hb'⟩
  · rw [hi] at hi'
    cases hi'
    rw [hn] at hn'
    exact Option.some.inj hn'
  · rw [hi] at hi'; cases hi'
  · rw [hi] at hi'; cases hi'
  · rw [hb] at hb'
    exact Option.some.inj hb'

theorem callsTo_mem {g h : Clif.Function} {t : Arm.ArmState} (hc : L.CallsTo g t h) :
    h ∈ L.P.funcs := by
  rcases hc with ⟨n, -, hn⟩ | ⟨-, hb⟩
  · exact (Clif.Program.func?_some hn).1
  · obtain ⟨a, -, ha⟩ := Option.bind_eq_some_iff.mp hb
    exact List.mem_of_find?_eq_some ha

open Classical in
/-- The function of `P` the step at `t` of `g`'s code calls, if any. -/
noncomputable def calleeAt (g : Clif.Function) (t : Arm.ArmState) : Option Clif.Function :=
  if h : ∃ h, L.CallsTo g t h then some (Classical.choose h) else none

theorem calleeAt_of {g h : Clif.Function} {t : Arm.ArmState} (hc : L.CallsTo g t h) :
    L.calleeAt g t = some h := by
  have hex : ∃ h, L.CallsTo g t h := ⟨h, hc⟩
  simp only [calleeAt, dif_pos hex]
  exact congrArg some (L.callsTo_unique (Classical.choose_spec hex) hc)

theorem calleeAt_none {g : Clif.Function} {t : Arm.ArmState} (hn : ∀ h, ¬ L.CallsTo g t h) :
    L.calleeAt g t = none := by
  have hex : ¬ ∃ h, L.CallsTo g t h := fun ⟨h, hc⟩ => hn h hc
  simp only [calleeAt, dif_neg hex]

open Classical in
/-- The first return of `h`'s run at depth `M` for a call at `t`, if any. -/
noncomputable def retIdx (M : Nat) (h : Clif.Function) (t : Arm.ArmState) : Option Nat :=
  if hx : ∃ N, RetOf (L.A h) t (runX (L.mach M h) N (enterAt (L.A h) t)) then
    some (firstNat _ hx) else none

theorem retIdx_some {M : Nat} {h : Clif.Function} {t : Arm.ArmState} {N : Nat}
    (hr : RetOf (L.A h) t (runX (L.mach M h) N (enterAt (L.A h) t)))
    (hm : ∀ N'' < N, ¬ RetOf (L.A h) t (runX (L.mach M h) N'' (enterAt (L.A h) t))) :
    L.retIdx M h t = some N := by
  have hex : ∃ N, RetOf (L.A h) t (runX (L.mach M h) N (enterAt (L.A h) t)) := ⟨N, hr⟩
  simp only [retIdx, dif_pos hex]
  obtain ⟨h1, h2⟩ := firstNat_spec _ hex
  exact congrArg some (firstRet_unique h1 h2 hr hm)

theorem retIdx_spec {M : Nat} {h : Clif.Function} {t : Arm.ArmState} {N : Nat}
    (he : L.retIdx M h t = some N) :
    RetOf (L.A h) t (runX (L.mach M h) N (enterAt (L.A h) t)) ∧
      ∀ N'' < N, ¬ RetOf (L.A h) t (runX (L.mach M h) N'' (enterAt (L.A h) t)) := by
  unfold retIdx at he
  split at he
  · rename_i hex
    cases he
    exact firstNat_spec _ hex
  · cases he

open Classical in
/-- The step of the `c`-th call of the run of `g`'s machine at depth `M` from `s`. -/
noncomputable def callStep (M : Nat) (g : Clif.Function) (s : Arm.ArmState) (c : Nat) : Nat :=
  if hx : ∃ i, CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) i s)) ∧
      callsBefore (L.mach M g) (L.A g).fa (L.A g).base s i = c then Classical.choose hx else 0

theorem callStep_eq {M : Nat} {g : Clif.Function} {s : Arm.ArmState} {i : Nat}
    (hcp : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) i s))) :
    L.callStep M g s (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s i) = i := by
  have hex : ∃ i', CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) i' s)) ∧
      callsBefore (L.mach M g) (L.A g).fa (L.A g).base s i' =
        callsBefore (L.mach M g) (L.A g).fa (L.A g).base s i := ⟨i, hcp, rfl⟩
  simp only [callStep, dif_pos hex]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hex
  exact callIdx_unique h1 hcp h2

/-! ## The counts and the bytes of the machine's table -/

/-- **The number of table entries of the `c`-th call** of `g`'s run at depth `M` from `s`: the
callee's own entry if it has slots, and its run's entries up to its first return. -/
noncomputable def callE : Nat → Clif.Function → Arm.ArmState → Nat → Nat
  | 0, _, _, _ => 0
  | M + 1, g, s, c =>
    match L.calleeAt g (runX (L.mach (M + 1) g) (L.callStep (M + 1) g s c) s) with
    | some h => slotted h +
      match L.retIdx M h (runX (L.mach (M + 1) g) (L.callStep (M + 1) g s c) s) with
      | some N' => Clif.sumTo (callE M h (enterAt (L.A h)
          (runX (L.mach (M + 1) g) (L.callStep (M + 1) g s c) s)))
          (callsBefore (L.mach M h) (L.A h).fa (L.A h).base
            (enterAt (L.A h) (runX (L.mach (M + 1) g) (L.callStep (M + 1) g s c) s)) N')
      | none => 0
    | none => 0

/-- The table entries of the first `N` steps of `g`'s run at depth `M` from `s`. -/
noncomputable def cntE (M : Nat) (g : Clif.Function) (s : Arm.ArmState) (N : Nat) : Nat :=
  Clif.sumTo (L.callE M g s) (callsBefore (L.mach M g) (L.A g).fa (L.A g).base s N)

theorem callE_zero (g : Clif.Function) (s : Arm.ArmState) : L.callE 0 g s = fun _ => 0 := rfl

theorem callE_call {M : Nat} {g h : Clif.Function} {s : Arm.ArmState} {i : Nat}
    (hcp : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M + 1) g) i s)))
    (hct : L.CallsTo g (runX (L.mach (M + 1) g) i s) h) :
    L.callE (M + 1) g s (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) =
      slotted h + match L.retIdx M h (runX (L.mach (M + 1) g) i s) with
        | some N' => L.cntE M h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s)) N'
        | none => 0 := by
  simp only [callE, L.callStep_eq hcp, L.calleeAt_of hct]
  rfl

theorem callE_noCall {M : Nat} {g : Clif.Function} {s : Arm.ArmState} {i : Nat}
    (hcp : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M + 1) g) i s)))
    (hn : ∀ h, ¬ L.CallsTo g (runX (L.mach (M + 1) g) i s) h) :
    L.callE (M + 1) g s (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) = 0 := by
  simp only [callE, L.callStep_eq hcp, L.calleeAt_none hn]

/-- **Entry `x` belongs to the `c`-th call** of the run (with base index `k`): its range starts
after the earlier calls' entries and, if the callee returns, ends with its own. -/
def Owns (M : Nat) (g : Clif.Function) (s : Arm.ArmState) (k c x : Nat) : Prop :=
  ∃ i h, CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M + 1) g) i s)) ∧
    callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i = c ∧
    L.CallsTo g (runX (L.mach (M + 1) g) i s) h ∧
    k + Clif.sumTo (L.callE (M + 1) g s) c < x ∧
    ((∃ N, RetOf (L.A h) (runX (L.mach (M + 1) g) i s)
        (runX (L.mach M h) N (enterAt (L.A h) (runX (L.mach (M + 1) g) i s)))) →
      x ≤ k + Clif.sumTo (L.callE (M + 1) g s) (c + 1))

open Classical in
/-- **The bytes of entry `x` of the machine's table** filled from base index `k` by the run of
`g` at depth `M` from `s`: the memory at the call owning `x` after the callee's stack probes
(`probeMem`, its body-entry memory, #581) if `x` is that callee's own entry, else the callee
run's entry. -/
noncomputable def tabB : Nat → Clif.Function → Arm.ArmState → Nat → Nat → Nat → BitVec 8
  | 0, _, _, _, _ => fun _ => 0
  | M + 1, g, s, k, x =>
    if hx : ∃ c, L.Owns M g s k c x then
      match L.calleeAt g (runX (L.mach (M + 1) g) (L.callStep (M + 1) g s (firstNat _ hx)) s) with
      | some h =>
        if x = k + Clif.sumTo (L.callE (M + 1) g s) (firstNat _ hx) + 1 ∧ slotted h = 1 then
          fun a => probeMem (L.A h).af
            (runX (L.mach (M + 1) g) (L.callStep (M + 1) g s (firstNat _ hx)) s) (BitVec.ofNat 64 a)
        else tabB M h (enterAt (L.A h)
            (runX (L.mach (M + 1) g) (L.callStep (M + 1) g s (firstNat _ hx)) s))
          (k + Clif.sumTo (L.callE (M + 1) g s) (firstNat _ hx) + slotted h) x
      | none => fun _ => 0
    else fun _ => 0

/-- **The owner of an entry in an error-free prefix**: an entry in the range of the call at step
`i` (whose earlier calls are followed by error-free states, so their callees returned) is owned
by no earlier call. -/
theorem tabB_at (hL : L.Ok) (hK : L.HooksKeep) {M : Nat} {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {s : Arm.ArmState}
    (hprog : s.program = (L.A g).fb.program (L.A g).base) {k i x : Nat} {h : Clif.Function}
    (herr : ∀ j ≤ i, Arm.r .ERR (runX (L.mach (M + 1) g) j s) = .None)
    (hcp : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M + 1) g) i s)))
    (hct : L.CallsTo g (runX (L.mach (M + 1) g) i s) h)
    (hlo : k + Clif.sumTo (L.callE (M + 1) g s)
      (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) < x)
    (hhi : (∃ N, RetOf (L.A h) (runX (L.mach (M + 1) g) i s)
        (runX (L.mach M h) N (enterAt (L.A h) (runX (L.mach (M + 1) g) i s)))) →
      x ≤ k + Clif.sumTo (L.callE (M + 1) g s)
        (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i + 1)) :
    L.tabB (M + 1) g s k x =
      if x = k + Clif.sumTo (L.callE (M + 1) g s)
          (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) + 1 ∧ slotted h = 1 then
        fun a => probeMem (L.A h).af (runX (L.mach (M + 1) g) i s) (BitVec.ofNat 64 a)
      else L.tabB M h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))
        (k + Clif.sumTo (L.callE (M + 1) g s)
          (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) + slotted h) x := by
  have hown : L.Owns M g s k (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) x :=
    ⟨i, h, hcp, rfl, hct, hlo, hhi⟩
  have hex : ∃ c, L.Owns M g s k c x := ⟨_, hown⟩
  have hfind : firstNat _ hex = callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i := by
    obtain ⟨hspec, hmin⟩ := firstNat_spec _ hex
    refine Nat.le_antisymm ?_ ?_
    · rcases Nat.lt_or_ge (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i)
        (firstNat _ hex) with hlt | hge
      · exact absurd hown (hmin _ hlt)
      · exact hge
    refine Classical.byContradiction fun hlt => ?_
    have hlt : firstNat _ hex < callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i := by
      omega
    obtain ⟨i', h', hcp', hcb', hct', hlo', hhi'⟩ := hspec
    have hii : i' < i := by
      rcases Nat.lt_or_ge i' i with h1 | h1
      · exact h1
      · rcases Nat.eq_or_lt_of_le h1 with h2 | h2
        · subst h2; omega
        · have := callsBefore_lt hcp h2; omega
    have hr : Arm.r .ERR (L.mach (M + 1) g (runX (L.mach (M + 1) g) i' s)) = .None := by
      have := herr (i' + 1) (by omega)
      rwa [runX_add _ i' 1] at this
    obtain ⟨M', hM, N₁, hr₁, -⟩ := L.callsTo_ret hct'
      (L.progBase_of_callsTo hL hg hct' ((L.runX_progK hK _ g i' s).trans hprog)) hr
    obtain rfl : M = M' := Nat.succ.inj hM
    have h1 := hhi' ⟨N₁, hr₁⟩
    have h2 := sumTo_mono (L.callE (M + 1) g s) (show firstNat _ hex + 1 ≤
      callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i by omega)
    omega
  simp only [tabB, dif_pos hex]
  rw [hfind, L.callStep_eq hcp, L.calleeAt_of hct]

/-! ## The table of every error-free prefix -/

/-- **The machine's table fits every error-free prefix** (module doc): for a table `b` agreeing
with `tabB M g s k` on the entries of the run (all from `k + 1` on, or, when the run returns
first at `n`, up to its count there), every error-free prefix (up to the return) has the
prefix-closed table of `b` with count `cntE`. -/
theorem tabUpToE_tabB (hL : L.Ok) (hK : L.HooksKeep) : ∀ (M : Nat) (g : Clif.Function),
    g ∈ L.P.funcs → ∀ (s : Arm.ArmState) (k : Nat) (b : Nat → Nat → BitVec 8) (lim : Option Nat)
    (N : Nat), s.program = (L.A g).fb.program (L.A g).base →
    (∀ x, k < x → (∀ n, lim = some n → x ≤ k + L.cntE M g s n) → b x = L.tabB M g s k x) →
    (∀ n, lim = some n → N ≤ n) →
    (∀ n, lim = some n → Arm.r .ERR (runX (L.mach M g) n s) = .None) →
    (∀ j < N, Arm.r .ERR (runX (L.mach M g) j s) = .None) →
    L.TabUpToE M g s b k N (L.cntE M g s N)
  | 0, g, _, s, _, _, _, N, _, _, _, _, _ => by
    show L.cntE 0 g s N = 0
    simp only [cntE, callE_zero, sumTo_zeroFn]
  | M + 1, g, hg, s, k, b, lim, N, hprog, hagree, hlimN, hlimE, herrN => by
    -- the states of the prefix, and the call states after which the prefix goes on, are
    -- error-free
    have herrAt : ∀ i < N, ∀ j ≤ i, Arm.r .ERR (runX (L.mach (M + 1) g) j s) = .None :=
      fun i hi j hj => herrN j (by omega)
    refine ⟨L.callE (M + 1) g s, rfl, fun i hi hcp => ⟨fun hn => L.callE_noCall hcp hn,
      fun h hct => ?_⟩⟩
    have hh : h ∈ L.P.funcs := L.callsTo_mem hct
    have hEc := L.callE_call hcp hct
    have hprogt : (runX (L.mach (M + 1) g) i s).program = (L.A g).fb.program (L.A g).base :=
      (L.runX_progK hK _ g i s).trans hprog
    have hprogE : (enterAt (L.A h) (runX (L.mach (M + 1) g) i s)).program =
        (L.A h).fb.program (L.A h).base := by
      simp [enterAt, Arm.w_program]
    -- the caller's bound: if the caller run returns first at `n`, its calls before `n` return
    have hcaller : ∀ n, lim = some n →
        ∃ N₁, L.retIdx M h (runX (L.mach (M + 1) g) i s) = some N₁ := by
      intro n hn
      have hle := hlimN n hn
      have hr : Arm.r .ERR (L.mach (M + 1) g (runX (L.mach (M + 1) g) i s)) = .None := by
        have := L.errFree_before hK (hlimE n hn) (i + 1) (by omega)
        rwa [runX_add _ i 1] at this
      obtain ⟨M', hM, N₁, hr₁, hm₁⟩ :=
        L.callsTo_ret hct (L.progBase_of_callsTo hL hg hct hprogt) hr
      obtain rfl : M = M' := Nat.succ.inj hM
      exact ⟨N₁, L.retIdx_some hr₁ hm₁⟩
    have hcb : ∀ n, lim = some n → callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i + 1 ≤
        callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s n :=
      fun n hn => callsBefore_lt hcp (by have := hlimN n hn; omega)
    -- the callee range's agreement
    have hEge : slotted h ≤ L.callE (M + 1) g s
        (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) := by rw [hEc]; omega
    have hupper : ∀ x, (∀ N₁, L.retIdx M h (runX (L.mach (M + 1) g) i s) = some N₁ →
        x ≤ k + Clif.sumTo (L.callE (M + 1) g s)
          (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) +
        slotted h + L.cntE M h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s)) N₁) →
        ∀ n, lim = some n → x ≤ k + L.cntE (M + 1) g s n := by
      intro x hx n hn
      obtain ⟨N₁, hN₁⟩ := hcaller n hn
      have h1 := hx N₁ hN₁
      have h2 := sumTo_mono (L.callE (M + 1) g s) (hcb n hn)
      have h3 : L.callE (M + 1) g s (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) =
          slotted h + L.cntE M h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s)) N₁ := by
        rw [hEc, hN₁]
      simp only [cntE]
      simp only [Clif.sumTo] at h2
      omega
    have hhiR : ∀ x, (∀ N₁, L.retIdx M h (runX (L.mach (M + 1) g) i s) = some N₁ →
        x ≤ k + Clif.sumTo (L.callE (M + 1) g s)
          (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) +
        slotted h + L.cntE M h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s)) N₁) →
        (∃ N, RetOf (L.A h) (runX (L.mach (M + 1) g) i s)
          (runX (L.mach M h) N (enterAt (L.A h) (runX (L.mach (M + 1) g) i s)))) →
        x ≤ k + Clif.sumTo (L.callE (M + 1) g s)
          (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i + 1) := by
      intro x hx ⟨N, hN⟩
      have hex : ∃ N, RetOf (L.A h) (runX (L.mach (M + 1) g) i s)
          (runX (L.mach M h) N (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))) := ⟨N, hN⟩
      obtain ⟨h1, h2⟩ := firstNat_spec _ hex
      have hN₁ := L.retIdx_some h1 h2
      have := hx _ hN₁
      have h3 : L.callE (M + 1) g s (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) =
          slotted h + L.cntE M h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))
            (firstNat _ hex) := by
        rw [hEc, hN₁]
      simp only [Clif.sumTo]
      omega
    have herri : ∀ j ≤ i, Arm.r .ERR (runX (L.mach (M + 1) g) j s) = .None := herrAt i hi
    refine ⟨fun h1 a _ => ?_, hEge, fun N' hN' hE' => ?_, fun N₁ hr₁ hm₁ => ?_⟩
    · -- the callee's own entry
      have hx : k + Clif.sumTo (L.callE (M + 1) g s)
            (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) + 1 ≤
          k + Clif.sumTo (L.callE (M + 1) g s)
            (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i + 1) := by
        simp only [Clif.sumTo]; omega
      rw [hagree _ (by omega) (hupper _ fun N₁ _ => by omega),
        L.tabB_at hL hK hg hprog herri hcp hct (by omega) (fun _ => hx), if_pos ⟨rfl, h1⟩]
    · -- the callee's prefixes before its return
      refine ⟨_, tabUpToE_tabB hL hK M h hh (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))
        (k + Clif.sumTo (L.callE (M + 1) g s)
          (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) + slotted h) b
        (L.retIdx M h (runX (L.mach (M + 1) g) i s)) N' hprogE
        (fun x hx hlimx => ?_) (fun n hn => ?_) (fun n hn => ?_) hE'⟩
      · rw [hagree x (by omega) (hupper x hlimx),
          L.tabB_at hL hK hg hprog herri hcp hct (by omega) (hhiR x hlimx),
          if_neg (fun ⟨e, e2⟩ => by omega)]
      · obtain ⟨hr, -⟩ := L.retIdx_spec hn
        rcases Nat.lt_or_ge n N' with hlt | hge
        · exact absurd hr (hN' n hlt)
        · exact hge
      · exact (L.retIdx_spec hn).1.2.1
    · -- the callee's run up to its return
      have hN₁ := L.retIdx_some hr₁ hm₁
      have herr₁ : ∀ j ≤ N₁, Arm.r .ERR (runX (L.mach M h) j
          (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))) = .None :=
        L.errFree_before hK hr₁.2.1
      have hE := tabUpToE_tabB hL hK M h hh (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))
        (k + Clif.sumTo (L.callE (M + 1) g s)
          (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) + slotted h) b
        (L.retIdx M h (runX (L.mach (M + 1) g) i s)) N₁ hprogE
        (fun x hx hlimx => by
          rw [hagree x (by omega) (hupper x hlimx),
            L.tabB_at hL hK hg hprog herri hcp hct (by omega) (hhiR x hlimx),
            if_neg (fun ⟨e, e2⟩ => by omega)])
        (fun n hn => by rw [hN₁] at hn; cases hn; exact Nat.le_refl _)
        (fun n hn => by rw [hN₁] at hn; cases hn; exact hr₁.2.1)
        (fun j hj => herr₁ j (by omega))
      have hcnt : L.callE (M + 1) g s (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) -
          slotted h = L.cntE M h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s)) N₁ := by
        rw [hEc, hN₁]; exact Nat.add_sub_cancel_left _ _
      rw [hcnt]
      exact L.tabUpTo_of_E hL hh M _ _ _ N₁ _
        (fun j _ => (L.runX_progK hK M h j _).trans hprogE)
        (fun j hj => herr₁ (j + 1) (by omega)) hE

/-- **The machine's own table** of the run of `g` at depth `M` from `s` (entries from `1`). -/
noncomputable def iniOf (M : Nat) (g : Clif.Function) (s : Arm.ArmState) : Clif.SlotInit :=
  ⟨L.tabB M g s 0, 0⟩

/-- **The run's table is the machine's own** (module doc). -/
theorem tableOfE_iniOf (hL : L.Ok) (hK : L.HooksKeep) {M : Nat} {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {s : Arm.ArmState} (hprog : s.program = (L.A g).fb.program (L.A g).base) :
    L.TableOfE M g s (L.iniOf M g s) := fun N _ herr =>
  ⟨_, L.tabUpToE_tabB hL hK M g hg s 0 _ none N hprog (fun _ _ _ => rfl)
    (fun _ h => by cases h) (fun _ h => by cases h) herr⟩

end LinkSys

end E2E

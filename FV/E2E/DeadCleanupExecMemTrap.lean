import FV.E2E.LinkMemTrap
import FV.E2E.DeadCleanupExecPeak

/-!
# Memory traps on the executable machine (A3, #412, slice F6)

`docs/plans/memfault.md`. The linked-program memory-trap theorem
(`backend_correct_program_memtrap_budget`, `_peak`: a state of the model's run at a trap site of
the entry function, `TrapAtM`, the per-state facts before it, `RunGoodLB`) carried to the
executable machine `step I B file`. The model's run is simulated up to the trap state only
(`act_simNB`: `act_simN` from the per-state facts before a step `n`).

* **`ExecTrapM mp I file f c e`**, the executable's observable of a trap with code `c`: the
  executable state `e` is at a trap site of `f` with `c` (`TrapAt`), and the instruction word of
  the file at its pc, executed by the processor, errs (the `udf` of an explicit trap) or faults
  under the memory map `mp` (`ArmFault.InstFaults`: the `ldaxr` of a trapping atomic whose access
  has an unmapped byte);
* `ExecRefinesM`: `ExecRefines` with `ExecTrapM` as its trap clause;
* `ReachNB`, `RunOkSNB`, `act_simNB`, `runOkSNB_of_good`: `ReachN`, `RunOkSN`, `act_simN`,
  `runOkSN_of_good` before step `n`;
* `exec_memtrap_of_model`; **`binary_correct_exec_memtrap`** (entries without a reachable call
  cycle), **`binary_correct_exec_memtrap_peak`** (the run's peak call depth): a whole-program CLIF
  run that traps with `tc` under `TrapsExplicitM` and `MapFaults mp` reaches, on the executable
  machine from `r`, a state with `ExecTrapM mp … tc`.

What this says (and does not): the executable machine's memory is total, so its run does not
stop at the trapping atomic. The theorem names the state at which the run is at the trapping
atomic's `ldaxr` and says that this instruction faults under `mp`; it does not say that no
earlier access of the run faults under `mp` (slice F8).
-/

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

/-! ## The observable -/

/-- **The executable's observable of a trap with code `c` of `f`**: a trap site of `f` with `c`
(`TrapAt`) whose instruction word in the file, executed by the processor, errs (`udf`) or faults
under the memory map `mp`. -/
def ExecTrapM (mp : ArmFault.MemMap) (I : LinkInput) (file : ByteArray) (f : Clif.Function)
    (c : Clif.TrapCode) (e : Arm.ArmState) : Prop :=
  TrapAt (art I f).fb (art I f).base c e ∧
    ∃ a, (fileWord file (Arm.r .PC e)).bind Arm.decode_raw_inst = some a ∧
      (Arm.r .ERR (Arm.exec_inst a e) ≠ .None ∨ ArmFault.InstFaults mp a e)

/-- **`ExecRefines` with memory traps**: a return as `ExecRefines`; a trap with `c` is a state of
the executable machine's run with `ExecTrapM mp … c`. -/
def ExecRefinesM (mp : ArmFault.MemMap) (I : LinkInput) (file : ByteArray) (f : Clif.Function)
    (ra : BitVec 64) (astep : Arm.ArmState → Arm.ArmState) (s : Arm.ArmState)
    (R : BitVec 64 → Prop) : Clif.Outcome → Prop
  | .returned vals cm => ∃ n, ArmRet ra s (runX astep n s) ∧
      (∀ (j : Nat) v, vals[j]? = some v → XHolds v (xreg j (runX astep n s))) ∧
      ∀ a b, cm.valid a 1 = true → cm.bytes a = some b → ¬ R (BitVec.ofNat 64 a) →
        Arm.read_mem (BitVec.ofNat 64 a) (runX astep n s) = b
  | .trapped c => ∃ n, ExecTrapM mp I file f c (runX astep n s)
  | .stuck _ | .outOfFuel => True

/-! ## The model's run before a step -/

section Defs

variable (I : LinkInput) (B : BaseEnv) (file : ByteArray)

/-- `ReachN` with the entry activation's index below `n`. -/
def ReachNB (n M : Nat) (f : Clif.Function) (c : Arm.ArmState) (M' : Nat) (g : Clif.Function)
    (t : Arm.ArmState) : Prop :=
  (∃ k < n, (∀ j ≤ k, ¬ Returned (art I f) c (runX ((sys I B).mach M f) j c)) ∧ M' = M ∧
      g = f ∧ t = runX ((sys I B).mach M f) k c) ∨
  (∃ M0 k h, M = M0 + 1 ∧ k < n ∧
      (∀ j ≤ k, ¬ Returned (art I f) c (runX ((sys I B).mach (M0 + 1) f) j c)) ∧
      CallsAt I B f (runX ((sys I B).mach (M0 + 1) f) k c) h ∧
      Arm.r .ERR (runX ((sys I B).mach (M0 + 1) f) (k + 1) c) = .None ∧
      ReachN I B M0 h (enterAt (art I h) (runX ((sys I B).mach (M0 + 1) f) k c)) M' g t)

/-- `RunOkSN` before step `n`. -/
def RunOkSNB (n M : Nat) (f : Clif.Function) (c : Arm.ArmState) : Prop :=
  ∀ M' g t, ReachNB I B n M f c M' g t → Arm.r .ERR ((sys I B).mach M' g t) = .None →
    StepOk I B file M' g t

end Defs

section Lemmas

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

theorem reachNB_mem {n M : Nat} {f : Clif.Function} {c : Arm.ArmState} {M' : Nat}
    {g : Clif.Function} {t : Arm.ArmState} (h : ReachNB I B n M f c M' g t)
    (hf : f ∈ (prog I).funcs) : g ∈ (prog I).funcs := by
  rcases h with ⟨k, -, -, -, e, -⟩ | ⟨M0, k, h, -, -, -, hcall, -, hR⟩
  · subst e; exact hf
  · exact reachN_mem hR (callee_mem hcall)

/-- **The states of `ReachNB` are states of `ReachLB`**, of an activation entered at an entry
whose return address is no second word. -/
theorem reachLB_of_reachNB (hI : okBCleanup I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {n M : Nat} {f : Clif.Function} {c : Arm.ArmState}
    {M' : Nat} {g : Clif.Function} {t : Arm.ArmState} (h : ReachNB I B n M f c M' g t)
    (hf : f ∈ (prog I).funcs) (hrun : (sys I B).RunGoodLB n M f c) (hs : ¬ Second I f (xreg 30 c)) :
    ∃ c', (sys I B).ReachLB n M f c M' g c' t ∧ ¬ Second I g (xreg 30 c') := by
  rcases h with ⟨k, hk, hj, e1, e2, e3⟩ | ⟨M0, k, h, e1, hk, hj, hcall, herr, hR⟩
  · subst e1 e2 e3
    exact ⟨c, .inl ⟨k, hk, hj, rfl, rfl, rfl, rfl⟩, hs⟩
  · subst e1
    have hu := hrun _ _ _ _ (.inl ⟨k, hk, hj, rfl, rfl, rfl, rfl⟩)
      (by rw [runX_succ'] at herr; exact herr)
    obtain ⟨X, K, G, gv, -, hG, -⟩ := hu
    unfold actGoodX at hG
    obtain ⟨c', hR', hs'⟩ := reachL_of_reachN hI hc hF hR (callee_mem hcall)
      (fun _ _ _ _ hr he => hrun _ _ _ _ (.inr ⟨M0, k, h, rfl, hk, hj, hcall, herr, hr⟩) he)
      (raNotSecond_enter hI hc hF hf hG.prog hcall)
    exact ⟨c', .inr ⟨M0, k, h, rfl, hk, hj, hcall, herr, hR'⟩, hs'⟩

/-- **`RunOkSNB` from the per-state facts before step `n`** (`runOkSN_of_good`). -/
theorem runOkSNB_of_good (hI : okBCleanup I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hH : HooksSim I B)
    (hD : ∀ g ∈ (prog I).funcs, (art I g).vcp.DestsInt) (hnogot : ∀ a, ¬ GotSlot I file a)
    {n M : Nat} {f : Clif.Function} (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (hgood : (sys I B).RunGoodLB n M f c) (hs : ¬ Second I f (xreg 30 c)) :
    RunOkSNB I B file n M f c := by
  intro M' g t hR he
  have hg := reachNB_mem hR hf
  obtain ⟨c', hRL, hs'⟩ := reachLB_of_reachNB hI hc hF hR hf hgood hs
  have hG := hgood _ _ _ _ hRL he
  exact stepOk_of_d hI hc hF hH hg (stepOkD_of_good hI hc hF hD hg hG hs' he
    ⟨insn_of_good hI hc hF hg hG, fun rl hrl ht _ rd G hrd h8 hin hw0 hw1 i hi =>
      (hnogot _ ⟨_, tab_mem (okBCleanup_names hI) hg, rl, hrl, ht, rd, G, hrd, h8, hin, hw0,
        hw1, i, hi, rfl⟩).elim⟩)

/-- A line without relocation is no second word of a pair. -/
theorem not_second_line {g : Clif.Function} (hF : FnOk I file g) {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : (art I g).fa.lines.toList[j]? = some (.ins x t))
    (hx : x.reloc? = none) :
    ¬ Second I g (wAt (art I g) (lineOffset (art I g).fa.lines.toList j)) := by
  rintro ⟨rl, hrl, ht, he⟩
  obtain ⟨-, -, r', hr', hr'o, hr't⟩ := pair_facts hF hrl ht
  obtain ⟨j2, i2, t2, hj2, hi2, ho2⟩ := (FnAsm.layout_relocs hF.layout r').1 hr'
  have h1 : insnAt (art I g).fa (art I g).base
      (wAt (art I g) (lineOffset (art I g).fa.lines.toList j)) = some x :=
    insnAt_of_line hF hj
  have h2 : insnAt (art I g).fa (art I g).base
      (wAt (art I g) (lineOffset (art I g).fa.lines.toList j)) = some i2 := by
    rw [he, ← hr'o, ← ho2]; exact insnAt_of_line hF hj2
  rw [h1] at h2
  cases h2
  rw [hx] at hi2
  cases hi2

end Lemmas

/-! ## The simulation before step `n` -/

section Core

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- **`act_simN` before step `n`**: the states of an activation before its step `n` that are no
second word of a pair are simulated, given `StepOk` at the states before step `n`. -/
theorem act_simNB (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M : Nat} {g : Clif.Function}
    {c e : Arm.ArmState} (hg : g ∈ (prog I).funcs) (hpc : Arm.r .PC c = (art I g).base)
    (hsim : Sim I c e) {n : Nat} (hrun : RunOkSNB I B file n M g c) :
    ∀ k ≤ n, (∀ j < k, ¬ Returned (art I g) c (runX ((sys I B).mach M g) j c)) →
    ¬ Second I g (Arm.r .PC (runX ((sys I B).mach M g) k c)) →
    Arm.r .ERR (runX ((sys I B).mach M g) k c) = .None →
    ∃ k', Sim I (runX ((sys I B).mach M g) k c) (runX (step I B file) k' e) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro hkn hret hsec herr
  have hFg := hF g hg
  have hok : ∀ j, j < n → (∀ j' ≤ j, ¬ Returned (art I g) c (runX ((sys I B).mach M g) j' c)) →
      Arm.r .ERR (runX ((sys I B).mach M g) (j + 1) c) = .None →
      StepOk I B file M g (runX ((sys I B).mach M g) j c) := fun j hjn hj he =>
    hrun _ _ _ (.inl ⟨j, hjn, hj, rfl, rfl, rfl⟩) (by rw [← runX_succ' ((sys I B).mach M g)]; exact he)
  cases k with
  | zero => exact ⟨0, hsim⟩
  | succ k0 =>
  have hok0 : StepOk I B file M g (runX ((sys I B).mach M g) k0 c) :=
    hok k0 (by omega) (fun j hj => hret j (by omega)) herr
  rw [runX_succ'] at hsec herr ⊢
  by_cases hs : Second I g (Arm.r .PC (runX ((sys I B).mach M g) k0 c))
  · -- the second word of a pair: two steps from its first word
    obtain ⟨rl, hrl, ht, he⟩ := hs
    cases k0 with
    | zero => exact (not_second_base hFg ⟨rl, hrl, ht, hpc.symm.trans he⟩).elim
    | succ k1 =>
    have hok1 : StepOk I B file M g (runX ((sys I B).mach M g) k1 c) :=
      hok k1 (by omega) (fun j hj => hret j (by omega)) hok0.err
    have hpc1 := hok1.cf rl hrl ht (by rw [← runX_succ' ((sys I B).mach M g) k1]; exact he)
    obtain ⟨k', hk'⟩ := ih k1 (by omega) (by omega) (fun j hj => hret j (by omega))
      (by rw [hpc1]; exact first_not_second hFg hrl ht) hok1.err
    refine ⟨k' + 2, ?_⟩
    rw [runX_succ', runX_add (step I B file) k' 2]
    exact pair_step hFg hrl ht hpc1 hok1
      (by rw [← runX_succ' ((sys I B).mach M g) k1]; exact hok0) hk'
  · obtain ⟨k', hk'⟩ := ih k0 (by omega) (by omega) (fun j hj => hret j (by omega)) hs hok0.err
    obtain ⟨i, hins, -, -⟩ := hok0.site
    obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hFg.layout
    obtain ⟨j0, t0, hj0, -⟩ := insnAt_spec hins
    have hb := progBase_of hFg hm hok0.program hj0
    -- a call of a function of the program
    have hprog : ∀ h, CallsAt I B g (runX ((sys I B).mach M g) k0 c) h →
        ∃ k'', Sim I ((sys I B).mach M g (runX ((sys I B).mach M g) k0 c))
          (runX (step I B file) k'' e) := by
      intro h hc
      have hh := callee_mem hc
      rw [mach_call hc] at herr ⊢
      cases M with
      | zero => exact absurd herr (junkAt_err _)
      | succ M' =>
      have hrun' : RunOkSN I B file M' h
          (enterAt (art I h) (runX ((sys I B).mach (M' + 1) g) k0 c)) :=
        fun M'' g' t hr he => hrun _ _ _ (.inr ⟨M', k0, h, rfl, by omega,
          fun j hj => hret j (by omega), hc,
          by rw [runX_succ', mach_call hc]; exact herr, hr⟩) he
      simp only [LinkSys.pcall] at herr ⊢
      have hent := call_enter hFg (hF h hh) hok0 hk' hc
      unfold linkedCall at herr ⊢
      split
      · rename_i hex
        obtain ⟨hN, hmin⟩ := firstNat_spec _ hex
        obtain ⟨k2, hk2⟩ := act_simN hF M' h _ _ hh (pc_enterAt _ _) hent hrun' _
          (fun j hj hr => hmin j hj (returned_iff.2 hr))
          (ret_not_secondN hF hg hh hok0 hc hrun' hN hmin) hN.2.1
        exact ⟨k' + 1 + k2, by rw [runX_add, runX_add]; exact sim_set_program _ hk2⟩
      · simp [‹¬ _›, junkAt, Arm.r_of_w_same] at herr
    by_cases hhk : i.hooked = false
    · exact ⟨k' + 1, by rw [runX_succ']; exact plain_step hFg hok0 hk' hins hhk⟩
    · cases i <;> simp only [Insn.hooked, Bool.true_eq_false, not_false_eq_true, not_true_eq_false] at hhk
      case bl n =>
        cases hn : (prog I).func? n with
        | none => exact ⟨k' + 1, by rw [runX_succ']; exact hook_step hFg hok0 hk' hins (.inl ⟨n, rfl, hn⟩)⟩
        | some h => exact hprog h (.inl ⟨n, by rw [hb]; exact hins, hn⟩)
      case blr x =>
        cases hn : (blrTarget (runX ((sys I B).mach M g) k0 c)).bind (symCallee (sys I B).Xb (prog I)) with
        | none => exact ⟨k' + 1, by rw [runX_succ']; exact hook_step hFg hok0 hk' hins (.inr (.inl ⟨x, rfl, hn⟩))⟩
        | some h => exact hprog h (.inr ⟨⟨x, by rw [hb]; exact hins⟩, hn⟩)
      case adrpGot a b => exact absurd (adrp_lands hFg hok0 hins (.inl ⟨a, b, rfl⟩)) hsec
      case adrp a b d => exact absurd (adrp_lands hFg hok0 hins (.inr ⟨a, b, d, rfl⟩)) hsec
      case ldrGotLo12 a b d => exact absurd (second_of_lo12 hFg hins (.inl ⟨a, b, d, rfl⟩)) hs
      case addLo12 a b d f => exact absurd (second_of_lo12 hFg hins (.inr ⟨a, b, d, f, rfl⟩)) hs
      case adrpTlsDesc a b =>
        exact ⟨k' + 1, by rw [runX_succ']; exact hook_step hFg hok0 hk' hins (.inr (.inr (.inl ⟨a, b, rfl⟩)))⟩
      case ldrTlsDescLo12 a b d =>
        exact ⟨k' + 1, by rw [runX_succ']; exact hook_step hFg hok0 hk' hins (.inr (.inr (.inr ⟨a, b, d, rfl⟩)))⟩

end Core

/-! ## The transfer -/

section Transfer

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- **The model's trap state gives the executable's observable**: a model state at a trap site
of `f` with `TrapAtM`, simulated by `e`, gives `ExecTrapM` at `e`. -/
theorem execTrapM_of_sim {f : Clif.Function} (hFf : FnOk I file f) {mp : ArmFault.MemMap}
    {c : Clif.TrapCode} {m e : Arm.ArmState}
    (ht : TrapAtM mp (art I f).fa (art I f).fb (art I f).base c m) (hs : Sim I m e) :
    ExecTrapM mp I file f c e := by
  obtain ⟨hat, hl⟩ := ht
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hFf.layout
  refine ⟨⟨by rw [hs.1]; exact hat.err, by rw [hs.1]; exact hat.site⟩, ?_⟩
  rcases hl with ⟨j, t, hj, hpc⟩ | ⟨j, bits, t, hj, hbits, hpc, hu⟩
  · obtain ⟨w, hw, hfw⟩ := fileWord_plain hFf hlm hj rfl
    obtain ⟨a, ha, hd⟩ := Insn.decode_encode hw
    obtain ⟨a', ha', he, -, -⟩ := exec_udf_insn ⟨lineOffset (art I f).fa.lines.toList j, (lm[·]?)⟩ e
    rw [ha] at ha'; cases ha'
    refine ⟨a, ?_, .inl he⟩
    rw [hs.1, hpc, show (art I f).base + BitVec.ofNat 64 (lineOffset (art I f).fa.lines.toList j) =
      wAt (art I f) (lineOffset (art I f).fa.lines.toList j) from rfl, hfw]
    exact hd
  · obtain ⟨w, hw, hfw⟩ := fileWord_plain hFf hlm hj rfl
    obtain ⟨a, ha, hd⟩ := Insn.decode_encode hw
    refine ⟨a, ?_, .inr (instFaults_ldaxr hbits ha (by rw [hs.1]; exact hu))⟩
    rw [hs.1, hpc, show (art I f).base + BitVec.ofNat 64 (lineOffset (art I f).fa.lines.toList j) =
      wAt (art I f) (lineOffset (art I f).fa.lines.toList j) from rfl, hfw]
    exact hd

/-- A `TrapAtM` state of `f` is no second word of a pair of `f`. -/
theorem not_second_trapAtM {f : Clif.Function} (hFf : FnOk I file f) {mp : ArmFault.MemMap}
    {c : Clif.TrapCode} {m : Arm.ArmState}
    (ht : TrapAtM mp (art I f).fa (art I f).fb (art I f).base c m) :
    ¬ Second I f (Arm.r .PC m) := by
  rcases ht.2 with ⟨j, t, hj, hpc⟩ | ⟨j, bits, t, hj, -, hpc, -⟩
  · rw [hpc]; exact not_second_line hFf hj rfl
  · rw [hpc]; exact not_second_line hFf hj rfl

/-- **The model's memory-trap observable transfers to the executable machine**: for an
activation of `f` entered in `c` (at `f`'s address, return address no second word of `f`) whose
run is at a `TrapAtM` state at step `n`, with the per-state facts before it and no return before
it, every executable state `e` simulating `c` runs to a state with `ExecTrapM`. -/
theorem exec_of_trapAtM (hI : okBCleanup I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hH : HooksSim I B)
    (hD : ∀ g ∈ (prog I).funcs, (art I g).vcp.DestsInt) (hnogot : ∀ a, ¬ GotSlot I file a)
    {M : Nat} {f : Clif.Function} (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (hpc : Arm.r .PC c = (art I f).base) (hs : ¬ Second I f (xreg 30 c))
    {mp : ArmFault.MemMap} {tc : Clif.TrapCode} {n : Nat}
    (ht : TrapAtM mp (art I f).fa (art I f).fb (art I f).base tc (runX ((sys I B).mach M f) n c))
    (hgood : (sys I B).RunGoodLB n M f c)
    (hnr : ∀ j < n, ¬ Returned (art I f) c (runX ((sys I B).mach M f) j c))
    (e : Arm.ArmState) (hsim : Sim I c e) :
    ∃ k, ExecTrapM mp I file f tc (runX (step I B file) k e) := by
  have hrun := runOkSNB_of_good hI hc hF hH hD hnogot hf hgood hs
  obtain ⟨k', hk'⟩ := act_simNB hF hf hpc hsim hrun n (Nat.le_refl _) hnr
    (not_second_trapAtM (hF f hf) ht) ht.1.err
  exact ⟨k', execTrapM_of_sim (hF f hf) ht hk'⟩

end Transfer

/-! ## The binary-level theorems -/

section Binary

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- `RunGoodLB` does not depend on the exterior `F` of the linked system. -/
theorem runGoodLB_F {F F' : BitVec 64 → Prop} {n M : Nat} {f : Clif.Function} {c : Arm.ArmState}
    (h : (LinkSys.ofInputCleanup I B F).RunGoodLB n M f c) :
    (LinkSys.ofInputCleanup I B F').RunGoodLB n M f c := by
  intro M' g c' t hR he
  refine goodAt_F (h M' g c' t ?_ (by rw [mach_F I B F F']; exact he))
  rcases hR with ⟨k, hk, hno, h1, h2, h3, h4⟩ | ⟨M0, k, h, h1, hk, hno, hcall, herr, hR⟩
  · refine .inl ⟨k, hk, ?_, h1, h2, h3, ?_⟩ <;> rw [mach_F I B F F']
    · exact hno
    · exact h4
  · refine .inr ⟨M0, k, h, h1, hk, ?_, ?_, ?_, ?_⟩ <;> rw [mach_F I B F F']
    · exact hno
    · exact hcall
    · exact herr
    · exact reachL_F hR

/-- The dead-cleanup chain's facts of every function of a checked input. -/
theorem compiledCleanup_of (hI : okBCleanup I = true) {F : BitVec 64 → Prop} {g : Clif.Function}
    (hg : g ∈ (prog I).funcs) :
    CompiledCleanup g ((LinkSys.ofInputCleanup I B F).A g).k ((LinkSys.ofInputCleanup I B F).A g).vc
      ((LinkSys.ofInputCleanup I B F).A g).vcp ((LinkSys.ofInputCleanup I B F).A g).rf
      ((LinkSys.ofInputCleanup I B F).A g).af ((LinkSys.ofInputCleanup I B F).A g).fa
      ((LinkSys.ofInputCleanup I B F).A g).fb :=
  have hf := factsCleanup hI hg
  ⟨hf.pipe.1, hf.lowerOk, hf.pipe.2.1, hf.prepOk, hf.check, hf.pipe.2.2.1, hf.pipe.2.2.2.1,
    hf.pipe.2.2.2.2.1⟩

/-- **The model's memory-trap observable gives the executable's**, for an outside call of `f`
in `r` (callees' budget `K`). -/
theorem exec_memtrap_of_model {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true) (hbin : DeadCleanupBinCheck.BinOk I D file)
    (hnogot : ∀ a, ¬ GotSlot I file a) (hB : BaseOk (sys I B)) (hH : HooksSim I B)
    {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f) {K : Nat}
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + K) r args cs.mem)
    (hr : ClifRun I B f r args cs) {M : Nat} {mp : ArmFault.MemMap} {tc : Clif.TrapCode} {N : Nat}
    (ht : TrapAtM mp (art I f).fa (art I f).fb (art I f).base tc
      (runX ((LinkSys.ofInputCleanup I B (worldF I f K r)).mach M f) N (modelOf I f r)))
    (hgood : (LinkSys.ofInputCleanup I B (worldF I f K r)).RunGoodLB N M f (modelOf I f r)) :
    ∃ k, ExecTrapM mp I file f tc (runX (step I B file) k r) := by
  have hfm := (Clif.Program.func?_some hf).1
  have hfacts := binFacts_of_checks hI hbin
  have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f K r)) := baseOk_F hB
  have hL0 := okBCleanup_sound hI hB' fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premises hL0 hfm hro ho hr
  have hL' := okBCleanup_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
  have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOk hI hbin hL' hg
  have hra : ∀ k < (art I f).fb.words.size,
      xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
    simp only [xreg, r_modelOf]; exact hent.raOutside
  rw [mach_F I B (worldF I f K r) (fun _ => False)] at ht
  exact exec_of_trapAtM hI hcm hF hH (fun g hg => destsInt_of_ok hL' hg) hnogot hfm
    (by rw [r_modelOf]; exact ho.pc) (raNotSecond_top (hF f hfm) hra) ht (runGoodLB_F hgood)
    (no_return (hF f hfm) hra ht.1.err) r (sim_modelOf (hfacts.modelOf_ne hX))

/-- **The binary theorem about the executable's own words with memory traps** (entries without
a reachable call cycle): under the premises of `binary_correct_exec_proven` (no GOT slot in the
executable), a whole-program CLIF run that traps with `tc` under the run premise `TrapsExplicitM`
(every callee returns; a statement traps only explicitly or at a trapping atomic) and the memory
map premise `MapFaults mp` reaches, on the executable machine from `r`, a trap site of `f` with
`tc` whose instruction errs (`udf`) or faults under `mp` (`ExecTrapM`). -/
theorem binary_correct_exec_memtrap {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true) (hbin : DeadCleanupBinCheck.BinOk I D file)
    (hnogot : ∀ a, ¬ GotSlot I file a) (B : BaseEnv) (hB : BaseOk (sys I B)) (hH : HooksSim I B)
    {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicitM (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    {mp : ArmFault.MemMap} (hmf : MapFaults mp (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    {tc : Clif.TrapCode} (hrun : Clif.runLoop B.env (prog I) (M + 1) cs = .trapped tc) :
    ∃ k, ExecTrapM mp I file f tc (runX (step I B file) k r) := by
  have hn := (DeadCleanupStackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  have hfm := (Clif.Program.func?_some hf).1
  have hf' : (progOf I.resultsCleanup).func? n = some f := hf
  unfold DeadCleanupStackBound.goodN at hn
  rw [hf'] at hn
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn
  have hbud : DeadCleanupStackBound.bud I f = b := by simp [DeadCleanupStackBound.bud, hb]
  have hfacts := binFacts_of_checks hI hbin
  have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)) :=
    baseOk_F hB
  have hL0 := okBCleanup_sound hI hB' fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, hres, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ := premises hL0 hfm hro ho hr
  have hκ := DeadCleanupStackBound.budget_of hI B (worldF I f (DeadCleanupStackBound.bud I f) r)
  have hκf : ∀ M, (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)).hybrid
      (DeadCleanupStackBound.budO I) (DeadCleanupStackBound.budMax I) M f =
      DeadCleanupStackBound.bud I f := fun M => by simp [LinkSys.hybrid, hb, hbud]
  obtain ⟨N, ht, hgood⟩ := backend_correct_program_memtrap_budget _ hL0 hκ hfm
    (compiledCleanup_of hI hfm) M hent
    (by rw [hκf]; exact hres) (by rw [hκf]; rfl) (by rw [hκf]; exact hgfree) himg hbe hargs
    hr.entry hsav hrel hpl htr hmf hrun
  exact exec_memtrap_of_model hI hcm hbin hnogot hB hH hf hX ho hr ht hgood

/-- **`binary_correct_exec_memtrap` for the run's peak call depth** (any program, recursive ones
included): the stack `frameDrop + D * d` of the run's call depth `d` (`Clif.DepthLe`), the run
premises of the callees running with fuel `F` and at most `d - 1` callers of their own
(`Clif.linkEnvD`). -/
theorem binary_correct_exec_memtrap_peak {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true) (hbin : DeadCleanupBinCheck.BinOk I D file)
    (hnogot : ∀ a, ¬ GotSlot I file a) (B : BaseEnv) (hB : BaseOk (sys I B)) (hH : HooksSim I B)
    {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f) (F d : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : TrapsExplicitM (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs)
    {mp : ArmFault.MemMap} (hmf : MapFaults mp (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs)
    {tc : Clif.TrapCode} (hrun : Clif.runLoop B.env (prog I) (F + 1) cs = .trapped tc) :
    ∃ k, ExecTrapM mp I file f tc (runX (step I B file) k r) := by
  have hfm := (Clif.Program.func?_some hf).1
  have hfacts := binFacts_of_checks hI hbin
  have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (I.D * d) r)) := baseOk_F hB
  have hL0 := okBCleanup_sound hI hB' fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, hres, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ := premises hL0 hfm hro ho hr
  obtain ⟨N, ht, hgood⟩ := backend_correct_program_memtrap_peak _ hL0 (LinkSys.budget_K _ hL0) hfm
    (compiledCleanup_of hI hfm) F d hent hres rfl hgfree himg hbe hargs hr.entry hsav hrel hpl
    hd htr hmf hrun
  exact exec_memtrap_of_model hI hcm hbin hnogot hB hH hf hX ho hr ht hgood

end Binary

end E2E.DeadCleanupExecBytes

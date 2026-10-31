import FV.E2E.DeadCleanupExecPeak
import FV.E2E.LinkTrapCallInd

/-! # Callee traps on the executable machine (S9d, #377)

The executable theorems (`DeadCleanupExecBytes.binary_correct_exec_proven`, `ExecRefines`) name,
for a trapping run, only the trap sites of the entered function `f`. A run that traps inside a
callee (a function of the program, or code outside it: a panic, a `__*ti3` helper dividing by
zero) reaches no such site. Here the trap observable of the linked machine (`LinkSys.TrapIn`,
S9c) is carried to the executable machine `step I B file`:

* **`TrapAtE I B c e`**: the executable machine state `e` is at a trap site with code `c` of a
  compiled function of the program, or at a call of a compiled function whose callee outside the
  program traps with `c` (`LinkSys.BaseTrapCall` of a model state `e` simulates: the same
  registers and bytes but at relocated instruction bytes);
* **`ExecRefinesC`**: `ExecRefines` with `TrapAtE` as its trap clause (`ExecRefines.toC`: the old
  clause implies it);
* **`exec_of_trapIn`**: by induction on `TrapIn`, each level's run is simulated up to its stop
  state (`act_simN`, its per-state facts from `Stop.good`); at a call of a trapping program
  callee the executable's `bl`/`blr` enters the callee (`call_enter`, the call state's facts
  from `ProgCallOk`), whose activation has the observable one level down;
* **`binary_correct_exec_trap`** (entries without a reachable call cycle, stack bound
  `stackFn`), **`binary_correct_exec_trap_peak`** (the run's peak call depth `d`): a whole-program
  CLIF run that traps with `c` under the run premise `TrapsD` (no memory-access trap; callee
  traps allowed) gives an executable state with `TrapAtE … c`.
-/

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

/-! ## The trap observable of the executable machine -/

/-- **The executable machine state `e` is at a trap with code `c`**: at a trap site of a compiled
function of the program (`TrapAt`), or at a call of a compiled function `g` whose callee outside
the program traps with `c` (`LinkSys.BaseTrapCall` at a model state `u` that `e` simulates). -/
def TrapAtE (I : LinkInput) (B : BaseEnv) (c : Clif.TrapCode) (e : Arm.ArmState) : Prop :=
  (∃ g ∈ (prog I).funcs, TrapAt (art I g).fb (art I g).base c e) ∨
    ∃ g ∈ (prog I).funcs, ∃ u, Sim I u e ∧ (sys I B).BaseTrapCall g c u

/-- **`ExecRefines` with callee traps**: a return as `ExecRefines`; a trap with `c` is a state of
the executable machine's run at a trap with `c` (`TrapAtE`: a trap site of any compiled function,
or a call whose callee outside the program traps). -/
def ExecRefinesC (I : LinkInput) (B : BaseEnv) (ra : BitVec 64)
    (astep : Arm.ArmState → Arm.ArmState) (s : Arm.ArmState) (R : BitVec 64 → Prop) :
    Clif.Outcome → Prop
  | .returned vals cm => ∃ n, ArmRet ra s (runX astep n s) ∧
      (∀ (j : Nat) v, vals[j]? = some v → XHolds v (xreg j (runX astep n s))) ∧
      ∀ a b, cm.valid a 1 = true → cm.bytes a = some b → ¬ R (BitVec.ofNat 64 a) →
        Arm.read_mem (BitVec.ofNat 64 a) (runX astep n s) = b
  | .trapped c => ∃ n, TrapAtE I B c (runX astep n s)
  | .stuck _ | .outOfFuel => True

/-- `ExecRefines` of a function of the program gives `ExecRefinesC`. -/
theorem ExecRefines.toC {I : LinkInput} {B : BaseEnv} {f : Clif.Function}
    (hf : f ∈ (prog I).funcs) {ra : BitVec 64} {astep : Arm.ArmState → Arm.ArmState}
    {s : Arm.ArmState} {R : BitVec 64 → Prop} {o : Clif.Outcome}
    (h : ExecRefines (art I f).fb (art I f).base ra astep s R o) : ExecRefinesC I B ra astep s R o := by
  cases o with
  | returned vals cm => exact h
  | trapped c => obtain ⟨n, hn⟩ := h; exact ⟨n, .inl ⟨f, hf, hn⟩⟩
  | stuck _ => trivial
  | outOfFuel => trivial

section Lemmas

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- A call word of `g` is no second word of a pair (that word is the pair's `ldr`/`add`). -/
theorem not_second_callPc {g : Clif.Function} (hF : FnOk I file g) {pc : BitVec 64}
    (hca : CallPc (art I g).fa (art I g).base pc) : ¬ Second I g pc := by
  rintro ⟨rl, hrl, ht, he⟩
  obtain ⟨j, x, t, hj, hx, hpc⟩ := hca
  obtain ⟨-, -, r', hr', hr'o, hr't⟩ := pair_facts hF hrl ht
  obtain ⟨j2, i2, t2, hj2, hi2, ho2⟩ := (FnAsm.layout_relocs hF.layout r').1 hr'
  have h1 : insnAt (art I g).fa (art I g).base pc = some x := by
    rw [hpc]; exact insnAt_of_line hF hj
  have h2 : insnAt (art I g).fa (art I g).base pc = some i2 := by
    rw [he, ← hr'o, ← ho2]; exact insnAt_of_line hF hj2
  rw [h1] at h2
  cases h2
  rw [hr't] at hi2
  rcases hx with ⟨n, rfl⟩ | ⟨r, rfl⟩ <;> rcases ht with h | h <;> rw [h] at hi2 <;>
    simp [Insn.reloc?, loOf] at hi2

/-- **`RunOkSN` from the per-state facts**, for an executable without GOT slots (D4 vacuous) and
an activation whose return address is no second word of its function. -/
theorem runOkSN_of_good (hI : okBCleanup I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hH : HooksSim I B)
    (hD : ∀ g ∈ (prog I).funcs, (art I g).vcp.DestsInt) (hnogot : ∀ a, ¬ GotSlot I file a)
    {M : Nat} {f : Clif.Function} (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (hgood : (sys I B).RunGoodL M f c) (hs : ¬ Second I f (xreg 30 c)) :
    RunOkSN I B file M f c := by
  refine runOkSN_of_n hI hc hF hH hf fun M' g t hR he => ?_
  obtain ⟨c', hRL, hs'⟩ := reachL_of_reachN hI hc hF hR hf hgood hs
  have hg := reachN_mem hR hf
  have hG := hgood _ _ _ _ hRL he
  exact stepOkD_of_good hI hc hF hD hg hG hs' he
    ⟨insn_of_good hI hc hF hg hG, fun rl hrl ht _ rd G hrd h8 hin hw0 hw1 i hi =>
      (hnogot _ ⟨_, tab_mem (okBCleanup_names hI) hg, rl, hrl, ht, rd, G, hrd, h8, hin, hw0,
        hw1, i, hi, rfl⟩).elim⟩

/-- The executable's `CallsAt` at a call of a function of the program (`LinkSys.ProgCallAt`). -/
theorem callsAt_of_progCallAt {F : BitVec 64 → Prop} (hL : (LinkSys.ofInputCleanup I B F).Ok)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {g h : Clif.Function} (hg : g ∈ (prog I).funcs)
    (hh : h ∈ (prog I).funcs) {u : Arm.ArmState}
    (hprog : u.program = (art I g).fb.program (art I g).base)
    (hp : (LinkSys.ofInputCleanup I B F).ProgCallAt g h u) :
    CallsAt I B g u h ∧ ∃ x, insnAt (art I g).fa (art I g).base (Arm.r .PC u) = some x ∧
      ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) := by
  obtain ⟨info, regs, i', hsite, hasg, hP, -, hdest⟩ := hp
  obtain ⟨x, hins, hx⟩ := (LinkSys.ofInputCleanup I B F).insnAt_callAt hL hg hP
  have hFg := hF g hg
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hFg.layout
  obtain ⟨j0, t0, hj0, -⟩ := insnAt_spec hins
  have hb := progBase_of hFg hm hprog hj0
  cases hd : info.dest with
  | sym n =>
    obtain ⟨d, us, ds⟩ := info
    simp only at hd
    subst hd
    obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    have hn : n = h.name := by
      rcases hdest with e | ⟨e, -⟩ <;> simp [destOf] at e
      exact e
    subst hn
    exact ⟨.inl ⟨h.name, by rw [hb]; exact hins, func?_of_mem hL.names hh⟩, _, hins,
      .inl ⟨_, rfl⟩⟩
  | reg r =>
    obtain ⟨tv, Lu, Ld, rfl, -⟩ := hL.blrRegs g hg info hsite (fun n => by rw [hd]; simp)
    obtain ⟨r0, us', ds', -, rfl⟩ := assign_call_reg hasg
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    have ht : (blrTarget u).bind (symCallee (sys I B).Xb (prog I)) = some h := by
      rcases hdest with e | ⟨-, e⟩
      · simp [destOf] at e
      · exact e
    exact ⟨.inr ⟨⟨r0, by rw [hb]; exact hins⟩, ht⟩, _, hins, .inr ⟨_, rfl⟩⟩

/-- **`StepOkD` at the call state of a trapping program callee**: the facts the executable's
call step needs, from the call line and `ProgCallOk` (the model's step there is the linked call's
error state, at the next word). -/
theorem stepOkD_progCall (hI : okBCleanup I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {F : BitVec 64 → Prop}
    (hL : (LinkSys.ofInputCleanup I B F).Ok) {M : Nat} {g h : Clif.Function}
    (hg : g ∈ (prog I).funcs) {u : Arm.ArmState} (herr : Arm.r .ERR u = .None)
    (hprog : u.program = (art I g).fb.program (art I g).base)
    (hx : ∃ x, insnAt (art I g).fa (art I g).base (Arm.r .PC u) = some x ∧
      ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r))
    (hnext : Arm.r .PC ((sys I B).mach M g u) = Arm.r .PC u + 4)
    (hok : (LinkSys.ofInputCleanup I B F).ProgCallOk g h u) : StepOkD I B file M g u := by
  have hFg := hF g hg
  obtain ⟨x, hins, hxk⟩ := hx
  obtain ⟨j0, t0, hj0, hpc0⟩ := insnAt_spec hins
  have hcpc : CallPc (art I g).fa (art I g).base (Arm.r .PC u) := ⟨j0, x, t0, hj0, hxk, hpc0.symm⟩
  refine ⟨herr, hprog, ⟨x, hins, .inr ?_⟩, fun rl hrl ht hpc => ?_, fun i hi hh => ?_,
    fun rl hrl ht hpc => ?_, fun x' h' hx' ht => ?_⟩
  · rcases hxk with ⟨n, rfl⟩ | ⟨r, rfl⟩ <;> rfl
  · rw [hnext, ← wAt_add4] at hpc
    exact (BitVec.add_left_inj _).mp hpc
  · rw [hins] at hi
    cases hi
    rcases hxk with ⟨n, rfl⟩ | ⟨r, rfl⟩ <;> cases hh
  · exact absurd ⟨rl, hrl, .inl ht, hpc⟩ (not_second_callPc hFg hcpc)
  · obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hFg.layout
    obtain ⟨j, tt, hj, hpc⟩ := insnAt_spec hx'
    obtain ⟨info, tv, hsi, hd, hbt⟩ := hok.blrAt x' h' hx' ht
    have hh' : h' ∈ (prog I).funcs := by
      obtain ⟨a, -, ha⟩ := Option.bind_eq_some_iff.1 ht
      exact List.mem_of_find?_eq_some ha
    obtain ⟨h4, w, -, hk⟩ := FnAsm.layout_word hFg.layout hm hj rfl
    have hfw := hFg.bin.plain _ w hk (fun r hr' ho => by
      obtain ⟨j', i', t', hj', hi', ho'⟩ := (FnAsm.layout_relocs hFg.layout r).1 hr'
      have := line_unique hj hj' (by omega)
      subst this
      simp [Insn.reloc?] at hi')
    have hrd := hL.imgCode g hg u hok.code _ w hk
    rw [show 4 * (lineOffset (art I g).fa.lines.toList j / 4) =
      lineOffset (art I g).fa.lines.toList j by omega] at hfw hrd
    refine ⟨hok.xzr x' hx', ?_, symAddr_of_blrTo (B := B) hI hc hg hh' hsi hd hbt⟩
    rw [← hpc]
    exact hfw.trans (congrArg some hrd.symm)

end Lemmas

/-! ## The transfer of the trap observable -/

section Transfer

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- **The linked machine's trap observable transfers to the executable machine**: for an
activation of `g` entered in `c` (at `g`'s address, return address no second word of `g`, no
return before its stop state) with the trap observable `TrapIn … c tc` of the linked program of
the input (any exterior `F`), every executable state `e` simulating `c` runs to a state at a trap
with `tc` (`TrapAtE`). -/
theorem exec_of_trapIn (hI : okBCleanup I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hH : HooksSim I B)
    (hD : ∀ g ∈ (prog I).funcs, (art I g).vcp.DestsInt) (hnogot : ∀ a, ¬ GotSlot I file a)
    {F : BitVec 64 → Prop} (hL : (LinkSys.ofInputCleanup I B F).Ok) {tc : Clif.TrapCode}
    {M : Nat} {g : Clif.Function} {c : Arm.ArmState}
    (hT : (LinkSys.ofInputCleanup I B F).TrapIn M g c tc) :
    g ∈ (prog I).funcs → Arm.r .PC c = (art I g).base → ¬ Second I g (xreg 30 c) →
    (∀ n, (LinkSys.ofInputCleanup I B F).Stop M g c n → ∀ j < n,
      ¬ Returned (art I g) c (runX ((sys I B).mach M g) j c)) →
    ∀ e, Sim I c e → ∃ k, TrapAtE I B tc (runX (step I B file) k e) := by
  induction hT with
  | @site M g c tc n hst hat =>
    intro hg hpc hs hnr e hsim
    have hmach := mach_F I B F (fun _ => False) M g
    have hrun := runOkSN_of_good hI hc hF hH hD hnogot hg (runGoodL_F hst.good) hs
    have herr : Arm.r .ERR (runX ((sys I B).mach M g) n c) = .None := by
      rw [← hmach]; exact hst.err
    have hret := hnr n hst
    rw [hmach] at hat
    by_cases hsec : Second I g (Arm.r .PC (runX ((sys I B).mach M g) n c))
    · -- a trap at a second word: one executable step after the first word
      obtain ⟨rl, hrl, ht, he⟩ := hsec
      cases n with
      | zero => exact (not_second_base (hF g hg) ⟨rl, hrl, ht, hpc.symm.trans he⟩).elim
      | succ n1 =>
      have hok1 := hrun _ _ _ (ReachN.act (k := n1) fun j hj => hret j (by omega))
        (by rw [← runX_succ' ((sys I B).mach M g)]; exact herr)
      have hpc1 := hok1.cf rl hrl ht (by rw [← runX_succ' ((sys I B).mach M g) n1]; exact he)
      obtain ⟨k', hk'⟩ := act_simN (B := B) hF M g c e hg hpc hsim hrun n1
        (fun j hj => hret j (by omega)) (by rw [hpc1]; exact first_not_second (hF g hg) hrl ht)
        hok1.err
      obtain ⟨hpcE, herrE⟩ := pair_first_pc (hF g hg) hrl ht hpc1 hok1 hk'
      refine ⟨k' + 1, .inl ⟨g, hg, ?_⟩⟩
      rw [runX_succ'] at hat ⊢
      exact ⟨by rw [← herrE]; exact hat.err, by rw [← hpcE]; exact hat.site⟩
    · obtain ⟨k', hk'⟩ := act_simN (B := B) hF M g c e hg hpc hsim hrun n hret hsec herr
      exact ⟨k', .inl ⟨g, hg, by rw [hk'.1]; exact hat.err, by rw [hk'.1]; exact hat.site⟩⟩
  | @base M g c tc n hst hbt =>
    intro hg hpc hs hnr e hsim
    have hmach := mach_F I B F (fun _ => False) M g
    have hrun := runOkSN_of_good hI hc hF hH hD hnogot hg (runGoodL_F hst.good) hs
    have herr : Arm.r .ERR (runX ((sys I B).mach M g) n c) = .None := by
      rw [← hmach]; exact hst.err
    rw [hmach] at hbt
    have hbt' := hbt
    obtain ⟨info, -, -, -, ops, regs, i', w, F', so, out, cc, -, -, hP, -⟩ := hbt'
    obtain ⟨k', hk'⟩ := act_simN (B := B) hF M g c e hg hpc hsim hrun n (hnr n hst)
      (not_second_callPc (hF g hg) hP.callPc) herr
    exact ⟨k', .inr ⟨g, hg, _, hk', hbt⟩⟩
  | @prog M g h c tc n hst hpca hok hra hT ih =>
    intro hg hpc hs hnr e hsim
    have hmach := mach_F I B F (fun _ => False) (M + 1) g
    have hrun := runOkSN_of_good hI hc hF hH hD hnogot hg (runGoodL_F hst.good) hs
    have herr : Arm.r .ERR (runX ((sys I B).mach (M + 1) g) n c) = .None := by
      rw [← hmach]; exact hst.err
    have hprog : (runX ((sys I B).mach (M + 1) g) n c).program = (art I g).fb.program (art I g).base := by
      rw [← hmach]; exact hst.prog
    have hret := hnr n hst
    rw [hmach] at hpca hok hra hT ih
    generalize hu : runX ((sys I B).mach (M + 1) g) n c = u at herr hprog hpca hok hra hT ih
    have hh : h ∈ (prog I).funcs := hok.mem
    obtain ⟨hcalls, hx⟩ := callsAt_of_progCallAt hL hF hg hh hprog hpca
    obtain ⟨info, regs, i', -, -, hP, -, -⟩ := hpca
    have hsec := not_second_callPc (hF g hg) hP.callPc
    obtain ⟨k', hk'⟩ := act_simN (B := B) hF (M + 1) g c e hg hpc hsim hrun n hret
      (by rw [hu]; exact hsec) (by rw [hu]; exact herr)
    rw [hu] at hk'
    -- the model's step at `u` is the linked call's error state, at the next word
    have hjunk := (LinkSys.ofInputCleanup I B F).pcall_junk hL hh hT hra
    have hnext : Arm.r .PC ((sys I B).mach (M + 1) g u) = Arm.r .PC u + 4 := by
      rw [mach_call hcalls]
      have e : (sys I B).pcall (M + 1) h u = (LinkSys.ofInputCleanup I B F).pcall (M + 1) h u := by
        simp only [LinkSys.pcall]; rw [hooks_F I B (fun _ => False) F]; rfl
      rw [e, hjunk]
      simp only [junkAt]
      rw [Arm.r_of_w_different (by simp), Arm.r_of_w_same]
    have hok0 : StepOk I B file (M + 1) g u :=
      stepOk_of_d hI hc hF hH hg (stepOkD_progCall hI hc hF hL hg herr hprog hx hnext hok)
    have hent := call_enter (hF g hg) (hF h hh) hok0 hk' hcalls
    obtain ⟨k'', hk''⟩ := ih hh (pc_enterAt _ _) (raNotSecond_enter hI hc hF hg hprog hcalls)
      (fun n' hst' j _ hR => (LinkSys.ofInputCleanup I B F).noRet_of_stop hL hh hst' hra j
        (by rw [mach_F I B F (fun _ => False)]; exact returned_iff.2 hR)) _ hent
    refine ⟨k' + 1 + k'', ?_⟩
    rw [runX_add, runX_succ']
    exact hk''

end Transfer

/-! ## The binary-level theorems -/

section Binary

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}
/-- The outside code's trap contract does not depend on the exterior `F`. -/
theorem baseTrapsOk_F {F F' : BitVec 64 → Prop}
    (h : (LinkSys.ofInputCleanup I B F).BaseTrapsOk) :
    (LinkSys.ofInputCleanup I B F').BaseTrapsOk :=
  ⟨h.xt, h.stop, h.err, h.tlsErr⟩

/-- The run premise `TrapsD` does not depend on the exterior `F`. -/
theorem trapsD_F (c : Nat → Clif.State → Clif.Outcome) (F F' : BitVec 64 → Prop) :
    ∀ M, ((LinkSys.ofInputCleanup I B F).withCrun c).TrapsD M =
      ((LinkSys.ofInputCleanup I B F').withCrun c).TrapsD M
  | 0 => rfl
  | M + 1 => by
    show ((LinkSys.ofInputCleanup I B F).withCrun c).TrapsAt (M + 1)
        (((LinkSys.ofInputCleanup I B F).withCrun c).TrapsD M) =
      ((LinkSys.ofInputCleanup I B F').withCrun c).TrapsAt (M + 1)
        (((LinkSys.ofInputCleanup I B F').withCrun c).TrapsD M)
    rw [trapsD_F c F F' M]
    rfl

theorem std_trapsD_F {F F' : BitVec 64 → Prop} {M : Nat} {g : Clif.Function} {cs : Clif.State}
    (h : (LinkSys.ofInputCleanup I B F).std.TrapsD M g cs) :
    (LinkSys.ofInputCleanup I B F').std.TrapsD M g cs := by
  have e := trapsD_F (I := I) (B := B) (fun M => Clif.runLoop (sys I B).base (sys I B).P M) F F' M
  exact e ▸ h

theorem peak_trapsD_F {F F' : BitVec 64 → Prop} {Fu M : Nat} {g : Clif.Function}
    {cs : Clif.State} (h : ((LinkSys.ofInputCleanup I B F).peak Fu).TrapsD M g cs) :
    ((LinkSys.ofInputCleanup I B F').peak Fu).TrapsD M g cs := by
  have e := trapsD_F (I := I) (B := B) (fun M => Clif.runD (sys I B).base (sys I B).P Fu M) F F' M
  exact e ▸ h


/-- **The model's trap observable gives the executable's**: for an outside call of `f` in `r`
(callees' budget `K`), the trap observable of the linked machine from the model state of `r`
gives an executable state of the run from `r` at a trap with the same code. -/
theorem exec_trap_of_model {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true) (hbin : DeadCleanupBinCheck.BinOk I D file)
    (hnogot : ∀ a, ¬ GotSlot I file a) (hB : BaseOk (sys I B)) (hH : HooksSim I B)
    {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f) {K : Nat}
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + K) r args cs.mem)
    (hr : ClifRun I B f r args cs) {M : Nat} {tc : Clif.TrapCode}
    (hT : (LinkSys.ofInputCleanup I B (worldF I f K r)).TrapIn M f (modelOf I f r) tc) :
    ∃ k, TrapAtE I B tc (runX (step I B file) k r) := by
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
  exact exec_of_trapIn hI hcm hF hH (fun g hg => destsInt_of_ok hL' hg) hnogot hL0 hT hfm
    (by rw [r_modelOf]; exact ho.pc) (raNotSecond_top (hF f hfm) hra)
    (fun n hst => no_return (hF f hfm) hra
      (by rw [← mach_F I B (worldF I f K r)]; exact hst.err))
    r (sim_modelOf (hfacts.modelOf_ne hX))

/-- The per-function facts of the trap theorem from the checker (`okBCleanup`), the lowering's
unwinding validator and no `try_call` terminator. -/
theorem trapsOk_of {F : BitVec 64 → Prop} (hI : okBCleanup I = true)
    (hU : ∀ g ∈ (prog I).funcs, lowerCheckU g (art I g).vc = true)
    (hnoTry : ∀ g ∈ (prog I).funcs, ∀ b ∈ g.blocks, b.term.isTry = false) :
    (LinkSys.ofInputCleanup I B F).TrapsOk where
  cleanup g hg := by
    have hf := factsCleanup hI hg
    exact ⟨hf.pipe.1, hf.lowerOk, hf.pipe.2.1, hf.prepOk, hf.check, hf.pipe.2.2.1,
      hf.pipe.2.2.2.1, hf.pipe.2.2.2.2.1⟩
  lowerU := hU
  noTry := hnoTry

/-- **The binary theorem about the executable's own words with callee traps** (entries without
a reachable call cycle): under the premises of `binary_correct_exec_proven` (no GOT slot in the
executable), the lowering's unwinding validator, no `try_call` terminator and the outside code's
trap contract (`BaseTrapsOk`), a whole-program CLIF run that traps with `tc` under the run premise
`TrapsD` (no memory-access trap; callee traps allowed) reaches, on the executable machine from
`r`, a state at a trap with `tc` (`TrapAtE`). -/
theorem binary_correct_exec_trap {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true) (hbin : DeadCleanupBinCheck.BinOk I D file)
    (hnogot : ∀ a, ¬ GotSlot I file a) (B : BaseEnv) (hB : BaseOk (sys I B)) (hH : HooksSim I B)
    (hU : ∀ g ∈ (prog I).funcs, lowerCheckU g (art I g).vc = true)
    (hnoTry : ∀ g ∈ (prog I).funcs, ∀ b ∈ g.blocks, b.term.isTry = false)
    (hBT : (sys I B).BaseTrapsOk) {n : String} {f : Clif.Function}
    (hf : (prog I).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs) (htr : (sys I B).std.TrapsD M f cs) {tc : Clif.TrapCode}
    (hrun : Clif.runLoop B.env (prog I) (M + 1) cs = .trapped tc) :
    ∃ k, TrapAtE I B tc (runX (step I B file) k r) := by
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
  have hT := backend_correct_program_trap_budget _ hL0 (trapsOk_of hI hU hnoTry) (baseTrapsOk_F hBT)
    hκ hfm M hent
    (by rw [hκf]; exact ⟨hres, by rw [← hκf M]; exact hκ.2 M f hfm⟩) (by rw [hκf]; rfl)
    (by rw [hκf]; exact hgfree) himg hbe hargs
    hr.entry hsav hrel hpl (std_trapsD_F htr) hrun
  exact exec_trap_of_model hI hcm hbin hnogot hB hH hf hX ho hr hT

/-- **`binary_correct_exec_trap` for the run's peak call depth** (any program, recursive ones
included): the stack `frameDrop + (D * d + pbMax I)` of the run's call depth `d` (`Clif.DepthLe`;
#581: with the stack probes of the deepest activation), the run
premise `TrapsD` of the callees running with fuel `F` and at most `d - 1` callers of their own
(`LinkSys.peak`). -/
theorem binary_correct_exec_trap_peak {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true) (hbin : DeadCleanupBinCheck.BinOk I D file)
    (hnogot : ∀ a, ¬ GotSlot I file a) (B : BaseEnv) (hB : BaseOk (sys I B)) (hH : HooksSim I B)
    (hU : ∀ g ∈ (prog I).funcs, lowerCheckU g (art I g).vc = true)
    (hnoTry : ∀ g ∈ (prog I).funcs, ∀ b ∈ g.blocks, b.term.isTry = false)
    (hBT : (sys I B).BaseTrapsOk) {n : String} {f : Clif.Function}
    (hf : (prog I).func? n = some f) (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + (I.D * d + pbMax I)) r
      args cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : ((sys I B).peak F).TrapsD d f cs) {tc : Clif.TrapCode}
    (hrun : Clif.runLoop B.env (prog I) (F + 1) cs = .trapped tc) :
    ∃ k, TrapAtE I B tc (runX (step I B file) k r) := by
  have hfm := (Clif.Program.func?_some hf).1
  have hfacts := binFacts_of_checks hI hbin
  have hB' : BaseOk (LinkSys.ofInputCleanup I B (worldF I f (I.D * d + pbMax I) r)) := baseOk_F hB
  have hL0 := okBCleanup_sound hI hB' fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, hres, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ := premises hL0 hfm hro ho hr
  have hT := backend_correct_program_trap_peak _ hL0 (trapsOk_of hI hU hnoTry) (baseTrapsOk_F hBT)
    (LinkSys.budget_K _ hL0) hfm F d hent ⟨hres, (LinkSys.budget_K _ hL0).2 d f hfm⟩ rfl hgfree himg
    hbe hargs hr.entry hsav hrel hpl
    hd (peak_trapsD_F htr) hrun
  exact exec_trap_of_model hI hcm hbin hnogot hB hH hf hX ho hr hT

end Binary

end E2E.DeadCleanupExecBytes

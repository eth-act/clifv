import FV.E2E.DeadCleanupExecFault
import FV.E2E.DeadCleanupExecPeak
import FV.E2E.LinkMemTrapW

/-!
# No access before the trap faults, on the executable machine (A3, #412, slices F8c/F8d)

`docs/plans/memfault.md`, F8. `binary_correct_exec_memtrap{,_peak}` (F6) name the executable
state at the trapping atomic's `ldaxr` (`ExecTrapM`); here the run of the fault-aware executable
machine `stepF mp I B file` (`FV/E2E/DeadCleanupExecFault.lean`) gets there: no step before it
faults under the memory map `mp` (`NoFault`), so it is the run of `step`, and its next step errs.

The premise on `mp` is `MapRelRW`: every byte `mp` does not allow to be written lies outside the
reserved stack, the stack arguments and every allocation of the entry's CLIF memory, and the
program's code is readable. So every byte valid in the entry's CLIF memory must be mapped
**read-write**, read-only data objects included (the F8a write guard, #472, will relax this to
the CLIF-writable bytes). The proof keeps the unwritable bytes `NW` with the code image
(`sysSK I B f K r NW`, as the GOT slots of `DeadCleanupExecGot`): then the per-state facts with
the writes (`RunGoodLBW`, `LinkMemTrapW`) say every access of every model state before the trap
is outside `NW` or a jump-table read (`RL.evsOk_of_goodXW`), and faults depend only on the
registers (`E2E.ExecBytes.evsOk_congr`), which the simulating executable state shares.

* `EvsOkAt`, `RunOkSNF`, `ActSimNF`, `RunOkSNBF`: the simulation's per-state hypotheses and
  conclusions with the faults: `act_coreNF`, `act_simNF`, `act_simNBF` (`act_coreN`, `act_simN`,
  `act_simNB` with "no earlier executable step faults");
* `noFault_plain`, `noFault_hook`, `noFault_call`, `noFault_pair`: the executable's step at each
  kind of site does not fault;
* `evsOkAt_of_goodW`, `runOkSNBF_of_good`: the hypotheses from `RunGoodLBW` of `sysSK … NW`;
* `exec_of_trapAtMF`; the observable `ExecTrapF` and the premise `MapRelRW`;
  **`binary_correct_exec_memtrapF_rw`**, **`binary_correct_exec_memtrapF_rw_peak`**.
-/

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

/-! ## Instructions without memory access -/

/-- An instruction that is no load or store accesses no byte a map forbids. -/
theorem evsOk_of_notLDST (mp : ArmFault.MemMap) {a : Arm.ArmInst} (h : ∀ i, a ≠ .LDST i)
    (s : Arm.ArmState) : ArmFault.evsOk mp (Concurrency.ArmInstFoot.instEvs a s) = true := by
  cases a with
  | LDST i => exact absurd rfl (h i)
  | BR i =>
    cases i <;> simp [Concurrency.ArmInstFoot.instEvs, ArmFault.evsOk, ArmFault.evOk,
      Concurrency.ArmInstFoot.dmbEv]
  | _ => rfl

section Lemmas

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- No fault at a step whose word decodes to an instruction that is no load or store. -/
theorem noFault_of_decode {mp : ArmFault.MemMap} {e : Arm.ArmState} {a : Arm.ArmInst}
    (ha : (fileWord file (Arm.r .PC e)).bind Arm.decode_raw_inst = some a)
    (h : ∀ i, a ≠ .LDST i) : NoFault mp I B file e :=
  noFault_of_evsOk fun a' _ ha' => by
    rw [ha] at ha'
    cases ha'
    exact evsOk_of_notLDST mp h e

end Lemmas

/-! ## The hypotheses with the faults -/

section Defs

variable (mp : ArmFault.MemMap) (I : LinkInput) (B : BaseEnv) (file : ByteArray)

/-- **No access of the model's step from `m` (of `g`) faults under `mp`**: the decoded word at
the pc of an instruction without hook accesses only bytes `mp` allows. -/
def EvsOkAt (g : Clif.Function) (m : Arm.ArmState) : Prop :=
  ∀ i, insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i → i.hooked = false →
    ∀ a, (fileWord file (Arm.r .PC m)).bind Arm.decode_raw_inst = some a →
    ArmFault.evsOk mp (Concurrency.ArmInstFoot.instEvs a m) = true

/-- `RunOkSN` with `EvsOkAt`. -/
def RunOkSNF (M : Nat) (f : Clif.Function) (c : Arm.ArmState) : Prop :=
  ∀ M' g t, ReachN I B M f c M' g t → Arm.r .ERR ((sys I B).mach M' g t) = .None →
    StepOk I B file M' g t ∧ EvsOkAt mp I file g t

/-- `RunOkSNB` with `EvsOkAt`. -/
def RunOkSNBF (n M : Nat) (f : Clif.Function) (c : Arm.ArmState) : Prop :=
  ∀ M' g t, ReachNB I B n M f c M' g t → Arm.r .ERR ((sys I B).mach M' g t) = .None →
    StepOk I B file M' g t ∧ EvsOkAt mp I file g t

/-- **`ActSimN` with the faults**: the simulating executable state is reached without a
faulting step. -/
def ActSimNF (M : Nat) : Prop :=
  ∀ g c e, g ∈ (prog I).funcs → Arm.r .PC c = (art I g).base → Sim I c e →
    RunOkSNF mp I B file M g c →
    ∀ k, (∀ j < k, ¬ Returned (art I g) c (runX ((sys I B).mach M g) j c)) →
    ¬ Second I g (Arm.r .PC (runX ((sys I B).mach M g) k c)) →
    Arm.r .ERR (runX ((sys I B).mach M g) k c) = .None →
    ∃ k', Sim I (runX ((sys I B).mach M g) k c) (runX (step I B file) k' e) ∧
      ∀ j < k', NoFault mp I B file (runX (step I B file) j e)

end Defs

/-! ## One step without fault -/

section Steps

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- **An instruction without hook**: the executable's step faults iff the model's does
(`evsOk_congr`), and the model's does not. -/
theorem noFault_plain {mp : ArmFault.MemMap} {M : Nat} {g : Clif.Function} {m e : Arm.ArmState}
    (hev : EvsOkAt mp I file g m) (hs : Sim I m e) {i : Insn}
    (hins : insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i) (hh : i.hooked = false) :
    NoFault mp I B file e :=
  noFault_of_evsOk fun a _ ha => by
    rw [hs.1 .PC] at ha
    rw [E2E.ExecBytes.evsOk_congr hs.1 mp a]
    exact hev i hins hh a ha

/-- **A call of outside code and the TLS sequence**: the hooks, which do not fault. -/
theorem noFault_hook {mp : ArmFault.MemMap} {M : Nat} {g : Clif.Function} {m e : Arm.ArmState}
    (h0 : StepOk I B file M g m) (hs : Sim I m e) {i : Insn}
    (hins : insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i)
    (hk : (∃ n, i = .bl n ∧ (prog I).func? n = none) ∨
      (∃ x, i = .blr x ∧ (blrTarget m).bind (symCallee (sys I B).Xb (prog I)) = none) ∨
      (∃ a b, i = .adrpTlsDesc a b) ∨ ∃ a b c, i = .ldrTlsDescLo12 a b c) :
    NoFault mp I B file e := by
  have hsite : siteAt I (Arm.r .PC e) = some (siteOf (prog I) i) := by
    rw [hs.1 .PC]; exact siteAt_of h0 hins
  apply noFault_of_site
  rcases hk with ⟨n, rfl, hn⟩ | ⟨x, rfl, hn⟩ | ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩
  · exact .inl ⟨n, by rw [hsite]; simp [siteOf, hn]⟩
  · refine .inr (.inr (.inr ⟨by rw [hsite]; rfl, ?_⟩))
    rw [blrTarget_sim hs (h0.plain _ hins rfl), hn]
    rfl
  · exact .inr (.inl (by rw [hsite]; rfl))
  · exact .inr (.inr (.inl ⟨a, c, by rw [hsite]; rfl⟩))

/-- **A call of a function of the program**: the `bl`/`blr` word, no memory access. -/
theorem noFault_call {mp : ArmFault.MemMap} {M : Nat} {g h : Clif.Function} (hF : FnOk I file g)
    {m e : Arm.ArmState} (h0 : StepOk I B file M g m) (hs : Sim I m e)
    (hc : CallsAt I B g m h) : NoFault mp I B file e := by
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hF.layout
  obtain ⟨i0, hi0, -, -⟩ := h0.site
  obtain ⟨j, t, hj, hpc⟩ := insnAt_spec hi0
  have hb : progBase m = (art I g).base := progBase_of hF hm h0.program hj
  have hpe : Arm.r .PC e = Arm.r .PC m := hs.1 .PC
  simp only [CallsAt, hb] at hc
  rcases hc with ⟨n, hins, hn⟩ | ⟨⟨x, hins⟩, hcal⟩
  · rw [hins] at hi0; cases hi0
    have hrl := line_reloc hF hj (show (Insn.bl n).reloc? = some (.call26, n, 0) from rfl)
    have hR := hF.bin.reloc _ hrl
    simp only [RelocOk] at hR
    obtain ⟨-, -, hrange, hword⟩ := hR
    obtain ⟨hd, -⟩ := ExecWords.blW_exec hrange
    exact noFault_of_decode (by
      rw [hpe, ← hpc]; show (readN _ 4 (wAt _ _)).bind _ = _; rw [hword, Option.bind_some]; exact hd)
      (fun _ h => by cases h)
  · rw [hins] at hi0; cases hi0
    obtain ⟨hx, -, -⟩ := h0.blr x h hins hcal
    obtain ⟨w, rn, -, hw, hdw⟩ := blr_word hF hm hj hx
    exact noFault_of_decode (by
      rw [hpe, ← hpc]; show (fileWord file (wAt _ _)).bind _ = _; rw [hw, Option.bind_some]
      exact hdw)
      (fun _ h => by cases h)

/-- **A pair** (`adrp` and `add`): two steps without memory access. A GOT pair (`adrp` and `ldr`
of a slot) does not occur: the executable has no GOT slot. -/
theorem noFault_pair (hI : okBCleanup I = true) (hnogot : ∀ a, ¬ GotSlot I file a)
    {mp : ArmFault.MemMap} {M : Nat} {g : Clif.Function} (hg : g ∈ (prog I).funcs)
    (hF : FnOk I file g) {rl : Reloc} (hrl : rl ∈ (art I g).fb.relocs)
    (ht : rl.type = .adrGotPage ∨ rl.type = .adrPrelPgHi21) {m e : Arm.ArmState}
    (hpc : Arm.r .PC m = wAt (art I g) rl.offset) (h0 : StepOk I B file M g m) (hs : Sim I m e) :
    NoFault mp I B file e ∧ NoFault mp I B file (step I B file e) := by
  obtain ⟨j, i, t, hj, hi, ho⟩ := (FnAsm.layout_relocs hF.layout rl).1 hrl
  have hR := hF.bin.reloc rl hrl
  have hins : insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i := by
    rw [hpc, ← ho]; exact insnAt_of_line hF hj
  obtain ⟨rd, hrd⟩ : ∃ rd : Reg, (rl.type = .adrGotPage ∧ i = .adrpGot rd rl.sym ∧ rl.addend = 0) ∨
      (rl.type = .adrPrelPgHi21 ∧ i = .adrp rd rl.sym rl.addend) := by
    rcases ht with ht | ht <;> rw [ht] at hi <;> cases i <;> simp [Insn.reloc?] at hi
    · exact ⟨_, .inl ⟨ht, by rw [hi.1], hi.2.symm⟩⟩
    · exact ⟨_, .inr ⟨ht, by rw [hi.1, hi.2]⟩⟩
  have hR' : rl.offset % 4 = 0 ∧ ∃ rdN x0 x1, rdN < 31 ∧
      (art I g).fb.words[rl.offset / 4]? = some (adrpW rdN 0) ∧
      (∃ r' ∈ (art I g).fb.relocs, r'.offset = rl.offset + 4 ∧ r'.type = loOf rl.type) ∧
      fileWord file (wAt (art I g) rl.offset) = some x0 ∧
      fileWord file (wAt (art I g) (rl.offset + 4)) = some x1 ∧
      PairOk (Elf.loadMem file) (wAt (art I g) rl.offset).toNat
        (I.symAddr rl.sym rl.addend).toNat rdN (decide (rl.type = .adrGotPage)) x0 x1 := by
    unfold RelocOk at hR
    rcases ht with ht | ht <;> rw [ht] at hR ⊢ <;>
    · obtain ⟨h4, rdN, x0, x1, hlt, hw0, -, ⟨r', hr', hr'o, hr't, -⟩, hx0, hx1, hp⟩ := hR
      exact ⟨h4, rdN, x0, x1, hlt, hw0, ⟨r', hr', hr'o, hr't⟩, hx0, hx1, hp⟩
  obtain ⟨-, rdN, x0, x1, hlt, -, -, hx0, hx1, hp⟩ := hR'
  have hpe : Arm.r .PC e = Arm.r .PC m := hs.1 .PC
  have hee : Arm.r .ERR e = .None := (hs.1 .ERR).trans h0.err
  have hsite0 : siteAt I (Arm.r .PC e) = some (siteOf (prog I) i) := by
    rw [hpe]; exact siteAt_of h0 hins
  have hstep0 : ∀ a, (fileWord file (Arm.r .PC e)).bind Arm.decode_raw_inst = some a →
      step I B file e = Arm.exec_inst a e := fun a ha => by
    rw [step_site hsite0, stepAt_real _ (by rcases hrd with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> simp)
      (by rcases hrd with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> simp)
      (by rcases hrd with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> simp)
      (by rcases hrd with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> simp), realStep_eq hee ha]
  cases hp with
  | adrpAdd hr e0 e1 =>
    subst e0 e1
    obtain ⟨ha0, hx0e⟩ := ExecWords.adrpW_exec hlt hr
    have hd0 : (fileWord file (Arm.r .PC e)).bind Arm.decode_raw_inst = some (ExecWords.adrpI rdN
        (pageOf (I.symAddr rl.sym rl.addend).toNat - pageOf (wAt (art I g) rl.offset).toNat)) := by
      rw [hpe, hpc, hx0, Option.bind_some]; exact ha0
    refine ⟨noFault_of_decode hd0 (fun _ h => by cases h), ?_⟩
    obtain ⟨ha1, -⟩ := ExecWords.addW_exec hlt hlt (Nat.mod_lt _ (by decide))
    have hpc1 : Arm.r .PC (step I B file e) = wAt (art I g) (rl.offset + 4) := by
      rw [hstep0 _ hd0, hx0e, Arm.r_of_w_same, hpe, hpc, wAt_add4]
    exact noFault_of_decode (by rw [hpc1, hx1, Option.bind_some]; exact ha1) (fun _ h => by cases h)
  | adrpLdr G hgot h8 hr e0 e1 hG =>
    subst e0 e1
    have hgt : rl.type = .adrGotPage := by simpa using hgot
    exact (hnogot _ ⟨_, tab_mem (okBCleanup_names hI) hg, rl, hrl, hgt, rdN, G, hlt, h8, hr, hx0,
      hx1, 0, by decide, rfl⟩).elim

end Steps

/-! ## The simulation without fault -/

section Core

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

theorem RunOkSNF.toS {mp : ArmFault.MemMap} {M : Nat} {f : Clif.Function} {c : Arm.ArmState}
    (h : RunOkSNF mp I B file M f c) : RunOkSN I B file M f c :=
  fun M' g t hR he => (h M' g t hR he).1

/-- One more executable step without fault. -/
theorem noFault_snoc {mp : ArmFault.MemMap} {e : Arm.ArmState} {k' : Nat}
    (hnf : ∀ j < k', NoFault mp I B file (runX (step I B file) j e))
    (hn : NoFault mp I B file (runX (step I B file) k' e)) :
    ∀ j < k' + 1, NoFault mp I B file (runX (step I B file) j e) := fun j hj => by
  rcases (show j < k' ∨ j = k' by omega) with hj | rfl
  · exact hnf j hj
  · exact hn

/-- **`act_coreN` with the faults.** -/
theorem act_coreNF (hI : okBCleanup I = true) (hnogot : ∀ a, ¬ GotSlot I file a)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {mp : ArmFault.MemMap} (M : Nat)
    (hcall : ∀ M', M = M' + 1 → ActSimNF mp I B file M') : ActSimNF mp I B file M := by
  intro g c e hg hpc hsim hrun k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro hret hsec herr
  have hFg := hF g hg
  have hok : ∀ j, (∀ j' ≤ j, ¬ Returned (art I g) c (runX ((sys I B).mach M g) j' c)) →
      Arm.r .ERR (runX ((sys I B).mach M g) (j + 1) c) = .None →
      StepOk I B file M g (runX ((sys I B).mach M g) j c) ∧
        EvsOkAt mp I file g (runX ((sys I B).mach M g) j c) := fun j hj he =>
    hrun _ _ _ (ReachN.act hj) (by rw [← runX_succ' ((sys I B).mach M g)]; exact he)
  cases k with
  | zero => exact ⟨0, hsim, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k0 =>
  obtain ⟨hok0, hev0⟩ := hok k0 (fun j hj => hret j (by omega)) herr
  rw [runX_succ'] at hsec herr ⊢
  by_cases hs : Second I g (Arm.r .PC (runX ((sys I B).mach M g) k0 c))
  · -- the second word of a pair: two steps from its first word
    obtain ⟨rl, hrl, ht, he⟩ := hs
    cases k0 with
    | zero => exact (not_second_base hFg ⟨rl, hrl, ht, hpc.symm.trans he⟩).elim
    | succ k1 =>
    obtain ⟨hok1, -⟩ := hok k1 (fun j hj => hret j (by omega)) hok0.err
    have hpc1 := hok1.cf rl hrl ht (by rw [← runX_succ' ((sys I B).mach M g) k1]; exact he)
    obtain ⟨k', hk', hnf⟩ := ih k1 (by omega) (fun j hj => hret j (by omega))
      (by rw [hpc1]; exact first_not_second hFg hrl ht) hok1.err
    obtain ⟨hn0, hn1⟩ := noFault_pair hI hnogot hg hFg hrl ht hpc1 hok1 hk'
    refine ⟨k' + 2, ?_, fun j hj => ?_⟩
    · rw [runX_succ', runX_add (step I B file) k' 2]
      exact pair_step hFg hrl ht hpc1 hok1
        (by rw [← runX_succ' ((sys I B).mach M g) k1]; exact hok0) hk'
    · rcases (show j < k' ∨ j = k' ∨ j = k' + 1 by omega) with hj | rfl | rfl
      · exact hnf j hj
      · exact hn0
      · rw [runX_succ']; exact hn1
  · obtain ⟨k', hk', hnf⟩ := ih k0 (by omega) (fun j hj => hret j (by omega)) hs hok0.err
    obtain ⟨i, hins, -, -⟩ := hok0.site
    obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hFg.layout
    obtain ⟨j0, t0, hj0, -⟩ := insnAt_spec hins
    have hb := progBase_of hFg hm hok0.program hj0
    -- one step of the executable
    have hone : ∀ x, NoFault mp I B file (runX (step I B file) k' e) →
        Sim I x (step I B file (runX (step I B file) k' e)) →
        ∃ k'', Sim I x (runX (step I B file) k'' e) ∧
          ∀ j < k'', NoFault mp I B file (runX (step I B file) j e) := fun x hn hx =>
      ⟨k' + 1, by rw [runX_succ']; exact hx, noFault_snoc hnf hn⟩
    -- a call of a function of the program
    have hprog : ∀ h, CallsAt I B g (runX ((sys I B).mach M g) k0 c) h →
        ∃ k'', Sim I ((sys I B).mach M g (runX ((sys I B).mach M g) k0 c))
          (runX (step I B file) k'' e) ∧
          ∀ j < k'', NoFault mp I B file (runX (step I B file) j e) := by
      intro h hc
      have hh := callee_mem hc
      have hn := noFault_call (mp := mp) hFg hok0 hk' hc
      rw [mach_call hc] at herr ⊢
      cases M with
      | zero => exact absurd herr (junkAt_err _)
      | succ M' =>
      have hrun' : RunOkSNF mp I B file M' h
          (enterAt (art I h) (runX ((sys I B).mach (M' + 1) g) k0 c)) :=
        fun M'' g' t hr he => hrun _ _ _ (ReachN.nest (fun j hj => hret j (by omega)) hc
          (by rw [runX_succ', mach_call hc]; exact herr) hr) he
      simp only [LinkSys.pcall] at herr ⊢
      have hent := call_enter hFg (hF h hh) hok0 hk' hc
      unfold linkedCall at herr ⊢
      split
      · rename_i hex
        obtain ⟨hN, hmin⟩ := firstNat_spec _ hex
        obtain ⟨k2, hk2, hnf2⟩ := hcall M' rfl h _ _ hh (pc_enterAt _ _) hent hrun' _
          (fun j hj hr => hmin j hj (returned_iff.2 hr))
          (ret_not_secondN hF hg hh hok0 hc hrun'.toS hN hmin) hN.2.1
        refine ⟨k' + 1 + k2, by rw [runX_add, runX_add]; exact sim_set_program _ hk2,
          fun j hj => ?_⟩
        rcases (show j < k' + 1 ∨ k' + 1 ≤ j by omega) with hj' | hj'
        · exact noFault_snoc hnf hn j hj'
        · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj'
          rw [runX_add, runX_add]
          exact hnf2 d (by omega)
      · simp [‹¬ _›, junkAt, Arm.r_of_w_same] at herr
    by_cases hhk : i.hooked = false
    · exact hone _ (noFault_plain (M := M) hev0 hk' hins hhk) (plain_step hFg hok0 hk' hins hhk)
    · cases i <;> simp only [Insn.hooked, Bool.true_eq_false, not_false_eq_true, not_true_eq_false] at hhk
      case bl n =>
        cases hn : (prog I).func? n with
        | none =>
          exact hone _ (noFault_hook hok0 hk' hins (.inl ⟨n, rfl, hn⟩))
            (hook_step hFg hok0 hk' hins (.inl ⟨n, rfl, hn⟩))
        | some h => exact hprog h (.inl ⟨n, by rw [hb]; exact hins, hn⟩)
      case blr x =>
        cases hn : (blrTarget (runX ((sys I B).mach M g) k0 c)).bind (symCallee (sys I B).Xb (prog I)) with
        | none =>
          exact hone _ (noFault_hook hok0 hk' hins (.inr (.inl ⟨x, rfl, hn⟩)))
            (hook_step hFg hok0 hk' hins (.inr (.inl ⟨x, rfl, hn⟩)))
        | some h => exact hprog h (.inr ⟨⟨x, by rw [hb]; exact hins⟩, hn⟩)
      case adrpGot a b => exact absurd (adrp_lands hFg hok0 hins (.inl ⟨a, b, rfl⟩)) hsec
      case adrp a b d => exact absurd (adrp_lands hFg hok0 hins (.inr ⟨a, b, d, rfl⟩)) hsec
      case ldrGotLo12 a b d => exact absurd (second_of_lo12 hFg hins (.inl ⟨a, b, d, rfl⟩)) hs
      case addLo12 a b d f => exact absurd (second_of_lo12 hFg hins (.inr ⟨a, b, d, f, rfl⟩)) hs
      case adrpTlsDesc a b =>
        exact hone _ (noFault_hook hok0 hk' hins (.inr (.inr (.inl ⟨a, b, rfl⟩))))
          (hook_step hFg hok0 hk' hins (.inr (.inr (.inl ⟨a, b, rfl⟩))))
      case ldrTlsDescLo12 a b d =>
        exact hone _ (noFault_hook hok0 hk' hins (.inr (.inr (.inr ⟨a, b, d, rfl⟩))))
          (hook_step hFg hok0 hk' hins (.inr (.inr (.inr ⟨a, b, d, rfl⟩))))

/-- **The simulation without fault at every depth.** -/
theorem act_simNF (hI : okBCleanup I = true) (hnogot : ∀ a, ¬ GotSlot I file a)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {mp : ArmFault.MemMap} :
    ∀ M, ActSimNF mp I B file M
  | 0 => act_coreNF hI hnogot hF 0 fun _ h => by cases h
  | M + 1 => act_coreNF hI hnogot hF (M + 1) fun M' h => by
    obtain rfl : M = M' := Nat.succ.inj h
    exact act_simNF hI hnogot hF M

/-- **`act_simNB` with the faults**: the states of the entry activation before its step `n`. -/
theorem act_simNBF (hI : okBCleanup I = true) (hnogot : ∀ a, ¬ GotSlot I file a)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {mp : ArmFault.MemMap} {M : Nat}
    {g : Clif.Function} {c e : Arm.ArmState} (hg : g ∈ (prog I).funcs)
    (hpc : Arm.r .PC c = (art I g).base) (hsim : Sim I c e) {n : Nat}
    (hrun : RunOkSNBF mp I B file n M g c) :
    ∀ k ≤ n, (∀ j < k, ¬ Returned (art I g) c (runX ((sys I B).mach M g) j c)) →
    ¬ Second I g (Arm.r .PC (runX ((sys I B).mach M g) k c)) →
    Arm.r .ERR (runX ((sys I B).mach M g) k c) = .None →
    ∃ k', Sim I (runX ((sys I B).mach M g) k c) (runX (step I B file) k' e) ∧
      ∀ j < k', NoFault mp I B file (runX (step I B file) j e) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro hkn hret hsec herr
  have hFg := hF g hg
  have hok : ∀ j, j < n → (∀ j' ≤ j, ¬ Returned (art I g) c (runX ((sys I B).mach M g) j' c)) →
      Arm.r .ERR (runX ((sys I B).mach M g) (j + 1) c) = .None →
      StepOk I B file M g (runX ((sys I B).mach M g) j c) ∧
        EvsOkAt mp I file g (runX ((sys I B).mach M g) j c) := fun j hjn hj he =>
    hrun _ _ _ (.inl ⟨j, hjn, hj, rfl, rfl, rfl⟩) (by rw [← runX_succ' ((sys I B).mach M g)]; exact he)
  cases k with
  | zero => exact ⟨0, hsim, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k0 =>
  obtain ⟨hok0, hev0⟩ := hok k0 (by omega) (fun j hj => hret j (by omega)) herr
  rw [runX_succ'] at hsec herr ⊢
  by_cases hs : Second I g (Arm.r .PC (runX ((sys I B).mach M g) k0 c))
  · obtain ⟨rl, hrl, ht, he⟩ := hs
    cases k0 with
    | zero => exact (not_second_base hFg ⟨rl, hrl, ht, hpc.symm.trans he⟩).elim
    | succ k1 =>
    obtain ⟨hok1, -⟩ := hok k1 (by omega) (fun j hj => hret j (by omega)) hok0.err
    have hpc1 := hok1.cf rl hrl ht (by rw [← runX_succ' ((sys I B).mach M g) k1]; exact he)
    obtain ⟨k', hk', hnf⟩ := ih k1 (by omega) (by omega) (fun j hj => hret j (by omega))
      (by rw [hpc1]; exact first_not_second hFg hrl ht) hok1.err
    obtain ⟨hn0, hn1⟩ := noFault_pair hI hnogot hg hFg hrl ht hpc1 hok1 hk'
    refine ⟨k' + 2, ?_, fun j hj => ?_⟩
    · rw [runX_succ', runX_add (step I B file) k' 2]
      exact pair_step hFg hrl ht hpc1 hok1
        (by rw [← runX_succ' ((sys I B).mach M g) k1]; exact hok0) hk'
    · rcases (show j < k' ∨ j = k' ∨ j = k' + 1 by omega) with hj | rfl | rfl
      · exact hnf j hj
      · exact hn0
      · rw [runX_succ']; exact hn1
  · obtain ⟨k', hk', hnf⟩ := ih k0 (by omega) (by omega) (fun j hj => hret j (by omega)) hs
      hok0.err
    obtain ⟨i, hins, -, -⟩ := hok0.site
    obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hFg.layout
    obtain ⟨j0, t0, hj0, -⟩ := insnAt_spec hins
    have hb := progBase_of hFg hm hok0.program hj0
    have hone : ∀ x, NoFault mp I B file (runX (step I B file) k' e) →
        Sim I x (step I B file (runX (step I B file) k' e)) →
        ∃ k'', Sim I x (runX (step I B file) k'' e) ∧
          ∀ j < k'', NoFault mp I B file (runX (step I B file) j e) := fun x hn hx =>
      ⟨k' + 1, by rw [runX_succ']; exact hx, noFault_snoc hnf hn⟩
    have hprog : ∀ h, CallsAt I B g (runX ((sys I B).mach M g) k0 c) h →
        ∃ k'', Sim I ((sys I B).mach M g (runX ((sys I B).mach M g) k0 c))
          (runX (step I B file) k'' e) ∧
          ∀ j < k'', NoFault mp I B file (runX (step I B file) j e) := by
      intro h hc
      have hh := callee_mem hc
      have hn := noFault_call (mp := mp) hFg hok0 hk' hc
      rw [mach_call hc] at herr ⊢
      cases M with
      | zero => exact absurd herr (junkAt_err _)
      | succ M' =>
      have hrun' : RunOkSNF mp I B file M' h
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
        obtain ⟨k2, hk2, hnf2⟩ := act_simNF hI hnogot hF M' h _ _ hh (pc_enterAt _ _) hent hrun' _
          (fun j hj hr => hmin j hj (returned_iff.2 hr))
          (ret_not_secondN hF hg hh hok0 hc hrun'.toS hN hmin) hN.2.1
        refine ⟨k' + 1 + k2, by rw [runX_add, runX_add]; exact sim_set_program _ hk2,
          fun j hj => ?_⟩
        rcases (show j < k' + 1 ∨ k' + 1 ≤ j by omega) with hj' | hj'
        · exact noFault_snoc hnf hn j hj'
        · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj'
          rw [runX_add, runX_add]
          exact hnf2 d (by omega)
      · simp [‹¬ _›, junkAt, Arm.r_of_w_same] at herr
    by_cases hhk : i.hooked = false
    · exact hone _ (noFault_plain (M := M) hev0 hk' hins hhk) (plain_step hFg hok0 hk' hins hhk)
    · cases i <;> simp only [Insn.hooked, Bool.true_eq_false, not_false_eq_true, not_true_eq_false] at hhk
      case bl n =>
        cases hn : (prog I).func? n with
        | none =>
          exact hone _ (noFault_hook hok0 hk' hins (.inl ⟨n, rfl, hn⟩))
            (hook_step hFg hok0 hk' hins (.inl ⟨n, rfl, hn⟩))
        | some h => exact hprog h (.inl ⟨n, by rw [hb]; exact hins, hn⟩)
      case blr x =>
        cases hn : (blrTarget (runX ((sys I B).mach M g) k0 c)).bind (symCallee (sys I B).Xb (prog I)) with
        | none =>
          exact hone _ (noFault_hook hok0 hk' hins (.inr (.inl ⟨x, rfl, hn⟩)))
            (hook_step hFg hok0 hk' hins (.inr (.inl ⟨x, rfl, hn⟩)))
        | some h => exact hprog h (.inr ⟨⟨x, by rw [hb]; exact hins⟩, hn⟩)
      case adrpGot a b => exact absurd (adrp_lands hFg hok0 hins (.inl ⟨a, b, rfl⟩)) hsec
      case adrp a b d => exact absurd (adrp_lands hFg hok0 hins (.inr ⟨a, b, d, rfl⟩)) hsec
      case ldrGotLo12 a b d => exact absurd (second_of_lo12 hFg hins (.inl ⟨a, b, d, rfl⟩)) hs
      case addLo12 a b d f => exact absurd (second_of_lo12 hFg hins (.inr ⟨a, b, d, f, rfl⟩)) hs
      case adrpTlsDesc a b =>
        exact hone _ (noFault_hook hok0 hk' hins (.inr (.inr (.inl ⟨a, b, rfl⟩))))
          (hook_step hFg hok0 hk' hins (.inr (.inr (.inl ⟨a, b, rfl⟩))))
      case ldrTlsDescLo12 a b d =>
        exact hone _ (noFault_hook hok0 hk' hins (.inr (.inr (.inr ⟨a, b, d, rfl⟩))))
          (hook_step hFg hok0 hk' hins (.inr (.inr (.inr ⟨a, b, d, rfl⟩))))

end Core

/-! ## The hypotheses from the per-state facts with the writes -/

section Good

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- A code line of a function of the program lies in the program's code image. -/
theorem img_line (hI : okBCleanup I = true) {g : Clif.Function} (hg : g ∈ (prog I).funcs)
    (hF : FnOk I file g) {j : Nat} {l : Line} (hj : (art I g).fa.lines.toList[j]? = some l)
    (hl : l.isLabel = false) {k : Nat} (hk : k < 4) :
    img I (wAt (art I g) (lineOffset (art I g).fa.lines.toList j) + BitVec.ofNat 64 k) := by
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hF.layout
  obtain ⟨h4, w, -, hw⟩ := FnAsm.layout_word hF.layout hm hj hl
  refine ⟨(g, art I g), tab_mem (okBCleanup_names hI) hg,
    ((art I g).base + BitVec.ofNat 64 (4 * (0 + lineOffset (art I g).fa.lines.toList j / 4)), w),
    ?_, ?_⟩
  · have := wordsAt_mem (base := (art I g).base) (k := 0) (ws := (art I g).fb.words.toList)
      (j := lineOffset (art I g).fa.lines.toList j / 4) (w := w) (by simpa using hw)
    simpa [FnBin.program] using this
  show ((wAt (art I g) (lineOffset (art I g).fa.lines.toList j) + BitVec.ofNat 64 k) - _).toNat < 4
  simp only [wAt]
  rw [Nat.zero_add, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h4),
    BitVec.add_comm ((art I g).base + _) (BitVec.ofNat 64 k), BitVec.add_sub_cancel]
  simp only [BitVec.toNat_ofNat]
  omega

/-- **`EvsOkAt` from the per-state facts with the writes** of the system keeping the bytes `S`,
when every byte `mp` does not allow to be written is a code byte or in `S`, and the code is
readable. -/
theorem evsOkAt_of_goodW (hI : okBCleanup I = true) (hF : ∀ g ∈ (prog I).funcs, FnOk I file g)
    {mp : ArmFault.MemMap} {f : Clif.Function} {K : Nat} {r : Arm.ArmState}
    {S : BitVec 64 → Prop} (hS : ∀ a, (mp a).allows .W = false → img I a ∨ S a)
    (hcode : ∀ a, img I a → (mp a).allows .R = true) {M : Nat} {g : Clif.Function}
    (hg : g ∈ (prog I).funcs) {c t : Arm.ArmState}
    (h : (sysSK I B f K r S).GoodAtW M g c t) : EvsOkAt mp I file g t := by
  obtain ⟨X, K, G, gv, -, hG, himg, -, -⟩ := h
  unfold actGoodXW at hG
  have hFg := hF g hg
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hFg.layout
  intro i hi hh a ha
  obtain ⟨j, tt, hj, hpc⟩ := insnAt_spec hi
  obtain ⟨x, ⟨jx, tx, hjx, hpcx⟩, htl⟩ := hG.1.line
  have hxi : x = i := by
    have h1 := insnAt_of_line hFg hjx
    have h2 : wAt (art I g) (lineOffset (art I g).fa.lines.toList jx) = Arm.r .PC t := hpcx.symm
    rw [h2, hi] at h1
    exact (Option.some.inj h1).symm
  subst hxi
  have hr : x.reloc? = none := (Insn.reloc_of_tlsTail htl).resolve_right (by rw [hh]; decide)
  obtain ⟨w, hw, hfw⟩ := fileWord_plain hFg hm hj hr
  have hpcw : Arm.r .PC t = wAt (art I g) (lineOffset (art I g).fa.lines.toList j) := hpc.symm
  rw [hpcw, hfw, Option.bind_some] at ha
  obtain ⟨a', ha', hd⟩ := Insn.decode_encode hw
  rw [ha] at hd
  cases hd
  exact RL.evsOk_of_goodXW hG (fun b hb => himg b (hS b hb))
    (fun j' tg bs hj' k hk => hcode _ (img_line hI hg hFg hj' rfl hk))
    (fun j' d hj' k hk => hcode _ (img_line hI hg hFg hj' rfl hk)) hj hpcw hh
    (by rw [RL.envL_of_lm hm]; exact ha')

/-- The `ReachLB` states of the plain system are those of the system keeping `S`. -/
theorem reachLB_sysSK {f0 : Clif.Function} {K : Nat} {r : Arm.ArmState} {S : BitVec 64 → Prop}
    {n M : Nat} {f : Clif.Function} {c : Arm.ArmState} {M' : Nat} {g : Clif.Function}
    {c' t : Arm.ArmState} (h : (sys I B).ReachLB n M f c M' g c' t) :
    (sysSK I B f0 K r S).ReachLB n M f c M' g c' t := by
  rcases h with ⟨k, hk, hno, h1, h2, h3, h4⟩ | ⟨M0, k, h, h1, hk, hno, hcall, herr, hR⟩
  · refine .inl ⟨k, hk, ?_, h1, h2, h3, ?_⟩ <;> rw [mach_sysSK]
    · exact hno
    · exact h4
  · refine .inr ⟨M0, k, h, h1, hk, ?_, ?_, ?_, ?_⟩ <;> try rw [mach_sysSK]
    · exact hno
    · exact hcall
    · exact herr
    · exact LinkSys.reachL_extImg (F := worldFS I f0 K r S) (S := S) (m := (modelOf I f0 r).mem)
        (E2E.DeadCleanupBinary.reachL_F (F := worldF I f0 K r) (F' := fun _ => False) hR)

/-- The per-state facts with the writes of the system keeping `S` give the plain system's. -/
theorem goodAt_of_sysSK {f0 : Clif.Function} {K : Nat} {r : Arm.ArmState} {S : BitVec 64 → Prop}
    {M : Nat} {g : Clif.Function} {c t : Arm.ArmState} (h : (sysSK I B f0 K r S).GoodAtW M g c t) :
    (sys I B).GoodAt M g c t := by
  obtain ⟨X, K', G, gv, heq, hg, hi, hm, hb⟩ := h
  have hh : (sysSK I B f0 K r S).hooks M = (sys I B).hooks M := by
    rw [sysSK, LinkSys.hooks_extImg, hooks_F]
  rw [hh, mach_sysSK] at heq
  rw [hh] at hg
  exact ⟨X, K', G, gv, heq, hg.toX, fun a ha => hi a (.inl ha),
    fun a ha => (hm a (.inl ha)).trans (mem_modelOf_img (f := f0) ha), hb⟩

/-- **`RunOkSNBF` from the per-state facts with the writes** of the system keeping the unwritable
bytes `S`. -/
theorem runOkSNBF_of_good (hI : okBCleanup I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hH : HooksSim I B)
    (hD : ∀ g ∈ (prog I).funcs, (art I g).vcp.DestsInt) (hnogot : ∀ a, ¬ GotSlot I file a)
    {mp : ArmFault.MemMap} {f0 : Clif.Function} {K : Nat} {r : Arm.ArmState}
    {S : BitVec 64 → Prop} (hS : ∀ a, (mp a).allows .W = false → img I a ∨ S a)
    (hcode : ∀ a, img I a → (mp a).allows .R = true)
    {n M : Nat} {f : Clif.Function} (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (hgood : (sysSK I B f0 K r S).RunGoodLBW n M f c) (hs : ¬ Second I f (xreg 30 c)) :
    RunOkSNBF mp I B file n M f c := by
  have hgood' : (sys I B).RunGoodLB n M f c := fun M' g c' t hR he =>
    goodAt_of_sysSK (hgood M' g c' t (reachLB_sysSK hR) (by rw [mach_sysSK]; exact he))
  have hrun := runOkSNB_of_good hI hc hF hH hD hnogot hf hgood' hs
  intro M' g t hR he
  refine ⟨hrun M' g t hR he, ?_⟩
  obtain ⟨c', hRL, -⟩ := reachLB_of_reachNB hI hc hF hR hf hgood' hs
  exact evsOkAt_of_goodW hI hF hS hcode (reachNB_mem hR hf)
    (hgood _ _ _ _ (reachLB_sysSK hRL) (by rw [mach_sysSK]; exact he))

end Good

/-! ## The transfer -/

section Transfer

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- The site of a `TrapAtM` state is a processor step. -/
theorem siteAt_trapAtM (hI : okBCleanup I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {f : Clif.Function} (hf : f ∈ (prog I).funcs)
    {mp : ArmFault.MemMap} {tc : Clif.TrapCode} {m : Arm.ArmState}
    (ht : TrapAtM mp (art I f).fa (art I f).fb (art I f).base tc m) :
    siteAt I (Arm.r .PC m) = some .real := by
  rcases ht.2 with ⟨j, t, hj, hpc⟩ | ⟨j, bits, t, hj, -, hpc, -⟩
  · rw [hpc]; exact siteAt_static hI hc hF hf (insnAt_of_line (hF f hf) hj)
  · rw [hpc]; exact siteAt_static hI hc hF hf (insnAt_of_line (hF f hf) hj)

/-- **The model's memory-trap state transfers to the fault-aware executable machine**: from
every executable state `e` simulating the entry `c`, the run of `stepF mp` reaches, without a
faulting step, a state with `ExecTrapM`, and its next step errs. -/
theorem exec_of_trapAtMF (hI : okBCleanup I = true) (hc : codeMapB I (tabOf I.resultsCleanup) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hnogot : ∀ a, ¬ GotSlot I file a)
    {M : Nat} {f : Clif.Function} (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (hpc : Arm.r .PC c = (art I f).base) {mp : ArmFault.MemMap} {tc : Clif.TrapCode} {n : Nat}
    (ht : TrapAtM mp (art I f).fa (art I f).fb (art I f).base tc (runX ((sys I B).mach M f) n c))
    (hrun : RunOkSNBF mp I B file n M f c)
    (hnr : ∀ j < n, ¬ Returned (art I f) c (runX ((sys I B).mach M f) j c))
    (e : Arm.ArmState) (hsim : Sim I c e) :
    ∃ k, (∀ j < k, NoFault mp I B file (runX (stepF mp I B file) j e)) ∧
      ExecTrapM mp I file f tc (runX (stepF mp I B file) k e) ∧
      Arm.r .ERR (runX (stepF mp I B file) (k + 1) e) ≠ .None := by
  obtain ⟨k, hk, hnf⟩ := act_simNBF hI hnogot hF hf hpc hsim hrun n (Nat.le_refl _) hnr
    (not_second_trapAtM (hF f hf) ht) ht.1.err
  have hpre : ∀ j ≤ k, runX (stepF mp I B file) j e = runX (step I B file) j e := fun j hj =>
    runX_stepF fun j' hj' => hnf j' (by omega)
  have hx := execTrapM_of_sim (hF f hf) ht hk
  refine ⟨k, fun j hj => by rw [hpre j (by omega)]; exact hnf j hj,
    by rw [hpre k (Nat.le_refl _)]; exact hx,
    ?_⟩
  rw [runX_succ', hpre k (Nat.le_refl _)]
  obtain ⟨⟨herr, -⟩, a, ha, hfa⟩ := hx
  exact stepF_err herr (by rw [hk.1 .PC]; exact siteAt_trapAtM hI hc hF hf ht) ha hfa

end Transfer

/-! ## The binary-level theorems -/

section Binary

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- **The fault-aware executable's observable of a trap with code `c` of `f`**: the run of the
executable machine with faults `stepF mp` from `r` reaches, with no faulting step before it
(`NoFault`: every earlier step is the step of `step`), a trap site of `f` with `c` whose
instruction errs (`udf`) or faults under `mp` (`ExecTrapM`), and its step there errs. -/
def ExecTrapF (mp : ArmFault.MemMap) (I : LinkInput) (B : BaseEnv) (file : ByteArray)
    (f : Clif.Function) (c : Clif.TrapCode) (r : Arm.ArmState) : Prop :=
  ∃ k, (∀ j < k, NoFault mp I B file (runX (stepF mp I B file) j r)) ∧
    ExecTrapM mp I file f c (runX (stepF mp I B file) k r) ∧
    Arm.r .ERR (runX (stepF mp I B file) (k + 1) r) ≠ .None

/-- **The memory map premise with every entry CLIF byte read-write** (F8; `_rw`): every byte
`mp` does not allow to be written lies outside the reserved stack `N` below `r`'s stack pointer,
the stack arguments and every allocation of the entry's CLIF memory `cm` (so read-only data
objects must be mapped read-write too), and the program's code is readable. -/
structure MapRelRW (mp : ArmFault.MemMap) (I : LinkInput) (f : Clif.Function) (N : Nat)
    (r : Arm.ArmState) (args : List Clif.Val) (cm : Clif.Mem) : Prop where
  nw : OutsideAvoids (fun a => (mp a).allows .W = false) f N r args cm
  code : ∀ a, img I a → (mp a).allows .R = true

/-- **The model's memory-trap state of `f` called in `r` gives the fault-aware executable's**,
from the per-state facts with the writes of the system keeping the unwritable bytes. -/
theorem exec_memtrapF_of_model {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true) (hbin : DeadCleanupBinCheck.BinOk I D file)
    (hnogot : ∀ a, ¬ GotSlot I file a) (hB : BaseOk (sys I B)) (hH : HooksSim I B)
    {f : Clif.Function} (hfm : f ∈ (prog I).funcs) {K : Nat} {r : Arm.ArmState}
    (hX : (imageOf file).Intact r) (hpc : Arm.r .PC r = (art I f).base)
    (hra : ∀ k < (art I f).fb.words.size,
      xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    {mp : ArmFault.MemMap} (hcode : ∀ a, img I a → (mp a).allows .R = true)
    {M : Nat} {tc : Clif.TrapCode} {N : Nat}
    (ht : TrapAtM mp (art I f).fa (art I f).fb (art I f).base tc
      (runX ((sys I B).mach M f) N (modelOf I f r)))
    (hgood : (sysSK I B f K r fun a => (mp a).allows .W = false).RunGoodLBW N M f (modelOf I f r)) :
    ExecTrapF mp I B file f tc r := by
  have hfacts := binFacts_of_checks hI hbin
  have hL' := okBCleanup_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
  have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOk hI hbin hL' hg
  have hs := raNotSecond_top (hF f hfm) hra
  exact exec_of_trapAtMF hI hcm hF hnogot hfm (by rw [r_modelOf]; exact hpc) ht
    (runOkSNBF_of_good hI hcm hF hH (fun g hg => destsInt_of_ok hL' hg) hnogot
      (fun a ha => .inr ha) hcode hfm hgood hs)
    (no_return (hF f hfm) hra ht.1.err) r (sim_modelOf (hfacts.modelOf_ne hX))

/-- **The binary theorem about the executable's own words with memory faults** (entries without
a reachable call cycle; every entry CLIF byte mapped read-write, `MapRelRW`): under the premises
of `binary_correct_exec_memtrap`, a whole-program CLIF run that traps with `tc` under
`TrapsExplicitM` and `MapFaults mp` makes the fault-aware executable machine `stepF mp` run from
`r` to a trap site of `f` with `tc` whose instruction errs (`udf`) or faults under `mp`
(`ExecTrapM`), with no faulting step before it (`NoFault`: every earlier step is the step of
`step`), and its step there errs. -/
theorem binary_correct_exec_memtrapF_rw {D : List Clif.DataObject} (hI : okBCleanup I = true)
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
    (hmap : MapRelRW mp I f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    {tc : Clif.TrapCode} (hrun : Clif.runLoop B.env (prog I) (M + 1) cs = .trapped tc) :
    ExecTrapF mp I B file f tc r := by
  have hn := (DeadCleanupStackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  have hfm := (Clif.Program.func?_some hf).1
  have hf' : (progOf I.resultsCleanup).func? n = some f := hf
  unfold DeadCleanupStackBound.goodN at hn
  rw [hf'] at hn
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn
  have hbud : DeadCleanupStackBound.bud I f = b := by simp [DeadCleanupStackBound.bud, hb]
  have ho' : OutsideCall I (BinCheck.roByte I D) f
      (frameDrop (art I f).af + DeadCleanupStackBound.bud I f) r args cs.mem := ho
  obtain ⟨hL, hent, hres, hgfree, hbe, hargs, hsav, hrel, hpl⟩ :=
    sysSK_entry hI hbin hB hfm hX ho' hmap.nw hr
  have hκ := DeadCleanupStackBound.budget_of hI B
    (worldF I f (DeadCleanupStackBound.bud I f) r)
  have hκf : ∀ M, (LinkSys.ofInputCleanup I B (worldF I f (DeadCleanupStackBound.bud I f) r)).hybrid
      (DeadCleanupStackBound.budO I) (DeadCleanupStackBound.budMax I) M f =
      DeadCleanupStackBound.bud I f := fun M => by simp [LinkSys.hybrid, hb, hbud]
  obtain ⟨N, ht, hgood⟩ := backend_correct_program_memtrapW_budget _ hL (hκ.extImg _ _ _) hfm
    (compiledCleanup_of (B := B) (F := worldF I f (DeadCleanupStackBound.bud I f) r) hI hfm) M hent
    (by rw [hκf]; exact hres) (by rw [hκf]; rfl) (by rw [hκf]; exact hgfree) (fun a _ => rfl) hbe
    hargs hr.entry hsav hrel hpl htr hmf hrun
  rw [mach_sysSK] at ht
  exact exec_memtrapF_of_model hI hcm hbin hnogot hB hH hfm hX ho.pc
    (by simp only [xreg, r_modelOf]; exact hent.raOutside) hmap.code ht hgood

/-- **`binary_correct_exec_memtrapF_rw` for the run's peak call depth** (any program, recursive
ones included). -/
theorem binary_correct_exec_memtrapF_rw_peak {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true) (hbin : DeadCleanupBinCheck.BinOk I D file)
    (hnogot : ∀ a, ¬ GotSlot I file a) (B : BaseEnv) (hB : BaseOk (sys I B)) (hH : HooksSim I B)
    {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f) (F d : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    (hr : ClifRun I B f r args cs) (hd : Clif.DepthLe B.env (prog I) d cs)
    (htr : TrapsExplicitM (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs)
    {mp : ArmFault.MemMap} (hmf : MapFaults mp (Clif.linkEnvD (prog I) B.env F d) (prog I).bare cs)
    (hmap : MapRelRW mp I f (frameDrop (art I f).af + I.D * d) r args cs.mem)
    {tc : Clif.TrapCode} (hrun : Clif.runLoop B.env (prog I) (F + 1) cs = .trapped tc) :
    ExecTrapF mp I B file f tc r := by
  have hfm := (Clif.Program.func?_some hf).1
  obtain ⟨hL, hent, hres, hgfree, hbe, hargs, hsav, hrel, hpl⟩ :=
    sysSK_entry hI hbin hB hfm hX ho hmap.nw hr
  obtain ⟨N, ht, hgood⟩ := backend_correct_program_memtrapW_peak _ hL
    ((LinkSys.budget_K _ (okBCleanup_sound hI (baseOk_F hB) fun _ h => .inr h)).extImg _ _ _) hfm
    (compiledCleanup_of (B := B) (F := worldF I f (I.D * d) r) hI hfm)
    F d hent hres rfl hgfree (fun a _ => rfl) hbe hargs hr.entry hsav hrel hpl hd htr hmf hrun
  rw [mach_sysSK] at ht
  exact exec_memtrapF_of_model hI hcm hbin hnogot hB hH hfm hX ho.pc
    (by simp only [xreg, r_modelOf]; exact hent.raOutside) hmap.code ht hgood

end Binary

end E2E.DeadCleanupExecBytes

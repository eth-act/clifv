import FV.E2E.SemanticExecTlsCf
import FV.Arm.Tpidr

/-! # The executable's TLS words, run for real (T1)

`binary_correct_exec_proven` runs the TLS sequence of `tls_value` through the base environment's
hook `Hb.tls` (`step`'s sites `.tlsAdrp`, `.tls`), whose contract `TlsOk` was trusted. rust-lld
relaxes Cranelift's TLSDESC sequence of a static executable to local exec (checked by
`BinCheck.RelocOk`), so the executable's six words are

```
movz x0, #hi, lsl #16 ; movk x0, #lo ; nop ; nop ; mrs tmp, tpidr_el0 ; add x0, x0, tmp
```

with `hi * 2^16 + lo = TpOff` the variable's offset from the thread pointer (AArch64 TLS
variant 1). The Arm model has the thread pointer (`StateField.TPIDR`, `MRS TPIDR_EL0`), so these
words run on the processor like every other word:

* `stepT`: the executable machine of `ExecBytes.step` where the TLS sites run the processor too
  (`realStep`); only calls of code outside the program are hooks.
* The model machine of the simulation is the one of `binary_correct_exec_proven` for the base
  environment `leBase I B file`: `B` with the TLS hook `leTls` (what the six words do, given the
  loader's thread pointer `B.tp`) and the flags it keeps (`tlsFlags`). `leTls` meets `TlsOk` by
  construction (`tlsOk_le`) and `HooksSim`'s TLS clause (`hooksSim_le`), so nothing about TLS
  is trusted beyond the loader contract `TlsLoader`.
* `tls_step`: the two model steps of a TLS sequence (`adrp`, then the hook) against the six
  processor steps of the executable, from a model state whose thread pointer is `B.tp`
  (`mach_tpidr`: no model step changes it, given `TlsLoader.call`).
* `act_simT`, `exec_of_modelT`: `act_simN`/`exec_of_modelN` for `stepT`; the model states at a
  TLSDESC `ldr` word (`TlsSecond`) are skipped as the second words of pairs are (D1 `RunTlsN`).
-/

namespace E2E.SemanticExecBytes

open Backend Backend.Proof E2E.LinkCheck E2E.SemanticBinary E2E.BinCheck E2E.ExecWords

/-! ## The machine and the loader contract -/

section Machine

variable (I : SemanticStackBound.CompilerInput) (B : BaseEnv) (file : ByteArray)

/-- **The hook-free executable machine**: the processor on the executable's words, including the
TLS sequence (lld's local-exec words); only calls of code outside the program run by the base
environment's hook. -/
noncomputable def stepT (s : Arm.ArmState) : Arm.ArmState :=
  match siteAt I (Arm.r .PC s) with
  | some .tlsAdrp => realStep file s
  | some (.tls _ _) => realStep file s
  | site => stepAt I B file site s

/-- The thread-pointer offset of the thread-local symbol `n` in the file (`TpOff` of its value;
0 when the file has none). -/
def tpOffOf (n : String) : BitVec 64 := BitVec.ofNat 64 ((TpOff file (I.addrOf n)).getD 0)

/-- **What lld's local-exec words of the TLS sequence of `n` do** from its `ldr` (the model's TLS
hook, `leBase`): `x0` the variable's address `I.symAddr n 0`, the temporary the thread pointer
`B.tp`, five words on; for the temporary `xzr` (which the allocation never gives), `x0` the
offset. -/
def leTls (n : String) (tmp : Reg) (s : Arm.ArmState) : Arm.ArmState :=
  if tmp.encZR.toOption.getD 31#5 = 31#5 then
    Arm.w .PC (Arm.r .PC s + 20) (Arm.w (.GPR 0#5) (tpOffOf I file n) s)
  else
    Arm.w .PC (Arm.r .PC s + 20)
      (Arm.w (.GPR (tmp.encZR.toOption.getD 31#5)) B.tp (Arm.w (.GPR 0#5) (I.symAddr n 0) s))

/-- **The base environment of the hook-free theorem**: `B` with the TLS hook `leTls` and the
flags the TLS words keep. -/
def leBase : BaseEnv :=
  { B with tlsFlags := fun _ w => Arm.read_pstate w, hooks := { B.hooks with tls := leTls I B file } }

/-- **The loader's thread-pointer contract** (trusted by design, as the OS loader placing the
segments): the thread pointer `TPIDR_EL0` of the entry state is `B.tp`; code outside the program
keeps it (a thread's pointer is set when the thread is created); and the running thread's
instance of every thread-local variable the program accesses (the symbol of a TLSDESC relocation)
is at `B.tp + TpOff` (TLS variant 1: the 16-byte TCB, then the TLS block), the address the CLIF
semantics gives it (`I.symAddr`, the one thread `Clif.run` models). -/
structure TlsLoader (r : Arm.ArmState) : Prop where
  tp : Arm.r .TPIDR r = B.tp
  call : ∀ d s, Arm.r .TPIDR (B.hooks.call d s) = Arm.r .TPIDR s
  addr : ∀ g ∈ (prog I).funcs, ∀ rl ∈ (art I g).fb.relocs, rl.type = .tlsDescAdrPage21 →
    B.tp + tpOffOf I file rl.sym = I.symAddr rl.sym 0

/-- **The simulation of the model's activations at depth `M` by the hook-free machine**
(`ActSimN` for `stepT`; target states neither a pair's second word nor a TLSDESC `ldr` word). -/
def ActSimT (M : Nat) : Prop :=
  ∀ g c e, g ∈ (prog I).funcs → Arm.r .PC c = (art I g).base → Sim I c e →
    RunOkSN I (leBase I B file) file M g c → RunTlsN I (leBase I B file) M g c →
    Arm.r .TPIDR c = B.tp →
    ∀ k, (∀ j < k, ¬ Returned (art I g) c (runX ((sys I (leBase I B file)).mach M g) j c)) →
    ¬ Second I g (Arm.r .PC (runX ((sys I (leBase I B file)).mach M g) k c)) →
    ¬ TlsSecond I g (Arm.r .PC (runX ((sys I (leBase I B file)).mach M g) k c)) →
    Arm.r .ERR (runX ((sys I (leBase I B file)).mach M g) k c) = .None →
    ∃ k', Sim I (runX ((sys I (leBase I B file)).mach M g) k c) (runX (stepT I B file) k' e)

end Machine

/-! ## The thread pointer along the model's run -/

section Tpidr

theorem runX_tpidr {f : Arm.ArmState → Arm.ArmState}
    (h : ∀ s, Arm.r .TPIDR (f s) = Arm.r .TPIDR s) :
    ∀ k s, Arm.r .TPIDR (runX f k s) = Arm.r .TPIDR s
  | 0, _ => rfl
  | k + 1, s => (runX_tpidr h k (f s)).trans (h s)

theorem armStepX_tpidr {X : ExtSem} {H : ArmHooks} {fa : FnAsm}
    (hc : ∀ d s, Arm.r .TPIDR (H.call d s) = Arm.r .TPIDR s)
    (ht : ∀ n tmp s, Arm.r .TPIDR (H.tls n tmp s) = Arm.r .TPIDR s) (s : Arm.ArmState) :
    Arm.r .TPIDR (ArmStepX X H fa s) = Arm.r .TPIDR s := by
  unfold ArmStepX
  dsimp only
  split <;> first
    | exact hc _ _
    | exact ht _ _ _
    | exact Arm.r_TPIDR_stepi s
    | simp [Arm.r_of_w_different]

theorem linkedCall_tpidr {M : Arm.ArmState → Arm.ArmState}
    (hM : ∀ s, Arm.r .TPIDR (M s) = Arm.r .TPIDR s) (a : Art) (s : Arm.ArmState) :
    Arm.r .TPIDR (linkedCall M a s) = Arm.r .TPIDR s := by
  unfold linkedCall
  split
  · rw [r_set_program, runX_tpidr hM]
    simp [enterAt, r_set_program, Arm.r_of_w_different]
  · simp [junkAt, Arm.r_of_w_different]

theorem hooks_tpidr (L : LinkSys) (hc : ∀ d s, Arm.r .TPIDR (L.Hb.call d s) = Arm.r .TPIDR s)
    (ht : ∀ n tmp s, Arm.r .TPIDR (L.Hb.tls n tmp s) = Arm.r .TPIDR s) :
    ∀ M, (∀ d s, Arm.r .TPIDR ((L.hooks M).call d s) = Arm.r .TPIDR s) ∧
      ∀ n tmp s, Arm.r .TPIDR ((L.hooks M).tls n tmp s) = Arm.r .TPIDR s
  | 0 => ⟨fun d s => by
      simp only [LinkSys.hooks, LinkSys.callHook]
      split
      · split
        · simp [junkAt, Arm.r_of_w_different]
        · exact hc _ _
      · split
        · simp [junkAt, Arm.r_of_w_different]
        · exact hc _ _, ht⟩
  | M + 1 =>
    have ih := hooks_tpidr L hc ht M
    ⟨fun d s => by
      simp only [LinkSys.hooks, LinkSys.callHook]
      split
      · split
        · exact linkedCall_tpidr (armStepX_tpidr ih.1 ih.2) _ _
        · exact hc _ _
      · split
        · exact linkedCall_tpidr (armStepX_tpidr ih.1 ih.2) _ _
        · exact hc _ _, ht⟩

/-- **No step of the linked machine changes the thread pointer** (given its base hooks keep it). -/
theorem mach_tpidr (L : LinkSys) (hc : ∀ d s, Arm.r .TPIDR (L.Hb.call d s) = Arm.r .TPIDR s)
    (ht : ∀ n tmp s, Arm.r .TPIDR (L.Hb.tls n tmp s) = Arm.r .TPIDR s) (M : Nat)
    (g : Clif.Function) (s : Arm.ArmState) : Arm.r .TPIDR (L.mach M g s) = Arm.r .TPIDR s :=
  armStepX_tpidr (hooks_tpidr L hc ht M).1 (hooks_tpidr L hc ht M).2 s

variable {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {file : ByteArray}

theorem leTls_tpidr (n : String) (tmp : Reg) (s : Arm.ArmState) :
    Arm.r .TPIDR (leTls I B file n tmp s) = Arm.r .TPIDR s := by
  unfold leTls; split <;> simp [Arm.r_of_w_different]

theorem mach_le_tpidr (hc : ∀ d s, Arm.r .TPIDR (B.hooks.call d s) = Arm.r .TPIDR s) (M : Nat)
    (g : Clif.Function) (s : Arm.ArmState) :
    Arm.r .TPIDR ((sys I (leBase I B file)).mach M g s) = Arm.r .TPIDR s :=
  mach_tpidr _ hc (fun n tmp s => leTls_tpidr n tmp s) M g s

end Tpidr

/-! ## The TLS hook of `leBase` -/

section Hook

variable {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {file : ByteArray}

theorem read_pstate_w {fld : Arm.StateField} (hf : ∀ fl, fld ≠ .FLAG fl) (v : Arm.state_value fld)
    (s : Arm.ArmState) : Arm.read_pstate (Arm.w fld v s) = Arm.read_pstate s := by
  cases fld with
  | FLAG fl => exact absurd rfl (hf fl)
  | _ => simp [Arm.read_pstate, Arm.w, Arm.write_base_gpr, Arm.write_base_sfp, Arm.write_base_pc,
      Arm.write_base_error]

theorem read_pstate_of_flags {s t : Arm.ArmState} (h : ∀ fl, Arm.r (.FLAG fl) s = Arm.r (.FLAG fl) t) :
    Arm.read_pstate s = Arm.read_pstate t := by
  have hN := h .N; have hZ := h .Z; have hC := h .C; have hV := h .V
  simp only [Arm.r, Arm.read_base_flag] at hN hZ hC hV
  apply Arm.PState.ext <;> simp only [Arm.read_pstate] <;> assumption

/-- **`leTls` meets the TLSDESC contract** `TlsOk` (no trust: it is the hook's definition). -/
theorem tlsOk_le {R : Res} {F' : BitVec 64 → Prop} (F : BitVec 64 → Prop) (K : Nat) :
    TlsOk F K (ofRes I R (leBase I B file) F').Xb (ofRes I R (leBase I B file) F').Hb where
  pc n tmp s _ := by
    show Arm.r .PC (leTls I B file n tmp s) = _
    unfold leTls; split <;> simp [Arm.r_of_w_same]
  seq n k s hk29 hk0 _ _ _ _ _ := by
    show xreg 0 (leTls I B file n (.x k) s) = _ ∧ Arm.r (.GPR (rnum k)) (leTls I B file n (.x k) s) = _ ∧
      (∀ f, _ → _ → _ → _ → _ → Arm.r f (leTls I B file n (.x k) s) = Arm.r f s) ∧
      (∀ a, _ → (leTls I B file n (.x k) s).mem a = s.mem a) ∧
      (leTls I B file n (.x k) s).program = s.program
    have he : (Reg.x k).encZR.toOption.getD 31#5 = rnum k := by
      simp [Reg.encZR, show k ≤ 30 by omega, Except.toOption, pure, Except.pure, rnum]
    have h31 : rnum k ≠ 31#5 := rnum_ne (by omega) (by omega) (by omega)
    have h0 : rnum k ≠ 0#5 := rnum_ne (b := 0) (by omega) (by omega) hk0
    unfold leTls
    rw [he, if_neg h31]
    refine ⟨?_, ?_, fun f hpc h0' hk h30 _ => ?_, fun a _ => ?_, ?_⟩
    · simp only [xreg]
      rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp [rnum] at h0 ⊢; exact Ne.symm h0),
        Arm.r_of_w_same]
      rfl
    · rw [Arm.r_of_w_different (by simp), Arm.r_of_w_same]; rfl
    · rw [Arm.r_of_w_different hpc, Arm.r_of_w_different hk,
        Arm.r_of_w_different (by simpa [rnum] using h0')]
    · simp [Arm.ArmState.mem_w_eq_mem]
    · simp [Arm.w_program]
  flags n k s w hw := by
    show Arm.read_pstate (leTls I B file n (.x k) s) = Arm.read_pstate w
    have hfl : Arm.read_pstate s = Arm.read_pstate w :=
      read_pstate_of_flags fun fl => hw.1 (.FLAG fl) (by simp [Masked])
    rw [← hfl]
    apply read_pstate_of_flags
    intro fl
    unfold leTls
    split <;> simp [Arm.r_of_w_different]

/-- **Non-vacuity of `BaseOk` with TLS**: the closed base environment with the local-exec TLS
hook (`leBase I closedBase file`) satisfies every base premise of the linked system of any
results, `tls_value` included (`baseOk_closedR` needs results without it). -/
theorem baseOk_closedLe {R : Res} {F : BitVec 64 → Prop} :
    BaseOk (ofRes I R (leBase I closedBase file) F) where
  baseNoAlloc := fun _ n gsem hn => by
    simp [ofRes, leBase, closedBase, Clif.Env.empty] at hn
  keepSyms := fun _ n f h => by simp [ofRes, leBase, closedBase, Clif.Env.empty] at h
  aliasSyms := fun _ _ _ _ _ _ _ _ _ _ => by simp [ofRes, leBase, closedBase, Clif.Env.empty]
  baseOs := fun g hg info hs hb F' K G s0 Pc ctx s _ _ _ c wh ops regs i' w outs w' _ _ _ _ _ _
      _ hsem => by simp [csem, ofRes, leBase, closedBase] at hsem
  basePc := fun d s _ _ _ => by simp [ofRes, leBase, closedBase, Arm.r_of_w_same]
  baseExt := fun d uses w outs w' _ hx => by simp [ofRes, leBase, closedBase] at hx
  baseX := fun g hg F' slotOff out c => by
    intro ext _ gs sl cm w d uses args vals rvals cm' he
    simp [ofRes, leBase, closedBase, Clif.Env.empty] at he
  baseXI := fun g hg F' slotOff out c sig _ n gsem sl cm w u args vals rvals cm' hgs => by
    simp [ofRes, leBase, closedBase, Clif.Env.empty] at hgs
  baseTls := fun _ _ _ F K => tlsOk_le F K
  baseTry := fun g hg F' ctx info ti _ c wh ops regs i' s w outs w' s' _ _ _ _ _ _ hsem => by
    simp [csem, ofRes, leBase, closedBase] at hsem
  baseNI := fun _ g hg F' c n sig vals cm args d uses Z w w' o x o' x' _ _ _ _ _ _ _ _ _ hx _ => by
    simp [ofRes, leBase, closedBase] at hx
  baseTlsNI := fun _ F' => closedBase_tlsNI (R := R) (F' := F) F'
  baseKeepsPlace := fun _ n gsem hn => by
    simp [ofRes, leBase, closedBase, Clif.Env.empty] at hn
  baseKeepsAllocs := fun _ n gsem hn => by
    simp [ofRes, leBase, closedBase, Clif.Env.empty] at hn

/-- The TCB-and-alignment part of the file's thread-pointer offsets (`TpOff file v = A + v`). -/
def tlsA (file : ByteArray) : Nat :=
  (((Elf.phdrs (Elf.fileRd file)).bind (·.find? (·.type == 7))).map
    fun p => let al := max p.align 1; (16 + al - 1) / al * al).getD 0

theorem tpOff_eq {v w : Nat} (h : TpOff file v = some w) : w = tlsA file + v := by
  simp only [TpOff, Elf.tpOff, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨phs, hph, p, hp, rfl⟩ := h
  simp [tlsA, hph, hp]

/-- **The address clause of `TlsLoader` is satisfiable**: with the thread pointer `-(tlsA file)`
the running thread's instance `tp + TpOff` of every thread-local symbol with an offset is its
CLIF address (the CLIF memory's symbols are at the symbols' values, `I.symAddr`). -/
theorem tlsLoader_addr_canon {n : String} {v : Nat} (h : TpOff file (I.addrOf n) = some v) :
    -BitVec.ofNat 64 (tlsA file) + tpOffOf I file n = I.symAddr n 0 := by
  rw [tpOffOf, h, Option.getD_some, tpOff_eq h, symAddr_zero, BitVec.ofNat_add, ← BitVec.add_assoc,
    BitVec.add_left_neg, BitVec.zero_add]

/-- **The outside-code contract `HooksSim` of `leBase`**: its call clause is `B`'s; its TLS clause
holds (`leTls` writes constants into registers). -/
theorem hooksSim_le (hc : ∀ d m e, Sim I m e → Sim I (B.hooks.call d m) (B.hooks.call d e)) :
    HooksSim I (leBase I B file) where
  call := hc
  tls n tmp m e h := by
    show Sim I (leTls I B file n tmp m) (leTls I B file n tmp e)
    unfold leTls
    rw [h.1 .PC]
    split
    · exact sim_w (sim_w h _ _) _ _
    · exact sim_w (sim_w (sim_w h _ _) _ _) _ _

end Hook

/-! ## The steps -/

section Steps

variable {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {file : ByteArray}

/-- The kind of an instruction's site is a TLS kind only at the TLSDESC `adrp` and `ldr`. -/
def _root_.Backend.Insn.tlsSite : Insn → Bool
  | .adrpTlsDesc .. | .ldrTlsDescLo12 .. => true
  | _ => false

theorem stepAt_leBase (site : Option Site) (s : Arm.ArmState)
    (h : ∀ tmp n, site ≠ some (.tls tmp n)) :
    stepAt I (leBase I B file) file site s = stepAt I B file site s := by
  rcases site with _ | x
  · rfl
  · cases x <;> first | rfl | exact absurd rfl (h _ _)

/-- Away from the TLS sites `stepT` is `step` of `leBase`. -/
theorem stepT_eq {s : Arm.ArmState} (h1 : siteAt I (Arm.r .PC s) ≠ some .tlsAdrp)
    (h2 : ∀ tmp n, siteAt I (Arm.r .PC s) ≠ some (.tls tmp n)) :
    stepT I B file s = step I (leBase I B file) file s := by
  unfold stepT step
  rw [stepAt_leBase _ _ h2]
  generalize siteAt I (Arm.r .PC s) = x at h1 h2 ⊢
  rcases x with _ | x
  · rfl
  · cases x <;> first | rfl | exact absurd rfl h1 | exact absurd rfl (h2 _ _)

/-- `stepT` at a model state's instruction that is not of the TLS sequence's `adrp`/`ldr`. -/
theorem stepT_of_ins {M : Nat} {g : Clif.Function} {m e : Arm.ArmState}
    (h0 : StepOk I (leBase I B file) file M g m) (hpc : Arm.r .PC e = Arm.r .PC m) {i : Insn}
    (hins : insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some i) (hi : i.tlsSite = false) :
    stepT I B file e = step I (leBase I B file) file e := by
  have hs := siteAt_of h0 hins
  rw [← hpc] at hs
  refine stepT_eq (by rw [hs]; cases i <;> simp_all [siteOf, Insn.tlsSite]; split <;> simp)
    (fun tmp n => by rw [hs]; cases i <;> simp_all [siteOf, Insn.tlsSite]; split <;> simp)

/-- The instruction at a second word of a pair is its `ldr`/`add`. -/
theorem second_insn {g : Clif.Function} (hF : FnOk I file g) {pc : BitVec 64} (hs : Second I g pc)
    {i : Insn} (hins : insnAt (art I g).fa (art I g).base pc = some i) : i.tlsSite = false := by
  obtain ⟨rl, hrl, ht, rfl⟩ := hs
  obtain ⟨-, -, r', hr', hr'o, hr't⟩ := pair_facts hF hrl ht
  obtain ⟨j, i2, t2, hj, hi2, ho⟩ := (FnAsm.layout_relocs hF.layout r').1 hr'
  have h2 := insnAt_of_line hF hj
  rw [ho, hr'o] at h2
  rw [h2] at hins
  cases hins
  rw [hr't] at hi2
  rcases ht with h | h <;> rw [h] at hi2 <;> cases i <;> simp_all [Insn.reloc?, loOf, Insn.tlsSite]

/-- The instruction at a TLSDESC `ldr` word is that `ldr`. -/
theorem tlsSecond_insn {g : Clif.Function} (hF : FnOk I file g)
    (hT : TlsClosed (art I g).fa.lines.toList) {pc : BitVec 64} (hs : TlsSecond I g pc)
    {i : Insn} (hins : insnAt (art I g).fa (art I g).base pc = some i) :
    ∃ tmp n, i = .ldrTlsDescLo12 tmp (.x 0) n := by
  obtain ⟨rl, hrl, ht, rfl⟩ := hs
  obtain ⟨j, t, hj, ho, tmp, -, ⟨t1, hj1⟩, -⟩ := tls_lines hF hT hrl ht
  have h1 := insnAt_of_line hF hj1
  rw [lineOffset_succ _ j _ hj, ho] at h1
  change insnAt _ _ (wAt _ (rl.offset + 4)) = _ at h1
  rw [h1] at hins
  cases hins
  exact ⟨_, _, rfl⟩

/-- The `ldr` of a TLS sequence is at a TLSDESC `ldr` word. -/
theorem tlsSecond_of_ldr {g : Clif.Function} (hF : FnOk I file g) {pc : BitVec 64}
    {tmp rn : Reg} {n : String}
    (hins : insnAt (art I g).fa (art I g).base pc = some (.ldrTlsDescLo12 tmp rn n)) :
    TlsSecond I g pc := by
  obtain ⟨j, t, hj, hpc⟩ := insnAt_spec hins
  have hR := hF.bin.reloc _ (line_reloc hF hj (show (Insn.ldrTlsDescLo12 tmp rn n).reloc? =
    some (.tlsDescLd64Lo12, n, 0) from rfl))
  unfold RelocOk at hR
  obtain ⟨-, r', hr', ht, ho⟩ := hR
  exact ⟨r', hr', ht, by rw [← hpc, ho]; rfl⟩

/-- The TLSDESC `adrp` word is neither a pair's second word nor a TLSDESC `ldr` word. -/
theorem tlsFirst_not {g : Clif.Function} (hF : FnOk I file g)
    (hT : TlsClosed (art I g).fa.lines.toList) {rl : Reloc} (hrl : rl ∈ (art I g).fb.relocs)
    (ht : rl.type = .tlsDescAdrPage21) :
    ¬ Second I g (wAt (art I g) rl.offset) ∧ ¬ TlsSecond I g (wAt (art I g) rl.offset) := by
  obtain ⟨j, t, hj, ho, -⟩ := tls_lines hF hT hrl ht
  have h0 := insnAt_of_line hF hj
  rw [ho] at h0
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · have := second_insn hF hs h0
    simp [Insn.tlsSite] at this
  · obtain ⟨tmp, n, h⟩ := tlsSecond_insn hF hT hs h0
    cases h

/-- The model's step at the TLSDESC `adrp` lands on its `ldr` word. -/
theorem tls_lands {M : Nat} {g : Clif.Function} (hF : FnOk I file g) {m : Arm.ArmState}
    (h0 : StepOk I B file M g m) {rd : Reg} {n : String}
    (hins : insnAt (art I g).fa (art I g).base (Arm.r .PC m) = some (.adrpTlsDesc rd n)) :
    TlsSecond I g (Arm.r .PC ((sys I B).mach M g m)) := by
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hF.layout
  obtain ⟨j, t, hj, hpc⟩ := insnAt_spec hins
  have hb : progBase m = (art I g).base := progBase_of hF hm h0.program hj
  refine ⟨_, line_reloc hF hj (show (Insn.adrpTlsDesc rd n).reloc? = some (.tlsDescAdrPage21, n, 0)
    from rfl), rfl, ?_⟩
  show _ = wAt _ _
  rw [← wAt_add4, show wAt (art I g) (lineOffset (art I g).fa.lines.toList j) = Arm.r .PC m from hpc]
  show Arm.r .PC (ArmStepX (sys I B).Xb ((sys I B).hooks M) (art I g).fa m) = _
  simp only [ArmStepX, hb, hins, Arm.r_of_w_same]

end Steps

end E2E.SemanticExecBytes

import FV.E2E.RegLevelCall

/-!
# `tls_value` on the machine (agent/stack-tls-proof)

The allocated `ElfTlsGetAddr n x0 tmp` emits Cranelift's TLSDESC sequence (`emit.rs`):

```
adrp x0, :tlsdesc:n ; ldr tmp, [x0, :tlsdesc_lo12:n] ; add x0, x0, :tlsdesc_lo12:n
blr tmp ; mrs tmp, tpidr_el0 ; add x0, x0, tmp
```

The Arm model has no system registers (`mrs` stops the machine with an error) and the TLS
resolver is code outside the function, so the machine `ArmStepX` hooks the sequence: the `adrp`
only advances the pc (the descriptor address is part of the resolver call), and at the `ldr`
the rest of the sequence runs as one hooked step `H.tls n tmp` to the instruction after the
final `add`. Its contract `TlsOk` is the trusted part (Cranelift's TLSDESC convention): the
variable's address `X.sym n 0` in x0 (one thread: its instance of the variable is the
link-time symbol, as in `Clif.run`), the thread pointer `X.tp` in `tmp`, every other register,
the memory outside the dead stack below `sp` (where a resolver may save registers) and the
program unchanged except x30 (the `blr` writes it) and the condition flags (`X.tlsFlags`: the
resolver may change them).

* `os_tls`: `CallSoundCtl` of the hooked sequence against `csem`'s clause, from `TlsOk`;
* `realizes_tls`: the `op`/`next` case of `Realizes`, an instance of `realizes_op_core`.
-/

namespace Backend.Proof

open Backend E2E

/-- **The TLSDESC contract** of the machine's hook `H.tls` (the TLSDESC sequence of `tls_value`
of symbol `n` with temporary `tmp`, from its `ldr`), relative to the external semantics `X`,
the addresses `F` outside the activation's world and its callees' stack budget `K` (the
trusted part of `tls_value`):

* `pc`: the hooked step ends at the instruction after the sequence (five instructions on);
* `seq`: for an allocatable temporary `x k` (`k ≠ 0`), when the `K` bytes below `sp` fit: x0
  holds the variable's address `X.sym n 0`, `x k` the thread pointer `X.tp`, every other state
  field but x30 and the condition flags and the program are unchanged, and so is the memory
  outside the `K` bytes below `sp` (the dead stack, where a resolver may save registers);
* `flags`: the flags are `X.tlsFlags n w` for a world `w` of the state. -/
structure TlsOk (F : BitVec 64 → Prop) (K : Nat) (X : ExtSem) (H : ArmHooks) : Prop where
  pc : ∀ n tmp s, Arm.r .ERR s = .None → Arm.r .PC (H.tls n tmp s) = Arm.r .PC s + 20
  seq : ∀ n k s, k < 29 → k ≠ 0 → k ≠ 16 → k ≠ 17 → k ≠ 18 → Arm.r .ERR s = .None →
    K ≤ (spOf s).toNat →
    xreg 0 (H.tls n (.x k) s) = X.sym n 0 ∧ Arm.r (.GPR (rnum k)) (H.tls n (.x k) s) = X.tp ∧
    (∀ f, f ≠ .PC → f ≠ .GPR (rnum 0) → f ≠ .GPR (rnum k) → f ≠ .GPR 30#5 →
      (∀ fl, f ≠ .FLAG fl) → Arm.r f (H.tls n (.x k) s) = Arm.r f s) ∧
    (∀ a, ¬ StackBelow K (spOf s) a → (H.tls n (.x k) s).mem a = s.mem a) ∧
    (H.tls n (.x k) s).program = s.program
  flags : ∀ n k s w, SameWorld F s w → Arm.read_pstate (H.tls n (.x k) s) = X.tlsFlags n w

theorem hasTls_of_mem {vc : VCode} {b k : Nat} {vb : VBlock} {n : String} {rd tmp : Reg}
    (hvb : vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.elfTlsGetAddr n rd tmp)) :
    vc.hasTls = true := by
  simp only [VCode.hasTls, Array.any_eq_true]
  obtain ⟨hb, rfl⟩ := Array.getElem?_eq_some_iff.mp hvb
  obtain ⟨hk, hk'⟩ := Array.getElem?_eq_some_iff.mp hi
  exact ⟨b, hb, k, hk, by rw [hk']⟩

/-- The hooked TLSDESC sequence as the machine runs it: the `adrp` step, then `H.tls` (for the
allocated form, x0 and another temporary). -/
def tlsExec (H : ArmHooks) : MInst → Arm.ArmState → Option Arm.ArmState
  | .elfTlsGetAddr n rd tmp, s =>
    if rd = .x 0 ∧ tmp ≠ .x 0 then some (H.tls n tmp (Arm.w .PC (Arm.r .PC s + 4) s)) else none
  | _, _ => none

theorem step_adrpTlsDesc {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat}
    {t : Option Clif.TrapCode} {n : String} {rd : Reg}
    (hj : R.L[j]? = some (.ins (.adrpTlsDesc rd n) t))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j) :
    R.step s = Arm.w .PC (Arm.r .PC s + 4) s := by
  simp only [RL.step, ArmStepX, insnAt_pc hR hj hprog hpc]

theorem step_ldrTlsDescLo12 {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat}
    {t : Option Clif.TrapCode} {n : String} {tmp rn : Reg}
    (hj : R.L[j]? = some (.ins (.ldrTlsDescLo12 tmp rn n) t))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j) :
    R.step s = R.H.tls n tmp s := by
  simp only [RL.step, ArmStepX, insnAt_pc hR hj hprog hpc]

theorem operands_tls (n : String) (d t : Nat) :
    (MInst.elfTlsGetAddr n (.vreg d .int) (.vreg t .int)).operands =
      .ok #[⟨d, .int, .def, .late, .fixed (.x 0)⟩, ⟨t, .int, .def, .early, .reg⟩] := rfl

theorem assign_tls {n : String} {d t : Nat} {regs : Array Reg} {i' : MInst}
    (h : (MInst.elfTlsGetAddr n (.vreg d .int) (.vreg t .int)).assign regs = .ok i') :
    ∃ r0 r1, regs = #[r0, r1] ∧ i' = .elfTlsGetAddr n r0 r1 := by
  unfold MInst.assign at h
  dsimp only at h
  cases h0 : regs[0]? with
  | none =>
    simp [MInst.visitOperands, h0, StateT.run, bind, StateT.bind, Except.bind, get, getThe,
      MonadStateOf.get, StateT.get, set, StateT.set, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, MonadLift.monadLift, Except.tryCatch] at h
  | some r0 =>
    cases h1 : regs[1]? with
    | none =>
      simp [MInst.visitOperands, h0, h1, StateT.run, bind, StateT.bind, Except.bind, get, getThe,
        MonadStateOf.get, StateT.get, set, StateT.set, pure, StateT.pure, Except.pure, throw,
        throwThe, MonadExceptOf.throw, StateT.lift, MonadLift.monadLift, Except.tryCatch] at h
    | some r1 =>
      simp [MInst.visitOperands, h0, h1, StateT.run, bind, StateT.bind, Except.bind, get, getThe,
        MonadStateOf.get, StateT.get, set, StateT.set, pure, StateT.pure, Except.pure, throw,
        throwThe, MonadExceptOf.throw, StateT.lift, MonadLift.monadLift] at h
      split at h
      · rename_i hs
        simp only [Except.ok.injEq] at h
        refine ⟨r0, r1, ?_, h.symm⟩
        apply Array.ext
        · simp [← hs]
        · intro k hk1 hk2
          have : k = 0 ∨ k = 1 := by simp at hk2; omega
          rcases this with rfl | rfl
          · simp [Array.getElem?_eq_some_iff] at h0; simpa using h0.2
          · simp [Array.getElem?_eq_some_iff] at h1; simpa using h1.2
      · cases h

theorem r_write_pstate_other {f : Arm.StateField} (hf : ∀ fl, f ≠ .FLAG fl) (P : Arm.PState)
    (w : Arm.ArmState) : Arm.r f (Arm.write_pstate P w) = Arm.r f w := by
  simp only [Arm.write_pstate]
  rw [Arm.r_of_w_different (hf _), Arm.r_of_w_different (hf _), Arm.r_of_w_different (hf _),
    Arm.r_of_w_different (hf _)]

theorem r_flag_of_pstate {s t : Arm.ArmState} (h : Arm.read_pstate s = Arm.read_pstate t)
    (fl : Arm.PFlag) : Arm.r (.FLAG fl) s = Arm.r (.FLAG fl) t := by
  simp only [Arm.read_pstate] at h
  cases fl <;> simp only [Arm.r, Arm.read_base_flag, h]

theorem read_pstate_write_pstate (P : Arm.PState) (w : Arm.ArmState) :
    Arm.read_pstate (Arm.write_pstate P w) = P := by
  obtain ⟨n, z, c, v⟩ := P
  simp [Arm.read_pstate, Arm.write_pstate, Arm.w, Arm.write_base_flag]

/-- **`CallSoundCtl` of the hooked TLSDESC sequence** (from `TlsOk`). -/
theorem os_tls {F : BitVec 64 → Prop} {K : Nat} {ctx : FnCtx} {X : ExtSem} {H : ArmHooks}
    (hT : TlsOk F K X H) (n : String) (d t : Nat) :
    CallSoundCtl F K (tlsExec H) (csem F ctx X) (.elfTlsGetAddr n (.vreg d .int) (.vreg t .int))
      .next := by
  intro s hK hD c wh ops regs i' w outs w' hops' hst hasg hw hal herr hsem
  rw [operands_tls] at hops'
  cases hops'
  obtain ⟨r0, r1, rfl, rfl⟩ := assign_tls hasg
  obtain ⟨-, hloc, hnd, -⟩ := checkStatic_facts hst
  have h0 := hloc (⟨d, .int, .def, .late, .fixed (.x 0)⟩, .reg r0) (by simp)
  have h1 := hloc (⟨t, .int, .def, .early, .reg⟩, .reg r1) (by simp)
  have hr0 : r0 = .x 0 := by
    have := h0.2 (.x 0) rfl
    simpa using this
  subst hr0
  obtain ⟨k, rfl, hk29, hk16, hk17, hk18⟩ := locOk_int h1.1
  have hk0 : k ≠ 0 := by
    intro e; subst e
    simp [Operand.kind] at hnd
  have huse : useVals #[(⟨d, .int, .def, .late, .fixed (.x 0)⟩ : Operand), ⟨t, .int, .def, .early, .reg⟩]
      #[.x 0, .x k] s = [] := by
    simp [useVals, Operand.isUse]
  rw [huse] at hsem
  simp only [csem, Option.some.injEq, Prod.mk.injEq] at hsem
  obtain ⟨rfl, rfl, -⟩ := hsem
  -- the state after the `adrp` step, and after the hooked step
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = Arm.w .PC (Arm.r .PC s + 4) s := ⟨_, rfl⟩
  have herr1 : Arm.r .ERR s1 = .None := by rw [hs1, Arm.r_of_w_different (by simp)]; exact herr
  have hw1 : SameWorld F s1 w := by rw [hs1]; exact SameWorld.w_left (by simp [Masked]) hw
  have hsp1 : spOf s1 = spOf s := by
    rw [hs1]; simp only [spOf]; exact Arm.r_of_w_different (by simp)
  obtain ⟨hx0, hxk, hfr, hmem, hprog⟩ :=
    hT.seq n k s1 hk29 hk0 hk16 hk17 hk18 herr1 (by rw [hsp1]; exact hK)
  rw [hsp1] at hmem
  have hfl := hT.flags n k s1 w hw1
  have hex : tlsExec H (.elfTlsGetAddr n (.x 0) (.x k)) s = some (H.tls n (.x k) s1) := by
    simp [tlsExec, hk0, hs1]
  have hr0 : rnum 0 ≠ rnum k := rnum_ne (by omega) (by omega) (Ne.symm hk0)
  -- the fields the hooked step keeps
  have hkeep : ∀ f, f ≠ .PC → f ≠ .GPR (rnum 0) → f ≠ .GPR (rnum k) → f ≠ .GPR 30#5 →
      (∀ fl, f ≠ .FLAG fl) → Arm.r f (H.tls n (.x k) s1) = Arm.r f s := by
    intro f h1 h2 h3 h4 h5
    rw [hfr f h1 h2 h3 h4 h5, hs1, Arm.r_of_w_different h1]
  refine ⟨_, hex, ⟨fun f hf => ?_, fun a ha => ?_, ?_⟩, ⟨?_, fun a hak => ?_⟩, ?_, ?_, ?_⟩
  · -- the world: the flags as `X.tlsFlags` says, every other unmasked field kept
    by_cases hff : ∃ fl, f = .FLAG fl
    · obtain ⟨fl, rfl⟩ := hff
      exact r_flag_of_pstate (by rw [hfl, read_pstate_write_pstate]) fl
    · have hnf : ∀ fl, f ≠ .FLAG fl := fun fl e => hff ⟨fl, e⟩
      rw [r_write_pstate_other hnf]
      have hpc : f ≠ .PC := fun e => hf (by rw [e]; simp [Masked])
      have h0 : f ≠ .GPR (rnum 0) := fun e => hf (by rw [e]; simp [Masked, rnum])
      have hk : f ≠ .GPR (rnum k) := fun e => hf (by rw [e]; exact Or.inl ⟨by
        rw [rnum_toNat (by omega)]; exact hk29, by rw [rnum_toNat (by omega)]; exact hk18⟩)
      have h30 : f ≠ .GPR 30#5 := fun e => hf (by rw [e]; simp [Masked])
      rw [hkeep f hpc h0 hk h30 hnf]
      exact hw.1 f hf
  · rw [hmem a (fun hb => ha (hD a hb)), hs1]
    simp only [Arm.ArmState.mem_w_eq_mem, Arm.write_pstate]
    exact hw.2.1 a ha
  · rw [hprog, hs1]
    simp only [Arm.w_program, Arm.write_pstate]
    exact hw.2.2
  · -- the frame: `sp` and memory kept
    simp only [spOf]
    exact hkeep _ (by simp) (by simp [rnum])
      (fun e => rnum_ne (a := 31) (b := k) (by omega) (by omega) (by omega)
        (Arm.StateField.GPR.inj e)) (by simp)
      (fun fl => by simp)
  · rw [hmem a hak.2, hs1]; simp [Arm.ArmState.mem_w_eq_mem]
  · -- the defs
    intro p hp
    simp only [defRegs] at hp
    simp [Operand.isDef] at hp
    rcases hp with rfl | rfl
    · simp only [regVal, ofX]
      rw [show rnum 0 = 0#5 from rfl]
      exact congrArg (BitVec.setWidth 128) hx0
    · simp only [regVal, ofX]
      exact congrArg (BitVec.setWidth 128) hxk
  · -- the other allocatable registers
    intro r hr hnd' _
    have hne0 : r ≠ .x 0 := fun e => hnd' (⟨d, .int, .def, .late, .fixed (.x 0)⟩, .x 0) (by simp) rfl e.symm
    have hnek : r ≠ .x k := fun e => hnd' (⟨t, .int, .def, .early, .reg⟩, .x k) (by simp) rfl e.symm
    rcases allocatable_cases hr with ⟨m, rfl, hm29, hm16, hm17, hm18⟩ | ⟨m, rfl, hm⟩
    · simp only [regVal]
      have hm0 : m ≠ 0 := fun e => hne0 (by rw [e])
      have hmk : m ≠ k := fun e => hnek (by rw [e])
      rw [hkeep _ (by simp) (by simp; exact rnum_ne (by omega) (by omega) hm0)
        (by simp; exact rnum_ne (by omega) (by omega) hmk)
        (fun e => rnum_ne (a := m) (b := 30) (by omega) (by omega) (by omega)
          (Arm.StateField.GPR.inj e))
        (fun fl => by simp)]
    · simp only [regVal]
      rw [hkeep _ (by simp) (by simp) (by simp) (by simp) (fun fl => by simp)]
  · intro r hr; simp [MInst.clobbers] at hr

/-- **`ElfTlsGetAddr` on the machine**: the `adrp` step, then the hooked step. -/
theorem realizes_tls {R : RL} (hR : R.Wf) (hT : TlsOk R.F R.K R.X R.H) {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {n : String} {d t : Nat} {ops : Array Operand} {outs : List CV}
    {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.elfTlsGetAddr n (.vreg d .int) (.vreg t .int)))
    (hops : (MInst.elfTlsGetAddr n (.vreg d .int) (.vreg t .int)).operands = .ok ops)
    (hsz : allocs.size = ops.size)
    (hsem : R.sem (.elfTlsGetAddr n (.vreg d .int) (.vreg t .int))
      (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' := by
  have hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
    have herr : Arm.r .ERR w = .None := by
      have hst := q_stRel hq
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    simp only [RL.sem, csem, Option.some.injEq, Prod.mk.injEq] at hsem
    obtain ⟨-, rfl, -⟩ := hsem
    exact ⟨by rw [r_write_pstate_other (fun fl => by simp)]; exact herr,
      by simp [Arm.write_pstate, Arm.w_program]⟩
  refine realizes_op_core hR hq hvb hi hops hsz hsem hlen hk (exec := fun _ => tlsExec R.H)
    (fun _ => (RL.callAt hR (os_tls hT n d t) (q_stRel hq).sp).toI _) (fun regs i' _ hex => ?_) hW'
  obtain ⟨_, s0, _, hex⟩ := hex
  cases i' with
  | elfTlsGetAddr n' rd tmp =>
    have hc : rd = .x 0 ∧ tmp ≠ .x 0 := by
      simp only [tlsExec] at hex
      split at hex
      · assumption
      · cases hex
    obtain ⟨rfl, htmp⟩ := hc
    have hl : ∀ ps, (MInst.elfTlsGetAddr n' (.x 0) tmp).lines R.ctx ps =
        .ok ([.ins (.adrpTlsDesc (.x 0) n'), .ins (.ldrTlsDescLo12 tmp (.x 0) n'),
          .ins (.addTlsDescLo12 (.x 0) (.x 0) n'), .ins (.blrTlsDesc tmp n'),
          .ins (.mrsTpidrEl0 tmp), .ins (.aluRRR .add true (.x 0) (.x 0) tmp)], ps) := by
      intro ps
      have : (tmp == Reg.x 0) = false := by simpa using htmp
      simp [MInst.lines, this, pure, Except.pure]
    refine ⟨_, hl, ?_, fun _ h => MInst.noConfusion h, fun _ h => MInst.noConfusion h, ?_⟩
    · intro ln hln
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hln
      rcases hln with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Line.plain, Insn.condTarget?]
    · intro j T s s' hd hprog hpc herr hex
      have hj : R.L[j]? = some (.ins (.adrpTlsDesc (.x 0) n')) := by
        have := congrArg (·[0]?) hd
        simpa [List.getElem?_drop] using this
      have hj1 : R.L[j + 1]? = some (.ins (.ldrTlsDescLo12 tmp (.x 0) n')) := by
        have := congrArg (·[1]?) hd
        simpa [List.getElem?_drop] using this
      simp only [tlsExec, htmp, ne_eq, not_false_eq_true, and_self, ↓reduceIte,
        Option.some.injEq] at hex
      subst hex
      have h1 := step_adrpTlsDesc hR hj hprog hpc
      have hprog1 : (Arm.w .PC (Arm.r .PC s + 4) s).program = R.fb.program R.base := by
        simp [Arm.w_program, hprog]
      have hpc1 : Arm.r .PC (Arm.w .PC (Arm.r .PC s + 4) s) = R.pcOf (j + 1) := by
        rw [Arm.r_of_w_same, hpc, pcOf_succ hj]
      have h2 := step_ldrTlsDescLo12 hR hj1 hprog1 hpc1
      refine ⟨2, by simp only [iterN, h1, h2], ?_⟩
      have herr1 : Arm.r .ERR (Arm.w .PC (Arm.r .PC s + 4) s) = .None := by
        rw [Arm.r_of_w_different (by simp)]; exact herr
      rw [hT.pc _ _ _ herr1, Arm.r_of_w_same, hpc]
      have hins : ∀ ln ∈ [Line.ins (.adrpTlsDesc (.x 0) n'), .ins (.ldrTlsDescLo12 tmp (.x 0) n'),
          .ins (.addTlsDescLo12 (.x 0) (.x 0) n'), .ins (.blrTlsDesc tmp n'),
          .ins (.mrsTpidrEl0 tmp), .ins (.aluRRR .add true (.x 0) (.x 0) tmp)],
          ∃ i t, ln = .ins i t := by
        intro ln hln
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hln
        rcases hln with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
      simp only [RL.pcOf, RL.L]
      rw [lineOffset_drop_ins (by simpa [RL.L] using hd) hins, BitVec.add_assoc, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add]
  | _ => simp [tlsExec] at hex

end Backend.Proof

import FV.E2E.RegLevelAtomic
import FV.E2E.DeadCleanupRealizes
import FV.E2E.RegLevelCorrectU
import FV.E2E.MemTrapStatement
import FV.Backend.Proof.PrepareMemTrap

/-!
# The register level of a memory trap (A3, #412, slice F4)

`docs/plans/memfault.md`, "Backend layers". A memory trap of the VCode run (`VMemTrapFrom`: the
run reaches an LL/SC loop with the trap code `c`, its address use `u` and size `n` satisfying
`A`) is, on the machine, the state at the loop's first line, `ldaxr x27, [x25]`, whose trap-table
entry has the code `c` (`TrapAt`) and whose `x25` holds the address. When the address range has a
byte the memory map `mp` does not map (`Unmapped mp`), that `ldaxr` faults under `mp`.

The observable (`E2E.TrapAtM mp fa fb base c`): a trap site with code `c` (`TrapAt`) at a `udf`
line (an explicit trap) or at an `ldaxr` line whose access range has an unmapped byte
(`LdaxrUnmapped`), which faults under `mp` (`LdaxrUnmapped.instFaults`; on the function's own
machine `faults_of_ldaxrUnmapped`, i.e. `TrapAtF`). The machine is the existing one, whose memory
is total: the theorem says that **if** the run reaches the trapping atomic, its `ldaxr` faults; it
does not say that no earlier access faulted (`docs/plans/memfault.md`, F8).

* `haltLoop c A sem`: `sem`, except that a loop with code `c` whose address satisfies `A` halts
  (a proof device, as `xrT` for the trapping callees): a `VMemTrapFrom` run is a run of
  `haltLoop` up to a halting loop (`memTrap_halt`), and a realisation of `sem` is one of
  `haltLoop` (`realizes_haltLoop`; the machine is unchanged);
* `trapAt_ins`: a line with a trap code is a trap site; `trap_udf_line`, `trap_trapIf_line`:
  `trap_udf`/`trap_trapIf` with the `udf` line of the trap site;
* `loop_ldaxr`: `Q` at a trapping LL/SC loop item is at the loop's `ldaxr` line, `x25` the
  loop's first use;
* **`regLevel_memtrap_world_value`**: the explicit traps and the memory traps of the VCode run
  under the dead-cleanup chain's value semantics, `TrapAtM` at a state of the machine run, every
  earlier state `GoodX`.
-/

namespace E2E

open Backend

/-- Some byte of `[x, x + n)` is not mapped (`Perm.none`). -/
def Unmapped (mp : ArmFault.MemMap) (x : BitVec 64) (n : Nat) : Prop :=
  ∃ k < n, mp (x + BitVec.ofNat 64 k) = .none

/-- The machine is at a `udf` line of `fa` (placed at `base`). -/
def UdfLine (fa : FnAsm) (base : BitVec 64) (s : Arm.ArmState) : Prop :=
  ∃ j t, fa.lines.toList[j]? = some (.ins (.udf 0xc11f) t) ∧
    Arm.r .PC s = base + BitVec.ofNat 64 (lineOffset fa.lines.toList j)

/-- The machine is at an `ldaxr x27, [x25]` line of `fa` (an LL/SC loop's load) whose access
range `[x25, x25 + bits / 8)` has a byte that `mp` does not map. -/
def LdaxrUnmapped (mp : ArmFault.MemMap) (fa : FnAsm) (base : BitVec 64) (s : Arm.ArmState) :
    Prop :=
  ∃ j bits t, fa.lines.toList[j]? = some (.ins (.ldaxr bits (.x 27) (.x 25)) t) ∧
    (bits = 8 ∨ bits = 16 ∨ bits = 32 ∨ bits = 64) ∧
    Arm.r .PC s = base + BitVec.ofNat 64 (lineOffset fa.lines.toList j) ∧
    Unmapped mp (Arm.r (.GPR 25#5) s) (bits / 8)

/-- **The trap observable with memory traps**: a trap site of the function with code `c`
(`TrapAt`), at a `udf` line (an explicit trap: the machine's next step errs) or at the `ldaxr` of
a trapping atomic whose access has an unmapped byte (its step faults under `mp`). -/
def TrapAtM (mp : ArmFault.MemMap) (fa : FnAsm) (fb : FnBin) (base : BitVec 64)
    (c : Clif.TrapCode) (s : Arm.ArmState) : Prop :=
  TrapAt fb base c s ∧ (UdfLine fa base s ∨ LdaxrUnmapped mp fa base s)

/-- The `ldaxr` of the LL/SC loops, encoded. -/
theorem ldaxr_toArmInst {bits : Nat} (hbits : bits = 8 ∨ bits = 16 ∨ bits = 32 ∨ bits = 64)
    (env : Env) : ∃ i : Arm.Reg_exclusive_cls,
      (Insn.ldaxr bits (.x 27) (.x 25)).toArmInst env = .ok (.LDST (.Reg_exclusive i)) ∧
      i.L = 1#1 ∧ i.Rn = 25#5 ∧ (8 <<< i.size.toNat) / 8 = bits / 8 := by
  rcases hbits with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- A load exclusive at `x25` with an unmapped byte faults. -/
theorem instFaults_excl {mp : ArmFault.MemMap} {s : Arm.ArmState} {i : Arm.Reg_exclusive_cls}
    (hL : i.L = 1#1) (hRn : i.Rn = 25#5)
    (hu : Unmapped mp (Arm.r (.GPR 25#5) s) ((8 <<< i.size.toNat) / 8)) :
    ArmFault.InstFaults mp (.LDST (.Reg_exclusive i)) s := by
  obtain ⟨k, hk, hm⟩ := hu
  refine ArmFault.instFaults_of_byte (e := ⟨Concurrency.ArmInstFoot.exclKind i,
    Arm.read_gpr 64 i.Rn s, (8 <<< i.size.toNat) / 8, Concurrency.ArmFoot.readM
      ((8 <<< i.size.toNat) / 8) (Arm.read_gpr 64 i.Rn s) s.mem⟩) ?_ hk ?_
  · simp [Concurrency.ArmInstFoot.instEvs, Concurrency.ArmInstFoot.exclEvs, hL, hRn]
  · simp [Arm.read_gpr, ArmFault.Perm.allows, Concurrency.ArmInstFoot.exclKind_R hL]
    rw [hRn, hm]

/-- **The `ldaxr` of an access range with an unmapped byte faults**, in any state whose `x25`
holds the address (the instruction's footprint reads `[x25, x25 + bits / 8)`). -/
theorem instFaults_ldaxr {mp : ArmFault.MemMap} {s : Arm.ArmState} {bits : Nat} {env : Env}
    {a : Arm.ArmInst} (hbits : bits = 8 ∨ bits = 16 ∨ bits = 32 ∨ bits = 64)
    (ha : (Insn.ldaxr bits (.x 27) (.x 25)).toArmInst env = .ok a)
    (hu : Unmapped mp (Arm.r (.GPR 25#5) s) (bits / 8)) : ArmFault.InstFaults mp a s := by
  obtain ⟨i, hi, hL, hRn, hsz⟩ := ldaxr_toArmInst hbits env
  rw [hi] at ha
  cases ha
  exact instFaults_excl hL hRn (by rw [hsz]; exact hu)

end E2E

namespace Backend.Proof

open Backend E2E Backend.DeadCleanup Backend.Proof.Driver

/-- The CLIF-level unmapped range (`MapFaults`'s byte) is an `Unmapped` 64-bit range. -/
theorem unmapped_of_addrPred {mp : ArmFault.MemMap} {u : BitVec 64} {n : Nat}
    (h : addrPred (fun a n => ∃ k < n, mp (BitVec.ofNat 64 (a + k)) = .none) u n) :
    Unmapped mp u n := by
  obtain ⟨a, rfl, k, hk, hm⟩ := h
  refine ⟨k, hk, ?_⟩
  rw [← hm]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

/-! ## The halting loops -/

/-- An LL/SC loop with trap code `c` whose address use (the first use) and size satisfy `A`. -/
def HaltsAt (c : Clif.TrapCode) (A : BitVec 64 → Nat → Prop) (i : MInst) (uses : List CV) :
    Prop :=
  ∃ n u us, loopTrap? i = some (c, n) ∧ uses = u :: us ∧ A (lo64 u) n

/-- Zero values for the defs of `i`. -/
def haltOuts (i : MInst) : List CV :=
  match i.operands with
  | .ok ops => (ops.toList.filter Operand.isDef).map (fun _ => 0)
  | .error _ => []

open Classical in
/-- **The semantics with halting loops** (proof device): `sem`, except that a loop with code `c`
whose address satisfies `A` halts, the world unchanged. -/
noncomputable def haltLoop (c : Clif.TrapCode) (A : BitVec 64 → Nat → Prop) (sem : Sem) : Sem :=
  fun i uses w => if HaltsAt c A i uses then some (haltOuts i, w, .halt) else sem i uses w

theorem haltLoop_of_not {c : Clif.TrapCode} {A : BitVec 64 → Nat → Prop} {sem : Sem} {i : MInst}
    {uses : List CV} (h : ¬ HaltsAt c A i uses) : haltLoop c A sem i uses = sem i uses := by
  funext w
  simp [haltLoop, h]

theorem haltLoop_of {c : Clif.TrapCode} {A : BitVec 64 → Nat → Prop} {sem : Sem} {i : MInst}
    {uses : List CV} (h : HaltsAt c A i uses) (w : Arm.ArmState) :
    haltLoop c A sem i uses w = some (haltOuts i, w, .halt) := by
  simp [haltLoop, h]

theorem haltOuts_length {i : MInst} {ops : Array Operand} (h : i.operands = .ok ops) :
    (haltOuts i).length = (ops.toList.filter Operand.isDef).length := by
  simp [haltOuts, h]

/-- A run to a halting loop is a run of `haltLoop` to the first halting loop. -/
theorem star_haltLoop {vc : VCode} {sem : Sem} {c : Clif.TrapCode} {A : BitVec 64 → Nat → Prop} :
    ∀ {x y : VConf CV Arm.ArmState}, Star (VStep vc sem) x y → ∀ {T : VState CV Arm.ArmState},
      y = .run T → (∃ vb i ops, vc.blocks[T.b]? = some vb ∧ vb.insts[T.k]? = some i ∧
        i.operands = .ok ops ∧ HaltsAt c A i (vuses ops T.ρ)) →
      ∃ Y : VState CV Arm.ArmState, Star (VStep vc (haltLoop c A sem)) x (.run Y) ∧
        ∃ vb i ops, vc.blocks[Y.b]? = some vb ∧ vb.insts[Y.k]? = some i ∧
          i.operands = .ok ops ∧ HaltsAt c A i (vuses ops Y.ρ) := by
  intro x y h
  induction h with
  | refl => intro T hT hh; subst hT; exact ⟨T, .refl _, hh⟩
  | step h1 _ ih =>
    intro T hT hh
    cases h1 with
    | @step b k ρ w vb i ops outs w' ctl c' hvb hi hops hsem hlen hn =>
      by_cases hx : HaltsAt c A i (vuses ops ρ)
      · exact ⟨⟨b, k, ρ, w⟩, .refl _, vb, i, ops, hvb, hi, hops, hx⟩
      · obtain ⟨Y, hY, hYh⟩ := ih hT hh
        have hs : haltLoop c A sem i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w =
            some (outs, w', ctl) := by
          rw [show (ops.toList.filter Operand.isUse).map (ρ ·.vreg) = vuses ops ρ from rfl,
            haltLoop_of_not hx]
          exact hsem
        exact ⟨Y, .step (VStep.step hvb hi hops hs hlen hn) hY, hYh⟩

/-- **A memory trap of the VCode run is a halt of `haltLoop`.** -/
theorem memTrap_halt {vc : VCode} {sem : Sem} {c : Clif.TrapCode} {A : BitVec 64 → Nat → Prop}
    {vs : VState CV Arm.ArmState} (h : VMemTrapFrom vc sem vs c A) :
    ∃ b k ρ w vb i ops, Star (VStep vc (haltLoop c A sem)) (.run vs) (.run ⟨b, k, ρ, w⟩) ∧
      vc.blocks[b]? = some vb ∧ vb.insts[k]? = some i ∧ i.operands = .ok ops ∧
      HaltsAt c A i (vuses ops ρ) ∧
      VStep vc (haltLoop c A sem) (.run ⟨b, k, ρ, w⟩) (.halt w) := by
  obtain ⟨b, k, ρ, w, vb, i, ops, u, us, n, hstar, hvb, hi, hops, hu, hlt, hA⟩ := h
  obtain ⟨⟨b', k', ρ', w'⟩, hY, vb', i', ops', hvb', hi', hops', hh⟩ :=
    star_haltLoop hstar rfl ⟨vb, i, ops, hvb, hi, hops, n, u, us, hlt, hu, hA⟩
  refine ⟨b', k', ρ', w', vb', i', ops', hY, hvb', hi', hops', hh, ?_⟩
  exact VStep.step hvb' hi' hops' (haltLoop_of hh w') (haltOuts_length hops') VNext.halt

/-- **A realisation of `sem` is one of `haltLoop c A sem`**: off the halting loops they agree;
at a halting loop the allocated code halts (the machine is unchanged). -/
theorem realizes_haltLoop {R : RL} {sem₀ : Sem} {c : Clif.TrapCode} {A : BitVec 64 → Nat → Prop}
    (hreal : Realizes R.vc R.rf sem₀ ckeep R.step (QA R) R.GoodX) :
    Realizes R.vc R.rf (haltLoop c A sem₀) ckeep R.step (QA R)
      R.GoodX := by
  intro s c0 c' hq hm
  cases hm with
  | move =>
    obtain ⟨n, c'', hm'', hq'', ht⟩ := hreal s _ _ hq .move
    exact ⟨n, c'', mstep_congr hm'' (fun _ _ _ _ _ _ _ _ _ hc => by cases hc), hq'', ht⟩
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsem hlen hho hcl hn =>
    have hstep : MStep R.vc (haltLoop c A sem₀) ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' :=
      MStep.op hvb hi hops hsz hsem hlen hho hcl hn
    by_cases hh : HaltsAt c A i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2))
    · rw [haltLoop_of hh] at hsem
      simp only [Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨-, -, rfl⟩ := hsem
      cases hn with
      | halt => exact ⟨0, _, hstep, .inl ⟨trivial, trivial⟩, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    · rw [haltLoop_of_not hh] at hsem
      obtain ⟨n, c'', hm'', hq'', ht⟩ := hreal s _ _ hq (MStep.op hvb hi hops hsz hsem hlen hho hcl hn)
      refine ⟨n, c'', mstep_congr hm'' fun b' k' allocs' its' m' w'' vb' i' ops' hc hvb' hi' hops' => ?_,
        hq'', ht⟩
      cases hc
      rw [hvb] at hvb'; cases hvb'
      rw [hi] at hi'; cases hi'
      rw [hops] at hops'; cases hops'
      exact congrFun (haltLoop_of_not hh).symm w

/-! ## The machine at a trap site -/

/-- **A line with a trap code is a trap site** (`trapAt_line` for any instruction). -/
theorem trapAt_ins {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {x : Insn}
    {code : Clif.TrapCode} (hj : R.L[j]? = some (.ins x (some code))) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) : TrapAt R.fb R.base code s := by
  refine ⟨herr, ⟨lineOffset R.L j, code⟩, ?_, rfl, hpc⟩
  exact ((FnAsm.layout_traps hR.layout).2 _).mpr ⟨j, _, hj, rfl⟩

/-- The machine at an instruction line decodes the line's instruction. -/
theorem decodeAt_line {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j) :
    ∃ a, x.toArmInst ⟨lineOffset R.fa.lines.toList j, (R.lm[·]?)⟩ = .ok a ∧
      Concurrency.ArmFoot.decodeAt s = some a := by
  obtain ⟨h4, w, hw, hk⟩ := FnAsm.layout_word hR.layout hR.lm hj rfl
  have hfetch : Arm.fetch_inst (Arm.r .PC s) s = some w := by
    rw [Arm.fetch_inst_from_program, hprog, hpc]
    have := FnBin.program_find (base := R.base)
      (by have := (FnAsm.layout_size hR.layout).1; have := hR.fit; omega) hk
    rwa [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h4)] at this
  obtain ⟨a, ha, hd⟩ := Insn.decode_encode hw
  refine ⟨a, ha, ?_⟩
  simp only [Concurrency.ArmFoot.decodeAt, hfetch, hd]

/-- **On the function's own machine an `LdaxrUnmapped` state faults** (`ArmFault.Faults`: the
next step of `ArmFault.stepF mp` is the memory fault). -/
theorem faults_of_ldaxrUnmapped {R : RL} (hR : R.Wf) {mp : ArmFault.MemMap} {s : Arm.ArmState}
    (h : LdaxrUnmapped mp R.fa R.base s) (hprog : s.program = R.fb.program R.base)
    (herr : Arm.r .ERR s = .None) : ArmFault.Faults mp s := by
  obtain ⟨j, bits, t, hj, hbits, hpc, hu⟩ := h
  obtain ⟨a, ha, hd⟩ := decodeAt_line hR hj hprog hpc
  have hf := instFaults_ldaxr hbits ha hu
  simp only [ArmFault.Faults, ArmFault.InstFaults] at hf ⊢
  simp only [Concurrency.ArmInstFoot.stepEvs, hd, show Arm.read_err s = .None from herr, ite_true]
  exact hf

/-- **`TrapAtM` with an unmapped `ldaxr` is `TrapAtF`** on the function's own machine. -/
theorem trapAtF_of_trapAtM {R : RL} (hR : R.Wf) {mp : ArmFault.MemMap} {c : Clif.TrapCode}
    {s : Arm.ArmState} (h : TrapAt R.fb R.base c s) (hl : LdaxrUnmapped mp R.fa R.base s)
    (hprog : s.program = R.fb.program R.base) : TrapAtF mp R.fb R.base c s :=
  ⟨h, faults_of_ldaxrUnmapped hR hl hprog h.err⟩

/-! ## Explicit traps with their `udf` line -/

/-- `trap_udf` with the trap site's `udf` line. -/
theorem trap_udf_line {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {code : Clif.TrapCode}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.udf code)) :
    TrapAt R.fb R.base code s ∧ UdfLine R.fa R.base s := by
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  obtain ⟨rfl, rfl⟩ := assign_none (fun f => rfl) hasg
  obtain rfl : c1 = [.inst (.udf code)] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  have hl1 := codeLinesE_single h1
  simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
  obtain ⟨rfl, -⟩ := hl1
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  rw [ftR_plain_append _ _ _ (by simp [Line.plain]) hZ] at hdrop
  have hj := drop_get (Z := []) (by simpa using hdrop)
  exact ⟨trapAt_line hR hj hpc hst.err, _, _, hj, hpc⟩

/-- `trap_trapIf` with the trap site's `udf` line. -/
theorem trap_trapIf_line {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {kk : CondBrKind}
    {code : Clif.TrapCode} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.trapIf kk code)) {ops : Array Operand}
    (hops : (MInst.trapIf kk code).operands = .ok ops)
    (hholds : kk.holds (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = true) :
    ∃ n, TrapAt R.fb R.base code (iterN R.step n s) ∧ UdfLine R.fa R.base (iterN R.step n s) ∧
      ∀ i < n, R.GoodX (iterN R.step i s) := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops', rfl, hit, hsplit,
    hasg, hc1', hops', hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  rw [hops] at hops'; cases hops'
  have hkk : ∀ r sz, kk = .zero r sz ∨ kk = .notZero r sz → r.isVregInt = true := by
    intro r sz hr
    have := ctlCheck_inst hck hvb hi
    rcases hr with rfl | rfl <;> simpa [ctlInstOk] using this
  obtain ⟨k', rfl, hkr⟩ := kind_alloc hkk (mk := fun k => MInst.trapIf k code) rfl
    (fun f => rfl) (fun f => rfl) hops hstat hasg m
  obtain rfl : c1 = [.inst (.trapIf k' code)] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  have hl1 := codeLinesE_single h1
  simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
  obtain ⟨rfl, hpsm⟩ := hl1
  -- the branch (relaxed or not) to the trap label is taken
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap ps1.traps.size)) none) ++
      (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, List.singleton_append, ftList_kind_trap k' ps1.traps.size _ hZ, relaxLines_cons,
      List.append_assoc]
  have hform : (∃ c, k'.insn (.trap ps1.traps.size) = .bcond c (.trap ps1.traps.size)) ∨
      (∃ nz w r, k'.insn (.trap ps1.traps.size) = .cbz nz w r (.trap ps1.traps.size)) ∨
      (∃ nz r bit, k'.insn (.trap ps1.traps.size) = .tbz nz r bit (.trap ps1.traps.size)) := by
    cases k' <;> simp [CondBrKind.insn]
  obtain ⟨nst, jl, hnst, hjt, -, -, -, hgx⟩ := reach_rcbX hR hdrop' hform (by simp) true
    (fun env a ha => by rw [kind_brCond hst hkr _ ha, hholds])
    (fun hct env a ha => by rw [kind_brCond_inv hst hkr _ _ hct ha, hholds])
    (by rw [hst.prog]) hpc hst.err hst.sp
  have hjl := hjt rfl
  -- the trap section entry of this trap
  have hpre : psm.traps.toList <+: R.psF.traps.toList :=
    (codeLinesE_traps h2).trans htr
  have hn : R.psF.traps.toList[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
    obtain ⟨t, ht⟩ := hpre
    rw [← ht, ← hpsm]
    simp
  obtain ⟨body, psF', hb, hL, -⟩ := emit_block hR.emit
  rw [relaxLines_append, relaxLines_trapLines,
    show emitFar ⟨R.fa.k, R.af.slotBase⟩ R.af = R.far from rfl] at hL
  obtain ⟨body', hb'⟩ := hR.psF
  have hk : R.ctx = ⟨R.fa.k, R.af.slotBase⟩ := rfl
  rw [hk, hb] at hb'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
  obtain ⟨-, rfl⟩ := hb'
  obtain ⟨hlab, hudf⟩ := trapLines_get _ _ _ hn
  have hlab' : R.L[(relaxLines R.far (ftList body)).length + 2 * ps1.traps.size]? = some (.label (.trap ps1.traps.size)) := by
    simp only [RL.L, hL]; rw [List.getElem?_append_right (by omega)]; simpa using hlab
  have hudf' : R.L[(relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1]? =
      some (.ins (.udf 0xc11f) (some code)) := by
    simp only [RL.L, hL]; rw [List.getElem?_append_right (by omega)]
    simpa [Nat.add_assoc] using hudf
  -- the branch reaches the label's offset, which is the trap site's
  have hoff : R.pcOf jl = R.pcOf ((relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1) := by
    have e1 := labelOffsets_label hR.lm hjl
    have e2 := labelOffsets_label hR.lm hlab'
    simp only [RL.pcOf]
    rw [lineOffset_succ _ _ _ hlab']
    simp only [RL.L] at e1 e2 ⊢
    rw [e1] at e2
    simp only [Option.some.injEq] at e2
    rw [e2]; simp [Line.size]
  have hpcF : Arm.r .PC (iterN R.step nst s) =
      R.pcOf ((relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1) := by
    rw [hnst, Arm.r_of_w_same, hoff]
  have herrF : Arm.r .ERR (iterN R.step nst s) = .None := by
    rw [hnst, Arm.r_of_w_different (by simp)]; exact hst.err
  exact ⟨nst, trapAt_line hR hudf' hpcF herrF, ⟨_, _, hudf', hpcF⟩, hgx⟩

/-! ## The trapping loops on the machine -/

set_option maxHeartbeats 4000000 in
/-- **`Q` at a trapping LL/SC loop item is at the loop's `ldaxr`**: the line after the loop's
label is `ldaxr x27, [x25]` with the flags' trap code, the machine is there without error, and
the loop's first use (the address) is the machine's `x25`. -/
theorem loop_ldaxr {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {i : MInst}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) {c : Clif.TrapCode} {n : Nat}
    (hlt : loopTrap? i = some (c, n)) :
    ∃ j bits, R.L[j]? = some (.ins (.ldaxr bits (.x 27) (.x 25)) (some c)) ∧
      (bits = 8 ∨ bits = 16 ∨ bits = 32 ∨ bits = 64) ∧ bits / 8 = n ∧
      Arm.r .PC s = R.pcOf j ∧ Arm.r .ERR s = .None ∧
      ∀ ops, i.operands = .ok ops → ∃ us,
        ((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2) = regVal s (.x 25) :: us := by
  cases i with
  | atomicRmwLoop ty op fl ra ro rd r1 r2 =>
    simp only [loopTrap?] at hlt
    split at hlt
    · rename_i hty
      cases htc : fl.trapCode with
      | none => simp [htc] at hlt
      | some c0 =>
      simp only [htc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hlt
      obtain ⟨rfl, rfl⟩ := hlt
      have hck := (lowerRFunc_ok hR.alloc).2.2
      have hok := ctlCheck_inst hck hvb hi
      simp only [ctlInstOk, Bool.and_eq_true] at hok
      obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hok
      obtain ⟨va, rfl⟩ := isVregInt_iff h0
      obtain ⟨vo, rfl⟩ := isVregInt_iff h1
      obtain ⟨vd, rfl⟩ := isVregInt_iff h2
      obtain ⟨v1, rfl⟩ := isVregInt_iff h3
      obtain ⟨v2, rfl⟩ := isVregInt_iff h4
      obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
        hasg, hc1', hops, hstat, hchk', hc2, hl1, hl2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
      have hops' : ops = #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨vo, .int, .use, .early, .fixed (.x 26)⟩,
          ⟨vd, .int, .def, .late, .fixed (.x 27)⟩, ⟨v1, .int, .def, .late, .fixed (.x 24)⟩,
          ⟨v2, .int, .def, .late, .fixed (.x 28)⟩] := by
        have e : (MInst.atomicRmwLoop ty op fl (.vreg va .int) (.vreg vo .int) (.vreg vd .int)
            (.vreg v1 .int) (.vreg v2 .int)).operands =
            .ok #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨vo, .int, .use, .early, .fixed (.x 26)⟩,
              ⟨vd, .int, .def, .late, .fixed (.x 27)⟩, ⟨v1, .int, .def, .late, .fixed (.x 24)⟩,
              ⟨v2, .int, .def, .late, .fixed (.x 28)⟩] := rfl
        rw [e] at hops; injection hops with h; exact h.symm
      subst hops'
      obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hstat
      obtain ⟨q0, q1, q2, q3, q4, rfl⟩ := regs5 (by simpa using hsz.symm)
      obtain rfl : q0 = .x 25 := fixed_reg (o := ⟨va, .int, .use, .early, .fixed (.x 25)⟩) hloc (by simp) rfl
      obtain rfl : q1 = .x 26 := fixed_reg (o := ⟨vo, .int, .use, .early, .fixed (.x 26)⟩) hloc (by simp) rfl
      obtain rfl : q2 = .x 27 := fixed_reg (o := ⟨vd, .int, .def, .late, .fixed (.x 27)⟩) hloc (by simp) rfl
      obtain rfl : q3 = .x 24 := fixed_reg (o := ⟨v1, .int, .def, .late, .fixed (.x 24)⟩) hloc (by simp) rfl
      obtain rfl : q4 = .x 28 := fixed_reg (o := ⟨v2, .int, .def, .late, .fixed (.x 28)⟩) hloc (by simp) rfl
      have hasg' : (MInst.atomicRmwLoop ty op fl (.vreg va .int) (.vreg vo .int) (.vreg vd .int)
          (.vreg v1 .int) (.vreg v2 .int)).assign #[.x 25, .x 26, .x 27, .x 24, .x 28] =
          .ok (.atomicRmwLoop ty op fl (.x 25) (.x 26) (.x 27) (.x 24) (.x 28)) := rfl
      rw [hasg'] at hasg; cases hasg
      obtain rfl : c1 = [.inst (.atomicRmwLoop ty op fl (.x 25) (.x 26) (.x 27) (.x 24) (.x 28))] := by
        rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
        · exact h
        · cases h
        · cases h
      have hl1' := codeLinesE_single hl1
      simp only [MInst.lines, bne_self_eq_false, Bool.or_false, Bool.and_false, Bool.false_eq_true,
        ite_false, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1'
      obtain ⟨rfl, rfl⟩ := hl1'
      have hdrop' := ftList_rmw hR hty ⟨_, rfl⟩ hdrop
      have hL0 : R.L[j0]? = some (.label (.loop ps1.aloop)) := by
        have := congrArg (·[0]?) hdrop'
        simpa [List.getElem?_drop, rmwLoopLines] using this
      have hL1 : R.L[j0 + 1]? = some (.ins (.ldaxr ty.bits (.x 27) (.x 25)) fl.trapCode) := by
        have := congrArg (·[1]?) hdrop'
        simpa [List.getElem?_drop, rmwLoopLines, rmwLoopBody] using this
      have hpc1 : Arm.r .PC s = R.pcOf (j0 + 1) := by rw [hpc, RL.pcOf_succ_label hL0]
      have hreg : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
        hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
      refine ⟨j0 + 1, ty.bits, by rw [hL1, htc], by rcases hty with rfl | rfl | rfl | rfl <;> simp [CTy.bits],
        rfl, hpc1, hst.err, fun ops' hops' => ⟨[regVal s (.x 26)], ?_⟩⟩
      rw [hops] at hops'; cases hops'
      simp [Operand.isUse, hreg (.x 25) rfl, hreg (.x 26) rfl]
    · cases hlt
  | atomicCasLoop ty fl ra re rx rd r1 =>
    simp only [loopTrap?] at hlt
    split at hlt
    · rename_i hty
      cases htc : fl.trapCode with
      | none => simp [htc] at hlt
      | some c0 =>
      simp only [htc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hlt
      obtain ⟨rfl, rfl⟩ := hlt
      have hck := (lowerRFunc_ok hR.alloc).2.2
      have hok := ctlCheck_inst hck hvb hi
      simp only [ctlInstOk, Bool.and_eq_true] at hok
      obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hok
      obtain ⟨va, rfl⟩ := isVregInt_iff h0
      obtain ⟨ve, rfl⟩ := isVregInt_iff h1
      obtain ⟨vx, rfl⟩ := isVregInt_iff h2
      obtain ⟨vd, rfl⟩ := isVregInt_iff h3
      obtain ⟨v1, rfl⟩ := isVregInt_iff h4
      obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
        hasg, hc1', hops, hstat, hchk', hc2, hl1, hl2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
      have hops' : ops = #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨ve, .int, .use, .early, .fixed (.x 26)⟩,
          ⟨vx, .int, .use, .early, .fixed (.x 28)⟩, ⟨vd, .int, .def, .late, .fixed (.x 27)⟩,
          ⟨v1, .int, .def, .late, .fixed (.x 24)⟩] := by
        have e : (MInst.atomicCasLoop ty fl (.vreg va .int) (.vreg ve .int) (.vreg vx .int)
            (.vreg vd .int) (.vreg v1 .int)).operands =
            .ok #[⟨va, .int, .use, .early, .fixed (.x 25)⟩, ⟨ve, .int, .use, .early, .fixed (.x 26)⟩,
              ⟨vx, .int, .use, .early, .fixed (.x 28)⟩, ⟨vd, .int, .def, .late, .fixed (.x 27)⟩,
              ⟨v1, .int, .def, .late, .fixed (.x 24)⟩] := rfl
        rw [e] at hops; injection hops with h; exact h.symm
      subst hops'
      obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hstat
      obtain ⟨q0, q1, q2, q3, q4, rfl⟩ := regs5 (by simpa using hsz.symm)
      obtain rfl : q0 = .x 25 := fixed_reg (o := ⟨va, .int, .use, .early, .fixed (.x 25)⟩) hloc (by simp) rfl
      obtain rfl : q1 = .x 26 := fixed_reg (o := ⟨ve, .int, .use, .early, .fixed (.x 26)⟩) hloc (by simp) rfl
      obtain rfl : q2 = .x 28 := fixed_reg (o := ⟨vx, .int, .use, .early, .fixed (.x 28)⟩) hloc (by simp) rfl
      obtain rfl : q3 = .x 27 := fixed_reg (o := ⟨vd, .int, .def, .late, .fixed (.x 27)⟩) hloc (by simp) rfl
      obtain rfl : q4 = .x 24 := fixed_reg (o := ⟨v1, .int, .def, .late, .fixed (.x 24)⟩) hloc (by simp) rfl
      have hasg' : (MInst.atomicCasLoop ty fl (.vreg va .int) (.vreg ve .int) (.vreg vx .int)
          (.vreg vd .int) (.vreg v1 .int)).assign #[.x 25, .x 26, .x 28, .x 27, .x 24] =
          .ok (.atomicCasLoop ty fl (.x 25) (.x 26) (.x 28) (.x 27) (.x 24)) := rfl
      rw [hasg'] at hasg; cases hasg
      obtain rfl : c1 = [.inst (.atomicCasLoop ty fl (.x 25) (.x 26) (.x 28) (.x 27) (.x 24))] := by
        rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
        · exact h
        · cases h
        · cases h
      have hl1' := codeLinesE_single hl1
      simp only [MInst.lines, bne_self_eq_false, Bool.or_false, Bool.false_eq_true,
        ite_false, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1'
      obtain ⟨rfl, rfl⟩ := hl1'
      have hdrop' : R.L.drop j0 = casLoopLines ty.bits fl (.loop ps1.aloop) (.loop (ps1.aloop + 1)) ++
          (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
        rw [hdrop, ftList_cas hty, relaxLines_append, relaxLines_loop (by
          rcases hty with rfl | rfl | rfl | rfl <;>
            simp (config := {decide := true}) [casLoopLines, casLoopHead, casLoopCmp, Insn.condTarget?,
              CTy.bits]), List.append_assoc]
      have hat : ∀ q ln, (casLoopLines ty.bits fl (.loop ps1.aloop) (.loop (ps1.aloop + 1)))[q]? = some ln →
          R.L[j0 + q]? = some ln := by
        intro q ln hq
        have := congrArg (·[q]?) hdrop'
        simp only [List.getElem?_drop] at this
        rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hq).1]; exact hq
      have hL0 : R.L[j0]? = some (.label (.loop ps1.aloop)) := hat 0 _ rfl
      have hL1 : R.L[j0 + 1]? = some (.ins (.ldaxr ty.bits (.x 27) (.x 25)) fl.trapCode) := hat 1 _ rfl
      have hpc1 : Arm.r .PC s = R.pcOf (j0 + 1) := by rw [hpc, RL.pcOf_succ_label hL0]
      have hreg : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
        hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
      refine ⟨j0 + 1, ty.bits, by rw [hL1, htc], by rcases hty with rfl | rfl | rfl | rfl <;> simp [CTy.bits],
        rfl, hpc1, hst.err, fun ops' hops' => ⟨[regVal s (.x 26), regVal s (.x 28)], ?_⟩⟩
      rw [hops] at hops'; cases hops'
      simp [Operand.isUse, hreg (.x 25) rfl, hreg (.x 26) rfl, hreg (.x 28) rfl]
    · cases hlt
  | _ => simp [loopTrap?] at hlt

/-! ## The core -/

private theorem valueSemV_halt' {gv : Nat → String → Prop} {F : BitVec 64 → Prop}
    {ctx : FnCtx} {X : ExtSem} {i : MInst} {us outs : List CV}
    {w w' : Arm.ArmState} (h : valueSemV gv F ctx X i us w = some (outs, w', .halt)) :
    csemV gv F ctx X i us w = some (outs, w', .halt) := by
  by_cases hp : specForm i = true
  · have hs : mspec ctx.slotBase i us w = some (outs, w', .halt) := by
      simpa [valueSemV, hp] using h
    have := mspec_spec_next hp hs
    cases this
  · simpa [valueSemV, hp] using h

/-- **The register level of the explicit and the memory traps** under the dead-cleanup chain's
value semantics (`regLevelCorrect_world_atX_value`'s trap half): an explicit trap of the VCode run
is a `udf` trap site of the machine run, a memory trap (`VMemTraps … c A`) whose address ranges
have an unmapped byte (`A` implies `Unmapped mp`) is the state at the trapping loop's `ldaxr`
(`TrapAtM`), every earlier state `GoodX`. -/
theorem regLevel_memtrap_world_value {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt vcp rf cc ins a0) (hok : EntryOk a0) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    (hC : CalleeOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K X H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r)))
    (mp : ArmFault.MemMap) :
    ∃ m₀ : Loc → CV,
    (∀ c, VTraps vcp (valueSemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) (ρsel m₀) w₀ c →
      ∃ n, TrapAtM mp fa fb base c (E2E.runX (ArmStepX X H fa) n s) ∧
        ∀ i < n, actGoodX vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) ∧
    (∀ c (A : BitVec 64 → Nat → Prop), (∀ x n, A x n → Unmapped mp x n) →
      VMemTraps vcp (valueSemV gv (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X) (ρsel m₀) w₀ c A →
      ∃ n, TrapAtM mp fa fb base c (E2E.runX (ArmStepX X H fa) n s) ∧
        ∀ i < n, actGoodX vcp rf af fa fb base s X H K G gv (E2E.runX (ArmStepX X H fa) i s)) := by
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let R : RL := ⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, gv⟩
  have hR : R.Wf := ⟨⟨cc, ins, a0, hcheck, hok⟩, halloc, hemit, hlayout, hlm, by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres,
    ⟨body, hb⟩, hent.program, hG⟩
  obtain ⟨n0, ht0, hq0, hA0, -⟩ := q_init hR hent hbe
  have hRz0 := realizes_value_all hR hC hCT hTls hcov
  have hmk : ∀ (n1 n23 : Nat), (∀ i < n1 + n23, R.GoodX (iterN R.step i (iterN R.step n0 s))) →
      ∀ i < n0 + (n1 + n23), actGoodX vcp rf af fa fb base s X H K G gv
        (E2E.runX (ArmStepX X H fa) i s) := by
    intro n1 n23 hb i hi
    rw [runX_eq]
    exact (trace_add ht0 hb i hi).act
  have hfin : ∀ n1 n2 n3, E2E.runX (ArmStepX X H fa) (n0 + n1 + n2 + n3) s =
      iterN R.step n3 (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s))) := by
    intro n1 n2 n3; rw [runX_eq]; simp only [iterN_add]; rfl
  refine ⟨locVal R.fr (iterN R.step n0 s), fun c htr => ?_, fun c A hA hmt => ?_⟩
  · -- an explicit trap
    have hck := (lowerRFunc_ok hR.alloc).2.2
    obtain ⟨Rl, hSim, hinit, -⟩ :=
      checkedAt_sound R.vc R.rf R.valueSem ckeep hcheck (locVal R.fr (iterN R.step n0 s))
        (ρsel (locVal R.fr (iterN R.step n0 s))) w₀ (hsel _)
    have hRz := hRz0
    obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩ := htr
    obtain ⟨n1, c1, hq1, hr1, ht1⟩ := forward hSim hRz hstar hinit (.inl ⟨hq0, hA0⟩)
    obtain ⟨hnil, hform⟩ := csem_halt (csemV_sub (valueSemV_halt' hsem))
    subst hnil
    have hdefs : ops.toList.filter Operand.isDef = [] := by
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
      · rw [udf_ops hops]; rfl
      · exact trapIf_nodefs hops
    have h1 : VStep R.vc R.valueSem (.run ⟨b, k, ρ, w⟩) (.halt w') :=
      VStep.step hvb hi hops hsem (by rw [hdefs]; rfl) VNext.halt
    obtain ⟨n2, c', c'', hq2, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hq1
    cases c'' with
    | run s' => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | ret vs m' w'' => cases hSim.ret hr3
    | halt w'' =>
      cases hms with
      | op hvb' hi' hops' hsz hsem2 hlen2 hho hcl hn =>
        obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
        simp only at hb' hk' hw'
        subst hb' hk' hw'
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        have hnr : ∀ us, i ≠ .rets us := by
          intro us h
          rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩ <;> cases h
        have hq2 := (qa_op hq2 hvb hi hnr).1
        rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
        · simp only [trapCode?, Option.some.injEq] at htc
          subst htc
          obtain ⟨htrap, hline⟩ := trap_udf_line hR hq2 hvb hi
          refine ⟨n0 + n1 + n2 + 0, by rw [hfin n1 n2]; exact ⟨htrap, .inl hline⟩,
            fun i hi => hmk n1 (n2 + 0)
              (trace_add ht1 (trace_add ht2 fun _ h => absurd h (Nat.not_lt_zero _))) i (by omega)⟩
        · cases hn with
          | halt =>
          obtain ⟨-, hform2⟩ := csem_halt (csemV_sub (valueSemV_halt' hsem2))
          rcases hform2 with ⟨_, e⟩ | ⟨kk', cd', e, hholds⟩
          · cases e
          · cases e
            simp only [trapCode?, Option.some.injEq] at htc
            subst htc
            obtain ⟨n3, htrap, hline, ht3⟩ := trap_trapIf_line hR hq2 hvb hi hops' hholds
            refine ⟨n0 + n1 + n2 + n3, by rw [hfin n1 n2]; exact ⟨htrap, .inl hline⟩,
              fun i hi => hmk n1 (n2 + n3) (trace_add ht1 (trace_add ht2 ht3)) i (by omega)⟩

  · -- a memory trap
    obtain ⟨b, k, ρ, w, vb, i, ops, hstar, hvb, hi, hops, hh, -⟩ := memTrap_halt hmt
    obtain ⟨hSim, hinit, -⟩ := checkedAt_sound_match (sem := haltLoop c A R.valueSem)
      (keep := ckeep) hcheck (locVal R.fr (iterN R.step n0 s))
      (ρsel (locVal R.fr (iterN R.step n0 s))) w₀ (hsel _)
    have hRz : Realizes R.vc R.rf (haltLoop c A R.valueSem) ckeep R.step
        (QA R) R.GoodX := realizes_haltLoop hRz0
    obtain ⟨n1, c1, hq1, hr1, ht1⟩ := forward hSim hRz hstar hinit (.inl ⟨hq0, hA0⟩)
    have h1 : VStep R.vc (haltLoop c A R.valueSem) (.run ⟨b, k, ρ, w⟩) (.halt w) :=
      VStep.step hvb hi hops (haltLoop_of hh w) (haltOuts_length hops) VNext.halt
    obtain ⟨n2, c', c'', hq2, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz h1 _ c1 _ (Nat.le_refl _) hr1 hq1
    cases hms with
    | move => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | @op b' k' allocs its m w2 vb' i2 ops2 outs2 outs2' w2' ctl m2 c3 hvb' hi' hops' hsz hsem2
        hlen2 hho hcl hn =>
      obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
      simp only at hb' hk' hw'
      subst hb' hk' hw'
      rw [hvb] at hvb'; cases hvb'
      rw [hi] at hi'; cases hi'
      rw [hops] at hops'; cases hops'
      have hU0 := matchRun_uses hcheck hr2 (MStep.op hvb hi hops hsz hsem2 hlen2 hho hcl hn) hvb hi
        hops
      obtain ⟨nb, u, us, hlt, hu, hAu⟩ := hh
      have hq2 := (qa_op hq2 hvb hi (fun _ h => by subst h; simp [loopTrap?] at hlt)).1
      obtain ⟨j, bits, hj, hbits, hnb, hpc, herr, huse⟩ := loop_ldaxr hR hq2 hvb hi hlt
      obtain ⟨us', hus'⟩ := huse ops hops
      have hu0 : u = regVal (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s))) (.x 25) := by
        have := hU0.symm.trans hus'
        rw [hu] at this
        exact (List.cons.inj this).1
      have hun : Unmapped mp (Arm.r (.GPR 25#5)
          (iterN R.step n2 (iterN R.step n1 (iterN R.step n0 s)))) (bits / 8) := by
        rw [hnb]
        have := hA _ _ hAu
        rwa [hu0, lo64_regVal_x] at this
      refine ⟨n0 + n1 + n2 + 0, ?_, fun i hi => hmk n1 (n2 + 0)
        (trace_add ht1 (trace_add ht2 fun _ h => absurd h (Nat.not_lt_zero _))) i (by omega)⟩
      rw [hfin n1 n2 0]
      exact ⟨trapAt_ins hR hj hpc herr, .inr ⟨j, bits, some c, hj, hbits, hpc, hun⟩⟩

end Backend.Proof

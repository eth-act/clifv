import FV.Concurrency.RealizeWitnessCas
import FV.Concurrency.CallLoadWitness

/-!
# `atomic_cas` storing a new value: `Realizes` on the whole run (T2j follow-up, #473)

`RealizeWitnessCas` runs the compiled `atomic_cas.i64` with the expected value `0` and the
replacement `0`. Its CLIF step may then have the read alone (a store leaving the bytes unchanged
is no event of the step), so only `Covers` follows there (`WitnessC.realizes_cas_cov`). Here the
same compiled function is entered with the replacement `1` in x2 (`RAC1`, CLIF entry `csC1`):

* `compiled_ofC1`, `run_cas1`: as `WitnessC.compiled_ofC`, `WitnessC.run_cas`; the `ldaxr`
  reads the bytes `0` (the expected value): `(convEv eR).val`;
* **the read value** `cstep_rd`: a CLIF step of `csC1` whose read has the bytes `0` has a second,
  write event (with the read alone the bytes would stay, but the step stores `1`: `stepZ`);
* `pair_full_rd`: a covering prefix of a private run ending in an exclusive pair is the whole run
  when the CLIF thread cannot stop at its start and its first step reading the pair's read bytes
  has a second non-fence event (as `WitnessR.pair_full`, the read value carried by `Refines`);
* **`realizes_cas_full`**: every execution of the whole run (its `rmw` the run's monitor pairs,
  which relate the `ldaxr`'s read to the `stlxr`'s write) is `Realizes`d by a CLIF thread from
  `csC1`.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.RealizeCompiled.WitnessC1

open Arm ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine
  ArmAllocThread ThreadCompose E2E ArmInstFoot Code RealizeCompiled.Witness RealizeCompiled.WitnessL
  RealizeCompiled.WitnessR RealizeCompiled.WitnessC
open ArmAllocThread.Witness (act)

/-! ## The activation with the replacement `1` -/

/-- The ABI entry state of `RAC` with `1` in x2. -/
def sC1 : ArmState := Arm.w (.GPR 2#5) 1#64 RAC.s0

/-- **The compiled `atomic_cas`, entered with x2 = 1** (otherwise as `RAC`). -/
abbrev RAC1 : RL := { act vcpC rfC with base := 0x20000#64, s0 := sC1 }

/-- `RAC`'s ABI entry. -/
theorem abiRC : AbiCall RAC.fb RAC.base 0x4000#64 RAC.s0 :=
  ArmAllocThread.Witness.abi_ofAt (by decide) (by decide) factsC.2.2.2.2.2.2.2.1 codeRC

theorem r_sC1 {f : StateField} (h : f ≠ .GPR 2#5) : Arm.r f sC1 = Arm.r f RAC.s0 :=
  Arm.r_of_w_different h

theorem program_sC1 : sC1.program = RAC1.fb.program RAC1.base := by
  show (Arm.w _ _ RAC.s0).program = _
  rw [w_program]
  exact abiRC.program

theorem spv_sC1 : E2E.spv sC1 = E2E.spv RAC.s0 := r_sC1 (by simp)

theorem codeAddr_sC1 {a : BitVec 64} : CodeAddr sC1 a ↔ CodeAddr RAC.s0 a := by
  unfold CodeAddr
  rw [show sC1.program = RAC.s0.program from w_program]

theorem stackC1 : StackAvail 0 (act vcpC rfC).af sC1 := by
  have h : StackAvail 0 RAC.af RAC.s0 := wfRC.stack
  unfold StackAvail StackRoom at h ⊢
  rw [spv_sC1]
  exact ⟨⟨h.1.1, fun a ha => h.1.2 a (codeAddr_sC1.mp ha)⟩, h.2⟩

theorem wfRC1 : RAC1.Wf := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -, h9⟩ := factsC
  exact CallSeg.WitnessC.wf_gen allocC h1 h2 h3 h4 h5 h6 h9 stackC1 program_sC1
    fun _ h => h.elim

theorem codeRC1 : ∀ k < RAC1.fb.words.size,
    Arm.read_mem_bytes 4 (0x20000#64 + BitVec.ofNat 64 (4 * k)) RAC1.s0 = RAC1.fb.words[k]! := by
  native_decide

theorem abiRC1 : AbiCall RAC1.fb RAC1.base 0x4000#64 RAC1.s0 where
  program := program_sC1
  code k w hk := by
    obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hk
    rw [show RAC1.base = 0x20000#64 from rfl, codeRC1 k hlt]
    simp [hlt]
  pc := by rw [show RAC1.s0 = sC1 from rfl, r_sC1 (by simp)]; exact abiRC.pc
  err := by rw [show RAC1.s0 = sC1 from rfl, r_sC1 (by simp)]; exact abiRC.err
  lr := by
    have h := abiRC.lr
    simp only [xreg] at h ⊢
    rw [r_sC1 (by simp)]
    exact h
  spAligned := by rw [show RAC1.s0 = sC1 from rfl, spv_sC1]; exact abiRC.spAligned
  fits := abiRC.fits

theorem entryArgRC1 : ∀ r, RAC1.vc.EntryArg r → r.isArgReg = true := entryArgRC

/-- The entry world of the body. -/
abbrev w₀C1 : ArmState := E2E.bodyOf RAC1.af RAC1.s0

theorem qRC1 : ∃ n, Q RAC1 (iterN RAC1.step n RAC1.s0)
      (MConf.init RAC1.rf (locVal RAC1.fr (iterN RAC1.step n RAC1.s0)) w₀C1) ∧
    AInv RAC1 (MConf.init RAC1.rf (locVal RAC1.fr (iterN RAC1.step n RAC1.s0)) w₀C1) := by
  obtain ⟨n, -, hq, hA, -⟩ := q_init wfRC1 abiRC1
    ((E2E.Binary.bodyEntry_bodyOf RAC1.af RAC1.s0).w RAC1.F entryArgRC1)
  exact ⟨n, hq, hA⟩

theorem scopeLSC1 : MemScopeLS RAC1 := scopeLSC

/-! ## The CLIF entry -/

/-- The arguments: `0 : i64` (the address), `0 : i64` (the expected value), `1 : i64` (the
replacement). -/
def argsC1 : List Clif.Val := [⟨.i64, 0⟩, ⟨.i64, 0⟩, ⟨.i64, 1⟩]

/-- The entry registers. -/
def regsC1 : Clif.Regs :=
  (Clif.Regs.empty.setMany (B0C.params.map (·.1)) argsC1).getD Clif.Regs.empty

/-- **The CLIF entry state**: block 0, `v0 = v1 = 0`, `v2 = 1`, no slots, one 8-byte allocation
at 0. -/
def csC1 : Clif.State :=
  { frame := { func := fC, regs := regsC1, slots := [], body := B0C.body, term := B0C.term }
    callers := []
    mem := memL }

/-- The memory relation's parameters. -/
def ΓC1 : E2E.Rel := ⟨RAC1.F, fun _ => none, RAC1.ctx.slotBase, 0⟩

theorem shapeC1 :
    (Clif.Regs.empty.setMany (B0C.params.map (·.1)) argsC1).isSome = true ∧
    argsC1.map (·.ty) = B0C.params.map (·.2) ∧ argsC1.map (·.ty) = fC.sig.params.map (·.ty) ∧
    (locsOf fC.sig).all (fun l => match l with | .stack _ => false | _ => true) = true ∧
    (E2E.spv w₀C1).toNat % 16 = 0 ∧ regVal RAC1.s0 (.x 0) = 0 ∧ regVal RAC1.s0 (.x 1) = 0 ∧
    regVal RAC1.s0 (.x 2) = 1 ∧ Arm.read_mem_bytes 8 0 w₀C1 = 0 ∧
    (∀ k < 8, w₀C1.mem (BitVec.ofNat 64 k) = 0) := by
  native_decide

theorem regsC1_eq : Clif.Regs.empty.setMany (B0C.params.map (·.1)) argsC1 = some regsC1 := by
  have h := shapeC1.1
  unfold regsC1
  revert h
  cases Clif.Regs.empty.setMany (B0C.params.map (·.1)) argsC1 with
  | none => intro h; cases h
  | some r => intro _; rfl

theorem errW₀C1 : Arm.r .ERR w₀C1 = .None := by
  rw [E2E.r_bodyOf _ _ (by simp) (by simp)]
  exact abiRC1.err

/-- **The first 8 bytes are no frame address.** -/
theorem notF_lowC1 : ∀ x < 8, ¬ RAC1.F (BitVec.ofNat 64 x) := by
  have h : ∀ x < 8, fB RAC1 (BitVec.ofNat 64 x) = false := by native_decide
  intro x hx hF
  have := h x hx
  rw [fB_of rfl (fun _ h => h) hF] at this
  cases this

theorem relC1 : E2E.RelW ΓC1 fC (E2E.spv w₀C1) [] memL w₀C1 := by
  refine ⟨⟨⟨fun a b _ hb => by simp [memL] at hb, fun a n hv => ?_, rfl⟩,
      fun id b h => by simp at h, E2E.outRel_zero _ _ _⟩, rfl, errW₀C1⟩
  simp only [Clif.Mem.valid, memL, List.any_cons, List.any_nil, Bool.or_false,
    Clif.Alloc.contains] at hv
  have hv' : a + n ≤ 8 := by
    revert hv; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  exact ⟨by omega, fun k hk => notF_lowC1 _ (by omega)⟩

theorem argsAtC1 : ArgsAtEntry RAC1.F fC.sig argsC1 w₀C1 := by
  intro loc v h
  rw [locsC] at h
  simp only [argsC1, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.mem_singleton,
    Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show VHolds _ _
    rw [VHolds, E2E.regVal_bodyOf _ _ (by decide), shapeC1.2.2.2.2.2.1]
    rfl
  · show VHolds _ _
    rw [VHolds, E2E.regVal_bodyOf _ _ (by decide), shapeC1.2.2.2.2.2.2.1]
    rfl
  · show VHolds _ _
    rw [VHolds, E2E.regVal_bodyOf _ _ (by decide), shapeC1.2.2.2.2.2.2.2.1]
    rfl

/-- `CompiledLS` for the compiled `atomic_cas` entered with x2 = 1, at every Arm state `Q`-related
to its entry configuration. -/
theorem compiled_ofC1 {s : ArmState}
    (hq : Q RAC1 s (MConf.init RAC1.rf (locVal RAC1.fr s) w₀C1))
    (hA : AInv RAC1 (MConf.init RAC1.rf (locVal RAC1.fr s) w₀C1)) (env : Clif.Env)
    (p : Clif.Program) : CompiledLS env p RAC1 csC1 s := by
  obtain ⟨hlow, hthr, hext, hind, hv, -, hout, hprep, -⟩ := checksC
  obtain ⟨ctx, st0, R, gn, bl, A, H, hbl⟩ := driverHyp_of (Γ := ΓC1) (fctx := RAC1.ctx)
    (X := RAC1.X) (c := E2E.spv w₀C1) (env := env) (p := p) hlow hthr (List.isEmpty_iff.mp hext)
    (List.isEmpty_iff.mp hind) hv cfgC hout rfl (fun _ _ h => by cases h)
  obtain ⟨-, hpar, hsig, hlocs, hc, -⟩ := shapeC1
  exact {
    wf := wfRC1
    scope := scopeLSC1
    gv := rfl
    front := ⟨fC, vcC, ctx, st0, R, gn, bl, A, _, [], ΓC1.slotOff, ΓC1.syms, B0C, argsC1, _, w₀C1,
      H, hbl, E2E.memRelOk_relW ΓC1 fC _, IselRefines.Witness.relW_wf hc,
      VCodeThread.Witness.X0_tls, memRefines_csem RAC1.F RAC1.ctx _ rfl (fun _ _ h => by cases h),
      E2E.mrStable_relW ΓC1 fC _,
      (fun off h => by
        have := List.all_eq_true.mp hlocs _ h
        simp at this),
      hprep, allocC, b0C, rfl, rfl, rfl, rfl, rfl, regsC1_eq, hpar, hsig, relC1, argsAtC1, hq,
      hA⟩ }

/-! ## The run through the loop -/

/-- The bytes of the 8 bytes at address 0 of a memory holding zeros there. -/
theorem bytesOf_readM_zero {m : Memory} (h : ∀ k < 8, m (BitVec.ofNat 64 k) = 0) :
    bytesOf 8 (ArmFoot.readM 8 0 m) = List.replicate 8 (some 0#8) := by
  apply List.ext_getElem (by simp [bytesOf])
  intro k h1 h2
  have hk : k < 8 := by simpa [bytesOf] using h1
  simp only [bytesOf, List.getElem_map, List.getElem_range, List.getElem_replicate]
  rw [ArmFoot.readM_byte 8 0 m k hk]
  simp only [read_store]
  rw [show (0 + BitVec.ofNat 64 k : BitVec 64) = BitVec.ofNat 64 k by bv_omega, h k hk]
  rfl

/-- The entry `args` as a step of the allocated code (as `WitnessC.args_stepC`). -/
theorem args_stepC1 (its : List RItem) (m : Loc → CV) (w : ArmState) :
    ∃ m', MStep RAC1.vc RAC1.sem ckeep RAC1.rf
      (.run ⟨0, .op 0 #[.reg (.x 0), .reg (.x 1), .reg (.x 2)] :: its, m, w⟩) (.run ⟨0, its, m', w⟩) ∧
      m' (.reg (.x 0)) = regVal w (.x 0) ∧ m' (.reg (.x 1)) = regVal w (.x 1) := by
  obtain ⟨hi, -, hsz⟩ := instsC
  refine ⟨_, MStep.op vb0C hi (operands_args [(0, .x 0), (1, .x 1), (2, .x 2)]) rfl rfl
    (by simp [argOps, Operand.isDef]) (HavocOuts.refl _ _ _)
    ⟨fun _ _ => rfl, fun c hc => by cases hc⟩ (MNext.next (by rw [hsz]; decide)), ?_, ?_⟩
  all_goals simp [writeM, argOps, Operand.isDef, Operand.isLate, Operand.isEarly, Backend.Proof.upd]

/-- **The run of the compiled `atomic_cas` entered with x2 = 1 through one successful iteration
of its loop** (as `WitnessC.run_cas`); the `ldaxr` reads the bytes `0`. -/
theorem run_cas1 : ∃ (n : Nat) (lsP : List Lab) (eR eW : Ev) (t' : ArmState × Mon),
    (∀ env p, CompiledLS env p RAC1 csC1 (iterN RAC1.step n RAC1.s0)) ∧
    PRun Policy.arm RAC1.step (OkPriv RAC1) (iterN RAC1.step n RAC1.s0, none) (pairLs lsP eR eW 2) t' ∧
    eR.k = .acqXR ∧ eW.k = .relXW ∧ eR.addr = 0 ∧ eW.addr = 0 ∧ eR.n = 8 ∧ eW.n = 8 ∧
    (convEv eR).val = List.replicate 8 (some 0#8) ∧
    (∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RAC1 e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR)) := by
  obtain ⟨n', hq, hA⟩ := qRC1
  have e0 := checksRunC.1
  have hq0 := hq
  have hA0 := hA
  simp only [MConf.init] at hq0 hA0
  rw [show RAC1.rf = rfC from rfl, e0] at hq0 hA0
  -- the saves
  obtain ⟨ls1, t1, r1, hq1, hA1, hev1⟩ := moves_fwdA wfRC1 (fun K => (K == .plainW) = true)
    savesL _ _ _ none hq0 hA0 (moves_kinds checksRunC.2.1) (by simp [savesL, Loc.isSave])
  -- the entry `args`
  obtain ⟨m', hst, hm0, hm1⟩ := args_stepC1 (spillC.map (fun p => RItem.move p.1 p.2) ++
    (.op 1 allocsC :: itsC)) _ w₀C1
  have hq2 := realizes_args wfRC1 hq1 hA1 vb0C instsC.1 hst
  have hA2 := Backend.Proof.aInv_step wfRC1 hq1 hA1 hst
  -- the spills and reloads
  obtain ⟨ls2, t2, r2, hq3, -, hev2⟩ := moves_fwdA wfRC1
    (fun K => (K == .plainW || K == .plainR) = true) spillC (.op 1 allocsC :: itsC) t1.1 m' t1.2
    hq2 hA2 (moves_kinds checksRunC.2.2.1) (by simp [spillC, Loc.isSave])
  -- the loop
  obtain ⟨fl, ra, re, rx, rd, q1, hi1⟩ := instsC.2.1
  obtain ⟨j0, nl, X, hdrop, hprog, hpc, herr, hstr⟩ :=
    cas_lines wfRC1 hq3 LoopWitness.hty64 vb0C hi1
  -- the address and the expected value: the arguments, `0`
  have hreg : ∀ (q : Nat), movesM spillC m' (.reg (.x q)) = 0 → (q = 25 ∨ q = 26) →
      Arm.r (.GPR (rnum q)) t2.1 = 0 := by
    intro q hv hq
    have hs := hstr.store (.reg (.x q)) (fun r h => by cases h; rcases hq with rfl | rfl <;> rfl)
      trivial
    rw [hv] at hs
    have := congrArg lo64 hs
    simp only [locVal, lo64_regVal_x] at this
    exact this.symm.trans (by simp [lo64])
  have hx25 : movesM spillC m' (.reg (.x 25)) = regVal w₀C1 (.x 0) := by
    simp [movesM, spillC, Backend.Proof.upd, hm0]
  have hx26 : movesM spillC m' (.reg (.x 26)) = regVal w₀C1 (.x 1) := by
    simp [movesM, spillC, Backend.Proof.upd, hm1]
  have hz0 : regVal w₀C1 (.x 0) = 0 := by
    rw [E2E.regVal_bodyOf _ _ (by decide), shapeC1.2.2.2.2.2.1]
  have hz1 : regVal w₀C1 (.x 1) = 0 := by
    rw [E2E.regVal_bodyOf _ _ (by decide), shapeC1.2.2.2.2.2.2.1]
  have h25 : Arm.r (.GPR 25#5) t2.1 = 0 := hreg 25 (hx25.trans hz0) (.inl rfl)
  have h26 : Arm.r (.GPR 26#5) t2.1 = 0 := hreg 26 (hx26.trans hz1) (.inr rfl)
  have hmem : Arm.read_mem_bytes (CTy.int 64).bytes (Arm.r (.GPR 25#5) t2.1) t2.1 =
      (Arm.r (.GPR 26#5) t2.1).setWidth ((CTy.int 64).bytes * 8) := by
    rw [h25, h26]
    show Arm.read_mem_bytes 8 0 t2.1 = (0 : BitVec 64).setWidth 64
    rw [read_mem_bytes_sameWorld hstr.world (fun k hk => by
      have := notF_lowC1 k hk; simpa using this), shapeC1.2.2.2.2.2.2.2.2.1]
    rfl
  obtain ⟨v, t3, r3⟩ := cas_fwd wfRC1 LoopWitness.hty64 hdrop hprog hpc herr hmem t2.2
  have hr := PRun.append (PRun.append r1 r2) r3
  have hevP : ∀ l ∈ ls1 ++ ls2, ∀ e' ∈ l.evs,
      PrivA RAC1 e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR) := by
    intro l hl e' he'
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨hF, hK⟩ := hev1 l hl e' he'
      exact ⟨privA_addr.2 hF, .inl (by simpa using hK)⟩
    · obtain ⟨hF, hK⟩ := hev2 l hl e' he'
      exact ⟨privA_addr.2 hF, by simpa using hK⟩
  -- the bytes the `ldaxr` reads: those of the world at 0, zeros
  have hval : (convEv (loopRd (CTy.int 64) t2.1 t2.1)).val = List.replicate 8 (some 0#8) := by
    show bytesOf 8 (ArmFoot.readM 8 (Arm.r (.GPR 25#5) t2.1) t2.1.mem) = _
    rw [h25]
    refine bytesOf_readM_zero fun k hk => ?_
    rw [hstr.world.2.1 _ (notF_lowC1 k hk)]
    exact shapeC1.2.2.2.2.2.2.2.2.2 k hk
  exact ⟨n', ls1 ++ ls2, _, _, _, fun env p => compiled_ofC1 hq hA env p, hr, rfl, rfl, h25, h25,
    rfl, rfl, hval, hevP⟩

/-! ## The read value -/

theorem bodyC1 : ∃ st rest, csC1.frame.body = st :: rest ∧ st.inst = .atomicCas .i64 {} 0 1 2 := by
  have h : csC1.frame.body.head?.map (·.inst) = some (.atomicCas .i64 {} 0 1 2) := by
    native_decide
  revert h
  cases csC1.frame.body with
  | nil => intro h; cases h
  | cons st rest => intro h; exact ⟨st, rest, rfl, by simpa using h⟩

theorem shapeC1' : evShape csC1 = [[(.scR, 8)], [(.scR, 8), (.scW, 8)]] := by
  obtain ⟨st, rest, hb, hi⟩ := bodyC1
  simp only [evShape, hb, hi]
  rfl

theorem regC1_0 : csC1.frame.regs 0 = some ⟨.i64, 0⟩ := by native_decide

theorem getC1 : ∃ ev v, csC1.frame.getAs 1 .i64 = .ok ev ∧ csC1.frame.getAs 2 .i64 = .ok v := by
  have h : (match csC1.frame.getAs 1 .i64, csC1.frame.getAs 2 .i64 with
      | .ok _, .ok _ => true | _, _ => false) = true := by
    native_decide
  revert h
  cases csC1.frame.getAs 1 .i64 <;> cases csC1.frame.getAs 2 .i64 <;> intro h <;>
    first | exact ⟨_, _, rfl, rfl⟩ | cases h

theorem loadC1 : ∃ old, (withBytes csC1 (fun _ => some 0)).mem.load {} (Clif.effAddr ⟨.i64, 0⟩ 0)
    Clif.Ty.i64.bytes Clif.Ty.i64.width = .ok old := by
  have h : (match (withBytes csC1 (fun _ => some 0)).mem.load {} (Clif.effAddr ⟨.i64, 0⟩ 0)
      Clif.Ty.i64.bytes Clif.Ty.i64.width with | .ok _ => true | _ => false) = true := by
    native_decide
  revert h
  cases (withBytes csC1 (fun _ => some 0)).mem.load {} (Clif.effAddr ⟨.i64, 0⟩ 0)
    Clif.Ty.i64.bytes Clif.Ty.i64.width with
  | ok v => intro _; exact ⟨v, rfl⟩
  | _ => intro h; cases h

theorem stepC1 : (match Clif.step default default (withBytes csC1 (fun _ => some 0)) with
    | .next _ => true | _ => false) = true := by native_decide

/-- The bytes `0` everywhere. -/
def B0 : Bytes := fun _ => some 0#8

/-- **On the zero bytes, the step of `csC1` stores `1`** (as a check). -/
theorem stepZ : (match res (Clif.step default default (withBytes csC1 B0)) with
    | some (_, B) => decide (B 0 = some 1#8) | none => false) = true := by native_decide

/-- The CLIF thread's step is the same in every environment and program. -/
theorem step_envC1 (env : Clif.Env) (p : Clif.Program) (B : Bytes) :
    Clif.step env p (withBytes csC1 B) = Clif.step default default (withBytes csC1 B) := by
  obtain ⟨st, rest, hb, hi⟩ := bodyC1
  have hb' : (withBytes csC1 B).frame.body = st :: rest := hb
  have hc : ∀ fn args, st.inst ≠ .call fn args := fun _ _ h => by rw [hi] at h; cases h
  have hci : ∀ sig callee args, st.inst ≠ .callIndirect sig callee args :=
    fun _ _ _ h => by rw [hi] at h; cases h
  rw [Clif.step_inst env p _ st rest hb' hc hci, Clif.step_inst default default _ st rest hb' hc hci]

/-- **The CLIF thread from `csC1` steps** (its `atomic_cas`). -/
theorem cstep_csC1 (env : Clif.Env) (p : Clif.Program) :
    ∃ evs t', CStep env p (.run csC1) evs t' := by
  obtain ⟨st, rest, hb, hi⟩ := bodyC1
  obtain ⟨ev, v, hev, hv⟩ := getC1
  obtain ⟨old, hold⟩ := loadC1
  have hb' : (withBytes csC1 (fun _ => some 0)).frame.body = st :: rest := hb
  obtain ⟨s', hs⟩ := step_next_of_check (env := env) (p := p) hb'
    (fun _ _ h => by rw [hi] at h; cases h) (fun _ _ _ h => by rw [hi] at h; cases h) default
    default stepC1
  exact ⟨_, _, ClifCStep.cstep_atomicCas hb' hi regC1_0 hev hv hold hs⟩

/-- The `atomic_cas` of `csC1` is on writable data (as a check). -/
theorem notRO_C1 : (match csC1.frame.body with
    | stm :: _ => (match IselClif.access csC1.frame stm.inst with
      | some (a, n) => csC1.mem.readonlyAt a n
      | none => false)
    | [] => false) = false := by native_decide

theorem notStop_csC1 (env : Clif.Env) (p : Clif.Program) : ¬ Stop env p (.run csC1) := by
  obtain ⟨evs, t', hs⟩ := cstep_csC1 env p
  rintro (hd | ⟨s, stm, rest, ty, fl, pp, ex, x, a, n, he, hb, -, hacc, hro⟩)
  · exact hd ⟨evs, t', hs⟩
  · cases he
    have h := notRO_C1
    rw [hb] at h
    simp only [hacc] at h
    rw [hro] at h
    cases h

/-- **The read value**: a CLIF step of `csC1` starts with a non-fence event, and when that read
has the bytes `0` (the expected value), the step has a second, non-fence event: with the read
alone the step would leave the bytes, but it stores `1`. -/
theorem cstep_rd (env : Clif.Env) (p : Clif.Program) {evs : List (Prog.Ev SKind BVal)}
    {t' : TState} (hs : CStep env p (.run csC1) evs t') :
    ∃ h0 : 0 < evs.length, evs[0].dir ≠ .F ∧
      (evs[0].val = List.replicate 8 (some 0#8) → ∃ hl : 1 < evs.length, evs[1].dir ≠ .F) := by
  obtain ⟨⟨hm, hd⟩, -, hall⟩ := hs
  rw [shapeC1'] at hm
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
  rcases hm with hm | hm
  · obtain ⟨x, rfl⟩ : ∃ x, evs = [x] := by
      rcases evs with _ | ⟨x, _ | ⟨y, rest⟩⟩ <;> simp at hm
      exact ⟨x, rfl⟩
    simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at hm
    have hxd : x.dir = .R := by rw [(hd x (by simp)).1, hm.1]; rfl
    refine ⟨by simp, by simp [hxd], fun hv => ?_⟩
    exfalso
    simp only [List.getElem_cons_zero] at hv
    have hag : Agrees bytesI B0 [x] := by
      refine ⟨fun _ => ?_, trivial⟩
      rw [hv, hm.2]
      simp [bytesI, getB, B0, List.map_const']
    obtain ⟨t'', hres, -⟩ := hall _ hag
    rw [step_envC1] at hres
    have hap : applyEvs bytesI B0 [x] = B0 := by
      simp [applyEvs, Prog.write1, hxd]
    rw [hap] at hres
    have h := stepZ
    rw [hres] at h
    simp [B0] at h
  · obtain ⟨x, y, rfl⟩ : ∃ x y, evs = [x, y] := by
      rcases evs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> simp at hm
      exact ⟨x, y, rfl⟩
    simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at hm
    refine ⟨by simp, ?_, fun _ => ⟨by simp, ?_⟩⟩
    · simp only [List.getElem_cons_zero]; rw [(hd x (by simp)).1, hm.1.1]; decide
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero]
      rw [(hd y (by simp)).1, hm.2.1]; decide

/-! ## The whole run -/

/-- **A covering prefix of a private run ending in an exclusive pair is the whole run** when the
CLIF thread cannot stop at its start and its first step starts with a non-fence event that, when
it reads the bytes of the pair's read, is followed by a second non-fence event: in a strict
prefix the one shared event is the read, and `Refines` carries its value. -/
theorem pair_full_rd {env : Clif.Env} {p : Clif.Program} {RA : RL} {cs : Clif.State}
    {lsP : List Lab} {eR eW : Ev} {M k : Nat} (hcov : Covers env p RA cs (pairLs lsP eR eW M) k)
    (hk : k ≤ (pairLs lsP eR eW M).length)
    (hevP : ∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RA e'.addr.toNat) (hgo : ¬ Stop env p (.run cs))
    (hrd : ∀ evs t', CStep env p (.run cs) evs t' → ∃ h0 : 0 < evs.length, evs[0].dir ≠ .F ∧
      (evs[0].val = (convEv eR).val → ∃ hl : 1 < evs.length, evs[1].dir ≠ .F)) :
    k = (pairLs lsP eR eW M).length := by
  rcases hcov with h | ⟨trS, st, ψ, h0, hst, href, hstop⟩
  · exact h
  refine Classical.byContradiction fun hne => ?_
  have hk' : k < (pairLs lsP eR eW M).length := by omega
  cases trS with
  | nil => exact hgo (by simpa [h0] using hstop)
  | cons evs rest =>
    have hs := hst 0 (by simp)
    simp only [List.getElem_cons_zero, h0] at hs
    have hat : ∀ i (hi : i < evs.length), evAt (evs :: rest) (0, i) = some evs[i] := fun i hi =>
      evAt_of (by simp) (by simpa using hi)
    have hpos : ∀ i (hi : i < evs.length), evs[i].dir ≠ .F →
        ψ (0, i) = (lsP.length, 0) ∧ evs[i].val = (convEv eR).val := by
      intro i hi hF
      obtain ⟨y, hy, -, -, hly, -, hvy⟩ := href.ev _ _ (hat i hi)
      have hnp := href.shared _ _ (hat i hi) hF
      rw [evAt_conv] at hy
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy
      have hlt : (ψ (0, i)).1 < k := by
        obtain ⟨h1, -⟩ := evAt_isSome (show (evAt (evTr ((pairLs lsP eR eW M).take k))
          ((ψ (0, i)).1, (ψ (0, i)).2)).isSome from by rw [hx]; rfl)
        simp [evTr] at h1; omega
      have hx' := evAt_take_some hx
      by_cases hq : (ψ (0, i)).1 < lsP.length
      · obtain ⟨l, hl', hxl⟩ := posP (j := (ψ (0, i)).1) (kk := (ψ (0, i)).2) hx' hq
        exact absurd (by rw [← hly]; exact hevP l hl' x hxl) hnp
      · rcases posE (j := (ψ (0, i)).1) (kk := (ψ (0, i)).2) hx' (by omega) with
          ⟨e1, e2, rfl⟩ | ⟨e1, -, -⟩
        · exact ⟨Prod.ext e1 e2, hvy.symm⟩
        · simp at hk'; omega
    obtain ⟨h0', hF0, h1⟩ := hrd evs _ hs
    obtain ⟨hp0, hv0⟩ := hpos 0 h0' hF0
    obtain ⟨hl, hF1⟩ := h1 hv0
    obtain ⟨hp1, -⟩ := hpos 1 hl hF1
    have := href.inj (by rw [hat 0 h0']; rfl) (by rw [hat 1 hl]; rfl) (hp0.trans hp1.symm)
    simp at this

/-- **`Realizes` on the compiled `atomic_cas` storing a new value, on the whole run** (module
doc): the run of `run_cas1` (the `ldaxr` reads `0`, the expected value); every execution of all of
it (its `rmw` the run's monitor pairs, which relate the `ldaxr`'s read to the `stlxr`'s write,
`rmw_full`) is `Realizes`d by a CLIF thread from `csC1` (`realizes_pair_cov`, `pair_full_rd` with
the read value `cstep_rd`). -/
theorem realizes_cas_full : ∃ (n : Nat) (lsP : List Lab) (eR eW : Ev) (t' : ArmState × Mon),
    PRun Policy.arm RAC1.step (OkPriv RAC1) (iterN RAC1.step n RAC1.s0, none) (pairLs lsP eR eW 2) t' ∧
    eR.k = .acqXR ∧ eW.k = .relXW ∧ eR.addr = 0 ∧ eW.addr = 0 ∧ eR.n = 8 ∧ eW.n = 8 ∧
    (convEv eR).val = List.replicate 8 (some 0#8) ∧
    (∀ l ∈ lsP, ∀ e' ∈ l.evs, PrivA RAC1 e'.addr.toNat ∧ (e'.k = .plainW ∨ e'.k = .plainR)) ∧
    rmwP (pairLs lsP eR eW 2) (pairLs lsP eR eW 2).length (.thr 0 lsP.length 0)
      (.thr 0 (lsP.length + 2 + 1) 0) ∧
    ∀ (env : Clif.Env) (p : Clif.Program) (M0 : Bytes),
      ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧ PC.st 0 0 = .run csC1 ∧
        PC.Runs (CStep env p) ∧
        Realizes (PA1 RAC1 (iterN RAC1.step n RAC1.s0) (pairLs lsP eR eW 2)
            (pairLs lsP eR eW 2).length) (locs1 lsP eR) M0
          (latestW (PA1 RAC1 (iterN RAC1.step n RAC1.s0) (pairLs lsP eR eW 2)
            (pairLs lsP eR eW 2).length) (locs1 lsP eR))
          (coL (PA1 RAC1 (iterN RAC1.step n RAC1.s0) (pairLs lsP eR eW 2)
            (pairLs lsP eR eW 2).length) (locs1 lsP eR))
          (rmwP (pairLs lsP eR eW 2) (pairLs lsP eR eW 2).length) PC [(eR.addr.toNat, eR.n)] M0
          φ (fun _ _ _ => True) := by
  obtain ⟨n, lsP, eR, eW, t', hc, hr, hkR, hkW, haR, haW, hnR, hnW, hval, hevP⟩ := run_cas1
  refine ⟨n, lsP, eR, eW, t', hr, hkR, hkW, haR, haW, hnR, hnW, hval, hevP,
    rmw_full hkR hkW fun l hl e he => (hevP l hl e he).2, fun env p M0 => ?_⟩
  obtain ⟨k, hk, hcv, h⟩ := realizes_pair_cov hc hr hevP hkR hkW (haW.trans haR.symm)
    (hnW.trans hnR.symm) env p M0
  obtain rfl := pair_full_rd hcv hk (fun l hl e' he' => (hevP l hl e' he').1) (notStop_csC1 env p)
    fun evs t' hs => by
      obtain ⟨h0, hF, h1⟩ := cstep_rd env p hs
      exact ⟨h0, hF, fun hv => h1 (hv.trans hval)⟩
  exact h

/-- **Non-vacuity of `thread_compiledLS_fullR`** on the compiled `atomic_cas` entered with x2 = 1:
from the body entry after its prologue, every precise run is realized on a prefix that is the
whole run or ends where the CLIF thread stops; where it has returned, the prefix is the whole run
or reaches a state related to the allocated code's end. -/
theorem thread_cas1_fullR (env : Clif.Env) (p : Clif.Program) : ∃ n, ∀ (mon : Mon) (ls : List Lab)
    (t' : ArmState × Mon),
    PRun Policy.arm RAC1.step (OkPriv RAC1) (iterN RAC1.step n RAC1.s0, mon) ls t' →
    ∃ (k : Nat) (trS : List (List (Ev SKind BVal))) (st : Nat → TState) (ψ : Nat × Nat → Nat × Nat),
      k ≤ ls.length ∧ st 0 = .run csC1 ∧
      (∀ j (h : j < trS.length), CStep env p (st j) trS[j] (st (j + 1))) ∧
      Refines Maps (PrivA RAC1) (MonPair (evTr (ls.take k))) trS (conv (evTr (ls.take k))) ψ ∧
      (k = ls.length ∨ Stop env p (st trS.length)) ∧
      ∀ v, st trS.length = .ret v → k = ls.length ∨
        ∃ tE cE, PRun Policy.arm RAC1.step (OkPriv RAC1) (iterN RAC1.step n RAC1.s0, mon)
          (ls.take k) tE ∧ RelQ RAC1 tE cE ∧ Done RAC1 cE := by
  obtain ⟨n, hq, hA⟩ := qRC1
  exact ⟨n, fun mon ls t' hr => thread_compiledLS_fullR (compiled_ofC1 hq hA env p) hr⟩

end Concurrency.RealizeCompiled.WitnessC1
